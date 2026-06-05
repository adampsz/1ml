module Color : sig
  val enable : bool -> unit
  val wrap : Format.formatter -> Format.formatter
end = struct
  let enabled = ref false
  let enable flag = enabled := flag

  let code = function
    | "bold" -> "\027[1m"
    | "red" -> "\027[31m"
    | "yellow" -> "\027[33m"
    | "blue" -> "\027[34m"
    | "purple" -> "\027[35m"
    | "gray" -> "\027[90m"
    | _ -> ""
  ;;

  let topen stack = function
    | Format.String_tag t ->
      let code = List.hd !stack ^ code t in
      stack := code :: !stack;
      code
    | _ -> ""
  ;;

  let tclose stack = function
    | Format.String_tag _ ->
      stack := List.tl !stack;
      List.hd !stack
    | _ -> ""
  ;;

  let wrap ppf =
    match !enabled with
    | false -> ppf
    | true ->
      let st = ref [ "\027[0m" ]
      and fns = Format.pp_get_formatter_out_functions ppf ()
      and tfns = Format.pp_get_formatter_stag_functions ppf () in
      let tfns = { tfns with mark_open_stag = topen st; mark_close_stag = tclose st } in
      let ppf = Format.formatter_of_out_functions fns in
      Format.pp_set_formatter_stag_functions ppf tfns;
      Format.pp_set_mark_tags ppf true;
      ppf
  ;;
end

type severity =
  | Error
  | Warning
  | Info

type t =
  { severity : severity
  ; message : string
  ; span : (Lexing.position * Lexing.position) option
  ; cause : exn option
  }

type diagnostic = t

let make ?span ?cause severity message = { span; severity; message; cause }
let error ?span fmt = Format.kasprintf (make ?span Error) fmt
let warning ?span fmt = Format.kasprintf (make ?span Warning) fmt
let info ?span fmt = Format.kasprintf (make ?span Info) fmt

module Error = struct
  exception Error of diagnostic

  let raise ?span ?cause severity msg = raise (Error (make ?span ?cause severity msg))
  let error ?span ?cause fmt = Format.kasprintf (raise ?span ?cause Error) fmt
  let warning ?span ?cause fmt = Format.kasprintf (raise ?span ?cause Warning) fmt
  let info ?span ?cause fmt = Format.kasprintf (raise ?span ?cause Info) fmt
end

let severity { severity; _ } = severity
let message { message; _ } = message
let span { span; _ } = span
let cause { cause; _ } = cause

let pp ?(read = Fun.const None) ppf diag =
  let open Lexing in
  let open Format in
  let shorten ml mr line =
    let trim = String.trim line in
    let index = String.index line (String.get trim 0) in
    let ml, mr = max ml index, min mr (String.length trim + index) in
    ml, max mr (ml + 1)
  in
  let pp_span ppf (p1, p2) =
    assert (p1.pos_fname = p2.pos_fname);
    let col p = p.pos_cnum - p.pos_bol in
    match p1.pos_fname, p1.pos_lnum, p2.pos_lnum, col p1, col p2 with
    | f, l1, l2, _, _ when l1 <> l2 -> fprintf ppf "File \"%s\", lines %d-%d:\n" f l1 l2
    | f, l, _, c1, c2 when c1 + 1 < c2 ->
      fprintf ppf "File \"%s\", line %d, characters %d-%d:\n" f l (c1 + 1) c2
    | f, l, _, _, c2 -> fprintf ppf "File \"%s\", line %d, character %d:\n" f l c2
  and pp_snippet color ppf (source, p1, p2) =
    let pp_line w ppf = function
      | no, line, Some (ml, mr) when mr > ml && String.trim line <> "" ->
        let ml, mr = shorten ml mr line in
        let mark = String.make (mr - ml) '^' in
        let pp = fprintf ppf "@{<gray>%*d |@} %s\n@{<gray>%*s |@} %*s@{<%s>%s@}\n" in
        pp w no line w "" ml "" color mark
      | no, line, _ -> fprintf ppf "@{<gray>%*d |@} %s\n" w no line
    in
    let aux w i line =
      match i + 1, p1.pos_lnum, p2.pos_lnum with
      | lno, l1, l2 when lno < l1 - 3 || lno > l2 + 3 -> ()
      | lno, l1, l2 when lno < l1 || lno > l2 -> pp_line w ppf (lno, line, None)
      | lno, l1, l2 ->
        let ml = if lno = l1 then p1.pos_cnum - p1.pos_bol else 0
        and mr = if lno = l2 then p2.pos_cnum - p2.pos_bol else String.length line in
        pp_line w ppf (lno, line, Some (ml, mr))
    in
    let lines = String.split_on_char '\n' source in
    let width n = (float_of_int n |> log10 |> int_of_float) + 1 in
    List.iteri (aux (width (min (p2.pos_lnum + 3) (List.length lines)))) lines
  in
  let color_of = function
    | Error -> "red"
    | Warning -> "yellow"
    | Info -> "blue"
  in
  let label_of = function
    | Error -> "Error"
    | Warning -> "Warning"
    | Info -> "Info"
  in
  let source_of diag =
    match diag.span with
    | None -> None
    | Some (l, r) -> read l.pos_fname |> Option.map (fun s -> s, l, r)
  in
  let ppf = Color.wrap ppf in
  let pp_head ppf diag =
    let color, severity = color_of diag.severity, label_of diag.severity in
    let pp = fprintf ppf "@{<bold>%a@}%a@{<bold>@{<%s>%s@}@}: @{<bold>%s@}\n" in
    let pp = pp (pp_print_option pp_span) diag.span in
    let pp = pp (pp_print_option (pp_snippet color)) (source_of diag) in
    let pp = pp color severity in
    pp diag.message
  in
  pp_head ppf diag;
  let rec walk = function
    | Some (Error.Error cause) ->
      fprintf ppf "  %s\n" cause.message;
      walk cause.cause
    | Some exn -> fprintf ppf "  %s\n" (Printexc.to_string exn)
    | _ -> ()
  in
  walk diag.cause;
  pp_print_flush ppf ()
;;

let print ?read diag =
  pp ?read Format.err_formatter diag;
  Format.pp_print_flush Format.err_formatter ()
;;

let read path =
  match open_in path |> In_channel.input_all with
  | contents -> Some contents
  | exception Sys_error _ -> None
;;

let protect ?(read = read) f =
  try Some (f ()) with
  | Error.Error diag ->
    print ~read diag;
    Printexc.print_backtrace stderr;
    flush stderr;
    None
;;

let _ =
  let f = function
    | Error.Error err -> Some (Format.asprintf "%a" (pp ?read:None) err)
    | _ -> None
  in
  Printexc.register_printer f
;;
