module Color : sig
  val enable : bool -> unit

  type 'a fmt = (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit

  val pp_bold : 'a fmt
  val pp_red : 'a fmt
  val pp_yellow : 'a fmt
  val pp_blue : 'a fmt
  val pp_purple : 'a fmt
end = struct
  type 'a fmt = (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit

  let enabled =
    match Sys.getenv_opt "TERM" with
    | Some "dumb" | Some "" | None -> false
    | Some _ -> Out_channel.isatty stderr
  ;;

  let enabled = ref enabled
  let enable flag = enabled := flag
  let wrap l r f ppf x = if !enabled then Format.fprintf ppf "%s%a%s" l f x r else f ppf x
  let pp_bold ppf = wrap "\027[1m" "\027[0m" ppf
  let pp_red ppf = wrap "\027[31m" "\027[0m" ppf
  let pp_yellow ppf = wrap "\027[33m" "\027[0m" ppf
  let pp_blue ppf = wrap "\027[34m" "\027[0m" ppf
  let pp_purple ppf = wrap "\027[35m" "\027[0m" ppf
end

type severity =
  | Error
  | Warning
  | Info
  | Bug

type t =
  { severity : severity
  ; message : string
  ; span : (Lexing.position * Lexing.position) option
  }

type diagnostic = t

let make ?span severity message = { span; severity; message }
let error ?span fmt = Format.kasprintf (make ?span Error) fmt
let warning ?span fmt = Format.kasprintf (make ?span Warning) fmt
let info ?span fmt = Format.kasprintf (make ?span Info) fmt
let bug ?span fmt = Format.kasprintf (make ?span Bug) fmt

module Error = struct
  exception Error of diagnostic

  let raise ?span severity message = raise (Error (make ?span severity message))
  let error ?span fmt = Format.kasprintf (raise ?span Error) fmt
  let warning ?span fmt = Format.kasprintf (raise ?span Warning) fmt
  let info ?span fmt = Format.kasprintf (raise ?span Info) fmt
  let bug ?span fmt = Format.kasprintf (raise ?span Bug) fmt
end

let read file =
  match open_in file |> In_channel.input_all with
  | contents -> Some contents
  | exception Sys_error _ -> None
;;

let pp ?(read = read) ppf diag =
  let open Lexing in
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
    | f, l1, l2, _, _ when l1 != l2 ->
      Format.fprintf ppf "File \"%s\", lines %d-%d:\n" f l1 l2
    | f, l, _, c1, c2 when c1 + 1 < c2 ->
      Format.fprintf ppf "File \"%s\", line %d, characters %d-%d:\n" f l (c1 + 1) c2
    | f, l, _, _, c2 -> Format.fprintf ppf "File \"%s\", line %d, character %d:\n" f l c2
  and pp_snippet pp_mark ppf (source, p1, p2) =
    let pp_line w ppf = function
      | no, line, Some (ml, mr) when mr > ml && String.trim line <> "" ->
        let ml, mr = shorten ml mr line in
        let mark = String.make (mr - ml) '^' in
        let pp = Format.fprintf ppf "%*d | %s\n%*s | %*s%a\n" in
        pp w no line w "" ml "" (pp_mark Format.pp_print_string) mark
      | no, line, _ -> Format.fprintf ppf "%*d | %s\n" w no line
    in
    let f w i line =
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
    List.iteri (f (width (min (p2.pos_lnum + 3) (List.length lines)))) lines
  in
  let pp_severity, severity =
    match diag.severity with
    | Error -> Color.pp_red, "Error"
    | Warning -> Color.pp_yellow, "Warning"
    | Info -> Color.pp_blue, "Info"
    | Bug -> Color.pp_purple, "Bug"
  in
  let source =
    match diag.span with
    | None -> None
    | Some (p1, p2) -> read p1.pos_fname |> Option.map (fun s -> s, p1, p2)
  in
  let pp = Format.fprintf ppf "%a%a%a: %s\n" in
  let pp = pp (Color.pp_bold (Format.pp_print_option pp_span)) diag.span in
  let pp = pp (Format.pp_print_option (pp_snippet pp_severity)) source in
  let pp = pp (pp_severity Format.pp_print_string) severity in
  pp diag.message
;;
