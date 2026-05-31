type meta =
  { prelude : string
  ; skip : bool
  }

let filename_join base path =
  if Filename.is_relative path then Filename.concat base path else path
;;

let is_space = function
  | ' ' | '\012' | '\n' | '\r' | '\t' -> true
  | _ -> false
;;

let words s =
  let rec auxl = function
    | i when i >= String.length s -> []
    | i when is_space s.[i] -> auxl (i + 1)
    | i -> auxr i (i + 1)
  and auxr i = function
    | j when j >= String.length s || is_space s.[j] -> String.sub s i (j - i) :: auxl j
    | j -> auxr i (j + 1)
  in
  auxl 0
;;

let parse file =
  let aux acc line =
    match words line with
    | [ "(*"; "@prelude"; "*)" ] -> { acc with prelude = Filename.null }
    | [ "(*"; "@prelude"; prelude; "*)" ] -> { acc with prelude }
    | [ "(*"; "@skip"; "*)" ] -> { acc with skip = true }
    | _ -> acc
  in
  let prelude = filename_join (Sys.getcwd ()) "prelude.1ml" in
  let meta = { prelude; skip = false } in
  In_channel.fold_lines aux meta (In_channel.open_text file)
;;

let run cmd file =
  match parse file with
  | { skip = true; _ } -> 0
  | { prelude; _ } ->
    let prelude = filename_join (Filename.dirname file) prelude in
    let args = [ "--f-omega"; "--prelude"; prelude; file ] in
    Sys.command (Filename.quote_command cmd args)
;;

let _ = exit (run Sys.argv.(1) Sys.argv.(2))
