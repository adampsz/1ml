type meta =
  { prelude : string
  ; skip : bool
  }

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
  let rec aux acc line =
    match words line with
    | [ "(*"; "@prelude"; "*)" ] -> { acc with prelude = "/dev/null" }
    | [ "(*"; "@prelude"; prelude; "*)" ] ->
      { acc with prelude = Filename.concat (Filename.dirname file) prelude }
    | [ "(*"; "@skip"; "*)" ] -> { acc with skip = true }
    | _ -> acc
  in
  let meta = { prelude = "./prelude.1ml"; skip = false } in
  In_channel.fold_lines aux meta (In_channel.open_text file)
;;

let run cmd file =
  match parse file with
  | { skip = true; _ } -> 0
  | { prelude; _ } ->
    let args = [ "--f-omega"; "--prelude"; prelude; file ] in
    Sys.command (Filename.quote_command cmd args)
;;

let _ = exit (run Sys.argv.(1) Sys.argv.(2))
