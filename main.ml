open Calc

let main () =
  let src = ref "" in
  let usage = "Usage run <file>" in
  let spec = [] in
  let _ = Arg.parse spec (
    fun x -> if Sys.file_exists x then src := x else raise (Arg.Bad (x ^ ": No file given"))
  ) usage in
  if !src = "" then Arg.usage spec usage
  else
  let file_channel = open_in !src in
  let lexbuf = Lexing.from_channel file_channel in
  let exp = Parser.file Lexer.start lexbuf in
  try
    print_endline "==== expression ====";
    ignore (Sys.command ("cat " ^ !src));
    print_newline (); print_newline ();
    print_endline "====== result ======";
    print_endline (val2str (calc exp))
  with Lexer.LexicalError -> print_endline (!src ^ ": Lexical Error")

let _ = main ()
