open Calc
open Simplify
open Util
open Solve


let prog : program -> unit
= fun p1 ->
  let _ = init_partial () in
  let _ = init_sym_cnt () in 
  let r1 = eval_exp p1 empty_env TRUE TRUE TRUE in
  (*let rv1 = list_simplify !partial_correct in*)
  let ctx = Z3_translator.new_ctx () in
  let solver = Z3.Solver.mk_solver ctx None in

  let _ = match Solve.solve ctx solver !partial_correct with
  | true -> print_endline ("Partial Correct")
  | false -> print_endline ("Partial Fail")

  in let _ = init_total() in
  let ctx = Z3_translator.new_ctx () in
  let solver = Z3.Solver.mk_solver ctx None in

  match Solve.total_solve ctx solver !total_correct with
  | true -> print_endline ("Total Correct")
  | false -> print_endline ("Total Fail")

let run : program -> unit
= fun pgm ->
  let rec print_aux : (value * path_cond * env) list -> int -> unit
  = fun l cnt ->
    match l with
    | [] -> print_newline ()
    | (v, pi, _)::tl ->
            print_endline ("<" ^ string_of_int cnt ^ ">");
            print_endline ("path condition: " ^ cond2str ((simplify_path (pi))));
            print_endline ("value: " ^ value2str (simplify_val (v)));
            print_newline ();
            print_aux tl (cnt + 1)
    in let r = eval_exp pgm empty_env TRUE TRUE TRUE in print_aux !partial_correct 1
    

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
  let exp = Parser.program Lexer.start lexbuf in
  try
    print_endline "==== expression ====";
    ignore (Sys.command ("cat " ^ !src));
    print_newline (); print_newline ();
    print_endline "====== result ======";
    run exp;
    prog exp;
    
    
  with Lexer.LexicalError -> print_endline (!src ^ ": Lexical Error")

let _ = main ()
