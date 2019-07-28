open Calc
open Z3.Expr
open Z3_translator

let simplify_val : value -> value
= fun v ->
  match v with
  | _ -> let expr = val2expr v in let expr = simplify expr None in expr2val expr

let simplify_path : path_cond -> path_cond
= fun p -> let expr = path2expr p in let expr = simplify expr None in expr2path expr

let rec list_simplify : (value * path_cond) list -> (value * path_cond) list
= fun l ->
  match l with
  | [] -> []
  | (v, p)::tl -> (simplify_val (v), simplify_path (p))::(list_simplify tl)