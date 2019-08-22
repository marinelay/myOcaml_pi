open Calc
open Z3_translator
open Z3
open Z3.Solver
open Z3.Expr
open Z3.Proof
open Z3enums


exception CannotCompare
exception ConvertFailure

let sat_check : path_cond -> bool
= fun pi ->
  let ctx = new_ctx() in
  let expr = path2expr_aux ctx pi in
  let solver = mk_solver ctx None in
  let _ = Z3.Solver.add solver [expr] in
  match (check solver []) with
  | UNSATISFIABLE -> false
  | UNKNOWN -> false
  | SATISFIABLE -> true
let rec solve : context -> solver -> (value * path_cond * env) list -> bool
= fun ctx solver l1 ->
  let r = Z3_translator.mk_const ctx "return" (Z3_translator.int_sort ctx) in
  let rec fold f l a=
    match l with
    | [] -> true
    | hd::tl -> f hd (fold f tl a)
    in let expr = fold (
      fun tup rst ->
      let _ = Z3.Solver.reset solver in
      let (v, pi, env) = tup in
      (*let eq_value = Z3_translator.eq ctx r (val2expr_aux ctx v) in (* ?? *)*)
      let exp_pi = path2expr_aux ctx pi in
      let not_exp_pi = not_b ctx exp_pi in
      let tmp = Expr.simplify not_exp_pi None in
      print_endline(Expr.to_string exp_pi);
      (*let exp = Z3_translator.and_b ctx eq_value exp_pi in*)
      let a1 = Z3.Boolean.mk_true ctx in 
      let result = eq ctx tmp a1 in
      let _ = Z3.Solver.add solver [result] in
      let partial = (match (check solver []) with
      
      | UNSATISFIABLE -> true
      | UNKNOWN -> raise(Failure "?")
      | _ ->       
      (match Z3.Solver.get_model solver with
        | Some m -> print_endline (Z3.Model.to_string m); false
        | _ -> raise (Failure "never happen"))
      ) in
      (*Z3_translator.and_b ctx (path2expr_aux ctx partial) rst*)
      print_endline(string_of_bool partial);
      partial && rst
    ) l1 (Z3_translator.const_b ctx true) in
    (*let expr = Z3_translator.not_b ctx expr in*)
    (*let _ = Z3.Solver.add solver [expr] in
    match (check solver []) with
    | UNSATISFIABLE -> true
    | _ -> false*)
    expr