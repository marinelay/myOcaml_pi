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

let rec solve : context -> solver -> (value * path_cond) list -> bool
= fun ctx solver l1 ->
  let r = Z3_translator.mk_const ctx "return" (Z3_translator.int_sort ctx) in
  let rec fold f l a=
    match l with
    | [] -> a
    | hd::tl -> f hd (fold f tl a)
    in let expr = fold (
      fun tup rst ->
      let (v, pi) = tup in
      let eq_value = Z3_translator.eq ctx r (val2expr_aux ctx v) in (* ?? *)
      let exp_pi = path2expr_aux ctx pi in
      let exp = Z3_translator.and_b ctx eq_value exp_pi in
      Z3_translator.or_b ctx exp rst
    ) l1 (Z3_translator.const_b ctx false) in
    let _ = Z3.Solver.add solver [expr] in
    match (check solver []) with
    | UNSATISFIABLE -> true
    | _ -> false