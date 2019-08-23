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

let rec total_solve : context -> solver -> (value list * path_cond) list -> bool
= fun ctx solver l1 ->
  
  let rec solve l1 =

    match l1 with
    
    | hd1::hd2::tl -> 
      let rec compare hd1 hd2 =
        (match hd1, hd2 with
        | ([], _), ([], _) -> false
        | (hd1::tl1, pi1), (hd2::tl2, pi2) ->

          let formula = eq ctx (val2expr_aux ctx hd1) (val2expr_aux ctx hd2) in
          let formula = and_b ctx (path2expr_aux ctx pi2) formula in
          let result = Expr.simplify formula None in
          let _ = Z3.Solver.add solver [result] in
          print_endline(Z3.Solver.to_string solver);
          (match (check solver []) with
            | UNSATISFIABLE ->
              let _ = Z3.Solver.reset solver in
              let formula = lt ctx (val2expr hd1) (val2expr hd2) in
              let formula = and_b ctx (path2expr_aux ctx pi2) formula in
              let result = Expr.simplify formula None in
              let _ = Z3.Solver.add solver [result] in
              (match (check solver []) with
                | UNSATISFIABLE -> false
                | _ -> true
              )
            | _ -> compare (tl1, pi1) (tl2, pi2)    
          )
        ) in let result = (compare hd1 hd2) in
        if result then (solve (hd2::tl)) else raise(Failure "Total is Fail")
    | hd::tl -> true   
    | [] -> raise(Failure"?")
  in solve l1 
      

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

      print_endline("---- expression ----");
      print_endline(Expr.to_string (Expr.simplify exp_pi None));
      print_endline("--------------------");

      let not_exp_pi = not_b ctx exp_pi in
      
      (*let exp = Z3_translator.and_b ctx eq_value exp_pi in*)
      let a1 = Z3.Boolean.mk_true ctx in 
      let result = eq ctx not_exp_pi a1 in
      let result = Expr.simplify result None in

      

      let _ = Z3.Solver.add solver [result] in
      let partial = (match (check solver []) with
      
      | UNSATISFIABLE -> true
      | UNKNOWN -> raise(Failure "?")
      | _ ->       
      (match Z3.Solver.get_model solver with
        | Some m -> print_endline (Z3.Model.to_string m); false
        | _ -> raise (Failure "never happen"))
      ) in
      print_endline(string_of_bool partial);
      (*Z3_translator.and_b ctx (path2expr_aux ctx partial) rst*)
      partial && rst
    ) l1 (Z3_translator.const_b ctx true) in
    (*let expr = Z3_translator.not_b ctx expr in*)
    (*let _ = Z3.Solver.add solver [expr] in
    match (check solver []) with
    | UNSATISFIABLE -> true
    | _ -> false*)
    expr