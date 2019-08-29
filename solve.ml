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

let rec total_solve : context -> solver -> (value list * value list * path_cond) list -> bool
= fun ctx solver l1 ->

  print_endline("Check Total Correctness");

  let num = 1 in
  let rec solve : (value list * value list * path_cond) list -> int -> bool =
  fun l1 num ->
  (match l1 with
  | [] -> true
  | hd::tl ->
    
    let rec compare : (value list * value list * path_cond) -> int -> bool =
      (fun l1 num ->
        (match l1 with
          | ([], [], _) -> true
          | (hd1::tl1, hd2::tl2, pi) ->
            let _ = Z3.Solver.reset solver in
            let formula = eq ctx (val2expr_aux ctx hd1) (val2expr_aux ctx hd2) in
            let formula = imply ctx (path2expr_aux ctx pi) formula in
            let formula = not_b ctx formula in
            let result = Expr.simplify formula None in
            let _ = Z3.Solver.add solver [result] in
            (match (check solver []) with
              | UNSATISFIABLE -> compare (tl1, tl2, pi) num
                
              | _ -> 
                let _ = Z3.Solver.reset solver in
                let formula1 = gt ctx (val2expr_aux ctx hd1) (val2expr_aux ctx hd2) in
                let formula2 = imply ctx (path2expr_aux ctx pi) formula1 in
                let formula = not_b ctx formula2 in
                let result = Expr.simplify formula None in
                let _ = Z3.Solver.add solver [result] in
                (match (check solver []) with
                  | UNSATISFIABLE -> true
                  | _ -> print_endline(Expr.to_string (Expr.simplify formula2 None)); false
                )
            )
        )
      ) in let result = compare hd num in 
      print_endline("[" ^ string_of_int num ^"] : " ^ string_of_bool result); solve tl (num+1) && result
  ) in solve l1 num

let rec solve : context -> solver -> (value * path_cond * env) list -> bool
= fun ctx solver l1 ->
  print_endline("Check Partial Correctness");
  let rec solve : (value * path_cond * env) list -> int -> bool 
  = fun l1 n -> 
  (match l1 with
  | [] -> true
  | hd::tl ->
      let _ = Z3.Solver.reset solver in
      let (v, pi, env) = hd in
      let exp_pi = path2expr_aux ctx pi in
      let not_exp_pi = not_b ctx exp_pi in
      let a1 = Z3.Boolean.mk_true ctx in 
      let result = eq ctx not_exp_pi a1 in
      let result = Expr.simplify result None in

      

      let _ = Z3.Solver.add solver [result] in
      let partial = (match (check solver []) with
      
      | UNSATISFIABLE -> true
      | UNKNOWN -> raise(Failure "?")
      | _ -> print_endline(Expr.to_string (Expr.simplify exp_pi None)); false          
      ) in
      print_endline("[" ^ string_of_int n ^ "] : " ^ string_of_bool partial);
      solve tl (n+1) && partial 
    ) in solve l1 1
    