
open Calc
open Str
open Util
open Z3
open Z3enums


let new_ctx () = mk_context []

(* sort *)
let int_sort ctx = Z3.Arithmetic.Integer.mk_sort ctx
let bool_sort ctx = Z3.Boolean.mk_sort ctx
let string_sort ctx = Z3.Seq.mk_string_sort ctx
(* sort Array *)
let arr_sort ctx = Z3.Z3Array.mk_sort ctx (int_sort ctx) (int_sort ctx)

(* var *)
let mk_symbol ctx str = Symbol.mk_string ctx str
let mk_const ctx str sort = Z3.Expr.mk_const_s ctx str sort
let const_n ctx n = Z3.Expr.mk_numeral_int ctx n (int_sort ctx)
let const_str ctx str = mk_const ctx str (string_sort ctx)
let const_b ctx b = Z3.Boolean.mk_val ctx b
(* var Array *)
let balance ctx str sort = Z3.Expr.mk_const_s ctx str sort (* mk_const랑 동일... *)
let balance_lower ctx arr_expr target_expr = Z3.Z3Array.mk_select ctx arr_expr target_expr
let balance_upper ctx arr_expr target_expr = Z3.Z3Array.mk_select ctx arr_expr target_expr

(* aop *)
let add ctx expr1 expr2 = Z3.Arithmetic.mk_add ctx [expr1; expr2]
let sub ctx expr1 expr2 = Z3.Arithmetic.mk_sub ctx [expr1; expr2]
let mul ctx expr1 expr2 = Z3.Arithmetic.mk_mul ctx [expr1; expr2]
let div ctx expr1 expr2 = Z3.Arithmetic.mk_div ctx expr1 expr2
let minus ctx expr = Z3.Arithmetic.mk_unary_minus ctx expr

(* bop *)
let and_b ctx expr1 expr2 = Z3.Boolean.mk_and ctx [expr1; expr2]
let or_b ctx expr1 expr2 = Z3.Boolean.mk_or ctx [expr1; expr2]
let lt ctx expr1 expr2 = Z3.Arithmetic.mk_lt ctx expr1 expr2
let gt ctx expr1 expr2 = Z3.Arithmetic.mk_gt ctx expr1 expr2
let le ctx expr1 expr2 = Z3.Arithmetic.mk_le ctx expr1 expr2
let ge ctx expr1 expr2 = Z3.Arithmetic.mk_ge ctx expr1 expr2
let not_b ctx expr = Z3.Boolean.mk_not ctx expr
let eq ctx expr1 expr2 = Z3.Boolean.mk_eq ctx expr1 expr2
let neq ctx expr1 expr2 = (not_b ctx (eq ctx expr1 expr2))

exception NotComputableValue

let rec val2expr_aux : context -> value -> Expr.expr
= fun ctx v ->
  match v with
  | Int n -> const_n ctx n
  | Bool b -> const_b ctx b
  | SInt id -> mk_const ctx ("alpha_" ^ string_of_int id) (int_sort ctx)
  | SBool id -> mk_const ctx ("beta_" ^ string_of_int id) (bool_sort ctx)
  | SArith (aop, v1, v2) ->
    (match aop with
    | SADD -> add ctx (val2expr_aux ctx v1) (val2expr_aux ctx v2)
    )
  | Sum l ->
    (
    match l with
    | [] -> val2expr_aux ctx (Int 0)
    | hd::tl -> add ctx (val2expr_aux ctx hd) (val2expr_aux ctx (Sum tl))
    )

let val2expr : value -> Expr.expr
= fun v -> val2expr_aux (new_ctx()) v

let rec expr2val : Expr.expr -> value
= fun expr -> 
  let op = FuncDecl.get_decl_kind (Expr.get_func_decl expr) in
  match op with
  | OP_ANUM -> (* int *)
    let str = Expr.to_string expr in
    let str = if Str.string_match (Str.regexp "(- ") str 0 then Str.replace_first (Str.regexp "(- ") "-" (Str.replace_first (Str.regexp ")") "" str) else str in
    let n = int_of_string (str) in Int n
  | OP_TRUE -> Bool true
  | OP_FALSE -> Bool false
  | OP_UNINTERPRETED -> (* symbol *)
    begin
      let str = Symbol.get_string (FuncDecl.get_name (Expr.get_func_decl expr)) in
      let l = Str.split (Str.regexp "_") str in
      match l with
      | [hd; tl] ->
        if hd = "alpha" then SInt (int_of_string tl)
        else if hd = "beta" then SBool (int_of_string tl)
        else raise (Failure "SHOULD NOT COME HERE")
      | _ -> raise (Failure "SHOULD NOT COME HERE")
    end
  | OP_ADD -> (* sum *)
    begin
      let n = Expr.get_num_args expr in
      if n = 2 then
      begin
        let [hd; tl] = Expr.get_args expr in
        SArith (SADD, expr2val hd, expr2val tl)
      end
      else if n > 2 then
      begin
        let l = Expr.get_args expr in
        Sum (map expr2val l)
      end
      else (* Expr.get_num_args < 2 *) raise (Failure "SHOULD NOT COME HERE")
    end

let rec path2expr_aux : context -> path_cond -> Expr.expr
= fun ctx p ->
  match p with
  | TRUE -> const_b ctx true
  | FALSE -> const_b ctx false
  | AND (p1, p2) -> and_b ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | OR (p1, p2) -> or_b ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | NOT p -> not_b ctx (path2expr_aux ctx p)
  | EQ (p1, p2) -> eq ctx (val2expr_aux ctx p1) (val2expr_aux ctx p2)
  | NOTEQ (p1, p2) -> neq ctx (val2expr_aux ctx p1) (val2expr_aux ctx p2)
  | LESSTHAN (p1, p2) -> lt ctx (val2expr_aux ctx p1) (val2expr_aux ctx p2)
  | LESSEQUAL (p1, p2) -> le ctx (val2expr_aux ctx p1) (val2expr_aux ctx p2)
  | GREATTHAN (p1, p2) -> gt ctx (val2expr_aux ctx p1) (val2expr_aux ctx p2)
  | GREATEQUAL (p1, p2) -> ge ctx (val2expr_aux ctx p1) (val2expr_aux ctx p2)

let path2expr : path_cond -> Expr.expr
= fun p -> path2expr_aux (new_ctx ()) p

let rec expr2path : Expr.expr -> path_cond
= fun expr ->
  let op = FuncDecl.get_decl_kind (Expr.get_func_decl expr) in
  match op with
  | OP_TRUE -> TRUE
  | OP_FALSE -> FALSE
  | OP_AND -> (* and *)
    begin
      let n = Expr.get_num_args expr in
      if n = 2 then
      begin
        let [hd; tl] = Expr.get_args expr in AND (expr2path hd, expr2path tl)
      end
      else if n > 2 then
      begin
        let l = Expr.get_args expr in ANDL (map expr2path l)
      end
      else (* Expr.get_num_args < 2 *) raise (Failure "SHOULD NOT COME HERE")
    end
  | OP_OR -> (* or *)
    begin
      let n = Expr.get_num_args expr in
      if n = 2 then
        let [hd; tl] = Expr.get_args expr in OR (expr2path hd, expr2path tl)
      else if n > 2 then
        let l = Expr.get_args expr in ANDL (map expr2path l)
      else (* Expr.get_num_args <  2 *) raise (Failure "SHOULD NOT COME HERE")
    end
  | OP_EQ -> (* equal *) let [hd; tl] = Expr.get_args expr in EQ (expr2val hd, expr2val tl)
  | OP_NOT -> let [e] = Expr.get_args expr in NOT (expr2path e)
  | OP_LE -> let [hd; tl] = Expr.get_args expr in LESSEQUAL (expr2val hd, expr2val tl)
  | OP_GE -> let [hd; tl] = Expr.get_args expr in GREATEQUAL (expr2val hd, expr2val tl)
  | OP_LT -> let [hd; tl] = Expr.get_args expr in LESSTHAN (expr2val hd, expr2val tl)
  | OP_GT -> let [hd; tl] = Expr.get_args expr in GREATTHAN (expr2val hd, expr2val tl)
  | _ -> raise (Failure "expr2path: Not Implemented")

let funcdecl2val : FuncDecl.func_decl -> value
= fun f ->
  let op = FuncDecl.get_decl_kind f in
  match op with
  | OP_UNINTERPRETED -> (* symbol *)
    begin
      let str = Symbol.get_string (FuncDecl.get_name f) in
      let l = Str.split (Str.regexp "_") str in
      match l with
      | ["return"] -> Return
      | [hd; tl] ->
        if hd = "alpha" then SInt (int_of_string tl)
        else if hd = "beta" then SBool (int_of_string tl)
        else raise (Failure "SHOULD NOT COME HERE")
      | _ -> raise (Failure "SHOULD NOT COME HERE")
    end
  | _ -> raise (Failure "funcdecl2eq: Not Implemented")