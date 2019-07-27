open Lang
open Z3
open Z3enums

let new_ctx () = mk_context []

(* sort *)
let int_sort ctx = Z3.Arithmetic.Integer.mk_sort ctx
let bool_sort ctx = Z3.Boolean.mk_sort ctx
let string_sort ctx = Z3.Seq.mk_string_sort ctx

(* var *)
let mk_symbol ctx str = Symbol.mk_string ctx str
let mk_const ctx str sort = Z3.Expr.mk_const_s ctx str sort
let const_n ctx n = Z3.Expr.mk_numeral_int ctx n (int_sort ctx)
let const_str ctx str = mk_const ctx str (string_sort ctx)
let const_b ctx b = Z3.Boolean.mk_val ctx b

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
  | Bool b -> const_n ctx b
  | SInt id -> mk_const ctx ("int_" ^ string_of_int id) (int_sort ctx)
  | SBool id -> mk_const ctx ("bool_" ^ string_of_int id) (bool_sort ctx)
  | SExp (aop, v1 v2) ->
    (match aop with
    | SADD -> add ctx (val2expr_aux ctx v1) (val2expr_aux ctx v2)
    )

let val2expr : value -> Expr.expr
= fun v -> val2expr_aux (new_ctx()) v

let rec path2expr_aux : context -> path_exp -> Expr.expr
= fun ctx p ->
  match p with
  | TRUE -> const_b ctx true
  | FALSE -> const_b ctx false
  | AND (p1, p2) -> and_b ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | OR (p1, p2) -> or_b ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | NOT p -> not_b ctx (path2expr_aux ctx p)
  | EQ (v1, v2) -> eq ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | NOTEQ (v1, v2) -> neq ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | LESSTHAN (v1, v2) -> lt ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | LESSEQUAL (v1, v2) -> le ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | GREATTHAN (v1, v2) -> gt ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | GREATEQUAL (v1, v2) -> ge ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)