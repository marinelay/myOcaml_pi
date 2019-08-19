
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
let arr_n ctx str sort = Z3.Expr.mk_const_s ctx str sort (* mk_const랑 동일... *)
let arr_select ctx arr_n i = Z3.Z3Array.mk_select ctx arr_n i
let arr_store ctx arr_n i v = Z3.Z3Array.mk_store ctx arr_n i v  

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

let quan quant = Z3.Quantifier.expr_of_quantifier quant

type bound_env = Z3.Symbol.symbol list

let empty_bound = []
let rec append_bound l bound_env
= let rec get_symbol l = 
  (match l with
  | [] -> []
  | hd::tl -> hd::(get_symbol tl)
  ) in bound_env@(get_symbol l)

let rec find_bound n bound_env 
= match bound_env with
  | [] -> raise(Failure "No bound var..")
  | hd::tl ->
    if n > 0 then find_bound (n-1) tl else hd

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
  | SIndex (id, v1, v2) ->
      let arr = arr_n ctx ("array_" ^ string_of_int id) (arr_sort ctx) in
      let arr = arr_store ctx arr (val2expr_aux ctx v1) (val2expr_aux ctx v2) in
      arr_select ctx arr (val2expr_aux ctx v1)
  | Sum l ->
    (
    match l with
    | [] -> val2expr_aux ctx (Int 0)
    | hd::tl -> add ctx (val2expr_aux ctx hd) (val2expr_aux ctx (Sum tl))
    )

let val2expr : value -> Expr.expr
= fun v -> val2expr_aux (new_ctx()) v

let rec expr2val : Expr.expr -> bound_env -> value
= fun expr env -> 
  if AST.is_var (Expr.ast_of_expr expr) (* quantifier *)
  then 
    let num = Quantifier.get_index expr in 
    print_endline(Expr.to_string expr ^ " : " ^ string_of_int num);
    let get_symbol = find_bound num env in
    let str = Symbol.get_string get_symbol in
    let l = Str.split (Str.regexp "_") str in
    match l with
    | [hd; tl] ->
      if hd = "alpha" then SInt (int_of_string tl)
      else if hd = "beta" then SBool (int_of_string tl)
      else raise (Failure "SHOULD NOT COME HERE")
    | _ -> raise (Failure "SHOULD NOT COME HERE")

  else
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
        SArith (SADD, expr2val hd env, expr2val tl env)
      end
      else if n > 2 then
      begin
        let l = Expr.get_args expr in
        Sum (map_env expr2val l env)
      end
      else (* Expr.get_num_args < 2 *) raise (Failure "SHOULD NOT COME HERE")
    end


(*let rec repair_quantifier : Expr.expr -> Quantifier.quantifier -> value
= fun expr quant ->

  if AST.is_var (Expr.ast_of_expr expr) (* quantifier *)
  then 
    let index = Quantifier.get_index expr in
    let rec find_val = fun l n ->
    begin
    match l with
    | [] -> raise (Failure "SHOULD NOT COME HERE")
    | hd::tl -> 
      if n > 0 then begin  find_val tl n-1 end else begin
      let str = Symbol.get_string hd in
      let get_name = (let l = Str.split (Str.regexp "_") str in
      begin
      match l with
      | [hd; tl] ->
        if hd = "alpha" then SInt (int_of_string tl)
        else if hd = "beta" then SBool (int_of_string tl)
        else raise (Failure "SHOULD NOT COME HERE")
      | _ -> raise (Failure "SHOULD NOT COME HERE")
      end
      )
    end
    end 
    in find_val (Quantifier.get_bound_variable_names quant) index

  else
  let op = FuncDecl.get_decl_kind (Expr.get_func_decl expr) in
  match op with
  | OP_ADD -> (* sum *)
    begin
      let n = Expr.get_num_args expr in
      if n = 2 then
      begin
        let [hd; tl] = Expr.get_args expr in
        SArith (SADD, expr2val (repair_quantifier hd), expr2val (repair_quantifier tl))
      end
      else if n > 2 then
      begin
        let l = Expr.get_args expr in
        Sum (map expr2val (repair_quantifier l))
      end
      else (* Expr.get_num_args < 2 *) raise (Failure "SHOULD NOT COME HERE")
    end
  | _ -> expr2val expr*)

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

  | QUAN_EXIST (p1, body) -> 
  quan (Z3.Quantifier.mk_exists_const ctx [(val2expr_aux ctx p1)] (path2expr_aux ctx body) None [] [] None None)

  | QUAN_ALL (p1, body) -> 
  quan (Z3.Quantifier.mk_forall_const ctx [(val2expr_aux ctx p1)] (path2expr_aux ctx body) None [] [] None None)

let path2expr : path_cond -> Expr.expr
= fun p -> path2expr_aux (new_ctx ()) p

let rec expr2path : Expr.expr -> bound_env -> path_cond
= fun expr env ->
  let is_quantifier = AST.get_ast_kind (Expr.ast_of_expr expr) in
  match is_quantifier with
  | QUANTIFIER_AST ->
    let quant = Quantifier.quantifier_of_expr expr in
    let name_list = Quantifier.get_bound_variable_names quant in
    let env = append_bound name_list env in
    let body = Quantifier.get_body quant in

    let hd::tl = name_list in 
    let str = Symbol.get_string hd in
    let l = Str.split (Str.regexp "_") str in
    let get_name = 
    (match l with
    | [hd; tl] ->
      if hd = "alpha" then SInt (int_of_string tl)
      else if hd = "beta" then SBool (int_of_string tl)
      else raise (Failure "SHOULD NOT COME HERE")
    | _ -> raise (Failure "SHOULD NOT COME HERE")
    ) in
    if Quantifier.is_universal quant
    then (* forall *)
      QUAN_ALL(get_name, expr2path body env)
    else (* exist *)
      QUAN_EXIST(get_name, expr2path body env)
  | _ ->
  begin
  
 
  let op = FuncDecl.get_decl_kind (Expr.get_func_decl expr) in
  match op with
  | OP_TRUE -> TRUE
  | OP_FALSE -> FALSE
  | OP_AND -> (* and *)
    begin
      let n = Expr.get_num_args expr in
      if n = 2 then
      begin
        let [hd; tl] = Expr.get_args expr in AND (expr2path hd env, expr2path tl env)
      end
      else if n > 2 then
      begin
        let l = Expr.get_args expr in ANDL (map_env expr2path l env)
      end
      else (* Expr.get_num_args < 2 *) raise (Failure "SHOULD NOT COME HERE")
    end
  | OP_OR -> (* or *)
    begin
      let n = Expr.get_num_args expr in
      if n = 2 then
        let [hd; tl] = Expr.get_args expr in OR (expr2path hd env, expr2path tl env)
      else if n > 2 then
        let l = Expr.get_args expr in ANDL (map_env expr2path l env)
      else (* Expr.get_num_args <  2 *) raise (Failure "SHOULD NOT COME HERE")
    end
  | OP_EQ -> (* equal *) let [hd; tl] = Expr.get_args expr in EQ (expr2val hd env, expr2val tl env)
  | OP_NOT -> let [e] = Expr.get_args expr in NOT (expr2path e env)
  | OP_LE -> let [hd; tl] = Expr.get_args expr in LESSEQUAL (expr2val hd env, expr2val tl env)
  | OP_GE -> let [hd; tl] = Expr.get_args expr in GREATEQUAL (expr2val hd env, expr2val tl env)
  | OP_LT -> let [hd; tl] = Expr.get_args expr in LESSTHAN (expr2val hd env, expr2val tl env)
  | OP_GT -> let [hd; tl] = Expr.get_args expr in GREATTHAN (expr2val hd env, expr2val tl env)

  | _ -> raise (Failure "expr2path: Not Implemented")
  end

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