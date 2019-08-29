
open Calc
open Str
open Util
open Z3
open Z3enums


let new_ctx () = mk_context [("timeout", "50")]

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
let imply ctx expr1 expr2 = Z3.Boolean.mk_implies ctx expr1 expr2
let xor_b ctx expr1 expr2 = Z3.Boolean.mk_xor ctx expr1 expr2
let lt ctx expr1 expr2 = Z3.Arithmetic.mk_lt ctx expr1 expr2
let gt ctx expr1 expr2 = Z3.Arithmetic.mk_gt ctx expr1 expr2
let le ctx expr1 expr2 = Z3.Arithmetic.mk_le ctx expr1 expr2
let ge ctx expr1 expr2 = Z3.Arithmetic.mk_ge ctx expr1 expr2
let not_b ctx expr = Z3.Boolean.mk_not ctx expr
let xnor_b ctx expr1 expr2 = (not_b ctx (xor_b ctx expr1 expr2))
let eq ctx expr1 expr2 = Z3.Boolean.mk_eq ctx expr1 expr2
let neq ctx expr1 expr2 = (not_b ctx (eq ctx expr1 expr2))

let quan quant = Z3.Quantifier.expr_of_quantifier quant

type bound_env = value list

let empty_bound = []
let rec append_bound l bound_env
= match l with
  | [] -> bound_env
  | hd::tl -> hd::(append_bound tl bound_env)

let rec find_bound n bound_env 
= match bound_env with
  | [] -> raise(Failure "No bound var..")
  | hd::tl ->
    if n > 0 then find_bound (n-1) tl else hd

(*let arr_env = ref []
let append_arr (x, e) env
= arr_env := (x, e)::env

let rec apply_arr x expr env
= match env with
  | [] -> let _ = arr_env := (x, expr)::!arr_env in expr 
  | (y, e)::tl -> if y=x then e else apply_arr x expr tl*)

exception NotComputableValue

let rec val2expr_aux : context -> value -> Expr.expr
= fun ctx v ->
  match v with
  | Int n -> const_n ctx n
  | Bool b -> const_b ctx b
  | SInt id -> mk_const ctx ("alpha_" ^ string_of_int id) (int_sort ctx)
  | SBool id -> mk_const ctx ("beta_" ^ string_of_int id) (bool_sort ctx)
  | SLen id -> mk_const ctx ("length_" ^ string_of_int id) (int_sort ctx)
  | SArith (aop, v1, v2) ->
    (match aop with
    | SADD -> add ctx (val2expr_aux ctx v1) (val2expr_aux ctx v2)
    | SSUB -> sub ctx (val2expr_aux ctx v1) (val2expr_aux ctx v2)
    | SDIV -> div ctx (val2expr_aux ctx v1) (val2expr_aux ctx v2)
    )
  | SSelect (arr, i) ->
      let arr_expr = arr_n ctx ("array_" ^ string_of_int (get_arr_id arr)) (arr_sort ctx) in
      let SArr (_, arr_list) = arr in
      let rec store_arr_value : (value * value) list -> context -> Expr.expr -> Expr.expr = fun arr_list ctx arr_expr ->
      (match arr_list with
      | [] -> arr_expr
      | (i, v)::tl -> 
        (match i with 
        | Bound _ -> store_arr_value tl ctx arr_expr
        | _ ->
          (match v with
          | None -> store_arr_value tl ctx arr_expr
          | _ ->
            let arr_expr = store_arr_value tl ctx arr_expr in
            (arr_store ctx arr_expr (val2expr_aux ctx i) (val2expr_aux ctx v))
          )
        )
      ) in let arr_expr = store_arr_value arr_list ctx arr_expr in
      arr_select ctx arr_expr (val2expr_aux ctx i)

  | Sum l ->
    (
    match l with
    | [] -> val2expr_aux ctx (Int 0)
    | hd::tl -> add ctx (val2expr_aux ctx hd) (val2expr_aux ctx (Sum tl))
    )
  | Bound id -> mk_const ctx ("bound_" ^ string_of_int id) (int_sort ctx)

let val2expr : value -> Expr.expr
= fun v -> val2expr_aux (new_ctx()) v

let rec expr2val : Expr.expr -> bound_env -> value
= fun expr env -> 
  if AST.is_var (Expr.ast_of_expr expr) (* quantifier *)
  then 
    let num = Quantifier.get_index expr in 
    find_bound num env

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
        else if hd = "length" then SLen (int_of_string tl)
        else if hd = "bound" then Bound (int_of_string tl)
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
  | OP_SUB -> (* sub *)
    begin
      let n = Expr.get_num_args expr in
      if n = 2 then
      begin
        let [hd; tl] = Expr.get_args expr in
        SArith (SSUB, expr2val hd env, expr2val tl env)
      end
      else if n > 2 then
      begin
        let l = Expr.get_args expr in
        Sum (map_env expr2val l env)
      end
      else (* Expr.get_num_args < 2 *) raise (Failure "SHOULD NOT COME HERE")
    end
  | OP_DIV -> (* div *)
    begin
      let n = Expr.get_num_args expr in
      if n = 2 then
      begin
        let [hd; tl] = Expr.get_args expr in
        SArith (SDIV, expr2val hd env, expr2val tl env)
      end
      else if n > 2 then
      begin
        let l = Expr.get_args expr in
        Sum (map_env expr2val l env)
      end
      else (* Expr.get_num_args < 2 *) raise (Failure "SHOULD NOT COME HERE")
    end
  |	OP_IDIV -> (* integer div *)
    begin
      let n = Expr.get_num_args expr in
      if n = 2 then
      begin
        let [hd; tl] = Expr.get_args expr in
        SArith (SDIV, expr2val hd env, expr2val tl env)
      end
      else if n > 2 then
      begin
        let l = Expr.get_args expr in
        Sum (map_env expr2val l env)
      end
      else (* Expr.get_num_args < 2 *) raise (Failure "SHOULD NOT COME HERE")
    end

  | OP_SELECT -> 
    begin
      let [store; select] = Expr.get_args expr in
      let rec solve2arr : Expr.expr -> (value * value) list -> value = fun expr val_list ->
      if (Expr.get_num_args expr) > 0
      then (
        let hd::[v1; v2] = Expr.get_args expr in 
        let v1 = expr2val v1 env in 
        let v2 = expr2val v2 env in 
        solve2arr hd ((v1, v2)::val_list)
          
        
      ) else (
        let str = Expr.to_string expr in
        let [hd; id] = Str.split (Str.regexp "_") str in
        SSelect(SArr(int_of_string id, val_list), expr2val select env)
      ) in solve2arr store []
    end

let rec path2expr_aux : context -> path_cond -> Expr.expr
= fun ctx p ->
  match p with
  | TRUE -> const_b ctx true
  | FALSE -> const_b ctx false
  | AND (p1, p2) -> and_b ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | OR (p1, p2) -> or_b ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | IMPLY (p1, p2) -> imply ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | XNOR (p1, p2) -> xnor_b ctx (path2expr_aux ctx p1) (path2expr_aux ctx p2)
  | NOT p -> not_b ctx (path2expr_aux ctx p)
  | EQ (p1, p2) -> eq ctx (val2expr_aux ctx p1) (val2expr_aux ctx p2)
  | NOTEQ (p1, p2) -> neq ctx (val2expr_aux ctx p1) (val2expr_aux ctx p2)
  | LESSTHAN (p1, p2) -> lt ctx (val2expr_aux ctx p1) (val2expr_aux ctx p2)
  | LESSEQUAL (p1, p2) -> le ctx (val2expr_aux ctx p1) (val2expr_aux ctx p2)
  | GREATTHAN (p1, p2) -> gt ctx (val2expr_aux ctx p1) (val2expr_aux ctx p2)
  | GREATEQUAL (p1, p2) -> ge ctx (val2expr_aux ctx p1) (val2expr_aux ctx p2)

  | QUAN_EXIST (p1, body) -> 
  quan (Z3.Quantifier.mk_exists_const ctx (map (val2expr_aux ctx) p1) (path2expr_aux ctx body) None [] [] None None)

  | QUAN_ALL (p1, body) -> 
  quan (Z3.Quantifier.mk_forall_const ctx (map (val2expr_aux ctx) p1) (path2expr_aux ctx body) None [] [] None None)

let path2expr : path_cond -> Expr.expr
= fun p -> path2expr_aux (new_ctx ()) p

let rec expr2path : Expr.expr -> bound_env -> path_cond
= fun expr env ->
  let is_quantifier = AST.get_ast_kind (Expr.ast_of_expr expr) in
  match is_quantifier with
  | QUANTIFIER_AST ->
    let quant = Quantifier.quantifier_of_expr expr in
    let symbol_list = Quantifier.get_bound_variable_names quant in

    let rec sym2val = fun symbol_list ->
    (match symbol_list with
    | [] -> []
    | hd::tl ->
      let str = Symbol.get_string hd in
      let l = Str.split (Str.regexp "_") str in
      let get_name = 
      (match l with
      | [hd; tl] ->
        if hd = "alpha" then SInt (int_of_string tl)
        else if hd = "beta" then SBool (int_of_string tl)
        else if hd = "length" then SLen (int_of_string tl)
        else if hd = "bound" then Bound (int_of_string tl)
        else raise (Failure "SHOULD NOT COME HERE")
      | _ -> raise (Failure "SHOULD NOT COME HERE")
      ) in
      get_name::(sym2val tl)
    ) in
    let val_list = sym2val symbol_list in

    let env = append_bound val_list env in
    let body = Quantifier.get_body quant in

    if Quantifier.is_universal quant
    then (* forall *)
      QUAN_ALL(val_list, expr2path body env)
    else (* exist *)
      QUAN_EXIST(val_list, expr2path body env)
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
  |	OP_IMPLIES -> let [hd; tl] = Expr.get_args expr in IMPLY (expr2path hd env, expr2path tl env)
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