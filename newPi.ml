type exp =
  | INT of int
  | TRUE | FALSE
  | VAR of var
  | IF of exp * exp * exp
  | ADD of exp * exp
  | LT of exp * exp
  | LE of exp * exp
  | GT of exp * exp
  | GE of exp * exp
  | SEQ of exp * exp
and var = string
;;

type value =
  | Int of int
  | Bool of bool
  (* symbol *)
  | SInt of id
  | SBool of id
  | SArith of arith_op * value * value
and arith_op = SADD
and id = int
and env = (var * value) list
;;

type sym_exp =
  | TRUE | FALSE
  | NOT of sym_exp
  | AND of sym_exp * sym_exp
  | OR of sym_exp * sym_exp
  | EQ of value * value
  | NOTEQ of value * value
  | LESSTHAN of value * value
  | LESSEQAUL of value * value
  | GREATTHAN of value * value
  | GREATEQUAL of value * value
and path_cond = sym_exp
;;

let sym_cnt = ref 0
let init_sym_cnt () = sym_cnt := 0
let new_sym () = sym_cnt := !sym_cnt + 1; !sym_cnt

let empty_env = []
let append_env env (x, v) = (x, v)::env
let rec apply_env env x =
  match env with
  | [] -> raise(Failure "None in env")
  | (y,v)::tl -> if y=x then v else apply_env tl x

let rec eval_exp : exp -> env -> path_cond -> (value * path_cond) list
= fun exp env pi ->
  match exp with
  | INT n -> [(Int n, pi)]
  | VAR v -> [(apply_env env v, pi)]
  | IF (cond, body1, body2) -> (* match 수정필요 *)
    let c = eval_exp cond env pi in
    (match c with
    | Bool b -> eval_exp (if b then body1 else body2) env pi
    | SBool _ -> (eval_exp body1 env (AND(pi, EQ(c, Bool true))))@
    (eval_exp body2 env (AND(pi, EQ(c, Bool false))))
    )
  | ADD (e1, e2) ->
    let v1 = eval_exp e1 env pi in
    let v2 = eval_exp e2 env pi in
    (match (v1,v2) with
    | Bool _, _ | SBool _, _
    | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : ADD")
    | Int n1, Int n2 -> [(Int (n1+n2), pi)]
    | _ -> [(SArith(SADD, n1, n2), pi)]
    )
  | SEQ (e1, e2) ->
    [(let _ = eval_env e1 env pi in eval_env e2 env pi, pi)]  