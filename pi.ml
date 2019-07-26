type stmt =
  | ASSIGN of var * aexp
  | SKIP
  | SEQ of stmt * stmt
  | IF of bexp * stmt * stmt

and aexp =
  | NUM of int
  | VAR of var
  | ADD of aexp * aexp
  | SUB of aexp * aexp
and bexp = TRUE | FALSE
  | NOT of bexp
  | AND of bexp * bexp
  | EQ of aexp * aexp
  | LE of aexp * aexp
  | LT of aexp * aexp
  | GE of aexp * aexp
  | GT of aexp * aexp
and var = string

type tree = NODE of bexp * bexp


type value =
  | Skip
  | Num of int
  | Bool of bool
and env = (var * value) list

type sym_value =
  ( * value * )
  | Num of int
  | Bool of bool
  | SNum of id
  | SBool of id
  | SVar of id
  | SExp of arithmetic_op * sym_value * sym_value
and arithmetic_op = SADD | SSUB
and id = int
and sym_env = (var * sym_value) list

type path_exp =
  | TRUE
  | FALSE
  | AND of path_exp * path_exp
  | NOT of path_exp
  | EQUAL of sym_value * sym_value
  | LESSTHAN of sym_value * sym_alue
  | LESSEQ of sym_value * sym_value
  | GREATTHAN of sym_value * sym_value
  | GREATEQ of sym_value * sym_value
and path_cond = path_exp

let sym_cnt = ref 0
let init_sym_cnt () = sym_cnt := 0
let new_sym () = sym_cnt := !sym_cnt + 1; !sym_cnt


let empty_env = []
let append_env (x, v) env = (x, v)::env
let rec apply_env x env =
  match env with
  | [] -> raise (Failure "There is no variable")
  | (y, v)::tl -> if y=x then v else apply_env x tl

let rec eval_stmt : stmt -> env -> value
= fun stmt env ->
  match stmt with
  | ASSIGN (v, e) -> Skip
  | SKIP -> Skip
  | SEQ (s1, s2) ->
    let _ = eval_stmt s1 env in eval_stmt s2 env
  | IF (b1, s1, s2) ->
    ( match eval_bexp b1 env with
    | Bool true -> eval_stmt s1 env
    | Bool false -> eval_stmt s2 env
    | _ -> raise (Failure "Error: IF")
    ) 

and eval_aexp : aexp -> env -> value
= fun aexp env ->
  match aexp with
  | NUM n1 -> Num n1;
  | VAR v1 -> apply_env v1 env
  | ADD (e1, e2) ->
    let v1 = eval_aexp e1 env in
    let v2 = eval_aexp e2 env in
      (match v1, v2 with
      | Num n1, Num n2 -> Num (n1 + n2)
      | _ -> raise (Failure "Type Error: non-num values") 
      )
  | SUB (e1, e2) ->
    let v1 = eval_aexp e1 env in
    let v2 = eval_aexp e2 env in
      (match v1, v2 with
      | Num n1, Num n2 -> Num (n1 - n2)
      | _ -> raise (Failure "Type Error: non-num values") 
      )

and eval_bexp : bexp -> env -> value
= fun bexp env ->
  match bexp with
  | TRUE -> Bool true
  | FALSE -> Bool false
  | NOT l1 ->
    let v1 = eval_bexp l1 env in
    (match v1 with
    | Bool b1 -> Bool (not b1)
    | _ -> raise (Failure "Type Error: non-boolean")
    )
  | AND (e1, e2) ->
    let v1 = eval_bexp e1 env in
    let v2 = eval_bexp e2 env in
    (match v1, v2 with
    | Bool b1, Bool b2 -> Bool (b1 && b2)
    | _ -> raise (Failure "Type Error: non-boolean values")
    )
  | EQ (e1, e2) ->
    let v1 = eval_aexp e1 env in
    let v2 = eval_aexp e2 env in
    (match v1, v2 with
    | Bool b1, Bool b2 -> Bool (b1 = b2)
    | _ -> raise (Failure "Type Error: non-boolean values")
    )
  | LE (e1, e2) ->
    let v1 = eval_aexp e1 env in
    let v2 = eval_aexp e2 env in
    (match v1, v2 with
    | Bool b1, Bool b2 -> Bool (b1 <= b2)
    | _ -> raise (Failure "Type Error: non-boolean values")
    )
  | LT (e1, e2) ->
    let v1 = eval_aexp e1 env in
    let v2 = eval_aexp e2 env in
    (match v1, v2 with
    | Bool b1, Bool b2 -> Bool (b1 < b2)
    | _ -> raise (Failure "Type Error: non-boolean values")
    )
  | GE (e1, e2) ->
    let v1 = eval_aexp e1 env in
    let v2 = eval_aexp e2 env in
    (match v1, v2 with
    | Bool b1, Bool b2 -> Bool (b1 >= b2)
    | _ -> raise (Failure "Type Error: non-boolean values")
    )
  | GT (e1, e2) ->
    let v1 = eval_aexp e1 env in
    let v2 = eval_aexp e2 env in
    (match v1, v2 with
    | Bool b1, Bool b2 -> Bool (b1 > b2)
    | _ -> raise (Failure "Type Error: non-boolean values")
    )
;;