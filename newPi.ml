type exp =
  | UNIT
  | INT of int
  | TRUE | FALSE
  | VAR of var
  | IF of exp * exp * exp
  | ADD of exp * exp
  | LT of exp * exp
  | LE of exp * exp
  | GT of exp * exp
  | GE of exp * exp
  | ASSIGN of var * exp
  | SEQ of exp * exp
and var = string
;;

type value =
  | Unit
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
  | LESSEQUAL of value * value
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

  (* 타입 맞춰주기 *)
  (*
  * if문을 예로 들면, condition을 받았다고 해보자
  * condition을 eval_exp하면 (value * path_cond) list가 나올테고
  * list 원소들의 value를 뽑아내야 하므로 eval_exp_aux를 통해
  * value와 path_cond을 뽑아내는 것이다
  *)
let rec eval_exp_aux : (value * path_cond) list -> (value -> path_cond -> (value * path_cond) list) -> (value * path_cond) list
= fun l f ->
  match l with
  | [] -> []
  | (y, pi)::tl -> (f y pi)@(eval_exp_aux tl f)

let rec eval_exp : exp -> env -> path_cond -> (value * path_cond) list
= fun exp env pi ->
  match exp with
  | UNIT -> [(Unit, pi)]
  | INT n -> [(Int n, pi)]
  | TRUE -> [(Bool true, pi)]
  | FALSE -> [(Bool false, pi)]
  | VAR v -> [(apply_env env v, pi)]
  | IF (cond, body1, body2) ->
    let l = eval_exp cond env pi in
      eval_exp_aux l (fun v pi ->
        (match v with
        | Bool b -> eval_exp (if b then body1 else body2) env pi
        | SBool _ -> (eval_exp body1 env (AND(pi, EQ(v, Bool true))))@
        (eval_exp body2 env (AND(pi, EQ(v, Bool false))))
        | _ -> raise(Failure "Type Error : IF")
        )
      )
  | ADD (e1, e2) ->
    let l1 = eval_exp e1 env pi in
      eval_exp_aux l1 (fun v1 pi ->
        let l2 = eval_exp e2 env pi in
          eval_exp_aux l2 (fun v2 pi ->
            (match (v1,v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : ADD")
            | Int n1, Int n2 -> [(Int (n1+n2), pi)]
            | _ -> [(SArith(SADD, v1, v2), pi)]
            )
          )
      )

  | LT (e1, e2) ->
    let l1 = eval_exp e1 env pi in
      eval_exp_aux l1 (fun v1 pi ->
        let l2 = eval_exp e2 env pi in
          eval_exp_aux l2 (fun v2 pi ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
            | Int n1, Int n2 -> [(Bool (n1 < n2), pi)]
            | _ -> [(Bool true, AND(pi, LESSTHAN(v1, v2))); (Bool false, AND(pi, GREATEQUAL(v1, v2)))]
            )
          )
      )
  | LE (e1, e2) ->
    let l1 = eval_exp e1 env pi in
      eval_exp_aux l1 (fun v1 pi ->
        let l2 = eval_exp e2 env pi in
          eval_exp_aux l2 (fun v2 pi ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
            | Int n1, Int n2 -> [(Bool (n1 <= n2), pi)]
            | _ -> [(Bool true, AND(pi, LESSEQUAL(v1, v2))); (Bool false, AND(pi, GREATTHAN(v1, v2)))]
            )
          )
      )
  | GT (e1, e2) ->
    let l1 = eval_exp e1 env pi in
      eval_exp_aux l1 (fun v1 pi ->
        let l2 = eval_exp e2 env pi in
          eval_exp_aux l2 (fun v2 pi ->
            (match (v1, v2) with
              | Bool _, _ | SBool _, _
              | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
              | Int n1, Int n2 -> [(Bool (n1 > n2), pi)]
              | _ -> [(Bool true, AND(pi, GREATTHAN(v1, v2))); (Bool false, AND(pi, LESSEQUAL(v1, v2)))]
            )
          )
      )
  | GE (e1, e2) ->
    let l1 = eval_exp e1 env pi in
      eval_exp_aux l1 (fun v1 pi ->
        let l2 = eval_exp e2 env pi in
          eval_exp_aux l2 (fun v2 pi ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
            | Int n1, Int n2 -> [(Bool (n1 >= n2), pi)]
            | _ -> [(Bool true, AND(pi, GREATEQUAL(v1, v2))); (Bool false, AND(pi, LESSTHAN(v1, v2)))]
            )
          )
      )
  | ASSIGN (x, e) -> 
    let l = eval_exp e env pi in
      eval_exp_aux l (fun v pi -> eval_exp x (append_env env (x, v) pi))
  | SEQ (e1, e2) ->
    let _ = eval_exp e1 env pi in eval_exp e2 env pi