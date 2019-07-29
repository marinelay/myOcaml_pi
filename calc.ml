open Util

type program = exp
and exp =
  | UNIT
  | INT of int
  | TRUE | FALSE
  | VAR of var
  | IF of exp * exp * exp * exp
  | ADD of exp * exp
  | LT of exp * exp
  | LE of exp * exp
  | GT of exp * exp
  | GE of exp * exp
  | ASSIGN of var * exp * exp
  | SEQ of exp * exp
  | FUNC_START of exp list * (var * var) list * exp * exp list
  | FOR of exp list * var * exp * exp * var * exp * exp * exp
  | RETURN of exp
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
  | Sum of value list
  | Return
and arith_op = SADD
and id = int
and env = (var * value) list


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
  | ANDL of sym_exp list
  | ORL of sym_exp list
and path_cond = sym_exp


let sym_cnt = ref 0
let init_sym_cnt () = sym_cnt := 0
let new_sym () = sym_cnt := !sym_cnt + 1; !sym_cnt

let empty_env = []
let rec append_env env (x, v) = (x, v)::env
let rec apply_env env x =
  match env with
  | [] -> raise(Failure "None in env")
  | (y,v)::tl -> if y=x then v else apply_env tl x

let rec value2str : value -> string
= fun v ->
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | SInt id -> "alpha" ^ string_of_int id
  | SBool id -> "beta" ^ string_of_int id
  | SArith (aop, v1, v2) ->
    (match aop with
    | SADD -> "(" ^ value2str v1 ^ " + " ^ value2str v2 ^ ")"
    )
  | Sum l -> "(" ^ fold (fun v1 s2 -> value2str v1 ^ (if s2 = ")" then "" else " + ") ^ s2) l ")"
  | Return -> "output"

let rec cond2str : sym_exp -> string
= fun pi ->
  match pi with
  | TRUE -> "true"
  | FALSE -> "false"
  | NOT e -> "!" ^ cond2str e
  | AND (e1, e2) -> "(" ^ cond2str e1 ^ " and " ^ cond2str e2 ^ ")"
  | OR (e1, e2) -> "(" ^ cond2str e1 ^ " or " ^ cond2str e2 ^ ")"
  | EQ (v1, v2) -> "(" ^ value2str v1 ^ " = " ^ value2str v2 ^ ")"
  | NOTEQ (v1, v2) -> "(" ^ value2str v1 ^ " != " ^ value2str v2 ^ ")"
  | LESSTHAN (v1, v2) -> "(" ^ value2str v1 ^ " < " ^ value2str v2 ^ ")"
  | LESSEQUAL (v1, v2) -> "(" ^ value2str v1 ^ " <= " ^ value2str v2 ^ ")"
  | GREATTHAN (v1, v2) -> "(" ^ value2str v1 ^ " > " ^ value2str v2 ^ ")"
  | GREATEQUAL (v1, v2) -> "(" ^ value2str v1 ^ " >= " ^ value2str v2 ^ ")"

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



let rec eval_exp : exp -> env -> path_cond -> exp list -> exp list -> (value * path_cond) list
= fun exp env pi pre post ->
  match exp with
  | UNIT -> [(Bool true, pi)]
  | INT n -> [(Int n, pi)]
  | TRUE -> [(Bool true, pi)]
  | FALSE -> [(Bool false, pi)]
  | VAR v -> [(apply_env env v, pi)]
  | IF (cond, body1, body2, out) ->
    let l = eval_exp cond env pi pre post in
      eval_exp_aux l (fun v pi ->
        (match v with
        | Bool b -> eval_exp (if b then body1 else body2) env pi pre post
        | SBool _ -> let l = (eval_exp body1 env (AND(pi, EQ(v, Bool true))) pre post)@
                              (eval_exp body2 env (AND(pi, EQ(v, Bool false))) pre post)
                    in eval_exp_aux l (fun v pi -> eval_exp out env pi pre post)
        | _ -> raise(Failure "Type Error : IF")
        )
      )
  | ADD (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi ->
        let l2 = eval_exp e2 env pi pre post in
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
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
            | Int n1, Int n2 -> [(Bool (n1 < n2), pi)]
            | _ -> [(Bool true, AND(pi, LESSTHAN(v1, v2)))]
            )
          )
      )
  | LE (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
            | Int n1, Int n2 -> [(Bool (n1 <= n2), pi)]
            | _ -> [(Bool true, AND(pi, LESSEQUAL(v1, v2)))]
            )
          )
      )
  | GT (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi ->
            (match (v1, v2) with
              | Bool _, _ | SBool _, _
              | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
              | Int n1, Int n2 -> [(Bool (n1 > n2), pi)]
              | _ -> [(Bool true, AND(pi, GREATTHAN(v1, v2)))]
            )
          )
      )
  | GE (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
            | Int n1, Int n2 -> [(Bool (n1 >= n2), pi)]
            | _ -> [(Bool true, AND(pi, GREATEQUAL(v1, v2)))]
            )
          )
      )
  | SEQ (e1, e2) ->
    let _ = eval_exp e1 env pi pre post in eval_exp e2 env pi pre post

  | ASSIGN (x, e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v pi -> eval_exp e2 (append_env env (x,v)) pi pre post)

  | FUNC_START (pre, args, body, post) -> 
    let rec args_to_value : (var * var) list -> env -> env
    = fun args env ->
      (match args with
      | [] -> env (* complete assign args *)
      | (vType, vName)::tl ->
        let l = new_sym () in
        (match vType with
        | "int" | "" -> args_to_value tl (append_env env (vName, SInt l))
        (*| SArray n1 -> args_to_value tl body (append_env env (vName, SArray l))*)
        ) 
      ) in let env = args_to_value args env in 
        let pre_exp = annotation_to_value pre env pi true in 
        eval_exp_aux pre_exp (fun v pi ->
          eval_exp body env pi pre post
        )

  (* 차후 구현 *)
  | FOR (pre, x1, init, cond, x2, next, body, out) ->
    let post = pre in 
    let pre_exp = annotation_to_value pre env pi (true) in
      eval_exp_aux pre_exp (fun v pi ->
        let init_exp = eval_exp init env pi pre post in
        eval_exp_aux init_exp (fun v1 pi ->
          let env = append_env env (x1, v1) in
            let cond_exp = eval_exp cond env pi pre post in
              eval_exp_aux cond_exp (fun v2 pi ->
                (match v2 with
                | Bool b -> eval_exp (if b then body else out) env pi pre post
                | SBool _ -> (let l1 = (eval_exp body env (AND(pi, EQ(v2, Bool true))) pre post) 
                              in eval_exp_aux l1 (fun v3 pi ->
                                let env = append_env env (x2, v3) in
                                let post_exp = annotation_to_value post env pi true in
                                  eval_exp_aux post_exp (fun v pi ->
                                    eval_exp out env pi pre post
                                  )
                              ))@(eval_exp out env (AND(pi, EQ(v2, Bool false))) pre post)
                | _ -> raise(Failure "Type Error : IF")
                )
              )
        )
      )

  | RETURN (b) ->
    let l = annotation_to_value post env pi 
      (match b with (* post condition은 not *)
      | TRUE -> false
      | FALSE -> true
      )
      in eval_exp_aux l (fun v pi -> 
        eval_exp UNIT env pi pre post
      )
    
and annotation_to_value : exp list -> env -> path_cond -> bool -> (value * path_cond) list
= fun logic env pi is_pre ->
  match logic with
  | [] -> if is_pre then [(Bool true, pi)] else [(Bool true, NOT pi)]
  | hd::tl -> let l = eval_exp hd env pi [] [] in
      eval_exp_aux l (fun v pi2 ->
        annotation_to_value tl env (AND(pi, pi2)) is_pre
      )
