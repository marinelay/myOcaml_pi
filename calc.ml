open Util

type program = exp
and exp =
  | UNIT
  | INT of int
  | TRUE | FALSE
  | VAR of var
  | ARR of var * exp
  | IF of exp * exp * exp
  | ADD of exp * exp
  | LT of exp * exp
  | LE of exp * exp
  | GT of exp * exp
  | GE of exp * exp
  | ASSIGN of var * exp
  | ASSIGN_ARR of var * exp * exp
  | SEQ of exp * exp
  | FUNC_START of exp list * exp list * exp * exp list
  | FOR of exp list * exp * exp * exp * exp
  | RETURN of exp
  | RETURN_FUNC of exp list
and var = string
;;

type value =
  | Unit
  | Int of int
  | Bool of bool
  (* symbol *)
  | SInt of id
  | SBool of id
  | SArr of var * value * value
  | SArith of arith_op * value * value
  | Sum of value list
  | Return
and arith_op = SADD
and id = int
and env = (var * value) list


and sym_exp =
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

let func_args = ref []
let append_args arg = func_args := !func_args@arg

let empty_algo = ref []
let append_algo algo = empty_algo := !empty_algo@algo

let sym_cnt = ref 0
let init_sym_cnt () = sym_cnt := 0
let new_sym () = sym_cnt := !sym_cnt + 1; !sym_cnt

let empty_env = []


let rec append_env env (x, v) 
= (x, v)::env

let rec apply_env env x =
  match env with
  | [] -> raise(Failure "None in env")
  | (y, v)::tl -> if y=x then v else apply_env tl x

let rec apply_arr env x i =
  match env with
  | [] -> raise(Failure "None in env_arr")
  | (y, v)::tl -> if y=x then
      (let rec find_index arr i =
      (match arr with
      | [] -> raise(Failure "None in arr")
      | (j, w)::tl -> if j=i then w else find_index tl i 
      ) in find_index v i)
      else apply_arr tl x i

let rec value2str : value -> string
= fun v ->
  match v with
  | Unit -> "Unit"
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

and cond2str : sym_exp -> string
= fun pi ->
  match pi with
  | TRUE -> "true"
  | FALSE -> "false"
  | NOT e -> "!" ^ cond2str e
  | AND (e1, e2) -> "(" ^ cond2str e1 ^ " and " ^ cond2str e2 ^ ")"
  | OR (e1, e2) -> "(" ^ cond2str e1 ^ " or " ^ cond2str e2 ^ ")"
  | EQ (v1, v2) -> "(" ^ value2str v1 ^ " == " ^ value2str v2 ^ ")"
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
let rec eval_exp_aux : (value * path_cond * env) list -> (value -> path_cond -> env -> (value * path_cond * env) list) -> (value * path_cond * env) list
= fun l f ->
  match l with
  | [] -> []
  | (y, pi, env)::tl -> (f y pi env)@(eval_exp_aux tl f)



let rec eval_exp : exp -> env -> path_cond -> exp list -> exp list -> (value * path_cond * env) list
= fun exp env pi pre post ->
  match exp with
  | UNIT -> [(Unit, pi, env)]
  | INT n -> [(Int n, pi, env)]
  | TRUE -> [(Bool true, pi, env)]
  | FALSE -> [(Bool false, pi, env)]
  | VAR v -> [(apply_env env v, pi, env)]
  | ARR (v, i) -> [(apply_arr env v i, pi, env)]
  | IF (cond, body1, body2) ->
    let l = eval_exp cond env pi pre post in
      eval_exp_aux l (fun v pi1 env ->
        (match v with
        | Bool b -> let AND(_, comp) = pi1 in
                      let l1 = eval_exp body1 env (AND(pi, comp)) pre post in
                      eval_exp_aux l1 (fun v1 pi_true env_true ->
                        let l2 = eval_exp body2 env (AND(pi, NOT(comp))) pre post in
                        eval_exp_aux l2 (fun v2 pi_false env_false ->
                          (match v1, v2 with
                          | Unit, _ -> [(v2, pi_false, env_false)]
                          | _, Unit -> [(v1, pi_true, env_true)]
                          | _, _ -> [(v1, pi_true, env_true); (v2, pi_false, env_false)]
                          )
                        )
                      )
                    (*let l2 = (eval_exp body1 env (AND(pi, comp)) pre post)@
                              (eval_exp body2 env (AND(pi, NOT (comp))) pre post)
                    in eval_exp_aux l2 (fun v pi env -> eval_exp out env pi pre post)*)
        | _ -> raise(Failure "Type Error : IF")
        )
      )
  | ADD (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi1 env1 ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env2 ->
            (match (v1,v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : ADD")
            | Int n1, Int n2 -> [(Int (n1+n2), pi, env)]
            | _ -> [(SArith(SADD, v1, v2), pi, env)]
            )
          )
      )

  | LT ( e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi1 env1 ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env2 ->

            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
            | Int n1, Int n2 -> [(Bool (n1 < n2), pi, env)]
            | _ -> [(Bool true, AND(pi, LESSTHAN(v1, v2)), env)]
            )
          )
      )
  | LE (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi1 env1 ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env2 ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LE")
            | Int n1, Int n2 -> [(Bool (n1 <= n2), pi, env)]
            | _ -> [(Bool true, AND(pi, LESSEQUAL(v1, v2)), env)]
            )
          )
      )
  | GT (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi1 env1 ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env2 ->
            (match (v1, v2) with
              | Bool _, _ | SBool _, _
              | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : GT")
              | Int n1, Int n2 -> [(Bool (n1 > n2), pi, env)]
              | _ -> [(Bool true, AND(pi, GREATTHAN(v1, v2)), env)]
            )
          )
      )
  | GE (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi1 env1 ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env2 ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : GE")
            | Int n1, Int n2 -> [(Bool (n1 >= n2), pi, env)]
            | _ -> [(Bool true, AND(pi, GREATEQUAL(v1, v2)), env)]
            )
          )
      )
  | SEQ (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in 
      eval_exp_aux l1 (fun v pi env -> 
      (match v with
      | Return -> eval_exp UNIT env pi pre post
      | _ -> eval_exp e2 env pi pre post
      )
      )

  (* 배열 추가 필요 - 1차 완료*)
  | ASSIGN (x, e1) ->
    let l1 = eval_exp e1 env pi pre post in
    eval_exp_aux l1 (fun v pi env ->
      [(v, pi, (append_env env (x, v)))]
    )

  | ASSIGN_ARR (x, i, e1) ->
    let l1 = eval_exp i env pi pre post in
    let l2 = eval_exp e1 env pi pre post in
    eval_exp_aux l1 (fun v1 pi env -> 
    eval_exp_aux l2 (fun v2 pi env ->
      let l1 = apply_env env x in
      (match l1 with
      | SArr arr -> [(Unit, pi, (append_env env (x, SArr ((v1,v2)::arr))))]
      | _ -> raise(Failure "Can't Assign...")
      )
    )
    )

  (* 배열 추가 필요 - 1차 완료*)
  | FUNC_START (pre, args, body, post) -> 
    let rec args_to_value : exp list -> env ->  env
    = fun args env ->
      (match args with
      | [] -> env (* complete assign args *)
      | hd::tl ->
        (match hd with
        | VAR n -> let _ = append_args [n] in
                    let l = new_sym () in
                    args_to_value tl (append_env env (n, SInt l))
        (* Add arr *)
        | ARR n -> let _ = append_args [n] in
                    let l = new_sym () in
                    args_to_value tl (append_env env (n, SArr([])))
        )
      ) in let env = args_to_value args env in 
        let pre_exp = annotation_to_value pre env TRUE true in 
          eval_exp_aux pre_exp (fun v pre_exp env -> 
            eval_exp body env (AND(pi, pre_exp)) pre post
          )

  (* 배열 추가 필요 - 1차 추가 완료*)
  | FOR (pre, init, cond, next, body) ->
    let post = pre in
    (* Partial Correctenss *)
    let init_exp = eval_exp init env pi pre post in
    eval_exp_aux init_exp (fun v_init pi_init env_init ->
      let pre_exp = annotation_to_value pre env_init TRUE true in
      eval_exp_aux pre_exp (fun v_pre pi_pre env_pre ->
        let _ = append_algo [(Bool true, AND(pi_init, pi_pre), env_init)] in
        (*let l = new_sym () in  <- 필요 없을듯??*)
        let cond_exp = eval_exp cond env_init TRUE pre post in
        eval_exp_aux cond_exp (fun v_cond pi_cond env_cond ->
          (* Cond is true *)
          let body_exp = eval_exp body env_cond (AND(pi_pre, pi_cond)) pre post in
          eval_exp_aux body_exp (fun v_body pi_body env_body ->
            let next_exp = eval_exp next env_body pi_body pre post in
            eval_exp_aux next_exp (fun v_next pi_next env_next ->
              let post_exp = annotation_to_value post env_next TRUE true in
              eval_exp_aux post_exp (fun v_post pi_post env_post ->
                let _ = append_algo [(Bool true, AND(pi_next, pi_post), env_post)] in
                (* Cond is false *) 
                eval_exp UNIT env_cond (AND(pi_pre, NOT (pi_cond))) pre post
              )
            )
          )
          
        )
      )
    )

  | RETURN (b) ->
    let l1 = eval_exp b env pi pre post in
      eval_exp_aux l1 (fun v pi env ->
        
        let l2 = annotation_to_value post env TRUE
        (match v with (* post condition은 not *)
        | Bool true -> false
        | Bool false -> true
        | _ -> raise(Failure "Return Error")
        )
        in eval_exp_aux l2 (fun v post_exp env -> 
          let _ = append_algo [(Return, AND(pi, post_exp), env)] in
          eval_exp UNIT env TRUE pre post
        )
      )

  (* 배열 추가 필요 *)
  | RETURN_FUNC (args) ->
    let rec args_to_value : exp list -> exp list -> env -> env
    = fun args_value args_name env ->
      (match args_value with
      | [] -> env (* complete assign args *)
      | hd_val::tl_val ->  let l1 = eval_exp hd_val env pi pre post in
                  let [(v, pi, env)] = l1 in
                    (match args_name with
                    | [] -> raise(Failure "Not enough args")
                    | hd_name::tl_name -> args_to_value tl_val tl_name (append_env env (hd_name, v)) 
                    )
                    
      ) in let env = args_to_value args !func_args env in
        let post_exp = annotation_to_value post env TRUE true in
        eval_exp_aux post_exp (fun v pi_post env_post ->
          let _ = append_algo [(Return, AND(pi, pi_post), env)] in
          eval_exp UNIT env TRUE pre post
        ) 

    
and annotation_to_value : exp list -> env -> path_cond -> bool -> (value * path_cond * env) list
= fun logic env pi is_pre ->
  match logic with
  | [] -> if is_pre then [(Bool true, pi, env)] else [(Bool true, NOT pi, env)]
  | hd::tl -> let l1 = eval_exp hd env pi [] [] in
      eval_exp_aux l1 (fun v pi2 env ->
        annotation_to_value tl env (AND(pi, pi2)) is_pre
      )
