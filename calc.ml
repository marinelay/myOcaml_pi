open Util

type program = exp
and exp =
  | UNIT
  | INT of int
  | TRUE | FALSE
  | VAR of var
  | BAR of var
  | ARR of var * exp
  | IF of exp * exp * exp
  | ADD of exp * exp
  | SUB of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | NOTEQUAL of exp * exp 
  | LT of exp * exp
  | LE of exp * exp
  | GT of exp * exp
  | GE of exp * exp
  | IMPLY_EXP of exp * exp
  | AND_EXP of exp * exp
  | ASSIGN of var * exp
  | ASSIGN_ARR of var * exp * exp
  | SEQ of exp * exp
  | FUNC_START of exp * exp list * exp * exp
  | FOR of exp * exp * exp * exp * exp
  | RETURN of exp
  | RETURN_FUNC of exp list
  

  | EXIST of var list * exp
  | FORALL of var list * exp

  | PAR of var list
and var = string
;;

type value =
  | Unit
  | Int of int
  | Bool of bool
  (* symbol *)
  | SInt of id
  | SLen of id
  | SBool of id
  | SArr of id * (value * value) list (* id, (index, value) *)
  | SSelect of value * value (* SArr, index *)
  | SArith of arith_op * value * value
  | None (* For array empty *)
  | Sum of value list
  | Bound of id (* for quantifier var *)
  | Return


and arith_op = SADD | SSUB | SDIV
and id = int
and env = (var * value) list


and sym_exp =
  | TRUE | FALSE
  | NOT of sym_exp
  | AND of sym_exp * sym_exp
  | OR of sym_exp * sym_exp
  | IMPLY of sym_exp * sym_exp
  | EQ of value * value
  | NOTEQ of value * value
  | LESSTHAN of value * value
  | LESSEQUAL of value * value
  | GREATTHAN of value * value
  | GREATEQUAL of value * value
  | LIST of sym_exp list
  | ANDL of sym_exp list
  | ORL of sym_exp list

  | QUAN_ALL of value list * sym_exp
  | QUAN_EXIST of value list * sym_exp
and path_cond = sym_exp

let func_args = ref []
let append_args arg = func_args := !func_args@arg

let empty_algo = ref []
let init_algo () = empty_algo := []
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

let rec append_arr : (var * value) list -> (var * value * value) -> (var * value) list = fun env (x, i, v) ->
let SArr (id, l) = apply_env env x
in (x, SArr(id, (i, v)::l))::env

let rec get_arr_value : value -> value -> value = fun arr i ->
  let SArr (id, arr_list) = arr in
    let rec find_index : (value * value) list -> value -> value = fun l i ->
    (match l with
    | [] -> None
    | hd::tl ->  
      (match hd with
      | (j, w) -> if j=i then w else find_index tl i
      )
    ) in find_index arr_list i

let rec get_arr_id : value -> id = fun arr ->
  let SArr (id, _) = arr in id



let rec value2str : value -> string
= fun v ->
  match v with
  | Unit -> "Unit"
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | SInt id -> "alpha" ^ string_of_int id
  | SBool id -> "beta" ^ string_of_int id
  | SLen id -> "length(" ^ string_of_int id ^ ")"
  | SSelect (arr, i) -> "array" ^ string_of_int (get_arr_id arr) ^ "[" ^ value2str i ^ "]" 

    
  (*| SIndex (id, v1, v2) -> "array" ^ string_of_int id ^ "[" ^ value2str v1 ^ "] is " ^ value2str v2*) 
  | SArith (aop, v1, v2) ->
    (match aop with
    | SADD -> "(" ^ value2str v1 ^ " + " ^ value2str v2 ^ ")"
    | SSUB -> "(" ^ value2str v1 ^ " - " ^ value2str v2 ^ ")"
    | SDIV -> "(" ^ value2str v1 ^ " / " ^ value2str v2 ^ ")"
    )
  | Sum l -> "(" ^ fold (fun v1 s2 -> value2str v1 ^ (if s2 = ")" then "" else " + ") ^ s2) l ")"
  | Return -> "output"
  | None -> "none"
  | Bound n -> "bound" ^ string_of_int n

and cond2str : sym_exp -> string
= fun pi ->
  match pi with
  | TRUE -> "true"
  | FALSE -> "false"
  | NOT e -> "!" ^ cond2str e
  | AND (e1, e2) -> "(" ^ cond2str e1 ^ " and " ^ cond2str e2 ^ ")"
  | OR (e1, e2) -> "(" ^ cond2str e1 ^ " or " ^ cond2str e2 ^ ")"
  | IMPLY (e1, e2) -> "(" ^ cond2str e1 ^ " -> " ^ cond2str e2 ^ ")"
  | EQ (v1, v2) -> "(" ^ value2str v1 ^ " == " ^ value2str v2 ^ ")"
  | NOTEQ (v1, v2) -> "(" ^ value2str v1 ^ " != " ^ value2str v2 ^ ")"
  | LESSTHAN (v1, v2) -> "(" ^ value2str v1 ^ " < " ^ value2str v2 ^ ")"
  | LESSEQUAL (v1, v2) -> "(" ^ value2str v1 ^ " <= " ^ value2str v2 ^ ")"
  | GREATTHAN (v1, v2) -> "(" ^ value2str v1 ^ " > " ^ value2str v2 ^ ")"
  | GREATEQUAL (v1, v2) -> "(" ^ value2str v1 ^ " >= " ^ value2str v2 ^ ")"
  | ANDL l -> "(" ^ fold (fun v1 s2 -> cond2str v1 ^ (if s2 = ")" then "" else " and ") ^ s2) l ")"
  | ORL l -> "(" ^ fold (fun v1 s2 -> cond2str v1 ^ (if s2 = ")" then "" else " or ") ^ s2) l ")"

  | QUAN_EXIST (v1, e) -> "(There Exist " ^ (map_list_value value2str v1) ^ " s.t. " ^ cond2str e ^ ")"
  | QUAN_ALL (v1, e) -> "(For All " ^ (map_list_value value2str v1) ^ " s.t. " ^ cond2str e ^ ")"

  (* 타입 맞춰주기 *)
  (*
  * if문을 예로 들면, condition을 받았다고 해보자
  * condition을 eval_exp하면 (value * path_cond) list가 나올테고
  * list 원소들의 value, path_cond를 뽑아내야 하므로 eval_exp_aux를 통해
  * value와 path_cond을 뽑아내는 것이다
  *)
let rec eval_exp_aux : (value * path_cond * env) list -> (value -> path_cond -> env -> (value * path_cond * env) list) -> (value * path_cond * env) list
= fun l f ->
  match l with
  | [] -> []
  | (y, pi, env)::tl -> (f y pi env)@(eval_exp_aux tl f)



let rec eval_exp : exp -> env -> path_cond -> exp -> exp -> (value * path_cond * env) list
= fun exp env pi pre post ->
  match exp with
  | UNIT -> [(Unit, pi, env)]
  | INT n -> [(Int n, pi, env)]
  | TRUE -> [(Bool true, pi, env)]
  | FALSE -> [(Bool false, pi, env)]
  | VAR v -> [(apply_env env v, pi, env)]
  | BAR v -> 
    let arr = apply_env env v in
    (match arr with
    | SArr (id, _) -> [(SLen id, pi, env)]
    | _ -> raise(Failure "None in arr")
    )
  | ARR (x, i) -> 
    let l = eval_exp i env pi pre post in
    eval_exp_aux l (fun w pi env ->
      let v = get_arr_value (apply_env env x) w in
      (match v with
      | None -> 
        let env = append_arr env (x, w, SInt (new_sym())) in (* 없을시 새로등록 *)
        [(SSelect(apply_env env x, w), pi, env)]
      | _ -> [(SSelect(apply_env env x, w), pi, env)]
      )
    )
  
  | IF (cond, body1, body2) ->
    let l = eval_exp cond env TRUE pre post in
      eval_exp_aux l (fun v pi1 env ->

        let l1 = eval_exp body1 env (AND(pi, pi1)) pre post in
        eval_exp_aux l1 (fun v1 pi_true env_true ->
          let l2 = eval_exp body2 env (AND(pi, NOT(pi1))) pre post in
          eval_exp_aux l2 (fun v2 pi_false env_false ->
            (match v1, v2 with
            | Unit, _ -> [(v2, pi_false, env_false)]
            | _, Unit -> [(v1, pi_true, env_true)]
            | _, _ -> [(v1, pi_true, env_true); (v2, pi_false, env_false)]
            )
          )
        )
      )
  | ADD (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi1 env ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env ->
            (match (v1,v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : ADD")
            | Int n1, Int n2 -> [(Int (n1+n2), pi, env)]
            | _ -> [(SArith(SADD, v1, v2), pi, env)]
            )
          )
      )
  | SUB (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi1 env ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env ->
            (match (v1,v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : ADD")
            | Int n1, Int n2 -> [(Int (n1-n2), pi, env)]
            | _ -> [(SArith(SSUB, v1, v2), pi, env)]
            )
          )
      )
  | DIV (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi1 env ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env ->
            (match (v1,v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : DIV")
            | Int n1, Int n2 -> [(Int (n1/n2), pi, env)]
            | _ -> [(SArith(SDIV, v1, v2), pi, env)]
            )
          )
      )

  | EQUAL (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi1 env ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
            | Int n1, Int n2 -> [(Bool (n1 = n2), AND(pi, if n1=n2 then TRUE else FALSE), env)]
            | _ -> [(Bool true, AND(pi, EQ(v1, v2)), env)]
            )
          )
      )

  | NOTEQUAL (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi1 env ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
            | Int n1, Int n2 -> [(Bool (n1 != n2), AND(pi, if n1!=n2 then TRUE else FALSE), env)]
            | _ -> [(Bool true, AND(pi, NOTEQ(v1, v2)), env)]
            )
          )
      )

  | LT (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post in
      eval_exp_aux l1 (fun v1 pi1 env ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env ->

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
      eval_exp_aux l1 (fun v1 pi1 env ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env ->
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
      eval_exp_aux l1 (fun v1 pi1 env ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env ->
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
      eval_exp_aux l1 (fun v1 pi1 env ->
        let l2 = eval_exp e2 env pi pre post in
          eval_exp_aux l2 (fun v2 pi2 env ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : GE")
            | Int n1, Int n2 -> [(Bool (n1 >= n2), pi, env)]
            | _ -> [(Bool true, AND(pi, GREATEQUAL(v1, v2)), env)]
            )
          )
      )

  | AND_EXP (e1, e2) ->
    let l1 = eval_exp e1 env TRUE pre post in
    eval_exp_aux l1 (fun v1 pi1 env -> 
      let l2 = eval_exp e2 env TRUE pre post in
      eval_exp_aux l2 (fun v2 pi2 env ->
            (match (v1, v2) with
            | _ -> [(Bool true, AND(pi, AND(pi1, pi2)), env)]
            )
      )
    )
    
  | IMPLY_EXP (e1, e2) ->
    let l1 = eval_exp e1 env TRUE pre post in
    eval_exp_aux l1 (fun v1 pi1 env -> 
      let l2 = eval_exp e2 env TRUE pre post in
      eval_exp_aux l2 (fun v2 pi2 env ->
            (match (v1, v2) with
            | _ -> [(Bool true, AND(pi, IMPLY(pi1, pi2)), env)]
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
    
      (*(match v with
      | SSelect (arr, i) -> [(w, pi, (append_env env (x, w)))]
      | _ -> [(v, pi, (append_env env (x, v)))]
      )*)
      
    )

  | ASSIGN_ARR (x, i, e1) ->
  
    let l1 = eval_exp i env pi pre post in
    let l2 = eval_exp e1 env pi pre post in
    eval_exp_aux l1 (fun v1 pi env -> 
    eval_exp_aux l2 (fun v2 pi env ->
      [(Bool true, pi, (append_arr env (x, v1, v2)))]  
    
    (*(match v2 with
      | SIndex (id, i, w) -> [(w, pi, (append_arr env (x, v1, w)))]
      | _ -> [(v2, pi, (append_arr env (x, v1, v2)))]
      )*)
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
        | ARR (n, _) -> let _ = append_args [n] in
                    let l = new_sym () in
                    args_to_value tl (append_env env (n, SArr(l, [])))
        )
      ) in let env = args_to_value args env in 
        let pre_exp = eval_exp pre env pi pre post in
          eval_exp_aux pre_exp (fun v pre_exp env -> 
            eval_exp body env (AND(pi, pre_exp)) pre post
          )

  (* 배열 추가 필요 - 1차 추가 완료*)
  | FOR (pre, init, cond, next, body) ->
    let post_for = pre in
    (* Partial Correctenss *)
    let init_exp = eval_exp init env pi pre post in
    eval_exp_aux init_exp (fun v_init pi_init env_init ->
      let pre_exp = eval_exp pre env_init TRUE pre post in
      eval_exp_aux pre_exp (fun v_pre pi_pre env_pre ->
        let _ = append_algo [(Bool true, IMPLY(pi_init, pi_pre), env_init)] in
        let pre_exp = eval_exp pre env TRUE pre post in
        eval_exp_aux pre_exp (fun v_pre pi_pre env_pre ->
        let cond_exp = eval_exp cond env pi_pre pre post in
        eval_exp_aux cond_exp (fun v_cond pi_cond env_cond ->
          (* Cond is true *)
          let body_exp = eval_exp body env_cond pi_cond pre post in
          eval_exp_aux body_exp (fun v_body pi_body env_body ->
            let next_exp = eval_exp next env_body pi_body pre post in
            eval_exp_aux next_exp (fun v_next pi_next env_next ->
              let post_exp = eval_exp post_for env_next TRUE pre post in
              eval_exp_aux post_exp (fun v_post pi_post env_post ->
                let _ = append_algo [(Bool true, IMPLY(pi_next, pi_post), env_post)] in
                (* Cond is false *) 
                eval_exp UNIT env_cond (AND(pi_pre, NOT (pi_cond))) pre post
              )
            )
          )
        )
        )
      )
    )

  | RETURN (b) ->
        let l2 = eval_exp post env TRUE pre post in
        eval_exp_aux l2 (fun v1 post_exp env -> 
          let _ = append_algo [(Return, IMPLY(pi, (if b = TRUE then post_exp else NOT post_exp)), env)] in
          eval_exp UNIT env FALSE pre post
        )

  | RETURN_FUNC (args) ->
    let post_before_exp = eval_exp post env TRUE pre post in
    eval_exp_aux post_before_exp (fun v pi_before_post env -> 
    let rec args_to_value : exp list -> string list -> env -> env
    = fun args_value args_name env ->
        (match args_value with
        | [] -> env (* complete assign args *)
        | hd_val::tl_val ->  let l1 = eval_exp hd_val env pi pre post in
                    let [(v, pi, env)] = l1 in
                      (match args_name with
                      | [] -> raise(Failure "Not enough args")
                      | hd_name::tl_name -> args_to_value tl_val tl_name (append_env env (hd_name, v)) 
                      )
                      
        ) in let env = args_to_value args (!func_args) env in
          let pre_exp = eval_exp pre env TRUE pre post in
          eval_exp_aux pre_exp (fun v pi_pre env_pre ->
            let _ = append_algo [(Return, IMPLY(pi, pi_pre), env)] in

            let post_exp = eval_exp post env TRUE pre post in
            eval_exp_aux post_exp (fun v pi_post env_post ->
              let _ = append_algo [(Return, IMPLY(pi, IMPLY(pi_post, pi_before_post)), env)] in
              eval_exp UNIT env FALSE pre post
            )
          )
    )

  | FORALL (v, conds) ->
    let rec is_there_bound_var = fun l env ->
    (match l with
    | [] -> env
    | hd::tl -> is_there_bound_var tl (append_env env (hd, Bound (new_sym())))
    ) in
    let env_bound = is_there_bound_var v env in
      let body = eval_exp conds env_bound pi pre post in
        eval_exp_aux body (fun w pi2 env_bound ->
          let rec bound_var_list = fun l env ->
          (match l with
          | [] -> []
          | hd::tl ->
          (apply_env env hd)::(bound_var_list tl env)
          ) in
          [(Bool true, IMPLY(pi, QUAN_ALL(bound_var_list v env_bound, pi2)), env)]
        )
        

  | EXIST (v, conds) ->
    let rec is_there_bound_var = fun l env ->
    (match l with
    | [] -> env
    | hd::tl -> is_there_bound_var tl (append_env env (hd, Bound (new_sym())))
    ) in
    let env_bound = is_there_bound_var v env in
      let body = eval_exp conds env_bound pi pre post in
      eval_exp_aux body (fun w pi2 env_bound ->
          let rec bound_var_list = fun l env ->
          (match l with
          | [] -> []
          | hd::tl -> (apply_env env hd)::(bound_var_list tl env)
          ) in
          [(Bool true, IMPLY(pi, QUAN_EXIST(bound_var_list v env_bound, pi2)), env)]
      )

  (*| PAR (v) ->
    let quant = [i; j] in
    let rec is_there_bound_var = fun l env ->
    (match l with
    | [] -> env
    | hd::tl -> is_there_bound_var tl (append_env env (hd, Bound (new_sym())))
    ) in
    let env_bound = is_there_bound_var quant env in
      let body = eval_exp conds env_bound pi pre post in
      eval_exp_aux body (fun w pi2 env_bound ->
          let rec bound_var_list = fun l env ->
          (match l with
          | [] -> []
          | hd::tl -> (apply_env env hd)::(bound_var_list tl env)
          ) in*)
