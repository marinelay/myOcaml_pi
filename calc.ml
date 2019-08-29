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
  | FUNC_START of exp * exp list * exp * exp * exp list * exp
  | FOR of exp * exp list * exp * exp * exp * exp * exp
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
and t_value = value list

and sym_exp =
  | TRUE | FALSE
  | NOT of sym_exp
  | AND of sym_exp * sym_exp
  | OR of sym_exp * sym_exp
  | IMPLY of sym_exp * sym_exp
  | XNOR of sym_exp * sym_exp
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
let func_total : exp list ref = ref []

let append_args arg = func_args := !func_args@arg

let partial_correct = ref []
let init_partial () = partial_correct := []
let append_partial partial = partial_correct := !partial_correct@partial

let total_correct : (value list * value list * path_cond) list ref  = ref [] (* why can't []? *)
let init_total () = total_correct := []
let append_total : (value list * value list * path_cond) list -> unit
= fun total -> total_correct := (!total_correct)@total

  

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
    | (j, w) -> if j=i then SSelect (arr, j) else find_index tl i
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
  | XNOR (e1, e2) -> "(" ^ cond2str e1 ^ " xnor " ^ cond2str e2 ^ ")"
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
let rec eval_exp_aux : (value * path_cond * env * path_cond * t_value) list -> (value -> path_cond -> env -> path_cond -> t_value -> (value * path_cond * env * path_cond * t_value) list) -> (value * path_cond * env * path_cond * t_value) list
= fun l f ->
  match l with
  | [] -> []
  | (y, pi, env, total, t_value)::tl -> (f y pi env total t_value)@(eval_exp_aux tl f)

  


let rec eval_exp : exp -> env -> path_cond -> exp -> exp -> path_cond -> t_value -> (value * path_cond * env * path_cond * t_value) list
= fun exp env pi pre post total t_value ->
  match exp with
  | UNIT -> [(Unit, pi, env, total, t_value)]
  | INT n -> [(Int n, pi, env, total, t_value)]
  | TRUE -> [(Bool true, pi, env, total, t_value)]
  | FALSE -> [(Bool false, pi, env, total, t_value)]
  | VAR v -> [(apply_env env v, pi, env, total, t_value)]
  | BAR v -> 
    let arr = apply_env env v in
    (match arr with
    | SArr (id, _) -> [(SLen id, pi, env, total, t_value)]
    | _ -> raise(Failure "None in arr")
    )
  | ARR (x, i) -> 
    let l = eval_exp i env pi pre post total t_value in
    eval_exp_aux l (fun w pi env total t_value ->
      let v = get_arr_value (apply_env env x) w in
      (match v with
      | None -> 
        let env = append_arr env (x, w, None) in (* 없을시 새로등록 *)
        [(SSelect(apply_env env x, w), pi, env, total, t_value)]
      | _ -> [(SSelect(apply_env env x, w), pi, env, total, t_value)]
      )
    )
  
  | IF (cond, body1, body2) ->
    let l = eval_exp cond env TRUE pre post TRUE t_value in
      eval_exp_aux l (fun v pi1 env total1 t_value ->

        let l1 = eval_exp body1 env (AND(pi, pi1)) pre post (AND(total, total1)) t_value in
        eval_exp_aux l1 (fun v1 pi_true env_true total_true t_value ->
          let l2 = eval_exp body2 env (AND(pi, NOT(pi1))) pre post (AND(total, NOT(total1))) t_value in
          eval_exp_aux l2 (fun v2 pi_false env_false total_false t_value ->
            (match v1, v2 with
            | Return, _ -> [(v2, pi_false, env_false, total_false, t_value)]
            | _, Unit -> [(v1, pi_true, env_true, total_true, t_value); (v2, pi_false, env_false, total_false, t_value)]
            | _, _ -> [(v1, pi_true, env_true, total_true, t_value); (v2, pi_false, env_false, total_false, t_value)]
            )
          )
        )
      )
  | ADD (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post total t_value in
      eval_exp_aux l1 (fun v1 pi1 env total t_value ->
        let l2 = eval_exp e2 env pi pre post total t_value in
          eval_exp_aux l2 (fun v2 pi2 env total t_value ->
            (match (v1,v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : ADD")
            | Int n1, Int n2 -> [(Int (n1+n2), pi, env, total, t_value)]
            | _ -> [(SArith(SADD, v1, v2), pi, env, total, t_value)]
            )
          )
      )
  | SUB (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post total t_value in
      eval_exp_aux l1 (fun v1 pi1 env total t_value ->
        let l2 = eval_exp e2 env pi pre post total t_value in
          eval_exp_aux l2 (fun v2 pi2 env total t_value ->
            (match (v1,v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : ADD")
            | Int n1, Int n2 -> [(Int (n1-n2), pi, env, total, t_value)]
            | _ -> [(SArith(SSUB, v1, v2), pi, env, total, t_value)]
            )
          )
      )
  | DIV (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post total t_value in
      eval_exp_aux l1 (fun v1 pi1 env total t_value ->
        let l2 = eval_exp e2 env pi pre post total t_value in
          eval_exp_aux l2 (fun v2 pi2 env total t_value ->
            (match (v1,v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : DIV")
            | Int n1, Int n2 -> [(Int (n1/n2), pi, env, total, t_value)]
            | _ -> [(SArith(SDIV, v1, v2), pi, env, total, t_value)]
            )
          )
      )

  | EQUAL (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post total t_value in
      eval_exp_aux l1 (fun v1 pi1 env total t_value ->
        let l2 = eval_exp e2 env pi pre post total t_value in
          eval_exp_aux l2 (fun v2 pi2 env total t_value ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
            | Int n1, Int n2 -> [(Bool (n1 = n2), AND(pi, if n1=n2 then TRUE else FALSE), env, AND(total, if n1=n2 then TRUE else FALSE), t_value)]
            | _ -> [(Bool true, AND(pi, EQ(v1, v2)), env, AND(total, EQ(v1, v2)), t_value)]
            )
          )
      )

  | NOTEQUAL (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post total t_value in
      eval_exp_aux l1 (fun v1 pi1 env total1 t_value ->
        let l2 = eval_exp e2 env pi pre post total t_value in
          eval_exp_aux l2 (fun v2 pi2 env total2 t_value ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
            | Int n1, Int n2 -> [(Bool (n1 != n2), AND(pi, if n1!=n2 then TRUE else FALSE), env, AND(total, if n1!=n2 then TRUE else FALSE), t_value)]
            | _ -> [(Bool true, AND(pi, NOTEQ(v1, v2)), env, AND(pi, NOTEQ(v1, v2)), t_value)]
            )
          )
      )

  | LT (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post total t_value in
      eval_exp_aux l1 (fun v1 pi1 env total1 t_value ->
        let l2 = eval_exp e2 env pi pre post total t_value in
          eval_exp_aux l2 (fun v2 pi2 env total2 t_value ->

            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LT")
            | Int n1, Int n2 -> [(Bool (n1 < n2), pi, env, total, t_value)]
            | _ -> [(Bool true, AND(pi, LESSTHAN(v1, v2)), env, AND(total, LESSTHAN(v1, v2)), t_value)]
            )
          )
      )
  | LE (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post total t_value in
      eval_exp_aux l1 (fun v1 pi1 env total1 t_value ->
        let l2 = eval_exp e2 env pi pre post total t_value in
          eval_exp_aux l2 (fun v2 pi2 env total2 t_value ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : LE")
            | Int n1, Int n2 -> [(Bool (n1 <= n2), pi, env, total, t_value)]
            | _ -> [(Bool true, AND(pi, LESSEQUAL(v1, v2)), env, AND(total, LESSEQUAL(v1, v2)), t_value)]
            )
          )
      )
  | GT (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post total t_value in
      eval_exp_aux l1 (fun v1 pi1 env total1 t_value ->
        let l2 = eval_exp e2 env pi pre post total t_value in
          eval_exp_aux l2 (fun v2 pi2 env total2 t_value ->
            (match (v1, v2) with
              | Bool _, _ | SBool _, _
              | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : GT")
              | Int n1, Int n2 -> [(Bool (n1 > n2), pi, env, total, t_value)]
              | _ -> [(Bool true, AND(pi, GREATTHAN(v1, v2)), env, AND(total, GREATTHAN(v1, v2)), t_value)]
            )
          )
      )
  | GE (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post total t_value in
      eval_exp_aux l1 (fun v1 pi1 env total1 t_value ->
        let l2 = eval_exp e2 env pi pre post total t_value in
          eval_exp_aux l2 (fun v2 pi2 env total2 t_value ->
            (match (v1, v2) with
            | Bool _, _ | SBool _, _
            | _, Bool _ | _, SBool _ -> raise(Failure "Type Error : GE")
            | Int n1, Int n2 -> [(Bool (n1 >= n2), pi, env, total, t_value)]
            | _ -> [(Bool true, AND(pi, GREATEQUAL(v1, v2)), env, AND(total, GREATEQUAL(v1, v2)), t_value)]
            )
          )
      )

  | AND_EXP (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post total t_value in
    eval_exp_aux l1 (fun v1 pi1 env total1 t_value -> 
      let l2 = eval_exp e2 env pi pre post total t_value in
      eval_exp_aux l2 (fun v2 pi2 env total2 t_value ->
            (match (v1, v2) with
            | _ -> [(Bool true, AND(pi, AND(pi1, pi2)), env, AND(total, IMPLY(total1, total2)), t_value)]
            )
      )
    )
    
  | IMPLY_EXP (e1, e2) ->
    let l1 = eval_exp e1 env TRUE pre post TRUE t_value in
    eval_exp_aux l1 (fun v1 pi1 env total1 t_value -> 
      let l2 = eval_exp e2 env TRUE pre post TRUE t_value in
      eval_exp_aux l2 (fun v2 pi2 env total2 t_value ->
            (match (v1, v2) with
            | _ -> [(Bool true, AND(pi, IMPLY(pi1, pi2)), env, AND(total, IMPLY(total1, total2)), t_value)]
            )
      )
    )


  | SEQ (e1, e2) ->
    let l1 = eval_exp e1 env pi pre post total t_value in 
      eval_exp_aux l1 (fun v pi env total t_value -> 
      (match v with
      | Return -> eval_exp UNIT env pi pre post total t_value
      | _ -> eval_exp e2 env pi pre post total t_value
      )
      )

  (* 배열 추가 필요 - 1차 완료*)
  | ASSIGN (x, e1) ->
    let l1 = eval_exp e1 env pi pre post total t_value in
    eval_exp_aux l1 (fun v pi env total t_value ->
      [(v, pi, (append_env env (x, v)), total, t_value)]
    
      (*(match v with
      | SSelect (arr, i) -> [(w, pi, (append_env env (x, w)))]
      | _ -> [(v, pi, (append_env env (x, v)))]
      )*)
      
    )

  | ASSIGN_ARR (x, i, e1) ->
  
    let l1 = eval_exp i env pi pre post total t_value in
    let l2 = eval_exp e1 env pi pre post total t_value in
    eval_exp_aux l1 (fun v1 pi env total t_value -> 
    eval_exp_aux l2 (fun v2 pi env total t_value ->
      [(Bool true, pi, (append_arr env (x, v1, v2)), total, t_value)]  
    
    (*(match v2 with
      | SIndex (id, i, w) -> [(w, pi, (append_arr env (x, v1, w)))]
      | _ -> [(v2, pi, (append_arr env (x, v1, v2)))]
      )*)
    )
    )

  (* 배열 추가 필요 - 1차 완료*)
  | FUNC_START (pre, args, body, post, total_exp, total_cond) -> 
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
        (* Total Correctness *)
        let rec get_total total env =
          (match total with
          | [] -> []
          | hd::tl -> 
            let _ = func_total := hd::(!func_total) in
            let [(v, _, _, _, _)] = eval_exp hd env TRUE TRUE TRUE TRUE t_value in
            v::(get_total tl env)
          ) in

        if total_cond != UNIT
        then (
          let total_cond = eval_exp total_cond env TRUE TRUE TRUE total t_value in
          eval_exp_aux total_cond (fun v_total pi_total env_total _ t_value ->
          let t_value = get_total total_exp env in
          let pre_exp = eval_exp pre env pi pre post total t_value in
            eval_exp_aux pre_exp (fun v pre_exp env total t_value -> 
              eval_exp body env (AND(pi, pre_exp)) pre post pi_total t_value
            )
          )
        )
        else (
          let pre_exp = eval_exp pre env pi pre post TRUE [] in
          eval_exp_aux pre_exp (fun v pre_exp env _ t_value -> 
            eval_exp body env (AND(pi, pre_exp)) pre post total t_value
          )
        )

  (* 배열 추가 필요 - 1차 추가 완료*)
  | FOR (pre, total_exp, total_pre, init, cond, next, body) ->
    (* Total Correctness *)
    let rec get_total total env =
      (match total with
      | [] -> []
      | hd::tl -> 
        let [(v, _, _, _, _)] = eval_exp hd env TRUE TRUE TRUE TRUE t_value in
        v::(get_total tl env)
      ) in
    (*  print_endline("total_pi : " ^ cond2str total_pi);
      print_endline("total : " ^ cond2str total);
      let total_list = get_total total_exp total_env in
      (*let total_pi = AND(total_pi, total) in*)
      
      let _ = append_total [(total_list, total_pi)] in
      eval_exp UNIT env TRUE pre post total (* Dummy *)
    ) in*)
    
    
    (* Partial Correctness *)
    let post_for = pre in
    let init_exp = eval_exp init env pi pre post TRUE t_value in
    eval_exp_aux init_exp (fun v_init pi_init env_init total_init t_value ->
      let total_pi = eval_exp total_pre env TRUE TRUE TRUE total t_value in
      eval_exp_aux total_pi (fun v_total pi_total env_total _ t_value ->
      
      (* Total Correctness *)
      let _ = 
      (if t_value != []
      then (
          let total_list = get_total total_exp env_init in
          let _ = append_total [(t_value, total_list, total)] in
          Unit
      )
      else (
        Unit
      )) in
      let total = (AND(pi_total, total)) in
      let t_value = get_total total_exp env in
      let pre_exp = eval_exp pre env_init TRUE pre post total t_value in
      eval_exp_aux pre_exp (fun v_pre pi_pre env_pre _ t_value ->
        let _ = append_partial [(Bool true, IMPLY(pi_init, pi_pre), env_init)] in
        let pre_exp = eval_exp pre env TRUE pre post total t_value in
        eval_exp_aux pre_exp (fun v_pre pi_pre env_pre _ t_value ->
          let cond_exp = eval_exp cond env TRUE pre post total t_value in
          eval_exp_aux cond_exp (fun v_cond pi_cond env_cond _ t_value ->
            (* Cond is true *)
            let body_exp = eval_exp body env_cond (AND(pi_pre, pi_cond)) pre post total t_value in
            let _ = eval_exp_aux body_exp (fun v_body pi_body env_body total t_value ->
              let next_exp = eval_exp next env_body pi_body pre post total t_value in
              eval_exp_aux next_exp (fun v_next pi_next env_next total t_value ->
                let post_exp = eval_exp post_for env_next TRUE pre post total t_value in
                  eval_exp_aux post_exp (fun v_post pi_post env_post total_post t_value ->

                  (* Total *)
                  (*let total_pi = eval_exp total_pre env_next TRUE TRUE TRUE total t_value in*)
                  (*let _ = eval_exp_aux total_pi (fun v total_pi total_env total t_value ->*)
                    let total_list = get_total total_exp env_next in
                    let total_pi = total in
                    let _ = append_total [(t_value, total_list, total_pi)] in
                    (*eval_exp UNIT env TRUE pre post total t_value (* Dummy *)*)
                  (*)) in*)

                  (* Partial *)
                  let _ = append_partial [(Bool true, IMPLY(pi_next, pi_post), env_post)] in
                  eval_exp UNIT env_cond TRUE pre post total t_value (* Dummy *)
                ) 
              )
            ) in 

            (* Cond is false *)
            eval_exp UNIT env_cond (AND(pi_pre, NOT (pi_cond))) pre post (AND (NOT (pi_cond), total)) t_value
          ) 
        )
      )
      )
    )
    

  | RETURN (b) ->
        let l2 = eval_exp post env TRUE pre post total t_value in
        eval_exp_aux l2 (fun v1 post_exp env total t_value -> 
          let _ = append_partial [(Return, IMPLY(pi, (if b = TRUE then post_exp else NOT post_exp)), env)] in
          (*eval_exp UNIT env FALSE pre post total t_value*)
          [(Return, pi, env, total, t_value)]
        )

  | RETURN_FUNC (args) ->
    let post_before_exp = eval_exp post env TRUE pre post total t_value in
    eval_exp_aux post_before_exp (fun v pi_before_post env _ t_value -> 
    let rec args_to_value : exp list -> string list -> env -> env
    = fun args_value args_name env ->
        (match args_value with
        | [] -> env (* complete assign args *)
        | hd_val::tl_val ->  let l1 = eval_exp hd_val env pi pre post total t_value in
                    let [(v, pi, env, total, t_value)] = l1 in
                      (match args_name with
                      | [] -> raise(Failure "Not enough args")
                      | hd_name::tl_name -> args_to_value tl_val tl_name (append_env env (hd_name, v)) 
                      )
                      
        ) in let env = args_to_value args (!func_args) env in
          (* Total *)
          let rec get_total : exp list -> value list =
            fun total_exp ->
            (match total_exp with
            | [] -> []
            | hd::tl ->
              let l1 = eval_exp hd env pi pre post total t_value in
              let tmp = eval_exp_aux l1 (fun v _ _ _ _ -> 
                [(v, pi, env, total, t_value)]
              ) in let [(v, pi, env, total, t_value)] = tmp in v::get_total tl
            ) in let total_result = get_total !func_total in
          let _ = if total_result != []
          then (
            let _ = append_total [(t_value, total_result, total)] in true
          ) else (
            true
          ) in

          (* Partial *)
          let pre_exp = eval_exp pre env TRUE pre post total t_value in
          eval_exp_aux pre_exp (fun v pi_pre env_pre total t_value ->
            let _ = append_partial [(Return, IMPLY(pi, pi_pre), env)] in

            let post_exp = eval_exp post env TRUE pre post total t_value in
            eval_exp_aux post_exp (fun v pi_post env_post total t_value ->
              let _ = append_partial [(Return, IMPLY(pi, XNOR(pi_post, pi_before_post)), env)] in
              eval_exp UNIT env FALSE pre post total t_value
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
      let body = eval_exp conds env_bound pi pre post total t_value in
        eval_exp_aux body (fun w pi2 env_bound total t_value ->
          let rec bound_var_list = fun l env ->
          (match l with
          | [] -> []
          | hd::tl ->
          (apply_env env hd)::(bound_var_list tl env)
          ) in
          [(Bool true, IMPLY(pi, QUAN_ALL(bound_var_list v env_bound, pi2)), env, total, t_value)]
        )
        

  | EXIST (v, conds) ->
    let rec is_there_bound_var = fun l env ->
    (match l with
    | [] -> env
    | hd::tl -> is_there_bound_var tl (append_env env (hd, Bound (new_sym())))
    ) in
    let env_bound = is_there_bound_var v env in
      let body = eval_exp conds env_bound pi pre post total t_value in
      eval_exp_aux body (fun w pi2 env_bound total t_value ->
          let rec bound_var_list = fun l env ->
          (match l with
          | [] -> []
          | hd::tl -> (apply_env env hd)::(bound_var_list tl env)
          ) in
          [(Bool true, IMPLY(pi, QUAN_EXIST(bound_var_list v env_bound, pi2)), env, total, t_value)]
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
