type exp =
  | UNIT
  | NUM of float
  | VAR of var
  | NEW of exp
  | REF of exp
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | CALL_FUN of exp * exp
  | IF of exp * exp * exp
  | ASSIGN of var * exp * exp
  | SEQ of exp * exp

  | TRUE
  | FALSE
  | AND of exp * exp
  | OR of exp * exp
  | NOT of exp
  | EQ of exp * exp
  | LT of exp * exp
  | LE of exp * exp
  | GT of exp * exp
  | GE of exp * exp
  and var = string
  and file = exp
  ;;
  
  type value = 
    | Unit
    | Float of float
    | Bool of bool
    | Loc of loc
    | RecProc of var * var * exp * env
  and loc = int
  and env = (var * value) list
  and mem = (loc * value) list
  ;;
  
  let val2str v =
    match v with
    | Float n -> string_of_float n
    | Bool b -> string_of_bool b
    | RecProc (f, x, e, env) -> "<fun>"
    | Loc l -> "loc " ^ string_of_int l
;;
  let empty_env = []
  let empty_mem = []
  
  let extend_env : var * value -> env -> env 
  = fun (x, v) e -> (x, v)::e
  let extend_mem (l, v) m = (l, v)::m
  
  let rec apply_env x e =
    match e with
    | [] -> raise (Failure ("variable " ^ x ^ " not found"))
    | (y,v)::tl -> if y=x then v else apply_env x tl
  let rec apply_mem : loc -> mem -> value 
  = fun loc mem ->
    match mem with
    | [] -> raise (Failure ("variable not found"))
    | (y,v)::tl -> if y=loc then v else apply_mem loc tl
  ;;
  
  let counter = ref 0
  let new_location () = counter := !counter + 1; !counter
  
  let rec eval : exp -> env -> mem -> value * mem
  = fun exp env mem ->
    match exp with
    | UNIT -> Unit, mem
    | NUM n1 -> Float n1, mem
    | VAR v1 -> apply_env v1 env, mem
    | NEW e1 -> let v, mem = eval e1 env mem in let l = new_location () in Loc l, extend_mem (l, v) mem 
    | REF e1 ->
      let l, mem = eval e1 env mem in
      (match l with
      | Loc l -> apply_mem l mem, mem
      | _ -> raise (Failure "not Loc")
      )
    | ADD (e1, e2) ->
      let v1, mem = eval e1 env mem in
      let v2, mem = eval e2 env mem in
        (match v1, v2 with
        | Float n1, Float n2 -> Float (n1 +. n2), mem
        | _ -> raise (Failure "Type Error: non-floating values") 
        )
    | SUB (e1, e2) ->
      let v1, mem = eval e1 env mem in
      let v2, mem = eval e2 env mem in
        (match v1, v2 with
        | Float n1, Float n2 -> Float (n1 -. n2), mem
        | _ -> raise (Failure "Type Error: non-floating values") 
        )
    | MUL (e1, e2) ->
      let v1, mem = eval e1 env mem in
      let v2, mem = eval e2 env mem in
        (match v1, v2 with
        | Float n1, Float n2 -> Float (n1 *. n2), mem
        | _ -> raise (Failure "Type Error: non-floating values") 
        )
    | DIV (e1, e2) ->
      let v1, mem = eval e1 env mem in
      let v2, mem = eval e2 env mem in
        (match v1, v2 with
        | Float n1, Float n2 -> 
          try Float (n1 /. n2), mem
          with Division_by_zero -> raise (Failure "Error: can't divide to zero")  
        | _ -> raise (Failure "Type Error: non-floating values") 
        )
    | LET (v1, e1, e2) ->
      let x, mem = eval e1 env mem in
      eval e2 (extend_env (v1, x) env ) mem
    | LETREC (f, x, e1, e2) ->
      let recproc = RecProc (f, x, e1, env) in eval e2 (extend_env (f, recproc) env) mem
    | CALL_FUN (e1, e2) ->
      let proc, mem = eval e1 env mem in
      let v, mem = eval e2 env mem in
        (match proc with
        | RecProc (f, x, body, env) -> eval body (extend_env (f, proc) (extend_env (x, v) env)) mem
        | _ -> raise (Failure "Undefiend")
        )
    | IF (e1, e2, e3) ->
      let c, mem = eval e1 env mem in
      (match c with
      | Bool b -> eval (if b then e2 else e3) env mem
      | _ -> raise (Failure "Undefined")
      )
    | ASSIGN (v1, e1, e2) ->
      (match apply_env v1 env with
      | Loc l -> let v, mem = eval e1 env mem in eval e2 env (extend_mem (l, v) mem)
      | _ -> raise (Failure "Undefined")
      )
    | SEQ (e1, e2) -> let _, mem = eval e1 env mem in eval e2 env mem  
  
    | TRUE -> Bool true, mem
    | FALSE -> Bool false, mem
    | AND (l1, l2) ->
      let v1, mem = eval l1 env mem in
      let v2, mem = eval l2 env mem in
        (match v1, v2 with
        | Bool b1, Bool b2 -> Bool (b1 && b2), mem
        | _ -> raise (Failure "Type Error: non-boolean")
        ) 
    | OR (l1, l2) ->
      let v1, mem = eval l1 env mem in
      let v2, mem = eval l2 env mem in
        (match v1, v2 with
        | Bool b1, Bool b2 -> Bool (b1 || b2), mem
        | _ -> raise (Failure "Type Error: non-boolean")
        ) 
    | NOT l1 ->
      let v1, mem = eval l1 env mem in
        (match v1 with
        | Bool b1 -> Bool (not b1), mem
        | _ -> raise (Failure "Type Error: non-boolean")
        )
    | EQ (l1, l2) ->
      let v1, mem = eval l1 env mem in
      let v2, mem = eval l2 env mem in
        (match v1, v2 with
        | Bool b1, Bool b2 -> Bool (b1 = b2), mem
        | Float b1, Float b2 -> Bool (b1 = b2), mem
        | _ -> raise (Failure "Type Error: non-boolean")
        )
    | LT (l1, l2) ->
      let v1, mem = eval l1 env mem in
      let v2, mem = eval l2 env mem in
        (match v1, v2 with
        | Float b1, Float b2 -> Bool (b1 < b2), mem
        | _ -> raise (Failure "Type Error: non-boolean")
        )
    | LE (l1, l2) ->
      let v1, mem = eval l1 env mem in
      let v2, mem = eval l2 env mem in
        (match v1, v2 with
        | Float b1, Float b2 -> Bool (b1 <= b2), mem
        | _ -> raise (Failure "Type Error: non-boolean")
        )
    | GT (l1, l2) ->
      let v1, mem = eval l1 env mem in
      let v2, mem = eval l2 env mem in
        (match v1, v2 with
        | Float b1, Float b2 -> Bool (b1 > b2), mem
        | _ -> raise (Failure "Type Error: non-boolean")
        )
    | GE (l1, l2) ->
      let v1, mem = eval l1 env mem in
      let v2, mem = eval l2 env mem in
        (match v1, v2 with
        | Float b1, Float b2 -> Bool (b1 >= b2), mem
        | _ -> raise (Failure "Type Error: non-boolean")
        )
  ;;
  
  let calc : exp -> value
  = fun e -> let v, _ = eval e empty_env empty_mem in v