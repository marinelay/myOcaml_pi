let rec map f l =
  match l with
  | [] -> []
  | hd::tl -> (f hd)::(map f tl)

let rec map_env f l env =
  match l with
  | [] -> []
  | hd::tl -> (f hd env)::(map_env f tl env)

let rec fold f l a=
  match l with
  | [] -> a
  | hd::tl -> f hd (fold f tl a)