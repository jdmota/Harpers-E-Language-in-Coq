
module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> m)
      (fun p -> (fun x -> x + 1) (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val eqb : int -> int -> bool **)

  let rec eqb n m =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ ->
      (fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun n' ->
      (fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ -> false)
        (fun m' -> eqb n' m')
        m)
      n

  (** val max : int -> int -> int **)

  let rec max n m =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ -> n)
        (fun m' -> (fun x -> x + 1) (max n' m'))
        m)
      n
 end

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val length : char list -> int **)

let rec length = function
| [] -> 0
| _::s' -> (fun x -> x + 1) (length s')

type set = int -> bool

(** val emptySet : set **)

let emptySet _ =
  false

(** val updateSet : set -> int -> set **)

let updateSet s v v' =
  if Nat.eqb v v' then true else s v'

type eExp =
| ENum of int
| EStr of char list
| EId of int
| EPlus of eExp * eExp
| ETimes of eExp * eExp
| ECat of eExp * eExp
| ELen of eExp
| ELet of eExp * int * eExp

(** val get_fresh_var : eExp -> int **)

let rec get_fresh_var = function
| EId x -> (fun x -> x + 1) x
| EPlus (e1, e2) -> Nat.max (get_fresh_var e1) (get_fresh_var e2)
| ETimes (e1, e2) -> Nat.max (get_fresh_var e1) (get_fresh_var e2)
| ECat (e1, e2) -> Nat.max (get_fresh_var e1) (get_fresh_var e2)
| ELen e1 -> get_fresh_var e1
| ELet (e1, x, e2) ->
  Nat.max (get_fresh_var e1) (Nat.max ((fun x -> x + 1) x) (get_fresh_var e2))
| _ -> 0

(** val fresh_rename : eExp -> set -> int -> eExp **)

let rec fresh_rename e bv offset =
  match e with
  | EId x -> if bv x then EId (Nat.add x offset) else EId x
  | EPlus (e1, e2) ->
    EPlus ((fresh_rename e1 bv offset), (fresh_rename e2 bv offset))
  | ETimes (e1, e2) ->
    ETimes ((fresh_rename e1 bv offset), (fresh_rename e2 bv offset))
  | ECat (e1, e2) ->
    ECat ((fresh_rename e1 bv offset), (fresh_rename e2 bv offset))
  | ELen e1 -> ELen (fresh_rename e1 bv offset)
  | ELet (e1, x, e2) ->
    let e1' = fresh_rename e1 bv offset in
    let x' = Nat.add x offset in
    let e2' = fresh_rename e2 (updateSet bv x) offset in ELet (e1', x', e2')
  | _ -> e

(** val subst' : eExp -> int -> eExp -> eExp **)

let rec subst' e' x e = match e with
| EId y -> if Nat.eqb x y then e' else e
| EPlus (e1, e2) -> EPlus ((subst' e' x e1), (subst' e' x e2))
| ETimes (e1, e2) -> ETimes ((subst' e' x e1), (subst' e' x e2))
| ECat (e1, e2) -> ECat ((subst' e' x e1), (subst' e' x e2))
| ELen e1 -> ELen (subst' e' x e1)
| ELet (e1, y, e2) ->
  if Nat.eqb x y
  then ELet ((subst' e' x e1), y, e2)
  else ELet ((subst' e' x e1), y, (subst' e' x e2))
| _ -> e

(** val subst : eExp -> int -> eExp -> eExp **)

let subst e' x e =
  let offset = Nat.max (get_fresh_var e) (get_fresh_var e') in
  subst' e' x (fresh_rename e emptySet offset)

(** val is_val : eExp -> bool **)

let is_val = function
| ENum _ -> true
| EStr _ -> true
| _ -> false

(** val eval : eExp -> eExp option **)

let rec eval = function
| EPlus (e1, e2) ->
  (match e1 with
   | ENum n1 ->
     (match e2 with
      | ENum n2 -> Some (ENum (Nat.add n1 n2))
      | _ ->
        if is_val e1
        then (match eval e2 with
              | Some e2' -> Some (EPlus (e1, e2'))
              | None -> None)
        else (match eval e1 with
              | Some e1' -> Some (EPlus (e1', e2))
              | None -> None))
   | _ ->
     if is_val e1
     then (match eval e2 with
           | Some e2' -> Some (EPlus (e1, e2'))
           | None -> None)
     else (match eval e1 with
           | Some e1' -> Some (EPlus (e1', e2))
           | None -> None))
| ETimes (e1, e2) ->
  (match e1 with
   | ENum n1 ->
     (match e2 with
      | ENum n2 -> Some (ENum (Nat.mul n1 n2))
      | _ ->
        if is_val e1
        then (match eval e2 with
              | Some e2' -> Some (ETimes (e1, e2'))
              | None -> None)
        else (match eval e1 with
              | Some e1' -> Some (ETimes (e1', e2))
              | None -> None))
   | _ ->
     if is_val e1
     then (match eval e2 with
           | Some e2' -> Some (ETimes (e1, e2'))
           | None -> None)
     else (match eval e1 with
           | Some e1' -> Some (ETimes (e1', e2))
           | None -> None))
| ECat (e1, e2) ->
  (match e1 with
   | EStr s1 ->
     (match e2 with
      | EStr s2 -> Some (EStr (append s1 s2))
      | _ ->
        if is_val e1
        then (match eval e2 with
              | Some e2' -> Some (ECat (e1, e2'))
              | None -> None)
        else (match eval e1 with
              | Some e1' -> Some (ECat (e1', e2))
              | None -> None))
   | _ ->
     if is_val e1
     then (match eval e2 with
           | Some e2' -> Some (ECat (e1, e2'))
           | None -> None)
     else (match eval e1 with
           | Some e1' -> Some (ECat (e1', e2))
           | None -> None))
| ELen e1 ->
  (match e1 with
   | EStr s1 -> Some (ENum (length s1))
   | _ -> (match eval e1 with
           | Some e1' -> Some (ELen e1')
           | None -> None))
| ELet (e1, x, e2) ->
  if is_val e1
  then Some (subst e1 x e2)
  else (match eval e1 with
        | Some e1' -> Some (ELet (e1', x, e2))
        | None -> None)
| _ -> None

(** val eval_big : eExp -> eExp option **)

let rec eval_big = function
| ENum n -> Some (ENum n)
| EStr s -> Some (EStr s)
| x -> (match eval x with
        | Some e' -> eval_big e'
        | None -> None)
