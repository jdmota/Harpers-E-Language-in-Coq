Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From Coq Require Import Strings.String.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Recdef.
From PFPL Require Import PartialMap_Set.

(** E Language *)
Inductive EExp : Type :=
  | ENum (n : nat)
  | EStr (s : string)
  | EId (x : nat)
  | EPlus (e1 e2 : EExp)
  | ETimes (e1 e2 : EExp)
  | ECat (e1 e2 : EExp)
  | ELen (e1 : EExp)
  | ELet (e1 : EExp) (x : nat) (e2: EExp). (* let x = e1 in e2 <=> (lambda e2) e1 *)

(** Depth of an expression (to help us prove the termination of some functions) *)
Fixpoint depth (e: EExp) : nat :=
  match e with
  | EId x => 0
  | ELet e1 x e2 => 1 + max (depth e1) (depth e2)
  | ENum _ => 0
  | EStr _ => 0
  | EPlus e1 e2 => 1 + max (depth e1) (depth e2)
  | ETimes e1 e2 => 1 + max (depth e1) (depth e2)
  | ECat e1 e2 => 1 + max (depth e1) (depth e2)
  | ELen e1 => 1 + depth e1
  end.

(** Returns the set of free variables *)
Fixpoint free_vars (e : EExp) : set :=
  match e with
  | EId x => singletonSet x
  | ELet e1 x e2 => unionSet (free_vars e1) (removeFromSet (free_vars e2) x)
  | ENum n => emptySet
  | EStr s => emptySet
  | EPlus e1 e2 => unionSet (free_vars e1) (free_vars e2)
  | ETimes e1 e2 => unionSet (free_vars e1) (free_vars e2)
  | ECat e1 e2 => unionSet (free_vars e1) (free_vars e2)
  | ELen e1 => free_vars e1
  end.

(** An expression is closed if it does not contain free variables *)
Definition closed (e : EExp) := free_vars e = emptySet.

(** Returns the set of bound variables *)
Fixpoint bound_vars (e : EExp) : set :=
  match e with
  | EId x => emptySet
  | ELet e1 x e2 => unionSet (bound_vars e1) (updateSet (bound_vars e2) x)
  | ENum n => emptySet
  | EStr s => emptySet
  | EPlus e1 e2 => unionSet (bound_vars e1) (bound_vars e2)
  | ETimes e1 e2 => unionSet (bound_vars e1) (bound_vars e2)
  | ECat e1 e2 => unionSet (bound_vars e1) (bound_vars e2)
  | ELen e1 => bound_vars e1
  end.

(** Returns the set of all variables *)
Fixpoint all_vars (e : EExp) : set :=
  match e with
  | EId x => singletonSet x
  | ELet e1 x e2 => unionSet (all_vars e1) (updateSet (all_vars e2) x)
  | ENum n => emptySet
  | EStr s => emptySet
  | EPlus e1 e2 => unionSet (all_vars e1) (all_vars e2)
  | ETimes e1 e2 => unionSet (all_vars e1) (all_vars e2)
  | ECat e1 e2 => unionSet (all_vars e1) (all_vars e2)
  | ELen e1 => all_vars e1
  end.

(** Returns a new variable not present in the expression *)
Fixpoint get_fresh_var (e : EExp) : nat :=
  match e with
  | EId x => S x
  | ELet e1 x e2 => max (get_fresh_var e1) (max (S x) (get_fresh_var e2))
  | ENum n => 0
  | EStr s => 0
  | EPlus e1 e2 => max (get_fresh_var e1) (get_fresh_var e2)
  | ETimes e1 e2 => max (get_fresh_var e1) (get_fresh_var e2)
  | ECat e1 e2 => max (get_fresh_var e1) (get_fresh_var e2)
  | ELen e1 => get_fresh_var e1
  end.

(** Rename one free variable for another *)
Fixpoint rename (e: EExp) (x x': nat) : EExp :=
  match e with
  | EId y => if x =? y then EId x' else EId y
  | ELet e1 y e2 => let e1' := rename e1 x x' in
                    if x =? y then ELet e1' y e2 else ELet e1' y (rename e2 x x')
  | ENum _ => e
  | EStr _ => e
  | EPlus e1 e2 => EPlus (rename e1 x x') (rename e2 x x')
  | ETimes e1 e2 => ETimes (rename e1 x x') (rename e2 x x')
  | ECat e1 e2 => ECat (rename e1 x x') (rename e2 x x')
  | ELen e1 => ELen (rename e1 x x')
  end.

(** Inductive definition of the alpha-equivalence relation *)
Inductive alpha_equiv_rel : EExp -> EExp -> Prop :=
  | alpha_equiv_rel_id : forall x, alpha_equiv_rel (EId x) (EId x)
  | alpha_equiv_rel_let :
    forall e1 x e2 e1' x' e2',
      alpha_equiv_rel e1 e1' ->
      (forall z, (all_vars e2) z = false -> (all_vars e2') z = false ->
      alpha_equiv_rel (rename e2 x z) (rename e2' x' z)) ->
      alpha_equiv_rel (ELet e1 x e2) (ELet e1' x' e2')
  | alpha_equiv_rel_num : forall n, alpha_equiv_rel (ENum n) (ENum n)
  | alpha_equiv_rel_str : forall s s', (eqb s s') = true -> alpha_equiv_rel (EStr s) (EStr s')
  | alpha_equiv_rel_plus : forall e1 e2 e1' e2', alpha_equiv_rel e1 e1' -> alpha_equiv_rel e2 e2' -> alpha_equiv_rel (EPlus e1 e2) (EPlus e1' e2')
  | alpha_equiv_rel_times : forall e1 e2 e1' e2', alpha_equiv_rel e1 e1' -> alpha_equiv_rel e2 e2' -> alpha_equiv_rel (ETimes e1 e2) (ETimes e1' e2')
  | alpha_equiv_rel_cat : forall e1 e2 e1' e2', alpha_equiv_rel e1 e1' -> alpha_equiv_rel e2 e2' -> alpha_equiv_rel (ECat e1 e2) (ECat e1' e2')
  | alpha_equiv_rel_len : forall e1 e1', alpha_equiv_rel e1 e1' -> alpha_equiv_rel (ELen e1) (ELen e1').

(** Auxiliary lemma to prove the termination of the following function *)
Lemma rename_keeps_depth : forall e x x', depth e = depth (rename e x x').
Proof.
  intros. induction e; simpl.
  - reflexivity.
  - reflexivity.
  - case_eq (x =? x0); intros; simpl; reflexivity.
  - f_equal. rewrite IHe1. rewrite IHe2. reflexivity.
  - f_equal. rewrite IHe1. rewrite IHe2. reflexivity.
  - f_equal. rewrite IHe1. rewrite IHe2. reflexivity.
  - f_equal. rewrite IHe. reflexivity.
  - case_eq (x =? x0); intros; simpl.
    + f_equal. rewrite IHe1. rewrite IHe2. reflexivity.
    + f_equal. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

(** Function to test alpha-equivalence of two expressions *)
Function alpha_equiv (e e' : EExp) {measure depth e} : bool :=
  match e, e' with
  | EId x, EId x' => x =? x'
  | ELet e1 x e2, ELet e1' x' e2' =>
    let z := (max (get_fresh_var e2) (get_fresh_var e2')) in
      alpha_equiv e1 e1' &&
      alpha_equiv (rename e2 x z) (rename e2' x' z)
  | ENum n, ENum n' => n =? n'
  | EStr s, EStr s' => eqb s s'
  | EPlus e1 e2, EPlus e1' e2' => alpha_equiv e1 e1' && alpha_equiv e2 e2'
  | ETimes e1 e2, ETimes e1' e2' => alpha_equiv e1 e1' && alpha_equiv e2 e2'
  | ECat e1 e2, ECat e1' e2' => alpha_equiv e1 e1' && alpha_equiv e2 e2'
  | ELen e1, ELen e1' => alpha_equiv e1 e1'
  | _, _ => false
  end.
Proof.
  intros. simpl. lia.
  intros. simpl. lia.
  intros. simpl. lia.
  intros. simpl. lia.
  intros. simpl. lia.
  intros. simpl. lia.
  intros. simpl. lia.
  intros. simpl.
  rewrite <- (rename_keeps_depth _ x (max (get_fresh_var e2) (get_fresh_var e2'))).
  lia.
  intros. simpl. lia.
Qed.

(** If two expressions have the same structure *)
Inductive same_structure : EExp -> EExp -> Prop :=
  | same_structure_id : forall x x',
      same_structure (EId x) (EId x')
  | same_structure_let : forall e1 x e2 e1' x' e2',
      same_structure e1 e1' -> same_structure e2 e2' -> same_structure (ELet e1 x e2) (ELet e1' x' e2')
  | same_structure_num : forall n n',
      same_structure (ENum n) (ENum n')
  | same_structure_str : forall s s',
      same_structure (EStr s) (EStr s')
  | same_structure_plus : forall e1 e2 e1' e2',
      same_structure e1 e1' -> same_structure e2 e2' -> same_structure (EPlus e1 e2) (EPlus e1' e2')
  | same_structure_times : forall e1 e2 e1' e2',
      same_structure e1 e1' -> same_structure e2 e2' -> same_structure (ETimes e1 e2) (ETimes e1' e2')
  | same_structure_cat : forall e1 e2 e1' e2',
      same_structure e1 e1' -> same_structure e2 e2' -> same_structure (ECat e1 e2) (ECat e1' e2')
  | same_structure_len : forall e1 e1',
      same_structure e1 e1' -> same_structure (ELen e1) (ELen e1').

(** Returns the True proposition if the constructors of the expressions are not the same *)
Function diff_constructor (e e' : EExp) : Prop :=
  match e, e' with
    | ENum _, ENum _ => False
    | EStr _, EStr _ => False
    | EId _, EId _ => False
    | EPlus _ _, EPlus _ _ => False
    | ETimes _ _, ETimes _ _ => False
    | ECat _ _, ECat _ _ => False
    | ELen _, ELen _ => False
    | ELet _ _ _, ELet _ _ _ => False
    | _, _ => True
    end.

(** Give fresh renamining to all bound variables and free variables in [bv] by summing [offset] *)
Fixpoint fresh_rename (e: EExp) (bv: set) (offset: nat) : EExp :=
  match e with
  | EId x => if bv x then EId (x + offset) else EId x
  | ELet e1 x e2 => let e1' := fresh_rename e1 bv offset in
                    let x' := x + offset in
                    let e2' := fresh_rename e2 (updateSet bv x) offset in
                    ELet e1' x' e2'
  | ENum _ => e
  | EStr _ => e
  | EPlus e1 e2 => EPlus (fresh_rename e1 bv offset) (fresh_rename e2 bv offset)
  | ETimes e1 e2 => ETimes (fresh_rename e1 bv offset) (fresh_rename e2 bv offset)
  | ECat e1 e2 => ECat (fresh_rename e1 bv offset) (fresh_rename e2 bv offset)
  | ELen e1 => ELen (fresh_rename e1 bv offset)
  end.

(** Substitution [[e'/x]e] without capture avoidance *)
Fixpoint subst' (e' : EExp) (x : nat) (e : EExp) : EExp :=
  match e with
  | EId y => if x =? y then e' else e
  | ELet e1 y e2 => if x =? y then
                      ELet (subst' e' x e1) y e2
                    else
                      ELet (subst' e' x e1) y (subst' e' x e2)
  | ENum _ => e
  | EStr _ => e
  | EPlus e1 e2 => EPlus (subst' e' x e1) (subst' e' x e2)
  | ETimes e1 e2 => ETimes (subst' e' x e1) (subst' e' x e2)
  | ECat e1 e2 => ECat (subst' e' x e1) (subst' e' x e2)
  | ELen e1 => ELen (subst' e' x e1)
  end.

(** Substitution [[e'/x]e] with capture avoidance *)
Definition subst (e' : EExp) (x : nat) (e : EExp)  : EExp :=
  (* Rename all bound variables in e to avoid free variables in e' *)
  let offset := max (get_fresh_var e) (get_fresh_var e') in
    subst' e' x (fresh_rename e emptySet offset).

(** Types *)
Inductive EType : Type :=
  | TNum
  | TStr.

(** Typing context *)
Definition context := partial_map EType.

(** Empty typing context *)
Definition empty_ctx := @empty EType.

(** Rules of the type system *)
Inductive hastype : context -> EExp -> EType -> Prop :=
  | T_Var : forall Gamma x t, Gamma x = Some(t) -> hastype Gamma (EId x) t
  | T_Str : forall Gamma s, hastype Gamma (EStr s) TStr
  | T_Num : forall Gamma n, hastype Gamma (ENum n) TNum
  | T_Plus : forall Gamma e1 e2, hastype Gamma e1 TNum -> hastype Gamma e2 TNum -> hastype Gamma (EPlus e1 e2) TNum
  | T_Times : forall Gamma e1 e2, hastype Gamma e1 TNum -> hastype Gamma e2 TNum -> hastype Gamma (ETimes e1 e2) TNum
  | T_Cat : forall Gamma e1 e2, hastype Gamma e1 TStr -> hastype Gamma e2 TStr -> hastype Gamma (ECat e1 e2) TStr
  | T_Len : forall Gamma e, hastype Gamma e TStr -> hastype Gamma (ELen e) TNum
  | T_Let : forall Gamma e1 t1 x e2 t2,
              hastype Gamma e1 t1 -> hastype (update Gamma x t1) e2 t2 -> hastype Gamma (ELet e1 x e2) t2.

(** Values of the language *)
Inductive Val : EExp -> Prop :=
  | valNum : forall n, (Val (ENum n))
  | valStr : forall s, (Val (EStr s)).

Definition is_val (e : EExp) : bool :=
  match e with ENum _ | EStr _ => true | _ => false end.

Lemma val_rel_equiv_is_val : forall e,
  Val e <-> is_val e = true.
Proof.
  intro; split; intro.
  - inversion H; subst; simpl; auto.
  - destruct e.
    constructor. constructor.
    all: simpl in H; discriminate.
Qed.

(** Small-step relation *)
Inductive Eval : EExp -> EExp -> Prop :=
  | evalPlus1 : forall n1 n2 n, n = n1 + n2 -> Eval (EPlus (ENum n1) (ENum n2)) (ENum n)
  | evalPlus2 : forall e1 e2 e1', Eval e1 e1' -> Eval (EPlus e1 e2) (EPlus e1' e2)
  | evalPlus3 : forall e1 e2 e2', Val e1 -> Eval e2 e2' -> Eval (EPlus e1 e2) (EPlus e1 e2')
  | evalTimes1 : forall n1 n2 n, n = n1 * n2 -> Eval (ETimes (ENum n1) (ENum n2)) (ENum n)
  | evalTimes2 : forall e1 e2 e1', Eval e1 e1' -> Eval (ETimes e1 e2) (ETimes e1' e2)
  | evalTimes3 : forall e1 e2 e2', Val e1 -> Eval e2 e2' -> Eval (ETimes e1 e2) (ETimes e1 e2')
  | evalCat1 : forall s1 s2 s, s = append s1 s2 -> Eval (ECat (EStr s1) (EStr s2)) (EStr s)
  | evalCat2 : forall e1 e2 e1', Eval e1 e1' -> Eval (ECat e1 e2) (ECat e1' e2)
  | evalCat3 : forall e1 e2 e2', Val e1 -> Eval e2 e2' -> Eval (ECat e1 e2) (ECat e1 e2')
  | evalLen1 : forall n s1, n = length s1 -> Eval (ELen (EStr s1)) (ENum n)
  | evalLen2 : forall e1 e1', Eval e1 e1' -> Eval (ELen e1) (ELen e1')
  | evalLet1 : forall e1 x e2 e1', Eval e1 e1' -> Eval (ELet e1 x e2) (ELet e1' x e2)
  | evalLet2 : forall e1 x e2, Val e1 -> Eval (ELet e1 x e2) (subst e1 x e2).

(** Star relation *)
Inductive EvalStar : EExp -> EExp -> Prop :=
  | star0 : forall e, EvalStar e e
  | starN : forall e e' e'', Eval e e'' -> EvalStar e'' e' -> EvalStar e e'.

(** N-times relation *)
Inductive EvalN : EExp -> EExp -> nat -> Prop :=
  | eval0 : forall e, EvalN e e 0
  | evalN : forall e e' e'' n, Eval e e' -> EvalN e' e'' n -> EvalN e e'' (S n).

(** Based on https://softwarefoundations.cis.upenn.edu/plf-current/StlcProp.html#lab244 *)
Definition stuck e : Prop := (~ exists e', Eval e e') /\ ~ Val e.

(** Big-step relation *)
Inductive EvalBig : EExp -> EExp -> Prop :=
  | evalBigNum : forall n, EvalBig (ENum n) (ENum n)
  | evalBigStr : forall s, EvalBig (EStr s) (EStr s)
  | evalBigPlus : forall e1 e2 n1 n2,
      EvalBig e1 (ENum n1) -> EvalBig e2 (ENum n2) -> EvalBig (EPlus e1 e2) (ENum (n1 + n2))
  | evalBigTimes : forall e1 e2 n1 n2,
      EvalBig e1 (ENum n1) -> EvalBig e2 (ENum n2) -> EvalBig (ETimes e1 e2) (ENum (n1 * n2))
  | evalBigCat : forall e1 e2 s1 s2,
      EvalBig e1 (EStr s1) -> EvalBig e2 (EStr s2) -> EvalBig (ECat e1 e2) (EStr (append s1 s2))
  | evalBigLen : forall e1 s1,
      EvalBig e1 (EStr s1) -> EvalBig (ELen e1) (ENum (length s1))
  | evalBigLet : forall e1 e2 x e1' e2',
      EvalBig e1 e1' -> EvalBig (subst e1' x e2) e2' ->  EvalBig (ELet e1 x e2) e2'.

(** Small-step implementation *)
Fixpoint eval (e : EExp) : option EExp :=
  match e with
  | EId _ | ENum _ | EStr _ => None
  | EPlus e1 e2 =>
    match e1, e2 with
    | ENum n1, ENum n2 => Some (ENum (n1 + n2))
    | _, _ =>
      if is_val e1 then
        match eval e2 with
        | Some e2' => Some (EPlus e1 e2')
        | None => None
        end
      else
        match eval e1 with
        | Some e1' => Some (EPlus e1' e2)
        | None => None
        end
      end
  | ETimes e1 e2 =>
    match e1, e2 with
    | ENum n1, ENum n2 => Some (ENum (n1 * n2))
    | _, _ =>
      if is_val e1 then
        match eval e2 with
        | Some e2' => Some (ETimes e1 e2')
        | None => None
        end
      else
        match eval e1 with
        | Some e1' => Some (ETimes e1' e2)
        | None => None
        end
      end
  | ECat e1 e2 =>
    match e1, e2 with
    | EStr s1, EStr s2 => Some (EStr (append s1 s2))
    | _, _ =>
      if is_val e1 then
        match eval e2 with
        | Some e2' => Some (ECat e1 e2')
        | None => None
        end
      else
        match eval e1 with
        | Some e1' => Some (ECat e1' e2)
        | None => None
        end
      end
  | ELen e1 =>
    match e1 with
    | EStr s1 => Some (ENum (length s1))
    | _ =>
      match eval e1 with
      | Some e1' => Some (ELen e1')
      | None => None
      end
    end
  | ELet e1 x e2 =>
    if is_val e1 then
      Some (subst e1 x e2)
    else
      match eval e1 with
      | Some e1' => Some (ELet e1' x e2)
      | None => None
      end
  end.

(** Function to count the number of subexpressions *)
Fixpoint subexprs_count (e : EExp) : nat :=
  match e with
  | EId _ => 1
  | ELet e1 x e2 => 1 + subexprs_count e1 + subexprs_count e2
  | ENum _ => 1
  | EStr _ => 1
  | EPlus e1 e2 => 1 + subexprs_count e1 + subexprs_count e2
  | ETimes e1 e2 => 1 + subexprs_count e1 + subexprs_count e2
  | ECat e1 e2 => 1 + subexprs_count e1 + subexprs_count e2
  | ELen e1 => 1 + subexprs_count e1
  end.

(** Big-step implementation can be found in the file [Theorems_Eval.v] *)
