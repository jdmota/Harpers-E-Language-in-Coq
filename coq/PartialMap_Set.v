Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Strings.String.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import Logic.FunctionalExtensionality.

(** Based on https://softwarefoundations.cis.upenn.edu/ *)

(* Partial Map *)

Definition partial_map (A : Type) := nat -> (option A).

Definition empty {A : Type} : partial_map A := (fun _ => None).

Definition update {A : Type} (m : partial_map A) (x : nat) (v : A) : partial_map A :=
  fun (x' : nat) => if x =? x' then Some(v) else m x'.

Notation "x '|->' v ';' m" := (update m x v) (at level 100, v at next level, right associativity).

Lemma update_neq : forall A (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma update_permute : forall A (m : partial_map A) v1 v2 x1 x2,
  x2 <> x1 -> (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 H.
  apply functional_extensionality. intros. unfold update.
  case_eq (x1 =? x); case_eq (x2 =? x); intros.
  - apply Nat.eqb_eq in H0. apply Nat.eqb_eq in H1. subst. unfold not in H.
    assert (Trivial : x = x). { reflexivity. }
    apply H in Trivial. contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. apply functional_extensionality. intros. unfold update.
  case_eq (x =? x0); intros.
  - reflexivity.
  - reflexivity.
Qed.

(* Set *)

Definition set := nat -> bool.
Definition emptySet : set := (fun _ => false).
Definition singletonSet (v : nat) : set := fun (v' : nat) => if v =? v' then true else false.
Definition updateSet (s : set) (v : nat) : set := fun (v' : nat) => if v =? v' then true else s v'.
Definition removeFromSet (s : set) (v : nat) : set := fun (v' : nat) => if v =? v' then false else s v'.
Definition unionSet (s1 s2 : set) : set := fun (v : nat) => s1 v || s2 v.
Definition intersectionSet (s1 s2 : set) : set := fun (v : nat) => s1 v && s2 v.

Lemma update_set_permute : forall s a b,
  updateSet (updateSet s a) b = updateSet (updateSet s b) a.
Proof.
  intros.
  unfold updateSet.
  apply functional_extensionality. intros.
  destruct (a =? x); destruct (b =? x).
  all: reflexivity.
Qed.

Lemma remove_from_set_permute : forall s a b,
  removeFromSet (removeFromSet s a) b = removeFromSet (removeFromSet s b) a.
Proof.
  intros.
  unfold removeFromSet.
  apply functional_extensionality. intros.
  destruct (a =? x); destruct (b =? x).
  all: reflexivity.
Qed.

Lemma singleton_set_equals_update_empty : forall x,
  singletonSet x = updateSet emptySet x.
Proof.
  intros.
  unfold updateSet. unfold singletonSet.
  apply functional_extensionality. intros.
  unfold emptySet. reflexivity.
Qed.

Lemma update_set_permute_singleton : forall a b,
  updateSet (singletonSet a) b = updateSet (singletonSet b) a.
Proof.
  intros.
  unfold updateSet.
  apply functional_extensionality. intros.
  case_eq (a =? x); case_eq (b =? x); intros.
  all: try unfold singletonSet.
  all: try rewrite H.
  all: try rewrite H0.
  all: try reflexivity.
Qed.

Lemma update_set_permute_remove : forall s a b,
  (a =? b) = false ->
  updateSet (removeFromSet s a) b = removeFromSet (updateSet s b) a.
Proof.
  intros.
  apply functional_extensionality. intros.
  unfold updateSet. unfold removeFromSet.
  case_eq (a =? x); case_eq (b =? x); intros.
  apply Nat.eqb_eq in H0. apply Nat.eqb_eq in H1. subst.
  rewrite Nat.eqb_refl in H. discriminate.
  all: reflexivity.
Qed.

Lemma update_set_shadow : forall s a,
  s a = true -> s = updateSet s a.
Proof.
  intros.
  unfold updateSet.
  apply functional_extensionality. intros.
  case_eq (a =? x); intros.
  apply Nat.eqb_eq in H0. subst. assumption.
  reflexivity.
Qed.

Lemma update_set_twice : forall s x,
  (updateSet (updateSet s x) x) = (updateSet s x).
Proof.
  intros.
  apply functional_extensionality. intros.
  unfold updateSet.
  destruct (x =? x0).
  reflexivity.
  reflexivity.
Qed.

Lemma remove_from_set_twice : forall s x,
  (removeFromSet (removeFromSet s x) x) = (removeFromSet s x).
Proof.
  intros.
  apply functional_extensionality. intros.
  unfold removeFromSet.
  destruct (x =? x0).
  reflexivity.
  reflexivity.
Qed.

Lemma remove_after_update_set_1 : forall s x,
  s x = false ->
  (removeFromSet (updateSet s x) x) = s.
Proof.
  intros.
  apply functional_extensionality. intros.
  unfold removeFromSet.
  case_eq (x =? x0); intro.
  apply Nat.eqb_eq in H0. subst. symmetry. assumption.
  unfold updateSet. rewrite H0. reflexivity.
Qed.

Lemma remove_after_update_set_2 : forall s x,
  (removeFromSet (updateSet s x) x) = removeFromSet s x.
Proof.
  intros.
  apply functional_extensionality. intros.
  unfold removeFromSet.
  unfold updateSet.
  destruct (x =? x0).
  all: reflexivity.
Qed.

Lemma remove_from_empty : forall x,
  removeFromSet emptySet x = emptySet.
Proof.
  intros.
  apply functional_extensionality. intros.
  unfold removeFromSet. unfold emptySet.
  destruct (x =? x0). all: reflexivity.
Qed.

Lemma remove_from_singleton : forall x,
  removeFromSet (singletonSet x) x = emptySet.
Proof.
  intros.
  apply functional_extensionality. intros.
  unfold removeFromSet. unfold singletonSet.
  destruct (x =? x0). all: reflexivity.
Qed.

Lemma remove_not_existant_from_singleton : forall x x',
  (x =? x') = false ->
  removeFromSet (singletonSet x) x' = singletonSet x.
Proof.
  intros.
  apply functional_extensionality. intros.
  unfold removeFromSet. unfold singletonSet.
  case_eq (x =? x0); case_eq (x' =? x0); intros.
  all: try reflexivity.
  apply Nat.eqb_eq in H1. subst.
  apply Nat.eqb_eq in H0. subst.
  rewrite Nat.eqb_refl in H. discriminate.
Qed.
