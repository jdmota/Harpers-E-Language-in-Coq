Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Strings.String.
From Coq Require Import Logic.Eqdep_dec.
From PFPL Require Import PartialMap_Set.
From PFPL Require Import Definitions.

Lemma same_structure_refl :
  forall e, same_structure e e.
Proof.
  induction e; constructor; auto.
Qed.

Lemma same_structure_sym :
  forall e e', same_structure e e' -> same_structure e' e.
Proof.
  intros e e' H. induction H; constructor; auto.
Qed.

Lemma same_structure_trans : forall e e' e'',
  same_structure e e' -> same_structure e' e'' ->
  same_structure e e''.
Proof.
  intros e e' e'' H. generalize dependent e''.
  induction H; intros.
  - inversion H. subst. constructor.
  - inversion H1. subst. constructor; auto.
  - inversion H. subst. constructor.
  - inversion H. subst. constructor.
  - inversion H1. subst. constructor; auto.
  - inversion H1. subst. constructor; auto.
  - inversion H1. subst. constructor; auto.
  - inversion H0. subst. constructor; auto.
Qed.

Lemma same_structure_equal_constructor :
  forall e e', same_structure e e' -> ~ diff_constructor e e'.
Proof.
  intros.
  induction H; subst; intro; simpl in H; contradiction.
Qed.

Lemma same_structure_num : forall e' n,
  same_structure (ENum n) e' -> (exists n', e' = ENum n').
Proof.
  intros. inversion H; subst.
  exists n'. auto.
Qed.

Lemma same_structure_str : forall e' s,
  same_structure (EStr s) e' -> (exists s', e' = EStr s').
Proof.
  intros. inversion H; subst.
  exists s'. auto.
Qed.

Lemma same_structure_id : forall e' x,
  same_structure (EId x) e' -> (exists x', e' = EId x').
Proof.
  intros. inversion H; subst.
  exists x'. auto.
Qed.

Lemma same_structure_plus : forall e1 e2 e',
  same_structure (EPlus e1 e2) e' ->
  (exists e1' e2', e' = EPlus e1' e2').
Proof.
  intros. inversion H; subst.
  exists e1'. exists e2'. auto.
Qed.

Lemma same_structure_times : forall e1 e2 e',
  same_structure (ETimes e1 e2) e' ->
  (exists e1' e2', e' = ETimes e1' e2').
Proof.
  intros. inversion H; subst.
  exists e1'. exists e2'. auto.
Qed.

Lemma same_structure_cat : forall e1 e2 e',
  same_structure (ECat e1 e2) e' ->
  (exists e1' e2', e' = ECat e1' e2').
Proof.
  intros. inversion H; subst.
  exists e1'. exists e2'. auto.
Qed.

Lemma same_structure_len : forall e1 e',
  same_structure (ELen e1) e' ->
  (exists e1', e' = ELen e1').
Proof.
  intros. inversion H; subst.
  exists e1'. auto.
Qed.

Lemma same_structure_let : forall e1 e2 x e',
  same_structure (ELet e1 x e2) e' ->
  (exists e1' x' e2', e' = ELet e1' x' e2').
Proof.
  intros. inversion H; subst.
  exists e1'. exists x'. exists e2'. auto.
Qed.
