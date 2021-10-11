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
