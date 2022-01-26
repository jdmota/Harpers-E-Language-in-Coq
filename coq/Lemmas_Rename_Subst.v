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
From PFPL Require Import Lemmas_Vars.
From PFPL Require Import Lemmas_Rename.
From PFPL Require Import Lemmas_Same_Structure.
From PFPL Require Import Lemmas_AlphaEquiv.
From PFPL Require Import Lemmas_Rename.
From PFPL Require Import Lemmas_FreshRename.
From PFPL Require Import Lemmas_Rename_FreshRename.
From PFPL Require Import Lemmas_FreshRename_AlphaEquiv.
From PFPL Require Import Lemmas_Subst.

Lemma rename_vs_subst : forall e e' x y z,
  (x =? y) = false ->
  (x =? z) = false ->
  free_vars e' y = false ->
  rename (subst' e' x e) y z = subst' e' x (rename e y z).
Proof.
  induction e; intros; simpl.
  - reflexivity.
  - reflexivity.
  - case_eq (x0 =? x); intro X0X.
    + apply Nat.eqb_eq in X0X. subst.
      rewrite Nat.eqb_sym. rewrite H.
      simpl. rewrite Nat.eqb_refl.
      symmetry.
      apply rename_non_existant_free. assumption.
    + simpl. case_eq (y =? x); intro YX.
      * apply Nat.eqb_eq in YX. subst.
        simpl. rewrite H0. reflexivity.
      * simpl. rewrite X0X. reflexivity.
  - f_equal.
    apply IHe1. assumption. assumption. assumption.
    apply IHe2. assumption. assumption. assumption.
  - f_equal.
    apply IHe1. assumption. assumption. assumption.
    apply IHe2. assumption. assumption. assumption.
  - f_equal.
    apply IHe1. assumption. assumption. assumption.
    apply IHe2. assumption. assumption. assumption.
  - f_equal.
    apply IHe. assumption. assumption. assumption.
  - case_eq (x0 =? x); intro X0X.
    + apply Nat.eqb_eq in X0X. subst.
      rewrite Nat.eqb_sym. rewrite H.
      simpl. rewrite Nat.eqb_refl.
      rewrite Nat.eqb_sym. rewrite H.
      f_equal.
      apply IHe1. assumption. assumption. assumption.
    + simpl. case_eq (y =? x); intro YX.
      * apply Nat.eqb_eq in YX. subst.
        simpl. rewrite H.
        f_equal.
        apply IHe1. assumption. assumption. assumption.
      * simpl. rewrite X0X. f_equal.
        apply IHe1. assumption. assumption. assumption.
        apply IHe2. assumption. assumption. assumption.
Qed.

Lemma subst'_vs_rename : forall e e' x x',
  all_vars e x' = false ->
  (subst' e' x e) = (subst' e' x' (rename e x x')).
Proof.
  induction e; intros e' z z' A; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (z =? x); simpl.
    rewrite Nat.eqb_refl. reflexivity.
    simpl in A. unfold singletonSet in A.
    rewrite Nat.eqb_sym. destruct (x =? z').
    discriminate. reflexivity.
  - simpl in A. unfold unionSet in A.
    apply orb_false_iff in A. destruct A as [A A'].
    f_equal; [apply IHe1 | apply IHe2]; auto.
  - simpl in A. unfold unionSet in A.
    apply orb_false_iff in A. destruct A as [A A'].
    f_equal; [apply IHe1 | apply IHe2]; auto.
  - simpl in A. unfold unionSet in A.
    apply orb_false_iff in A. destruct A as [A A'].
    f_equal; [apply IHe1 | apply IHe2]; auto.
  - simpl in A. f_equal. apply IHe. auto.
  - simpl in A. unfold unionSet in A.
    apply orb_false_iff in A. destruct A as [A A'].
    unfold updateSet in A'.
    case_eq (x =? z'); intro XZ'; rewrite XZ' in A'.
    discriminate.
    case_eq (z =? x); intro ZX.
    + apply Nat.eqb_eq in ZX. subst z.
      simpl. rewrite Nat.eqb_sym. rewrite XZ'.
      f_equal. auto.
      apply subst_non_free_var.
      apply not_in_expr_not_free. auto.
    + simpl. rewrite Nat.eqb_sym. rewrite XZ'.
      f_equal. auto. apply IHe2. auto.
Qed.
