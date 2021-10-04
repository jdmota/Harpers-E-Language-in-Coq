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
From PFPL Require Import Induction_Expr.
From PFPL Require Import Lemmas_AlphaEquiv.
From PFPL Require Import Lemmas_Rename.
From PFPL Require Import Lemmas_FreshRename.
From PFPL Require Import Lemmas_Rename_FreshRename.
From PFPL Require Import Lemmas_FreshRename_AlphaEquiv.

(** Applying a fresh_renaming produces an expression
where the bound variables do not conflict with any free variables of the replacement *)
Lemma fresh_rename_removes_conflicts : forall e e' o,
  o = max (get_fresh_var e) (get_fresh_var e') ->
  (forall v, bound_vars (fresh_rename e emptySet o) v = true -> free_vars e' v = false).
Proof.
  intros.
  assert (T := fresh_rename_new_bounds e emptySet o v H0).
  apply not_in_conj_not_in_free.
  apply fresh_var_not_in_conj_vars.
  apply (le_trans _ o _).
  rewrite H. apply le_max_r.
  assumption.
Qed.

Lemma not_in_free_vars_after_subst : forall e e' x,
  free_vars e' x = false ->
  free_vars (subst' e' x e) x = false.
Proof.
  induction e; intros; simpl.
  - reflexivity.
  - reflexivity.
  - case_eq (x0 =? x); intro X0X.
    assumption.
    simpl. unfold singletonSet. rewrite Nat.eqb_sym.
    rewrite X0X. reflexivity.
  - unfold unionSet. apply orb_false_iff.
    split; [apply IHe1 | apply IHe2].
    all: assumption.
  - unfold unionSet. apply orb_false_iff.
    split; [apply IHe1 | apply IHe2].
    all: assumption.
  - unfold unionSet. apply orb_false_iff.
    split; [apply IHe1 | apply IHe2].
    all: assumption.
  - apply IHe. assumption.
  - case_eq (x0 =? x); intro X0X;
    simpl; unfold unionSet; apply orb_false_iff;
    split.
    + apply IHe1. assumption.
    + unfold removeFromSet. rewrite Nat.eqb_sym. rewrite X0X. reflexivity.
    + apply IHe1. assumption.
    + unfold removeFromSet. rewrite Nat.eqb_sym. rewrite X0X.
      apply IHe2. assumption.
Qed.

Lemma subst_non_free_var : forall e e' x,
  free_vars e x = false ->
  e = subst' e' x e.
Proof.
  induction e; intros; simpl.
  - reflexivity.
  - reflexivity.
  - simpl in H. unfold singletonSet in H.
    rewrite Nat.eqb_sym. destruct (x =? x0).
    discriminate. reflexivity.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H as [H H'].
    f_equal; [apply IHe1 | apply IHe2].
    all: assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H as [H H'].
    f_equal; [apply IHe1 | apply IHe2].
    all: assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H as [H H'].
    f_equal; [apply IHe1 | apply IHe2].
    all: assumption.
  - simpl in H. f_equal. apply IHe. assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H as [H H'].
    unfold removeFromSet in H'.
    rewrite Nat.eqb_sym in H'.
    case_eq (x0 =? x); intro X0X; f_equal.
    + apply IHe1. assumption.
    + apply IHe1. assumption.
    + rewrite X0X in H'. apply IHe2. assumption.
Qed.

Lemma subst'_same_depth : forall e e' e'' x,
  depth e' = 0 ->
  depth e'' = depth e ->
  depth e'' = depth (subst' e' x e).
Proof.
  induction e; intros; simpl; simpl in H0.
  - assumption.
  - assumption.
  - destruct (x0 =? x).
    rewrite H. rewrite H0. reflexivity.
    simpl. assumption.
  - rewrite H0. f_equal.
    assert (depth e1 = depth (subst' e' x e1)).
    apply IHe1. assumption. reflexivity.
    assert (depth e2 = depth (subst' e' x e2)).
    apply IHe2. assumption. reflexivity.
    rewrite H1. rewrite H2. reflexivity.
  - rewrite H0. f_equal.
    assert (depth e1 = depth (subst' e' x e1)).
    apply IHe1. assumption. reflexivity.
    assert (depth e2 = depth (subst' e' x e2)).
    apply IHe2. assumption. reflexivity.
    rewrite H1. rewrite H2. reflexivity.
  - rewrite H0. f_equal.
    assert (depth e1 = depth (subst' e' x e1)).
    apply IHe1. assumption. reflexivity.
    assert (depth e2 = depth (subst' e' x e2)).
    apply IHe2. assumption. reflexivity.
    rewrite H1. rewrite H2. reflexivity.
  - rewrite H0. f_equal.
    assert (depth e = depth (subst' e' x e)).
    apply IHe. assumption. reflexivity. assumption.
  - rewrite H0. case_eq (x0 =? x); intro; simpl; f_equal.
    + assert (depth e1 = depth (subst' e' x0 e1)).
      apply IHe1. assumption. reflexivity.
      rewrite H2. reflexivity.
    + assert (depth e1 = depth (subst' e' x0 e1)).
      apply IHe1. assumption. reflexivity.
      assert (depth e2 = depth (subst' e' x0 e2)).
      apply IHe2. assumption. reflexivity.
      rewrite H2. rewrite H3. reflexivity.
Qed.

Lemma subst_same_depth : forall e e' x,
  depth e' = 0 ->
  depth e = depth (subst e' x e).
Proof.
  intros. unfold subst.
  apply subst'_same_depth.
  assumption.
  rewrite <- fresh_rename_keeps_depth.
  reflexivity.
Qed.
