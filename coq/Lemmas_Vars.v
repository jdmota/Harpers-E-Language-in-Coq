Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Strings.String.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lia.
From PFPL Require Import PartialMap_Set.
From PFPL Require Import Definitions.

Lemma all_vars_free_plus_bound : forall e, all_vars e = unionSet (free_vars e) (bound_vars e).
Proof.
  intros e. apply functional_extensionality. intros v.
  unfold unionSet. induction e.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. unfold emptySet. rewrite orb_false_r. reflexivity.
  - simpl. unfold unionSet. rewrite IHe1. rewrite IHe2.
    case_eq (free_vars e1 v); intros; subst; simpl.
    reflexivity.
    rewrite orb_comm.
    case_eq (free_vars e2 v); intros; subst; simpl.
    reflexivity.
    rewrite orb_comm.
    reflexivity.
  - simpl. unfold unionSet. rewrite IHe1. rewrite IHe2.
    case_eq (free_vars e1 v); intros; subst; simpl.
    reflexivity.
    rewrite orb_comm.
    case_eq (free_vars e2 v); intros; subst; simpl.
    reflexivity.
    rewrite orb_comm.
    reflexivity.
  - simpl. unfold unionSet. rewrite IHe1. rewrite IHe2.
    case_eq (free_vars e1 v); intros; subst; simpl.
    reflexivity.
    rewrite orb_comm.
    case_eq (free_vars e2 v); intros; subst; simpl.
    reflexivity.
    rewrite orb_comm.
    reflexivity.
  - simpl. assumption.
  - simpl. unfold unionSet. unfold updateSet. unfold removeFromSet. rewrite IHe1. rewrite IHe2.
    case_eq (free_vars e1 v); intros; subst; simpl.
    reflexivity.
    rewrite orb_comm.
    case_eq (x =? v); intros; subst; simpl.
    rewrite orb_true_r. reflexivity.
    case_eq (free_vars e2 v); intros; subst; simpl.
    reflexivity.
    rewrite orb_comm. reflexivity.
Qed.

Lemma not_in_expr_not_free : forall e z,
  all_vars e z = false -> free_vars e z = false.
Proof.
  intros. induction e; simpl; simpl in H.
  - assumption.
  - assumption.
  - assumption.
  - unfold unionSet. unfold unionSet in H.
    apply orb_false_iff. apply orb_false_iff in H. destruct H.
    split.
    apply IHe1. assumption. apply IHe2. assumption.
  - unfold unionSet. unfold unionSet in H.
    apply orb_false_iff. apply orb_false_iff in H. destruct H.
    split.
    apply IHe1. assumption. apply IHe2. assumption.
  - unfold unionSet. unfold unionSet in H.
    apply orb_false_iff. apply orb_false_iff in H. destruct H.
    split.
    apply IHe1. assumption. apply IHe2. assumption.
  - apply IHe. assumption.
  - unfold unionSet. unfold unionSet in H.
    apply orb_false_iff. apply orb_false_iff in H. destruct H.
    unfold updateSet in H0.
    split.
    apply IHe1. assumption.
    unfold removeFromSet.
    destruct (x =? z). discriminate.
    apply IHe2. assumption.
Qed.

Lemma fresh_var_not_in_all_vars :
  forall e v, get_fresh_var e <= v -> all_vars e v = false.
Proof.
  intros e. induction e; intros v H.
  - simpl. unfold emptySet. reflexivity.
  - simpl. unfold emptySet. reflexivity.
  - simpl. unfold singletonSet. simpl in H.
    case_eq (x =? v); intros. apply Nat.eqb_eq in H0. lia.
    reflexivity.
  - simpl. unfold unionSet. simpl in H.
    apply orb_false_iff. split.
    apply IHe1. lia. apply IHe2. lia.
  - simpl. unfold unionSet. simpl in H.
    apply orb_false_iff. split.
    apply IHe1. lia. apply IHe2. lia.
  - simpl. unfold unionSet. simpl in H.
    apply orb_false_iff. split.
    apply IHe1. lia. apply IHe2. lia.
  - simpl. apply IHe. simpl in H. auto.
  - simpl. unfold unionSet. unfold updateSet. simpl in H.
    apply orb_false_iff. split.
    apply IHe1. lia.
    case_eq (x =? v); intros.
    apply Nat.eqb_eq in H0. destruct (get_fresh_var e2); lia.
    apply IHe2. destruct (get_fresh_var e2); lia.
Qed.

Lemma fresh_var_not_in_all_vars_left :
  forall e e', all_vars e (max (get_fresh_var e) (get_fresh_var e')) = false.
Proof.
  intros. apply fresh_var_not_in_all_vars. lia.
Qed.

Lemma fresh_var_not_in_all_vars_right :
  forall e e', all_vars e' (max (get_fresh_var e) (get_fresh_var e')) = false.
Proof.
  intros. apply fresh_var_not_in_all_vars. lia.
Qed.

Lemma variables_below_fresh : forall e v,
  all_vars e v = true -> v < get_fresh_var e.
Proof.
  intros e. induction e; intros; simpl; simpl in H.
  - unfold emptySet in H. discriminate.
  - unfold emptySet in H. discriminate.
  - unfold singletonSet in H.
    case_eq (x =? v); intros; rewrite H0 in H.
    apply Nat.eqb_eq in H0. lia.
    discriminate.
  - unfold unionSet in H. apply orb_true_iff in H.
    apply max_lt_iff.
    destruct H.
    left. apply IHe1. auto.
    right. apply IHe2. auto.
  - unfold unionSet in H. apply orb_true_iff in H.
    apply max_lt_iff.
    destruct H.
    left. apply IHe1. auto.
    right. apply IHe2. auto.
  - unfold unionSet in H. apply orb_true_iff in H.
    apply max_lt_iff.
    destruct H.
    left. apply IHe1. auto.
    right. apply IHe2. auto.
  - apply IHe. auto.
  - unfold unionSet in H. apply orb_true_iff in H.
    unfold updateSet in H.
    apply max_lt_iff.
    destruct H.
    left. apply IHe1. auto.
    right.
    case_eq (x =? v); intros.
    apply Nat.eqb_eq in H0. subst.
    destruct (get_fresh_var e2).
    lia. lia.
    rewrite H0 in H.
    apply IHe2 in H.
    destruct (get_fresh_var e2).
    lia. lia.
Qed.

Lemma complex_max : forall e e' a b c d newX,
  newX = (max
    (max (get_fresh_var e) (get_fresh_var e'))
    (max (max (S a) (S b)) (max (S c) (S d)))
  ) ->
  (a =? newX) = false /\ (b =? newX) = false /\
  (c =? newX) = false /\ (d =? newX) = false /\
  all_vars e newX = false /\
  all_vars e' newX = false.
Proof.
  intros.
  split. apply Nat.eqb_neq. lia.
  split. apply Nat.eqb_neq. lia.
  split. apply Nat.eqb_neq. lia.
  split. apply Nat.eqb_neq. lia.
  split.
  apply fresh_var_not_in_all_vars. lia.
  apply fresh_var_not_in_all_vars. lia.
Qed.

Lemma complex_max_2 : forall e e' e'' e''' a b c d newX,
  newX = max
    (max
      (max (get_fresh_var e) (get_fresh_var e'))
      (max (get_fresh_var e'') (get_fresh_var e'''))
    )
    (max (max (S a) (S b)) (max (S c) (S d))) ->
  (a =? newX) = false /\ (b =? newX) = false /\
  (c =? newX) = false /\ (d =? newX) = false /\
  all_vars e newX = false /\
  all_vars e' newX = false /\
  all_vars e'' newX = false /\
  all_vars e''' newX = false.
Proof.
  intros.
  split. apply Nat.eqb_neq. lia.
  split. apply Nat.eqb_neq. lia.
  split. apply Nat.eqb_neq. lia.
  split. apply Nat.eqb_neq. lia.
  split. apply fresh_var_not_in_all_vars. lia.
  split. apply fresh_var_not_in_all_vars. lia.
  split. apply fresh_var_not_in_all_vars. lia.
  apply fresh_var_not_in_all_vars. lia.
Qed.

Lemma max_zero : forall a b,
  max a b = 0 -> a = 0 /\ b = 0.
Proof.
  intros. lia.
Qed.

Lemma fresh_var_zero : forall e,
  get_fresh_var e = 0 ->
  (forall e', same_structure e e' -> get_fresh_var e' = 0).
Proof.
  induction e; intros H1 e' H2;
  inversion H2; subst; simpl; simpl in H1.
  - reflexivity.
  - reflexivity.
  - discriminate.
  - apply max_zero in H1. destruct H1 as [H1 H1'].
    assert (T1 := IHe1 H1 e1' H3).
    assert (T2 := IHe2 H1' e2' H5).
    rewrite T1. rewrite T2. auto.
  - apply max_zero in H1. destruct H1 as [H1 H1'].
    assert (T1 := IHe1 H1 e1' H3).
    assert (T2 := IHe2 H1' e2' H5).
    rewrite T1. rewrite T2. auto.
  - apply max_zero in H1. destruct H1 as [H1 H1'].
    assert (T1 := IHe1 H1 e1' H3).
    assert (T2 := IHe2 H1' e2' H5).
    rewrite T1. rewrite T2. auto.
  - apply IHe; assumption.
  - apply max_zero in H1. destruct H1 as [H1 H1'].
    destruct (get_fresh_var e2); discriminate.
Qed.

Lemma all_vars_impl_let_1 : forall e1 x e2 o,
  (forall v : nat,
     all_vars (ELet e1 x e2) v = true ->
     all_vars (ELet e1 x e2) (o + v) = false) ->
  (forall v : nat,
     all_vars e1 v = true ->
     all_vars e1 (o + v) = false).
Proof.
  intros.
  assert (H := H v).
  simpl in H.
  unfold unionSet in H.
  rewrite orb_true_iff in H.
  rewrite orb_false_iff in H.
  assert (H := H (or_introl H0)).
  destruct H. assumption.
Qed.

Lemma all_vars_impl_let_2 : forall e1 x e2 o,
  (forall v : nat,
     all_vars (ELet e1 x e2) v = true ->
     all_vars (ELet e1 x e2) (o + v) = false) ->
  (forall v : nat,
     all_vars e2 v = true ->
     all_vars e2 (o + v) = false).
Proof.
  intros.
  assert (H := H v).
  simpl in H.
  unfold unionSet in H.
  rewrite orb_true_iff in H.
  rewrite orb_false_iff in H.
  unfold updateSet in H.
  rewrite H0 in H.
  assert (T : (if x =? v then true else true) = true).
  destruct (x =? v). reflexivity. reflexivity.
  rewrite T in H. clear T.
  assert (H := H (or_intror Logic.eq_refl)).
  destruct H. destruct (x =? o + v).
  discriminate. assumption.
Qed.

Lemma all_vars_impl_let_x : forall e1 x e2 o,
  (forall v : nat,
     all_vars (ELet e1 x e2) v = true ->
     all_vars (ELet e1 x e2) (o + v) = false) ->
  all_vars e2 (o + x) = false.
Proof.
  intros.
  assert (H := H x).
  simpl in H.
  unfold unionSet in H.
  rewrite orb_true_iff in H.
  rewrite orb_false_iff in H.
  unfold updateSet in H.
  rewrite Nat.eqb_refl in H.
  assert (H := H (or_intror Logic.eq_refl)).
  destruct H.
  destruct (x =? o + x).
  discriminate. assumption.
Qed.

Lemma x_in_let : forall e1 x e2,
  all_vars (ELet e1 x e2) x = true.
Proof.
  intros.
  simpl. unfold unionSet.
  apply orb_true_iff. right.
  unfold updateSet.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma not_in_main_not_in_subexprs : forall e1 x e2 z,
  all_vars (ELet e1 x e2) z = false ->
  all_vars e2 z = false.
Proof.
  intros. simpl in H.
  unfold unionSet in H.
  apply orb_false_iff in H.
  destruct H.
  unfold updateSet in H0.
  destruct (x =? z). discriminate.
  assumption.
Qed.

Lemma all_vars_impl_plus_1 : forall e1 e2 o,
  (forall v : nat,
     all_vars (EPlus e1 e2) v = true ->
     all_vars (EPlus e1 e2) (o + v) = false) ->
  (forall v : nat,
     all_vars e1 v = true ->
     all_vars e1 (o + v) = false).
Proof.
  intros.
  assert (H := H v).
  simpl in H.
  unfold unionSet in H.
  rewrite orb_true_iff in H.
  rewrite orb_false_iff in H.
  assert (H := H (or_introl H0)).
  destruct H. assumption.
Qed.

Lemma all_vars_impl_plus_2 : forall e1 e2 o,
  (forall v : nat,
     all_vars (EPlus e1 e2) v = true ->
     all_vars (EPlus e1 e2) (o + v) = false) ->
  (forall v : nat,
     all_vars e2 v = true ->
     all_vars e2 (o + v) = false).
Proof.
  intros.
  assert (H := H v).
  simpl in H.
  unfold unionSet in H.
  rewrite orb_true_iff in H.
  rewrite orb_false_iff in H.
  unfold updateSet in H.
  assert (H := H (or_intror H0)).
  destruct H. assumption.
Qed.

Lemma all_vars_impl_times_1 : forall e1 e2 o,
  (forall v : nat,
     all_vars (ETimes e1 e2) v = true ->
     all_vars (ETimes e1 e2) (o + v) = false) ->
  (forall v : nat,
     all_vars e1 v = true ->
     all_vars e1 (o + v) = false).
Proof.
  intros.
  assert (H := H v).
  simpl in H.
  unfold unionSet in H.
  rewrite orb_true_iff in H.
  rewrite orb_false_iff in H.
  assert (H := H (or_introl H0)).
  destruct H. assumption.
Qed.

Lemma all_vars_impl_times_2 : forall e1 e2 o,
  (forall v : nat,
     all_vars (ETimes e1 e2) v = true ->
     all_vars (ETimes e1 e2) (o + v) = false) ->
  (forall v : nat,
     all_vars e2 v = true ->
     all_vars e2 (o + v) = false).
Proof.
  intros.
  assert (H := H v).
  simpl in H.
  unfold unionSet in H.
  rewrite orb_true_iff in H.
  rewrite orb_false_iff in H.
  unfold updateSet in H.
  assert (H := H (or_intror H0)).
  destruct H. assumption.
Qed.

Lemma all_vars_impl_cat_1 : forall e1 e2 o,
  (forall v : nat,
     all_vars (ECat e1 e2) v = true ->
     all_vars (ECat e1 e2) (o + v) = false) ->
  (forall v : nat,
     all_vars e1 v = true ->
     all_vars e1 (o + v) = false).
Proof.
  intros.
  assert (H := H v).
  simpl in H.
  unfold unionSet in H.
  rewrite orb_true_iff in H.
  rewrite orb_false_iff in H.
  assert (H := H (or_introl H0)).
  destruct H. assumption.
Qed.

Lemma all_vars_impl_cat_2 : forall e1 e2 o,
  (forall v : nat,
     all_vars (ECat e1 e2) v = true ->
     all_vars (ECat e1 e2) (o + v) = false) ->
  (forall v : nat,
     all_vars e2 v = true ->
     all_vars e2 (o + v) = false).
Proof.
  intros.
  assert (H := H v).
  simpl in H.
  unfold unionSet in H.
  rewrite orb_true_iff in H.
  rewrite orb_false_iff in H.
  unfold updateSet in H.
  assert (H := H (or_intror H0)).
  destruct H. assumption.
Qed.

Lemma all_vars_impl_len : forall e1 o,
  (forall v : nat,
     all_vars (ELen e1) v = true ->
     all_vars (ELen e1) (o + v) = false) ->
  (forall v : nat,
     all_vars e1 v = true ->
     all_vars e1 (o + v) = false).
Proof.
  intros.
  simpl in H.
  apply H. assumption.
Qed.

