Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Strings.String.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import Logic.FunctionalExtensionality.
From PFPL Require Import PartialMap_Set.
From PFPL Require Import Definitions.

Lemma all_vars_free_plus_bound : forall e, conj_vars e = unionSet (free_vars e) (bound_vars e).
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

Lemma not_in_conj_not_in_free : forall e z,
  conj_vars e z = false -> free_vars e z = false.
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

Lemma fresh_var_not_in_conj_vars :
  forall e v, get_fresh_var e <= v -> conj_vars e v = false.
Proof.
  intros e. induction e; intros v H.
  - simpl. unfold emptySet. reflexivity.
  - simpl. unfold emptySet. reflexivity.
  - simpl. unfold singletonSet. case_eq (x =? S x); intros.
    + apply Nat.eqb_eq in H0. apply neq_succ_diag_r in H0. contradiction.
    + simpl in H. case_eq (x =? v); intros.
      * apply Nat.eqb_eq in H1. subst. apply nle_succ_diag_l in H. contradiction.
      * reflexivity.
  - simpl. unfold unionSet. simpl in H.
    assert (H1 := max_lub_l (get_fresh_var e1) (get_fresh_var e2) v H).
    assert (H2 := max_lub_r (get_fresh_var e1) (get_fresh_var e2) v H).
    apply orb_false_intro.
    apply IHe1. assumption. apply IHe2. assumption.
  - simpl. unfold unionSet. simpl in H.
    assert (H1 := max_lub_l (get_fresh_var e1) (get_fresh_var e2) v H).
    assert (H2 := max_lub_r (get_fresh_var e1) (get_fresh_var e2) v H).
    apply orb_false_intro.
    apply IHe1. assumption. apply IHe2. assumption.
  - simpl. unfold unionSet. simpl in H.
    assert (H1 := max_lub_l (get_fresh_var e1) (get_fresh_var e2) v H).
    assert (H2 := max_lub_r (get_fresh_var e1) (get_fresh_var e2) v H).
    apply orb_false_intro.
    apply IHe1. assumption. apply IHe2. assumption.
  - simpl. apply IHe. simpl in H. assumption.
  - simpl. unfold unionSet. unfold updateSet.
    unfold get_fresh_var in H. fold get_fresh_var in H.
    assert (H1 := max_lub_l (get_fresh_var e1) (max (S x) (get_fresh_var e2)) v H).
    assert (H2 := max_lub_r (get_fresh_var e1) (max (S x) (get_fresh_var e2)) v H).
    apply orb_false_intro.
    apply IHe1. assumption.
    assert (H3 := max_lub_l (S x) (get_fresh_var e2) v H2).
    assert (H4 := max_lub_r (S x) (get_fresh_var e2) v H2).
    case_eq (x =? v); intros.
    + apply Nat.eqb_eq in H0. subst. apply nle_succ_diag_l in H3. contradiction.
    + apply IHe2. assumption.
Qed.

Lemma fresh_var_not_in_conj_vars_left :
  forall e e', conj_vars e (max (get_fresh_var e) (get_fresh_var e')) = false.
Proof.
  intros.
  apply fresh_var_not_in_conj_vars.
  apply le_max_l.
Qed.

Lemma fresh_var_not_in_conj_vars_right :
  forall e e', conj_vars e' (max (get_fresh_var e) (get_fresh_var e')) = false.
Proof.
  intros.
  apply fresh_var_not_in_conj_vars.
  apply le_max_r.
Qed.

Lemma variables_below_fresh : forall e v,
  conj_vars e v = true -> v < get_fresh_var e.
Proof.
  intros e. induction e; intros; simpl; simpl in H.
  - unfold emptySet in H. discriminate.
  - unfold emptySet in H. discriminate.
  - unfold singletonSet in H.
    case_eq (x =? v); intros;
    rewrite H0 in H.
    apply Nat.eqb_eq in H0. subst. apply lt_succ_diag_r.
    discriminate.
  - unfold unionSet in H. apply orb_true_iff in H.
    apply max_lt_iff.
    destruct H.
    left. apply IHe1. assumption.
    right. apply IHe2. assumption.
  - unfold unionSet in H. apply orb_true_iff in H.
    apply max_lt_iff.
    destruct H.
    left. apply IHe1. assumption.
    right. apply IHe2. assumption.
  - unfold unionSet in H. apply orb_true_iff in H.
    apply max_lt_iff.
    destruct H.
    left. apply IHe1. assumption.
    right. apply IHe2. assumption.
  - apply IHe. assumption.
  - unfold unionSet in H. apply orb_true_iff in H.
    unfold updateSet in H.
    apply max_lt_iff.
    destruct H.
    left. apply IHe1. assumption.
    right.
    case_eq (x =? v); intros.
    apply Nat.eqb_eq in H0. subst.
    destruct (get_fresh_var e2).
    apply lt_succ_diag_r.
    rewrite succ_max_distr.
    apply max_lt_iff. left. apply lt_succ_diag_r.
    rewrite H0 in H.
    destruct (get_fresh_var e2).
    assert (IHe2 := IHe2 v H).
    apply except. apply (nlt_0_r v). assumption.
    rewrite succ_max_distr.
    apply max_lt_iff. right.
    apply IHe2. assumption.
Qed.

Lemma complex_max : forall e e' a b c d newX,
  newX = (max
    (max (get_fresh_var e) (get_fresh_var e'))
    (max (max (S a) (S b)) (max (S c) (S d)))
  ) ->
  (a =? newX) = false /\ (b =? newX) = false /\
  (c =? newX) = false /\ (d =? newX) = false /\
  conj_vars e newX = false /\
  conj_vars e' newX = false.
Proof.
  intros.
  split.
  case_eq (a =? newX); intros.
  apply Nat.eqb_eq in H0. subst.
  symmetry in H0.
  apply eq_le_incl in H0.
  apply Max.max_lub_r in H0.
  apply Max.max_lub_l in H0.
  apply Max.max_lub_l in H0.
  apply nle_succ_diag_l in H0.
  contradiction.
  reflexivity.
  split.
  case_eq (b =? newX); intros.
  apply Nat.eqb_eq in H0. subst.
  symmetry in H0.
  apply eq_le_incl in H0.
  apply Max.max_lub_r in H0.
  apply Max.max_lub_l in H0.
  apply Max.max_lub_r in H0.
  apply nle_succ_diag_l in H0.
  contradiction.
  reflexivity.
  split.
  case_eq (c =? newX); intros.
  apply Nat.eqb_eq in H0. subst.
  symmetry in H0.
  apply eq_le_incl in H0.
  apply Max.max_lub_r in H0.
  apply Max.max_lub_r in H0.
  apply Max.max_lub_l in H0.
  apply nle_succ_diag_l in H0.
  contradiction.
  reflexivity.
  split.
  case_eq (d =? newX); intros.
  apply Nat.eqb_eq in H0. subst.
  symmetry in H0.
  apply eq_le_incl in H0.
  apply Max.max_lub_r in H0.
  apply Max.max_lub_r in H0.
  apply Max.max_lub_r in H0.
  apply nle_succ_diag_l in H0.
  contradiction.
  reflexivity.
  split.
  apply fresh_var_not_in_conj_vars.
  symmetry in H.
  apply eq_le_incl in H.
  apply Max.max_lub_l in H.
  apply Max.max_lub_l in H.
  assumption.
  apply fresh_var_not_in_conj_vars.
  symmetry in H.
  apply eq_le_incl in H.
  apply Max.max_lub_l in H.
  apply Max.max_lub_r in H.
  assumption.
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
  conj_vars e newX = false /\
  conj_vars e' newX = false /\
  conj_vars e'' newX = false /\
  conj_vars e''' newX = false.
Proof.
  intros.
  split.
  case_eq (a =? newX); intros.
  apply Nat.eqb_eq in H0. subst.
  symmetry in H0.
  apply eq_le_incl in H0.
  apply Max.max_lub_r in H0.
  apply Max.max_lub_l in H0.
  apply Max.max_lub_l in H0.
  apply nle_succ_diag_l in H0.
  contradiction.
  reflexivity.
  split.
  case_eq (b =? newX); intros.
  apply Nat.eqb_eq in H0. subst.
  symmetry in H0.
  apply eq_le_incl in H0.
  apply Max.max_lub_r in H0.
  apply Max.max_lub_l in H0.
  apply Max.max_lub_r in H0.
  apply nle_succ_diag_l in H0.
  contradiction.
  reflexivity.
  split.
  case_eq (c =? newX); intros.
  apply Nat.eqb_eq in H0. subst.
  symmetry in H0.
  apply eq_le_incl in H0.
  apply Max.max_lub_r in H0.
  apply Max.max_lub_r in H0.
  apply Max.max_lub_l in H0.
  apply nle_succ_diag_l in H0.
  contradiction.
  reflexivity.
  split.
  case_eq (d =? newX); intros.
  apply Nat.eqb_eq in H0. subst.
  symmetry in H0.
  apply eq_le_incl in H0.
  apply Max.max_lub_r in H0.
  apply Max.max_lub_r in H0.
  apply Max.max_lub_r in H0.
  apply nle_succ_diag_l in H0.
  contradiction.
  reflexivity.
  split.
  apply fresh_var_not_in_conj_vars.
  symmetry in H.
  apply eq_le_incl in H.
  apply Max.max_lub_l in H.
  apply Max.max_lub_l in H.
  apply Max.max_lub_l in H.
  assumption.
  split.
  apply fresh_var_not_in_conj_vars.
  symmetry in H.
  apply eq_le_incl in H.
  apply Max.max_lub_l in H.
  apply Max.max_lub_l in H.
  apply Max.max_lub_r in H.
  assumption.
  split.
  apply fresh_var_not_in_conj_vars.
  symmetry in H.
  apply eq_le_incl in H.
  apply Max.max_lub_l in H.
  apply Max.max_lub_r in H.
  apply Max.max_lub_l in H.
  assumption.
  apply fresh_var_not_in_conj_vars.
  symmetry in H.
  apply eq_le_incl in H.
  apply Max.max_lub_l in H.
  apply Max.max_lub_r in H.
  apply Max.max_lub_r in H.
  assumption.
Qed.

Lemma max_zero : forall a b,
  max a b = 0 -> a = 0 /\ b = 0.
Proof.
  intros.
  destruct a; destruct b.
  - split; reflexivity.
  - simpl in H. discriminate.
  - simpl in H. discriminate.
  - simpl in H. discriminate.
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

Lemma conj_vars_impl_let_1 : forall e1 x e2 o,
  (forall v : nat,
     conj_vars (ELet e1 x e2) v = true ->
     conj_vars (ELet e1 x e2) (o + v) = false) ->
  (forall v : nat,
     conj_vars e1 v = true ->
     conj_vars e1 (o + v) = false).
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

Lemma conj_vars_impl_let_2 : forall e1 x e2 o,
  (forall v : nat,
     conj_vars (ELet e1 x e2) v = true ->
     conj_vars (ELet e1 x e2) (o + v) = false) ->
  (forall v : nat,
     conj_vars e2 v = true ->
     conj_vars e2 (o + v) = false).
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

Lemma conj_vars_impl_let_x : forall e1 x e2 o,
  (forall v : nat,
     conj_vars (ELet e1 x e2) v = true ->
     conj_vars (ELet e1 x e2) (o + v) = false) ->
  conj_vars e2 (o + x) = false.
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
  conj_vars (ELet e1 x e2) x = true.
Proof.
  intros.
  simpl. unfold unionSet.
  apply orb_true_iff. right.
  unfold updateSet.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma not_in_main_not_in_subexprs : forall e1 x e2 z,
  conj_vars (ELet e1 x e2) z = false ->
  conj_vars e2 z = false.
Proof.
  intros. simpl in H.
  unfold unionSet in H.
  apply orb_false_iff in H.
  destruct H.
  unfold updateSet in H0.
  destruct (x =? z). discriminate.
  assumption.
Qed.

Lemma conj_vars_impl_plus_1 : forall e1 e2 o,
  (forall v : nat,
     conj_vars (EPlus e1 e2) v = true ->
     conj_vars (EPlus e1 e2) (o + v) = false) ->
  (forall v : nat,
     conj_vars e1 v = true ->
     conj_vars e1 (o + v) = false).
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

Lemma conj_vars_impl_plus_2 : forall e1 e2 o,
  (forall v : nat,
     conj_vars (EPlus e1 e2) v = true ->
     conj_vars (EPlus e1 e2) (o + v) = false) ->
  (forall v : nat,
     conj_vars e2 v = true ->
     conj_vars e2 (o + v) = false).
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

Lemma conj_vars_impl_times_1 : forall e1 e2 o,
  (forall v : nat,
     conj_vars (ETimes e1 e2) v = true ->
     conj_vars (ETimes e1 e2) (o + v) = false) ->
  (forall v : nat,
     conj_vars e1 v = true ->
     conj_vars e1 (o + v) = false).
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

Lemma conj_vars_impl_times_2 : forall e1 e2 o,
  (forall v : nat,
     conj_vars (ETimes e1 e2) v = true ->
     conj_vars (ETimes e1 e2) (o + v) = false) ->
  (forall v : nat,
     conj_vars e2 v = true ->
     conj_vars e2 (o + v) = false).
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

Lemma conj_vars_impl_cat_1 : forall e1 e2 o,
  (forall v : nat,
     conj_vars (ECat e1 e2) v = true ->
     conj_vars (ECat e1 e2) (o + v) = false) ->
  (forall v : nat,
     conj_vars e1 v = true ->
     conj_vars e1 (o + v) = false).
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

Lemma conj_vars_impl_cat_2 : forall e1 e2 o,
  (forall v : nat,
     conj_vars (ECat e1 e2) v = true ->
     conj_vars (ECat e1 e2) (o + v) = false) ->
  (forall v : nat,
     conj_vars e2 v = true ->
     conj_vars e2 (o + v) = false).
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

Lemma conj_vars_impl_len : forall e1 o,
  (forall v : nat,
     conj_vars (ELen e1) v = true ->
     conj_vars (ELen e1) (o + v) = false) ->
  (forall v : nat,
     conj_vars e1 v = true ->
     conj_vars e1 (o + v) = false).
Proof.
  intros.
  simpl in H.
  apply H. assumption.
Qed.

