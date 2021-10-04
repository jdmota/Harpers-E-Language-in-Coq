Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import Logic.FunctionalExtensionality.
From PFPL Require Import PartialMap_Set.
From PFPL Require Import Definitions.
From PFPL Require Import Lemmas_Vars.
From PFPL Require Import Lemmas_Same_Structure.
From PFPL Require Import Induction_Expr.

Lemma rename_keeps_structure :
  forall e x x', same_structure e (rename e x x').
Proof.
  intros.
  induction e.
  all: simpl.
  all: try constructor.
  destruct (x =? x0); constructor.
  all: auto.
  destruct (x =? x0); constructor.
  all: auto.
  apply same_structure_refl.
Qed.

Lemma rename_the_same :
  forall e x, e = rename e x x.
Proof.
  intros.
  induction e.
  all: simpl.
  reflexivity.
  reflexivity.
  case_eq (x =? x0); intros.
  apply Nat.eqb_eq in H. subst.
  reflexivity. reflexivity.
  rewrite <- IHe1. rewrite <- IHe2. reflexivity.
  rewrite <- IHe1. rewrite <- IHe2. reflexivity.
  rewrite <- IHe1. rewrite <- IHe2. reflexivity.
  rewrite <- IHe. reflexivity.
  rewrite <- IHe1. rewrite <- IHe2.
  destruct (x =? x0).
  reflexivity. reflexivity.
Qed.

Lemma rename_non_existant : forall e x x',
  conj_vars e x = false -> e = rename e x x'.
Proof.
  intros.
  induction e; simpl.
  - reflexivity.
  - reflexivity.
  - simpl in H. unfold singletonSet in H.
    assert(H1 := Nat.eqb_sym x0 x).
    rewrite <- H1.
    destruct (x0 =? x).
    discriminate. reflexivity.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H.
    f_equal.
    apply IHe1. assumption.
    apply IHe2. assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H.
    f_equal.
    apply IHe1. assumption.
    apply IHe2. assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H.
    f_equal.
    apply IHe1. assumption.
    apply IHe2. assumption.
  - simpl in H.
    f_equal.
    apply IHe. assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H.
    unfold updateSet in H0.
    assert(H1 := Nat.eqb_sym x0 x).
    rewrite <- H1.
    destruct (x0 =? x).
    discriminate.
    f_equal.
    apply IHe1. assumption.
    apply IHe2. assumption.
Qed.

Lemma rename_non_existant_free : forall e x x',
  free_vars e x = false -> e = rename e x x'.
Proof.
  intros.
  induction e; simpl.
  - reflexivity.
  - reflexivity.
  - simpl in H. unfold singletonSet in H.
    assert(H1 := Nat.eqb_sym x0 x).
    rewrite <- H1.
    destruct (x0 =? x).
    discriminate. reflexivity.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H.
    f_equal.
    apply IHe1. assumption.
    apply IHe2. assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H.
    f_equal.
    apply IHe1. assumption.
    apply IHe2. assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H.
    f_equal.
    apply IHe1. assumption.
    apply IHe2. assumption.
  - simpl in H.
    f_equal.
    apply IHe. assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H.
    unfold updateSet in H0.
    rewrite Nat.eqb_sym.
    case_eq (x0 =? x); intros.
    apply Nat.eqb_eq in H1. subst.
    f_equal.
    apply IHe1. assumption.
    f_equal.
    apply IHe1. assumption.
    apply IHe2. unfold removeFromSet in H0.
    rewrite H1 in H0.
    assumption.
Qed.

Lemma rename_non_existant_free_2 : forall e x x',
  (x =? x' = false) -> e = rename e x x' -> free_vars e x = false.
Proof.
  intros.
  induction e; simpl.
  - reflexivity.
  - reflexivity.
  - simpl in H0. unfold singletonSet.
    rewrite Nat.eqb_sym.
    case_eq (x =? x0); intros.
    rewrite H1 in H0.
    apply Nat.eqb_eq in H1. subst.
    inversion H0. subst.
    rewrite Nat.eqb_refl in H. discriminate.
    reflexivity.
  - simpl in H0. inversion H0.
    unfold unionSet.
    apply orb_false_iff. split.
    rewrite <- H2. apply IHe1. assumption.
    rewrite <- H3. apply IHe2. assumption.
  - simpl in H0. inversion H0.
    unfold unionSet.
    apply orb_false_iff. split.
    rewrite <- H2. apply IHe1. assumption.
    rewrite <- H3. apply IHe2. assumption.
  - simpl in H0. inversion H0.
    unfold unionSet.
    apply orb_false_iff. split.
    rewrite <- H2. apply IHe1. assumption.
    rewrite <- H3. apply IHe2. assumption.
  - simpl in H0. inversion H0.
    rewrite <- H2. apply IHe. assumption.
  - simpl in H0.
    unfold unionSet.
    apply orb_false_iff.
    case_eq (x =? x0); intros; rewrite H1 in H0; inversion H0.
    + apply Nat.eqb_eq in H1. subst.
      split.
      rewrite <- H3. apply IHe1. assumption.
      unfold removeFromSet.
      rewrite Nat.eqb_refl.
      reflexivity.
    + split.
      rewrite <- H3. apply IHe1. assumption.
      unfold removeFromSet.
      rewrite Nat.eqb_sym in H1.
      rewrite H1.
      rewrite <- H4.
      apply IHe2. assumption.
Qed.

Lemma rename_removes_free_vars : forall e x x',
  (x =? x' = false) -> free_vars (rename e x x') x = false.
Proof.
  intros e x x'.
  induction e using expr_ind; intros.
  - simpl. rewrite Nat.eqb_sym.
    case_eq (x0 =? x); intros.
    all: simpl.
    all: unfold singletonSet.
    rewrite Nat.eqb_sym.
    rewrite H.
    reflexivity.
    rewrite H0.
    reflexivity.
  - simpl.
    case_eq (x =? x0); intros;
    rewrite Nat.eqb_sym in H2.
    all: simpl; unfold unionSet.
    all: apply orb_false_iff; split.
    + apply H.
      apply same_structure_refl.
      assumption.
    + unfold removeFromSet.
      rewrite H2.
      reflexivity.
    + apply H.
      apply same_structure_refl.
      assumption.
    + unfold removeFromSet.
      rewrite H2.
      apply H0.
      apply same_structure_refl.
      assumption.
  - simpl. unfold emptySet. reflexivity.
  - simpl. unfold emptySet. reflexivity.
  - simpl. unfold unionSet.
    apply orb_false_iff. split.
    apply H.
    apply same_structure_refl.
    assumption.
    apply H0.
    apply same_structure_refl.
    assumption.
  - simpl. unfold unionSet.
    apply orb_false_iff. split.
    apply H.
    apply same_structure_refl.
    assumption.
    apply H0.
    apply same_structure_refl.
    assumption.
  - simpl. unfold unionSet.
    apply orb_false_iff. split.
    apply H.
    apply same_structure_refl.
    assumption.
    apply H0.
    apply same_structure_refl.
    assumption.
  - simpl.
    apply H.
    apply same_structure_refl.
    assumption.
Qed.

Lemma rename_keeps_other_free_vars : forall e x x' v,
  (v =? x = false) ->
  (v =? x' = false) ->
  free_vars e v = free_vars (rename e x x') v.
Proof.
  intros.
  case_eq (x =? x'); intros.
  - apply Nat.eqb_eq in H1. subst.
    rewrite <- rename_the_same.
    reflexivity.
  - induction e; simpl.
    + reflexivity.
    + reflexivity.
    + case_eq (x =? x0); intros.
      all: simpl.
      all: unfold singletonSet.
      all: case_eq (x0 =? v); intros.
      all: case_eq (x' =? v); intros.
      reflexivity.
      rewrite Nat.eqb_eq in H2. subst.
      rewrite Nat.eqb_eq in H3. subst.
      rewrite Nat.eqb_refl in H. discriminate.
      rewrite Nat.eqb_eq in H2. subst.
      rewrite Nat.eqb_eq in H4. subst.
      rewrite Nat.eqb_refl in H0. discriminate.
      all: reflexivity.
    + unfold unionSet.
      rewrite IHe1. rewrite IHe2. reflexivity.
    + unfold unionSet.
      rewrite IHe1. rewrite IHe2. reflexivity.
    + unfold unionSet.
      rewrite IHe1. rewrite IHe2. reflexivity.
    + assumption.
    + unfold unionSet. unfold removeFromSet.
      case_eq (x0 =? v); case_eq (x =? x0); intros.
      all: simpl.
      all: unfold unionSet.
      all: unfold removeFromSet.
      all: rewrite H3.
      rewrite IHe1. reflexivity.
      rewrite IHe1. reflexivity.
      rewrite IHe1. reflexivity.
      rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Lemma rename_keeps_other_vars : forall e x x' v,
  (v =? x = false) ->
  (v =? x' = false) ->
  conj_vars e v = conj_vars (rename e x x') v.
Proof.
  intros.
  case_eq (x =? x'); intros.
  - apply Nat.eqb_eq in H1. subst.
    rewrite <- rename_the_same.
    reflexivity.
  - induction e; simpl.
    + reflexivity.
    + reflexivity.
    + case_eq (x =? x0); intros.
      all: simpl.
      all: unfold singletonSet.
      all: case_eq (x0 =? v); intros.
      all: case_eq (x' =? v); intros.
      reflexivity.
      rewrite Nat.eqb_eq in H2. subst.
      rewrite Nat.eqb_eq in H3. subst.
      rewrite Nat.eqb_refl in H. discriminate.
      rewrite Nat.eqb_eq in H2. subst.
      rewrite Nat.eqb_eq in H4. subst.
      rewrite Nat.eqb_refl in H0. discriminate.
      all: reflexivity.
    + unfold unionSet.
      rewrite IHe1. rewrite IHe2. reflexivity.
    + unfold unionSet.
      rewrite IHe1. rewrite IHe2. reflexivity.
    + unfold unionSet.
      rewrite IHe1. rewrite IHe2. reflexivity.
    + assumption.
    + unfold unionSet. unfold removeFromSet.
      case_eq (x0 =? v); case_eq (x =? x0); intros.
      all: simpl.
      all: unfold updateSet.
      all: unfold unionSet.
      all: rewrite H3.
      rewrite IHe1. reflexivity.
      rewrite IHe1. reflexivity.
      rewrite IHe1. reflexivity.
      rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Lemma rename_the_free_var : forall e x x',
  free_vars e x = true -> conj_vars e x' = false ->
  free_vars (rename e x x') x' = true.
Proof.
  intros.
  case_eq (x =? x'); intros.
  rewrite Nat.eqb_eq in H1. subst.
  assert (H2 : e = rename e x' x').
  apply rename_the_same.
  rewrite <- H2.
  assumption.
  induction e using expr_ind; intros.
  - simpl in H. unfold singletonSet in H.
    case_eq (x0 =? x); intros.
    apply Nat.eqb_eq in H2. subst.
    simpl. rewrite Nat.eqb_refl. simpl.
    unfold singletonSet.
    rewrite Nat.eqb_refl. reflexivity.
    rewrite H2 in H. discriminate.
  - simpl in H.
    unfold unionSet in H.
    apply orb_true_iff in H.
    simpl.
    unfold removeFromSet in H.
    simpl in H0.
    unfold unionSet in H0.
    apply orb_false_iff in H0.
    destruct H0.
    unfold updateSet in H4.
    case_eq (x0 =? x'); intros.
    rewrite H5 in H4. discriminate.
    rewrite H5 in H4.
    case_eq (x =? x0); intros.
    + apply Nat.eqb_eq in H6. subst.
      rewrite Nat.eqb_refl in H.
      simpl.
      apply orb_true_iff.
      destruct H.
      left.
      apply H2. apply same_structure_refl.
      assumption.
      assumption.
      discriminate.
    + rewrite Nat.eqb_sym in H.
      rewrite H6 in H.
      simpl.
      apply orb_true_iff.
      destruct H.
      left.
      apply H2. apply same_structure_refl.
      assumption. assumption.
      right.
      unfold removeFromSet.
      rewrite H5.
      apply H3. apply same_structure_refl.
      assumption. assumption.
  - inversion H.
  - inversion H.
  - simpl in H. unfold unionSet in H.
    apply orb_true_iff in H.
    simpl in H0. unfold unionSet in H0.
    apply orb_false_iff in H0.
    destruct H0.
    simpl. unfold unionSet.
    apply orb_true_iff.
    destruct H.
    left.
    apply H2. apply same_structure_refl.
    assumption. assumption.
    right.
    apply H3. apply same_structure_refl.
    assumption. assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_true_iff in H.
    simpl in H0. unfold unionSet in H0.
    apply orb_false_iff in H0.
    destruct H0.
    simpl. unfold unionSet.
    apply orb_true_iff.
    destruct H.
    left.
    apply H2. apply same_structure_refl.
    assumption. assumption.
    right.
    apply H3. apply same_structure_refl.
    assumption. assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_true_iff in H.
    simpl in H0. unfold unionSet in H0.
    apply orb_false_iff in H0.
    destruct H0.
    simpl. unfold unionSet.
    apply orb_true_iff.
    destruct H.
    left.
    apply H2. apply same_structure_refl.
    assumption. assumption.
    right.
    apply H3. apply same_structure_refl.
    assumption. assumption.
  - simpl in H.
    simpl in H0.
    simpl.
    apply H2. apply same_structure_refl.
    assumption. assumption.
Qed.

Lemma rename_commu : forall e a b c d,
  a =? c = false ->
  a =? d = false ->
  b =? c = false ->
  b =? d = false ->
  (rename (rename e a b) c d) = (rename (rename e c d) a b).
Proof.
  intros e.
  induction e using expr_ind; intros.
  - simpl.
    case_eq (a =? x); case_eq (c =? x); intros.
    + apply Nat.eqb_eq in H3. subst.
      rewrite H in H4. discriminate.
    + apply Nat.eqb_eq in H4. subst.
      simpl. rewrite Nat.eqb_sym.
      rewrite H1. rewrite Nat.eqb_refl.
      reflexivity.
    + apply Nat.eqb_eq in H3. subst.
      simpl. rewrite Nat.eqb_refl.
      rewrite H0.
      reflexivity.
    + simpl. rewrite H3. rewrite H4.
      reflexivity.
  - simpl.
    case_eq (a =? x); case_eq (c =? x); intros.
    + apply Nat.eqb_eq in H5. subst.
      rewrite H1 in H6. discriminate.
    + apply Nat.eqb_eq in H6. subst.
      simpl. rewrite H5. rewrite Nat.eqb_refl.
      f_equal.
      apply H.
      apply same_structure_refl.
      rewrite Nat.eqb_sym. assumption.
      assumption.
      assumption.
      assumption.
    + apply Nat.eqb_eq in H5. subst.
      simpl. rewrite H1. rewrite Nat.eqb_refl.
      f_equal.
      apply H.
      apply same_structure_refl.
      assumption. assumption.
      assumption. assumption.
    + simpl. rewrite H5. rewrite H6.
      f_equal.
      apply H.
      apply same_structure_refl.
      assumption. assumption.
      assumption. assumption.
      apply H0.
      apply same_structure_refl.
      assumption. assumption.
      assumption. assumption.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. f_equal.
    apply (H e1 (same_structure_refl e1) a b c d H1 H2 H3 H4).
    apply (H0 e2 (same_structure_refl e2) a b c d H1 H2 H3 H4).
  - simpl. f_equal.
    apply (H e1 (same_structure_refl e1) a b c d H1 H2 H3 H4).
    apply (H0 e2 (same_structure_refl e2) a b c d H1 H2 H3 H4).
  - simpl. f_equal.
    apply (H e1 (same_structure_refl e1) a b c d H1 H2 H3 H4).
    apply (H0 e2 (same_structure_refl e2) a b c d H1 H2 H3 H4).
  - simpl. f_equal.
    apply (H e (same_structure_refl e) a b c d H0 H1 H2 H3).
Qed.

Lemma rename_does_not_add_new_var : forall e x x' z,
  x' =? z = false -> conj_vars e z = false -> conj_vars (rename e x x') z = false.
Proof.
  intros.
  rewrite Nat.eqb_sym in H.
  case_eq (z =? x); intro.
  - apply Nat.eqb_eq in H1. subst.
    rewrite <- rename_non_existant; assumption.
  - assert (T := rename_keeps_other_vars e x x' z H1 H).
    rewrite <- T. assumption.
Qed.

Lemma rename_keeps_bound_vars : forall e x x' v,
  bound_vars e v = bound_vars (rename e x x') v.
Proof.
  induction e; intros; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (x0 =? x).
    all: simpl; reflexivity.
  - f_equal.
    all: apply functional_extensionality; intro.
    apply IHe1. apply IHe2.
  - f_equal.
    all: apply functional_extensionality; intro.
    apply IHe1. apply IHe2.
  - f_equal.
    all: apply functional_extensionality; intro.
    apply IHe1. apply IHe2.
  - apply IHe.
  - case_eq (x0 =? x); intro; simpl.
    + f_equal.
      all: apply functional_extensionality; intro.
      apply IHe1.
    + f_equal.
      all: apply functional_extensionality; intro.
      apply IHe1.
      unfold updateSet.
      destruct (x =? x1).
      reflexivity.
      apply IHe2.
Qed.

Lemma rename_twice : forall e a b c,
  (a =? b) = false ->
  conj_vars e b = false ->
  (rename e a b) = (rename (rename e a b) a c).
Proof.
  intros.
  assert (T1 := rename_removes_free_vars e a b H).
  apply rename_non_existant_free.
  assumption.
Qed.
