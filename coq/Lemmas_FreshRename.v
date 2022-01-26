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
From PFPL Require Import Lemmas_Vars.
From PFPL Require Import Lemmas_Rename.
From PFPL Require Import Lemmas_Same_Structure.
From PFPL Require Import Induction_Expr.
From PFPL Require Import Lemmas_AlphaEquiv.

Lemma fresh_rename_keeps_depth : forall e bv x, depth e = depth (fresh_rename e bv x).
Proof.
  induction e; intros.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. case_eq (bv x); intros; simpl; reflexivity.
  - simpl. f_equal. rewrite (IHe1 bv x). rewrite (IHe2 bv x). reflexivity.
  - simpl. f_equal. rewrite (IHe1 bv x). rewrite (IHe2 bv x). reflexivity.
  - simpl. f_equal. rewrite (IHe1 bv x). rewrite (IHe2 bv x). reflexivity.
  - simpl. f_equal. rewrite (IHe bv x). reflexivity.
  - simpl. f_equal. rewrite (IHe1 bv x0). rewrite (IHe2 (updateSet bv x) x0). reflexivity.
Qed.

Lemma fresh_rename_keeps_structure : forall e bv o,
  same_structure e (fresh_rename e bv o).
Proof.
  induction e; intros; simpl.
  all: try constructor.
  all: auto.
  destruct (bv x); constructor.
Qed.

Lemma fresh_rename_non_existant : forall e bv x o,
  all_vars e x = false ->
  (fresh_rename e bv o) = (fresh_rename e (removeFromSet bv x) o).
Proof.
  induction e using expr_ind; intros; simpl.
  - simpl in H. unfold singletonSet in H.
    case_eq (x =? x0); intros.
    rewrite H0 in H. discriminate.
    unfold removeFromSet.
    rewrite Nat.eqb_sym. rewrite H0.
    reflexivity.
  - simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1 as [H1 H2].
    unfold updateSet in H2.
    case_eq (x =? x0); intros.
    rewrite H3 in H2. discriminate.
    rewrite H3 in H2.
    f_equal.
    apply H. apply same_structure_refl.
    assumption.
    cut ((updateSet (removeFromSet bv x0) x) = (removeFromSet (updateSet bv x) x0)). intro U.
    rewrite U.
    apply (H0 e2 (same_structure_refl e2) (updateSet bv x) x0 o H2).
    apply update_set_permute_remove.
    rewrite Nat.eqb_sym. assumption.
  - reflexivity.
  - reflexivity.
  - simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1 as [H1 H2].
    f_equal.
    apply H. apply same_structure_refl. assumption.
    apply H0. apply same_structure_refl. assumption.
  - simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1 as [H1 H2].
    f_equal.
    apply H. apply same_structure_refl. assumption.
    apply H0. apply same_structure_refl. assumption.
  - simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1 as [H1 H2].
    f_equal.
    apply H. apply same_structure_refl. assumption.
    apply H0. apply same_structure_refl. assumption.
  - simpl in H0.
    f_equal.
    apply H. apply same_structure_refl. assumption.
Qed.

Lemma fresh_rename_non_existant_free : forall e bv x o,
  free_vars e x = false ->
  (fresh_rename e (updateSet bv x) o) = (fresh_rename e bv o).
Proof.
  induction e using expr_ind; intros; simpl.
  - simpl in H. unfold singletonSet in H.
    case_eq (x =? x0); intros.
    rewrite H0 in H. discriminate.
    unfold updateSet.
    rewrite Nat.eqb_sym. rewrite H0.
    reflexivity.
  - simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1 as [H1 H2].
    unfold removeFromSet in H2.
    case_eq (x =? x0); intros.
    rewrite H3 in H2. apply Nat.eqb_eq in H3. subst. clear H2.
    f_equal.
    apply H. apply same_structure_refl.
    assumption.
    rewrite update_set_twice. reflexivity.
    rewrite H3 in H2.
    f_equal.
    apply H. apply same_structure_refl.
    assumption.
    cut ((updateSet (updateSet bv x0) x) = (updateSet (updateSet bv x) x0)). intro U.
    rewrite U.
    apply (H0 e2 (same_structure_refl e2) (updateSet bv x) x0 o H2).
    apply update_set_permute.
  - reflexivity.
  - reflexivity.
  - simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1 as [H1 H2].
    f_equal.
    apply H. apply same_structure_refl. assumption.
    apply H0. apply same_structure_refl. assumption.
  - simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1 as [H1 H2].
    f_equal.
    apply H. apply same_structure_refl. assumption.
    apply H0. apply same_structure_refl. assumption.
  - simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1 as [H1 H2].
    f_equal.
    apply H. apply same_structure_refl. assumption.
    apply H0. apply same_structure_refl. assumption.
  - simpl in H0.
    f_equal.
    apply H. apply same_structure_refl. assumption.
Qed.

Lemma fresh_rename_fresh_var : forall e bv o,
  get_fresh_var (fresh_rename e bv o) <= get_fresh_var e + o.
Proof.
  induction e using expr_ind; intros; simpl.
  - destruct (bv x).
    simpl. lia.
    simpl. lia.
  - assert (T1 := H e1 (same_structure_refl e1) bv o).
    assert (T2 := H0 e2 (same_structure_refl e2) bv o).
    assert (T3 := H0 e2 (same_structure_refl e2) (updateSet bv x) o).
    case_eq (get_fresh_var (fresh_rename e2 (updateSet bv x) o)); intros;
    case_eq (get_fresh_var e2); intros.
    lia. lia. lia. lia.
  - lia.
  - lia.
  - assert (T1 := H e1 (same_structure_refl e1) bv o).
    assert (T2 := H0 e2 (same_structure_refl e2) bv o).
    lia.
  - assert (T1 := H e1 (same_structure_refl e1) bv o).
    assert (T2 := H0 e2 (same_structure_refl e2) bv o).
    lia.
  - assert (T1 := H e1 (same_structure_refl e1) bv o).
    assert (T2 := H0 e2 (same_structure_refl e2) bv o).
    lia.
  - assert (T := H e (same_structure_refl e) bv o).
    assumption.
Qed.

Lemma fresh_rename_new_bounds : forall e bv o,
  (forall v, bound_vars (fresh_rename e bv o) v = true -> o <= v).
Proof.
  induction e using expr_ind; intros bv o v B.
  all: simpl in B.
  - destruct (bv x).
    all: simpl in B; unfold emptySet in B; discriminate.
  - unfold unionSet in B. apply orb_true_iff in B. destruct B.
    apply (H e1 (same_structure_refl e1) bv o v H1).
    unfold updateSet in H1.
    case_eq (x + o =? v); intro XOV; rewrite XOV in H1.
    apply Nat.eqb_eq in XOV. lia.
    apply (H0 e2 (same_structure_refl e2) (fun v' : nat => if x =? v' then true else bv v') o v H1).
  - discriminate.
  - discriminate.
  - unfold unionSet in B. apply orb_true_iff in B. destruct B.
    apply (H e1 (same_structure_refl e1) bv o v H1).
    apply (H0 e2 (same_structure_refl e2) bv o v H1).
  - unfold unionSet in B. apply orb_true_iff in B. destruct B.
    apply (H e1 (same_structure_refl e1) bv o v H1).
    apply (H0 e2 (same_structure_refl e2) bv o v H1).
  - unfold unionSet in B. apply orb_true_iff in B. destruct B.
    apply (H e1 (same_structure_refl e1) bv o v H1).
    apply (H0 e2 (same_structure_refl e2) bv o v H1).
  - apply (H e (same_structure_refl e) bv o v B).
Qed.

Lemma fresh_rename_removes_vars : forall e o bv v,
  v < o ->
  bv v = true ->
  all_vars (fresh_rename e bv o) v = false.
Proof.
  induction e; intros; simpl.
  - reflexivity.
  - reflexivity.
  - case_eq (bv x); intro BVx; simpl; unfold singletonSet.
    + case_eq (x + o =? v); intro XOV.
      apply Nat.eqb_eq in XOV. subst. lia.
      reflexivity.
    + case_eq (x =? v); intro XV.
      apply Nat.eqb_eq in XV. subst. rewrite BVx in H0.
      discriminate. reflexivity.
  - unfold unionSet. apply orb_false_iff. split.
    apply IHe1; auto.
    apply IHe2; auto.
  - unfold unionSet. apply orb_false_iff. split.
    apply IHe1; auto.
    apply IHe2; auto.
  - unfold unionSet. apply orb_false_iff. split.
    apply IHe1; auto.
    apply IHe2; auto.
  - apply IHe; auto.
  - unfold unionSet. apply orb_false_iff. split.
    apply IHe1; auto.
    unfold updateSet.
    case_eq (x + o =? v); intro XOV.
    apply Nat.eqb_eq in XOV. subst. lia.
    apply IHe2; auto.
    rewrite H0. destruct (x =? v); auto.
Qed.
