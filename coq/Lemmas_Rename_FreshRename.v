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
From PFPL Require Import Lemmas_FreshRename.

Lemma fresh_rename_vs_rename : forall e bv o x x',
  (forall v, all_vars e v = true -> all_vars e (o + v) = false) ->
  all_vars e (x + o) = false ->
  all_vars e x' = false ->
  bv x' = false ->
  rename (fresh_rename e (updateSet bv x) o) (x + o) x' = fresh_rename (rename e x x') (updateSet bv x) o.
Proof.
  induction e using expr_ind; intros; simpl.
  - simpl in H. unfold updateSet.
    case_eq (x0 =? x); intros X0X.
    + apply Nat.eqb_eq in X0X. subst.
      simpl. rewrite Nat.eqb_refl.
      cut (x =? x' = false). intro.
      rewrite H2. rewrite H3. reflexivity.
      case_eq (x =? x'); intros.
      apply Nat.eqb_eq in H3. subst.
      simpl in H1. unfold singletonSet in H1.
      rewrite Nat.eqb_refl in H1. assumption.
      reflexivity.
    + case_eq (bv x); intro BVX.
      simpl. rewrite X0X. rewrite BVX.
      cut (x0 + o =? x + o = false). intro S.
      rewrite S. reflexivity.
      rewrite Nat.eqb_neq. rewrite Nat.eqb_neq in X0X. lia.
      simpl. rewrite X0X. rewrite BVX.
      simpl in H0. unfold singletonSet in H0.
      rewrite Nat.eqb_sym. destruct (x =? x0 + o).
      discriminate. reflexivity.
  - simpl in H2. unfold unionSet in H2.
    apply orb_false_iff in H2. destruct H2 as [H2 H2'].
    unfold updateSet in H2'.
    simpl in H3. unfold unionSet in H3.
    apply orb_false_iff in H3. destruct H3 as [H3 H3'].
    unfold updateSet in H3'.
    case_eq (x0 =? x); intros X0X.
    + apply Nat.eqb_eq in X0X. subst.
      rewrite Nat.eqb_refl. simpl.
      f_equal. apply H.
      apply same_structure_refl.
      intros. assert (H1 := H1 v).
      simpl in H1. unfold unionSet in H1.
      rewrite orb_true_iff in H1.
      assert (H1 := H1 (or_introl H5)).
      apply orb_false_iff in H1. destruct H1.
      assumption. assumption. assumption. assumption.
    + cut (x0 + o =? x + o = false). intro S.
      rewrite S. clear S. simpl.
      f_equal.
      apply H.
      apply same_structure_refl.
      intros. assert (H1 := H1 v).
      simpl in H1. unfold unionSet in H1.
      rewrite orb_true_iff in H1.
      assert (H1 := H1 (or_introl H5)).
      apply orb_false_iff in H1. destruct H1.
      assumption. assumption. assumption. assumption.
      cut ((updateSet (updateSet bv x0) x) = (updateSet (updateSet bv x) x0)). intro U.
      rewrite U.
      apply (H0 e2 (same_structure_refl e2)
        (updateSet bv x)
      ).
      intros.
      cut ((if x =? v then true else true) = true). intro.
      assert (H1 := H1 v).
      simpl in H1. unfold unionSet in H1.
      rewrite orb_true_iff in H1.
      unfold updateSet in H1.
      rewrite H5 in H1.
      assert (H1 := H1 (or_intror H6)).
      apply orb_false_iff in H1. destruct H1.
      destruct (x =? o + v). discriminate. assumption.
      destruct (x =? v). reflexivity. reflexivity.
      destruct (x =? x0 + o). discriminate. assumption.
      destruct (x =? x'). discriminate. assumption.
      unfold updateSet.
      destruct (x =? x'). assumption. assumption.
      apply update_set_permute.
      rewrite Nat.eqb_neq. rewrite Nat.eqb_neq in X0X. lia.
  - reflexivity.
  - reflexivity.
  - simpl in H1. unfold unionSet in H1.
    simpl in H2. unfold unionSet in H2.
    apply orb_false_iff in H2. destruct H2 as [H2 H2'].
    simpl in H3. unfold unionSet in H3.
    apply orb_false_iff in H3. destruct H3 as [H3 H3'].
    f_equal.
    apply H. apply same_structure_refl. intros.
    assert (H1 := H1 v).
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_introl H5)). destruct H1.
    assumption. assumption. assumption. assumption.
    apply H0. apply same_structure_refl. intros.
    assert (H1 := H1 v).
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_intror H5)). destruct H1.
    assumption. assumption. assumption. assumption.
  - simpl in H1. unfold unionSet in H1.
    simpl in H2. unfold unionSet in H2.
    apply orb_false_iff in H2. destruct H2 as [H2 H2'].
    simpl in H3. unfold unionSet in H3.
    apply orb_false_iff in H3. destruct H3 as [H3 H3'].
    f_equal.
    apply H. apply same_structure_refl. intros.
    assert (H1 := H1 v).
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_introl H5)). destruct H1.
    assumption. assumption. assumption. assumption.
    apply H0. apply same_structure_refl. intros.
    assert (H1 := H1 v).
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_intror H5)). destruct H1.
    assumption. assumption. assumption. assumption.
  - simpl in H1. unfold unionSet in H1.
    simpl in H2. unfold unionSet in H2.
    apply orb_false_iff in H2. destruct H2 as [H2 H2'].
    simpl in H3. unfold unionSet in H3.
    apply orb_false_iff in H3. destruct H3 as [H3 H3'].
    f_equal.
    apply H. apply same_structure_refl. intros.
    assert (H1 := H1 v).
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_introl H5)). destruct H1.
    assumption. assumption. assumption. assumption.
    apply H0. apply same_structure_refl. intros.
    assert (H1 := H1 v).
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_intror H5)). destruct H1.
    assumption. assumption. assumption. assumption.
  - simpl in H0.
    simpl in H1.
    simpl in H2.
    f_equal.
    apply H. apply same_structure_refl.
    assumption. assumption. assumption. assumption.
Qed.

Lemma fresh_rename_vs_rename_2 : forall e x x' bv o,
  all_vars e x' = false ->
  get_fresh_var e <= o ->
  bv x = false ->
  bv x' = false ->
  (forall z, bv z = true -> x =? z + o = false) ->
  rename (fresh_rename e bv o) x x' = fresh_rename (rename e x x') bv o.
Proof.
  induction e; intros z z' bv o A O BVZ BVZ' BV2; simpl.
  - reflexivity.
  - reflexivity.
  - simpl in O.
    case_eq (z =? x); intro ZX; simpl.
    + apply Nat.eqb_eq in ZX. subst.
      rewrite BVZ. rewrite BVZ'.
      simpl. rewrite Nat.eqb_refl. reflexivity.
    + case_eq (bv x); intro BVX; simpl.
      apply BV2 in BVX. rewrite BVX. reflexivity.
      rewrite ZX. reflexivity.
  - simpl in A. unfold unionSet in A.
    apply orb_false_iff in A. destruct A.
    simpl in O.
    f_equal; [apply IHe1 | apply IHe2]; auto.
    lia. lia.
  - simpl in A. unfold unionSet in A.
    apply orb_false_iff in A. destruct A.
    simpl in O.
    f_equal; [apply IHe1 | apply IHe2]; auto.
    lia. lia.
  - simpl in A. unfold unionSet in A.
    apply orb_false_iff in A. destruct A.
    simpl in O.
    f_equal; [apply IHe1 | apply IHe2]; auto.
    lia. lia.
  - simpl in A.
    simpl in O.
    f_equal. apply IHe; auto.
  - simpl in A. unfold unionSet in A.
    apply orb_false_iff in A. destruct A.
    unfold updateSet in H0.
    case_eq (x =? z'); intro XZ'.
    rewrite XZ' in H0. discriminate.
    simpl in O.
    case_eq (z =? x); intro ZX; simpl.
    + apply Nat.eqb_eq in ZX. subst.
      case_eq (x =? x + o); intro XXO.
      apply Nat.eqb_eq in XXO.
      destruct (get_fresh_var e2); lia.
      f_equal.
      apply IHe1; auto. lia.
      rewrite <- rename_non_existant.
      reflexivity.
      apply fresh_rename_removes_vars.
      destruct (get_fresh_var e2); lia.
      unfold updateSet. rewrite Nat.eqb_refl. reflexivity.
    + case_eq (z =? x + o); intro ZXO.
      f_equal.
      apply IHe1; auto. lia.
      apply Nat.eqb_eq in ZXO. subst z.
      rewrite <- rename_non_existant.
      reflexivity.
      apply fresh_var_not_in_all_vars.
      destruct (get_fresh_var e2); lia.
      f_equal.
      apply IHe1; auto. lia.
      apply IHe2.
      rewrite XZ' in H0. auto.
      destruct (get_fresh_var e2); lia.
      unfold updateSet. rewrite Nat.eqb_sym.
      rewrite ZX. auto.
      unfold updateSet. rewrite XZ'. auto.
      intros.
      case_eq (x =? z0); intro XZ0.
      apply Nat.eqb_eq in XZ0. subst z0.
      auto. apply BV2.
      unfold updateSet in H1.
      rewrite XZ0 in H1. auto.
Qed.

Lemma fresh_rename_vs_rename_3 : forall e x x' o,
  all_vars e x' = false ->
  get_fresh_var e <= o ->
  rename (fresh_rename e emptySet o) x x' = fresh_rename (rename e x x') emptySet o.
Proof.
  intros.
  apply fresh_rename_vs_rename_2; auto.
  intros. unfold emptySet in H1. discriminate.
Qed.
