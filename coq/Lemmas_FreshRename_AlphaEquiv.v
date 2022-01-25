Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Strings.String.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import Lia.
From PFPL Require Import PartialMap_Set.
From PFPL Require Import Definitions.
From PFPL Require Import Lemmas_Vars.
From PFPL Require Import Lemmas_Rename.
From PFPL Require Import Lemmas_Same_Structure.
From PFPL Require Import Induction_Expr.
From PFPL Require Import Lemmas_AlphaEquiv.
From PFPL Require Import Lemmas_Rename_AlphaEquiv.
From PFPL Require Import Lemmas_FreshRename.
From PFPL Require Import Lemmas_Rename_FreshRename.
From PFPL Require Import Lemmas_AlphaEquiv_2.

Lemma fresh_rename_keeps_alpha_equiv_aux : forall e bv o,
  (forall v, all_vars e v = true -> all_vars e (o + v) = false) ->
  (forall v, free_vars e v = true -> bv v = false) ->
  alpha_equiv_rel e (fresh_rename e bv o).
Proof.
  induction e using expr_ind; intros; simpl.
  - cut (bv x = false). intro.
    rewrite H1. apply alpha_equiv_rel_id.
    apply H0. simpl. unfold singletonSet. rewrite Nat.eqb_refl. reflexivity.
  - assert (O : 0 < o). {
    destruct o. assert (H1 := H1 x).
    assert (all_vars (ELet e1 x e2) x = true).
    simpl. unfold unionSet. apply orb_true_iff.
    right. unfold updateSet. rewrite Nat.eqb_refl.
    reflexivity. assert (H1 := H1 H3).
    simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1 as [H1 H1'].
    unfold updateSet in H1'. rewrite Nat.eqb_refl in H1'.
    discriminate. apply lt_0_succ. }
    apply alpha_equiv_rel_let.
    apply (H e1 (same_structure_refl e1) bv o).
    intros.
    assert (H1 := H1 v).
    simpl in H1. unfold unionSet in H1.
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_introl H3)).
    destruct H1. assumption.
    intros.
    apply H2. simpl. unfold unionSet.
    apply orb_true_iff. left. assumption.
    intros.
    remember (x + o + S z + get_fresh_var e2) as newX.
    cut (all_vars e2 newX = false). intro CV_newX.
    cut (all_vars (fresh_rename e2 (updateSet bv x) o) newX = false). intro CV_F_newX.
    apply (alpha_equiv_renamed e2 (fresh_rename e2 (updateSet bv x) o)
      x (x + o) newX z CV_newX CV_F_newX H3 H4
    ).
    cut (removeFromSet bv newX newX = false). intro BVR.
    cut ((newX =? x) = false). intro newX_X.
    cut (forall v : nat, all_vars e2 v = true -> all_vars e2 (o + v) = false). intro FORALL.
    cut (all_vars e2 (x + o) = false). intro CV_XO.
    assert (T1 := fresh_rename_vs_rename e2 (removeFromSet bv newX) o x newX FORALL CV_XO CV_newX BVR).
    assert (T2 : fresh_rename e2 (updateSet bv x) o = fresh_rename e2 (removeFromSet (updateSet bv x) newX) o).
    { apply fresh_rename_non_existant. assumption. }
    rewrite <- (update_set_permute_remove _ _ _ newX_X) in T2.
    rewrite <- T2 in T1. clear T2.
    assert (T3 : fresh_rename (rename e2 x newX) (updateSet (removeFromSet bv newX) x) o =
      fresh_rename (rename e2 x newX) (removeFromSet bv newX) o).
    apply fresh_rename_non_existant_free.
    apply rename_removes_free_vars.
    rewrite Nat.eqb_sym. assumption.
    rewrite T3 in T1. clear T3.
    rewrite T1.
    cut ((forall v : nat,
      all_vars (rename e2 x newX) v = true ->
      all_vars (rename e2 x newX) (o + v) = false)). intro FORALL1.
    cut ((forall v : nat,
      free_vars (rename e2 x newX) v = true ->
     (removeFromSet bv newX v = false))). intro FORALL2.
    assert (T4 := H0 (rename e2 x newX) (rename_keeps_structure e2 x newX)
      (removeFromSet bv newX) o FORALL1 FORALL2
    ).
    assumption.
    (* let's prove what is left... *)
    intros.
    assert (H6 := H2 v). case_eq (x =? v); intro XV.
    apply Nat.eqb_eq in XV. subst v.
    rewrite Nat.eqb_sym in newX_X.
    assert (H7 := rename_removes_free_vars e2 x newX newX_X).
    rewrite H7 in H5. discriminate.
    simpl in H6. unfold removeFromSet in H6.
    unfold unionSet in H6. rewrite XV in H6.
    unfold removeFromSet.
    case_eq (newX =? v); intro newX_V.
    reflexivity.
    apply H6. apply orb_true_iff. right.
    rewrite Nat.eqb_sym in XV.
    rewrite Nat.eqb_sym in newX_V.
    assert (H7 := rename_keeps_other_free_vars e2 x newX v XV newX_V).
    rewrite H5 in H7. assumption.
    (* - *)
    intros.
    assert (H6 := rename_keeps_other_vars e2 x newX v).
    assert (H7 := H1 v).
    simpl in H7. unfold unionSet in H7.
    unfold updateSet in H7.
    case_eq (v =? x); intro XV.
    rewrite Nat.eqb_sym in XV. rewrite XV in H7.
    assert (H8 : all_vars e1 v || true = true).
    apply orb_true_iff. right. reflexivity.
    assert (H7 := H7 H8). clear H8.
    apply orb_false_iff in H7. destruct H7 as [_ H7].
    case_eq (x =? o + v); intro XOV.
    rewrite XOV in H7. discriminate.
    rewrite XOV in H7.
    apply rename_does_not_add_new_var.
    apply Nat.eqb_eq in XV. subst v.
    rewrite Nat.eqb_neq. lia.
    assumption.
    assert (H6 := H6 XV).
    rewrite Nat.eqb_sym in XV. rewrite XV in H7.
    case_eq (v =? newX); intro V_newX.
    apply Nat.eqb_eq in V_newX.
    subst v.
    apply rename_does_not_add_new_var.
    rewrite Nat.eqb_neq. lia.
    apply fresh_var_not_in_all_vars. lia.
    assert (H6 := H6 V_newX).
    rewrite H6 in H7.
    rewrite orb_true_iff in H7.
    assert (H7 := H7 (or_intror H5)).
    apply orb_false_iff in H7. destruct H7 as [_ H7].
    case_eq (x =? o + v); intro XOV; rewrite XOV in H7.
    discriminate.
    apply rename_does_not_add_new_var.
    case_eq (newX =? o + v); intro newX_OV.
    apply Nat.eqb_eq in newX_OV.
    rewrite HeqnewX in newX_OV.
    rewrite (add_comm o v) in newX_OV.
    rewrite <- (add_assoc) in newX_OV.
    rewrite (add_comm (x + o)) in newX_OV.
    rewrite add_assoc in newX_OV.
    rewrite add_cancel_r in newX_OV.
    assert (all_vars e2 v = false).
    apply fresh_var_not_in_all_vars. lia.
    rewrite H5 in H6. rewrite H6 in H8.
    assumption. reflexivity.
    assumption.
    (* - *)
    assert (H1 := H1 x).
    simpl in H1. unfold unionSet in H1.
    unfold updateSet in H1.
    rewrite Nat.eqb_refl in H1.
    rewrite orb_true_iff in H1.
    assert (H1 := H1 (or_intror Logic.eq_refl)).
    rewrite orb_false_iff in H1. destruct H1 as [_ H1].
    destruct (x =? o + x). discriminate.
    rewrite add_comm. assumption.
    (* - *)
    intros.
    assert (H1 := H1 v).
    simpl in H1. unfold unionSet in H1.
    unfold updateSet in H1.
    assert ((if x =? v then true else all_vars e2 v) = true).
    rewrite H5. destruct (x =? v). reflexivity. reflexivity.
    rewrite orb_true_iff in H1.
    assert (H1 := H1 (or_intror H6)). clear H6.
    rewrite orb_false_iff in H1. destruct H1 as [_ H1].
    destruct (x =? o + v). discriminate.
    assumption.
    (* - *)
    case_eq (newX =? x); intro.
    rewrite Nat.eqb_eq in H5. subst. lia.
    reflexivity.
    (* - *)
    unfold removeFromSet.
    rewrite Nat.eqb_refl. reflexivity.
    (* - *)
    apply fresh_var_not_in_all_vars.
    rewrite <- add_assoc in HeqnewX.
    rewrite <- add_assoc in HeqnewX.
    rewrite add_comm in HeqnewX.
    rewrite (add_comm (S z)) in HeqnewX.
    rewrite add_assoc in HeqnewX.
    apply (le_trans _ (get_fresh_var e2 + o) _).
    apply (fresh_rename_fresh_var e2 (updateSet bv x) o).
    lia.
    (* - *)
    apply fresh_var_not_in_all_vars. lia.
  - apply alpha_equiv_rel_num.
  - apply alpha_equiv_rel_str. apply eqb_eq. reflexivity.
  - simpl in H1. unfold unionSet in H1.
    simpl in H2. unfold unionSet in H2.
    apply alpha_equiv_rel_plus.
    apply H. apply same_structure_refl.
    intros. assert (H1 := H1 v).
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_introl H3)).
    destruct H1. assumption.
    intros. apply H2.
    rewrite orb_true_iff. left. assumption.
    apply H0. apply same_structure_refl.
    intros. assert (H1 := H1 v).
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_intror H3)).
    destruct H1. assumption.
    intros. apply H2.
    rewrite orb_true_iff. right. assumption.
  - simpl in H1. unfold unionSet in H1.
    simpl in H2. unfold unionSet in H2.
    apply alpha_equiv_rel_times.
    apply H. apply same_structure_refl.
    intros. assert (H1 := H1 v).
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_introl H3)).
    destruct H1. assumption.
    intros. apply H2.
    rewrite orb_true_iff. left. assumption.
    apply H0. apply same_structure_refl.
    intros. assert (H1 := H1 v).
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_intror H3)).
    destruct H1. assumption.
    intros. apply H2.
    rewrite orb_true_iff. right. assumption.
  - simpl in H1. unfold unionSet in H1.
    simpl in H2. unfold unionSet in H2.
    apply alpha_equiv_rel_cat.
    apply H. apply same_structure_refl.
    intros. assert (H1 := H1 v).
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_introl H3)).
    destruct H1. assumption.
    intros. apply H2.
    rewrite orb_true_iff. left. assumption.
    apply H0. apply same_structure_refl.
    intros. assert (H1 := H1 v).
    rewrite orb_true_iff in H1.
    rewrite orb_false_iff in H1.
    assert (H1 := H1 (or_intror H3)).
    destruct H1. assumption.
    intros. apply H2.
    rewrite orb_true_iff. right. assumption.
  - simpl in H0. simpl in H1.
    apply alpha_equiv_rel_len.
    apply H. apply same_structure_refl.
    assumption.
    assumption.
Qed.

Lemma fresh_rename_keeps_alpha_equiv : forall e x,
  get_fresh_var e <= x ->
  alpha_equiv_rel e (fresh_rename e emptySet x).
Proof.
  intros.
  apply fresh_rename_keeps_alpha_equiv_aux.
  intros.
  apply fresh_var_not_in_all_vars.
  apply (le_trans _ x _).
  assumption. apply le_add_r.
  intros. reflexivity.
Qed.

Lemma fresh_rename_keeps_alpha_equiv_2 : forall e e' o o',
  (forall v, all_vars e v = true -> all_vars e (o + v) = false) ->
  (forall v, all_vars e' v = true -> all_vars e' (o' + v) = false) ->
  alpha_equiv_rel e e' ->
  alpha_equiv_rel (fresh_rename e emptySet o) (fresh_rename e' emptySet o').
Proof.
  intros.
  assert (forall v : nat, free_vars e v = true -> emptySet v = false).
  intros. reflexivity.
  assert (forall v : nat, free_vars e' v = true -> emptySet v = false).
  intros. reflexivity.
  assert (T1 := fresh_rename_keeps_alpha_equiv_aux e emptySet o H H2).
  assert (T2 := fresh_rename_keeps_alpha_equiv_aux e' emptySet o' H0 H3).
  apply alpha_equiv_sym in T1.
  assert (T3 := alpha_equiv_trans (fresh_rename e emptySet o) e e' T1 H1).
  apply (alpha_equiv_trans (fresh_rename e emptySet o) e' (fresh_rename e' emptySet o') T3 T2).
Qed.
