Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From Coq Require Import Strings.String.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import Classes.RelationClasses.
From PFPL Require Import PartialMap_Set.
From PFPL Require Import Definitions.
From PFPL Require Import Lemmas_Vars.
From PFPL Require Import Lemmas_Rename.
From PFPL Require Import Lemmas_Same_Structure.
From PFPL Require Import Induction_Expr.
From PFPL Require Import Lemmas_AlphaEquiv.
From PFPL Require Import Lemmas_Rename_AlphaEquiv.

Lemma alpha_equiv_trans : forall e e' e'',
  alpha_equiv_rel e e' -> alpha_equiv_rel e' e'' ->
  alpha_equiv_rel e e''.
Proof.
  induction e using expr_ind; intros.
  - inversion H. subst.
    inversion H0. subst.
    apply alpha_equiv_rel_id.
  - inversion H1. subst.
    inversion H2. subst.
    apply alpha_equiv_rel_let.
    apply (H e1 (same_structure_refl e1) e1').
    assumption. assumption.
    intros.
    remember (
      max (get_fresh_var e2) (max (get_fresh_var e2') (get_fresh_var e2'0))
    ) as newX.
    assert (H11 : all_vars e2 newX = false).
    apply fresh_var_not_in_all_vars. lia.
    assert (H12 : all_vars e2' newX = false).
    apply fresh_var_not_in_all_vars. lia.
    assert (H13 : all_vars e2'0 newX = false).
    apply fresh_var_not_in_all_vars. lia.
    assert (H14 := H0
      (rename e2 x newX)
      (rename_keeps_structure e2 x newX)
      (rename e2' x' newX)
      (rename e2'0 x'0 newX)
    ).
    assert (H15 := alpha_equiv_renamed e2 e2'0 x x'0 newX z H11 H13 H3 H4).
    apply H15.
    apply H14.
    apply H8. assumption. assumption.
    apply H10. assumption. assumption.
  - inversion H. subst. inversion H0. subst.
    assumption.
  - inversion H. subst. inversion H0.
    apply eqb_eq in H2. subst.
    apply eqb_eq in H3. subst.
    assumption.
  - inversion H1. subst.
    inversion H2. subst.
    apply alpha_equiv_rel_plus.
    apply (H e1 (same_structure_refl e1) e1' e1'0).
    assumption. assumption.
    apply (H0 e2 (same_structure_refl e2) e2' e2'0).
    assumption. assumption.
  - inversion H1. subst.
    inversion H2. subst.
    apply alpha_equiv_rel_times.
    apply (H e1 (same_structure_refl e1) e1' e1'0).
    assumption. assumption.
    apply (H0 e2 (same_structure_refl e2) e2' e2'0).
    assumption. assumption.
  - inversion H1. subst.
    inversion H2. subst.
    apply alpha_equiv_rel_cat.
    apply (H e1 (same_structure_refl e1) e1' e1'0).
    assumption. assumption.
    apply (H0 e2 (same_structure_refl e2) e2' e2'0).
    assumption. assumption.
  - inversion H0. subst.
    inversion H1. subst.
    apply alpha_equiv_rel_len.
    apply (H e (same_structure_refl e) e1' e1'0).
    assumption. assumption.
Qed.
