Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From Coq Require Import Strings.String.
From Coq Require Import Logic.Eqdep_dec.
From Coq Require Import Logic.FunctionalExtensionality.
From PFPL Require Import PartialMap_Set.
From PFPL Require Import Definitions.
From PFPL Require Import Lemmas_Vars.
From PFPL Require Import Lemmas_Rename.
From PFPL Require Import Lemmas_Same_Structure.
From PFPL Require Import Induction_Expr.

Lemma alpha_equiv_refl : forall e,
  alpha_equiv_rel e e.
Proof.
  induction e using expr_ind; intros.
  - apply alpha_equiv_rel_id.
  - apply alpha_equiv_rel_let.
    apply H. apply same_structure_refl.
    intros.
    apply H0.
    apply rename_keeps_structure.
  - apply alpha_equiv_rel_num.
  - apply alpha_equiv_rel_str. apply eqb_refl.
  - apply alpha_equiv_rel_plus.
    apply H. apply same_structure_refl.
    apply H0. apply same_structure_refl.
  - apply alpha_equiv_rel_times.
    apply H. apply same_structure_refl.
    apply H0. apply same_structure_refl.
  - apply alpha_equiv_rel_cat.
    apply H. apply same_structure_refl.
    apply H0. apply same_structure_refl.
  - apply alpha_equiv_rel_len.
    apply H. apply same_structure_refl.
Qed.

Lemma alpha_equiv_sym : forall e e',
  alpha_equiv_rel e e' -> alpha_equiv_rel e' e.
Proof.
  intros e e' H. induction H.
  - apply alpha_equiv_rel_id.
  - apply alpha_equiv_rel_let.
    assumption.
    intros. apply H1; assumption.
  - apply alpha_equiv_rel_num.
  - apply alpha_equiv_rel_str.
    rewrite eqb_sym. assumption.
  - apply alpha_equiv_rel_plus; assumption.
  - apply alpha_equiv_rel_times; assumption.
  - apply alpha_equiv_rel_cat; assumption.
  - apply alpha_equiv_rel_len; assumption.
Qed.

Lemma alpha_equiv_have_same_structure : forall e e',
  alpha_equiv_rel e e' -> same_structure e e'.
Proof.
  intros e e' H. induction H; simpl; auto; constructor; auto.
  remember (max (get_fresh_var e2) (get_fresh_var e2')) as z.
  apply (same_structure_trans _ (rename e2 x z) _).
  apply rename_keeps_structure.
  apply (same_structure_trans _ (rename e2' x' z) _).
  apply H1.
  subst z.
  apply (fresh_var_not_in_conj_vars_left e2 e2').
  subst z.
  apply (fresh_var_not_in_conj_vars_right e2 e2').
  apply same_structure_sym.
  apply rename_keeps_structure.
Qed.

Lemma diff_constructor_not_alpha : forall e e',
  diff_constructor e e' ->
  forall e'' e''',
    same_structure e e'' -> same_structure e' e''' ->
    alpha_equiv_rel e'' e''' -> False.
Proof.
  intros.
  assert (H3 := alpha_equiv_have_same_structure e'' e''' H2).
  assert (H4 := same_structure_trans e e'' e''' H0 H3).
  apply same_structure_sym in H1.
  assert (H5 := same_structure_trans e e''' e' H4 H1).
  clear H0 H1 H2 H3 H4 e'' e'''. rename H5 into H2.
  destruct e.
  all: destruct e'.
  all: inversion H.
  all: inversion H2.
Qed.

Lemma alpha_equiv_same_free_vars : forall e e',
  alpha_equiv_rel e e' -> free_vars e = free_vars e'.
Proof.
  intros e e' H. induction H; simpl; auto.
  - rewrite <- IHalpha_equiv_rel.
    remember (max
      (get_fresh_var (ELet e1 x e2))
      (get_fresh_var (ELet e1' x' e2'))
    ) as z.
    assert (XZ : (x =? z) = false).
    {
      assert (T := fresh_var_not_in_conj_vars_left (ELet e1 x e2) (ELet e1' x' e2')).
      rewrite <- Heqz in T.
      simpl in T. unfold unionSet in T.
      apply orb_false_iff in T.
      destruct T.
      unfold updateSet in H3.
      destruct (x =? z). discriminate.
      reflexivity.
    }
    assert (X'Z : (x' =? z) = false).
    {
      assert (T := fresh_var_not_in_conj_vars_right (ELet e1 x e2) (ELet e1' x' e2')).
      rewrite <- Heqz in T.
      simpl in T. unfold unionSet in T.
      apply orb_false_iff in T.
      destruct T.
      unfold updateSet in H3.
      destruct (x' =? z). discriminate.
      reflexivity.
    }
    assert (Zconj : conj_vars e2 z = false).
    {
      assert (T := fresh_var_not_in_conj_vars_left (ELet e1 x e2) (ELet e1' x' e2')).
      rewrite <- Heqz in T.
      simpl in T. unfold unionSet in T.
      apply orb_false_iff in T. destruct T.
      unfold updateSet in H3.
      destruct (x =? z). discriminate. assumption.
    }
    assert (Zconj' : conj_vars e2' z = false).
    {
      assert (T := fresh_var_not_in_conj_vars_right (ELet e1 x e2) (ELet e1' x' e2')).
      rewrite <- Heqz in T.
      simpl in T. unfold unionSet in T.
      apply orb_false_iff in T. destruct T.
      unfold updateSet in H3.
      destruct (x' =? z). discriminate. assumption.
    }
    assert (T2 : alpha_equiv_rel (rename e2 x z) (rename e2' x' z)).
    { apply H0; assumption. }
    assert (T3 : free_vars (rename e2 x z) = free_vars (rename e2' x' z)).
    { apply H1; assumption. }
    assert (T4 := rename_removes_free_vars e2 x z XZ).
    assert (T5 := rename_removes_free_vars e2' x' z X'Z).
    assert (T6 := rename_keeps_other_free_vars e2 x z).
    assert (T7 := rename_keeps_other_free_vars e2' x' z).
    assert (R : removeFromSet (free_vars e2) x = removeFromSet (free_vars e2') x').
    {
      apply functional_extensionality. intros.
      unfold removeFromSet.
      case_eq (x =? x0); case_eq (x' =? x0); intros.
      reflexivity.
      apply Nat.eqb_eq in H3. subst x0.
      rewrite Nat.eqb_sym in H2.
      assert (T8 := T7 x H2 XZ).
      rewrite <- T3 in T8.
      symmetry. rewrite T8. assumption.
      apply Nat.eqb_eq in H2. subst x0.
      rewrite Nat.eqb_sym in H3.
      assert (T9 := T6 x' H3 X'Z).
      rewrite T3 in T9.
      rewrite T5 in T9.
      assumption.
      rewrite Nat.eqb_sym in H2.
      rewrite Nat.eqb_sym in H3.
      case_eq (x0 =? z); intros.
      + apply Nat.eqb_eq in H4. subst x0.
        rewrite not_in_conj_not_in_free.
        rewrite not_in_conj_not_in_free.
        all: auto.
      + assert (T8 := T7 x0 H2 H4).
        assert (T9 := T6 x0 H3 H4).
        rewrite T8. rewrite T9.
        rewrite T3. reflexivity.
    }
    rewrite R. reflexivity.
  - rewrite IHalpha_equiv_rel1. rewrite IHalpha_equiv_rel2. auto.
  - rewrite IHalpha_equiv_rel1. rewrite IHalpha_equiv_rel2. auto.
  - rewrite IHalpha_equiv_rel1. rewrite IHalpha_equiv_rel2. auto.
Qed.
