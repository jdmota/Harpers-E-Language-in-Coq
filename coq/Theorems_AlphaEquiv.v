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
From Coq Require Import Classes.Morphisms.
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
From PFPL Require Import Lemmas_FreshRename_AlphaEquiv.
From PFPL Require Import Lemmas_AlphaEquiv_2.
From PFPL Require Import Lemmas_Subst.
From PFPL Require Import Lemmas_Rename_Subst.

Lemma alpha_equiv_func_equiv_rel_1 :
  forall e e', alpha_equiv_rel e e' -> (alpha_equiv e e') = true.
Proof.
  intros e e' H.
  induction H; intros; rewrite alpha_equiv_equation.
  - apply Nat.eqb_refl.
  - apply andb_true_iff. split.
    assumption.
    apply H1.
    apply fresh_var_not_in_conj_vars_left.
    apply fresh_var_not_in_conj_vars_right.
  - apply Nat.eqb_refl.
  - assumption.
  - apply andb_true_iff. split; assumption.
  - apply andb_true_iff. split; assumption.
  - apply andb_true_iff. split; assumption.
  - assumption.
Qed.

Lemma alpha_equiv_func_equiv_rel_2 :
  forall e e', alpha_equiv e e' = true -> alpha_equiv_rel e e'.
Proof.
  intros e e'.
  induction e, e' using expr_pair_ind; intro AE;
  rewrite alpha_equiv_equation in AE.
  - apply Nat.eqb_eq in AE. subst. apply alpha_equiv_rel_id.
  - apply andb_true_iff in AE. destruct AE as [AE AE'].
    apply alpha_equiv_rel_let.
    apply H. apply same_structure_refl.
    apply same_structure_refl. assumption.
    intros.
    remember (max (get_fresh_var e'2) (get_fresh_var e'4)) as newX.
    cut (conj_vars e'2 newX = false). intro C1.
    cut (conj_vars e'4 newX = false). intro C2.
    assert (R := alpha_equiv_renamed e'2 e'4 x x' newX z C1 C2 H1 H2).
    apply R. apply H0; try apply rename_keeps_structure.
    assumption.
    all: subst newX.
    apply fresh_var_not_in_conj_vars_right.
    apply fresh_var_not_in_conj_vars_left.
  - apply Nat.eqb_eq in AE. subst. apply alpha_equiv_rel_num. 
  - apply alpha_equiv_rel_str. assumption.
  - apply andb_true_iff in AE. destruct AE as [AE AE'].
    apply alpha_equiv_rel_plus.
    apply H; try apply same_structure_refl. assumption.
    apply H0; try apply same_structure_refl. assumption.
  - apply andb_true_iff in AE. destruct AE as [AE AE'].
    apply alpha_equiv_rel_times.
    apply H; try apply same_structure_refl. assumption.
    apply H0; try apply same_structure_refl. assumption.
  - apply andb_true_iff in AE. destruct AE as [AE AE'].
    apply alpha_equiv_rel_cat.
    apply H; try apply same_structure_refl. assumption.
    apply H0; try apply same_structure_refl. assumption.
  - apply alpha_equiv_rel_len.
    apply H; try apply same_structure_refl. assumption.
  - unfold diff_constructor in H.
    destruct e'1; destruct e'2.
    all: try contradiction.
    all: try discriminate.
Qed.

(** Proof of correcteness of the alpha equivalence testing function *)
Theorem alpha_equiv_func_equiv_rel :
  forall e e', alpha_equiv_rel e e' <-> (alpha_equiv e e') = true.
Proof.
  intros. split.
  apply alpha_equiv_func_equiv_rel_1.
  apply alpha_equiv_func_equiv_rel_2.
Qed.

(** Alpha equivalence is a equivalence relation *)
Instance alpha_equiv_Equiv : Equivalence alpha_equiv_rel.
Proof.
  split.
  unfold Reflexive. apply alpha_equiv_refl.
  unfold Symmetric. apply alpha_equiv_sym.
  unfold Transitive. apply alpha_equiv_trans.
Qed.

(** Alpha equivalence is preserved by the [EPlus] operator *)
Lemma alpha_equiv_preserved_by_plus :
  Proper (alpha_equiv_rel ==> alpha_equiv_rel ==> alpha_equiv_rel) (EPlus).
Proof.
  intros e e' H1 e'' e''' H2.
  apply alpha_equiv_rel_plus. all: assumption.
Qed.

(** Alpha equivalence is preserved by the [ETimes] operator *)
Lemma alpha_equiv_preserved_by_times :
  Proper (alpha_equiv_rel ==> alpha_equiv_rel ==> alpha_equiv_rel) (ETimes).
Proof.
  intros e e' H1 e'' e''' H2.
  apply alpha_equiv_rel_times. all: assumption.
Qed.

(** Alpha equivalence is preserved by the [ECat] operator *)
Lemma alpha_equiv_preserved_by_cat :
  Proper (alpha_equiv_rel ==> alpha_equiv_rel ==> alpha_equiv_rel) (ECat).
Proof.
  intros e e' H1 e'' e''' H2.
  apply alpha_equiv_rel_cat. all: assumption.
Qed.

(** Alpha equivalence is preserved by the [ELen] operator *)
Lemma alpha_equiv_preserved_by_len :
  Proper (alpha_equiv_rel ==> alpha_equiv_rel) (ELen).
Proof.
  intros e e' H1.
  apply alpha_equiv_rel_len. all: assumption.
Qed.

Definition ELet2 x e1 e2 := ELet e1 x e2.

(** Alpha equivalence is preserved by the [ELet] operator *)
Lemma alpha_equiv_preserved_by_let (x : nat) :
  Proper (alpha_equiv_rel ==> alpha_equiv_rel ==> alpha_equiv_rel) (ELet2 x).
Proof.
  intros e e' H1 e'' e''' H2. unfold ELet2.
  apply alpha_equiv_rel_let.
  assumption.
  intros.
  apply rename_keeps_alpha_equiv.
  all: assumption.
Qed.

(** Alpha equivalence is preserved by substitution (auxiliary) *)
Lemma substitutivity_aux : forall e e' e'' e''' x,
  (forall v, bound_vars e v = true -> free_vars e'' v = false) ->
  (forall v, bound_vars e' v = true -> free_vars e''' v = false) ->
  alpha_equiv_rel e e' ->
  alpha_equiv_rel e'' e''' ->
  alpha_equiv_rel (subst' e'' x e) (subst' e''' x e').
Proof.
  intros.
  generalize dependent H0.
  generalize dependent H.
  induction H1; intros; simpl.
  - destruct (x =? x0). assumption. apply alpha_equiv_refl.
  - case_eq (x =? x0); case_eq (x =? x'); intros X1 X2.
    all: apply alpha_equiv_rel_let; [
      apply IHalpha_equiv_rel; [
        intros; apply H3; simpl; unfold unionSet;
        apply orb_true_iff; left; assumption |
        intros; apply H4; simpl; unfold unionSet;
        apply orb_true_iff; left; assumption
      ] |
    ].
    + assumption.
    + intros.
      remember (
        max
          (max (get_fresh_var e2) (get_fresh_var e2'))
          (max (max (S x) (S x')) (max (S x0) (S z)))
      ) as newX.
      assert (M := complex_max e2 e2' x x' x0 z newX HeqnewX).
      destruct M as [M1 [M2 [M3 [M4 [M5 M6]]]]].
      cut (free_vars e2' x = false). intro FV.
      rewrite <- subst_non_free_var; [ | assumption].
      rewrite <- subst_non_free_var in H6; [ | assumption].
      apply H; assumption.
      apply Nat.eqb_eq in X2. subst x0.
      assert (T1 := alpha_equiv_same_free_vars (rename e2 x newX) (rename e2' x' newX) (H newX M5 M6)).
      assert (T2 := rename_removes_free_vars e2 x newX M1).
      rewrite T1 in T2.
      assert (T3 := rename_keeps_other_free_vars e2' x' newX x X1 M1).
      rewrite T3. assumption.
    + intros.
      remember (
        max
          (max (get_fresh_var e2) (get_fresh_var e2'))
          (max (max (S x) (S x')) (max (S x0) (S z)))
      ) as newX.
      assert (M := complex_max e2 e2' x x' x0 z newX HeqnewX).
      destruct M as [M1 [M2 [M3 [M4 [M5 M6]]]]].
      cut (free_vars e2 x = false). intro FV.
      rewrite <- subst_non_free_var; [ | assumption].
      rewrite <- subst_non_free_var in H5; [ | assumption].
      apply H; assumption.
      apply Nat.eqb_eq in X1. subst x'.
      assert (T1 := alpha_equiv_same_free_vars (rename e2 x0 newX) (rename e2' x newX) (H newX M5 M6)).
      assert (T2 := rename_removes_free_vars e2' x newX M2).
      rewrite <- T1 in T2.
      assert (T3 := rename_keeps_other_free_vars e2 x0 newX x X2 M2).
      rewrite T3. assumption.
    + intros.
      remember (
        max
          (max
            (max (get_fresh_var e2) (get_fresh_var e2'))
            (max (get_fresh_var (subst' e'' x e2)) (get_fresh_var (subst' e''' x e2')))
          )
          (max (max (S x) (S x')) (max (S x0) (S z)))
      ) as newX.
      assert (M := complex_max_2 e2 e2' (subst' e'' x e2) (subst' e''' x e2') x x' x0 z newX HeqnewX).
      destruct M as [M1 [M2 [M3 [M4 [M5 [M6 [M7 M8]]]]]]].
      apply (alpha_equiv_renamed _ _ _ _ newX _ M7 M8 H5 H6).
      rewrite rename_vs_subst.
      rewrite rename_vs_subst.
      all: try assumption.
      apply H0. assumption. assumption.
      intros.
      rewrite <- rename_keeps_bound_vars in H7.
      apply H3. simpl. unfold unionSet.
      apply orb_true_iff. right.
      unfold updateSet. rewrite H7.
      destruct (x0 =? v); reflexivity.
      intros.
      rewrite <- rename_keeps_bound_vars in H7.
      apply H4. simpl. unfold unionSet.
      apply orb_true_iff. right.
      unfold updateSet. rewrite H7.
      destruct (x' =? v); reflexivity.
      apply H4. simpl. unfold unionSet.
      apply orb_true_iff. right.
      unfold updateSet. rewrite Nat.eqb_refl. reflexivity.
      apply H3. simpl. unfold unionSet.
      apply orb_true_iff. right.
      unfold updateSet. rewrite Nat.eqb_refl. reflexivity.
  - apply alpha_equiv_rel_num.
  - apply alpha_equiv_rel_str. assumption.
  - apply alpha_equiv_rel_plus; [
      apply IHalpha_equiv_rel1; intros;
      [apply H | apply H0] |
      apply IHalpha_equiv_rel2; intros;
      [apply H | apply H0]
    ].
    all: simpl; unfold unionSet; apply orb_true_iff.
    all: try (left; assumption).
    all: try (right; assumption).
  - apply alpha_equiv_rel_times; [
      apply IHalpha_equiv_rel1; intros;
      [apply H | apply H0] |
      apply IHalpha_equiv_rel2; intros;
      [apply H | apply H0]
    ].
    all: simpl; unfold unionSet; apply orb_true_iff.
    all: try (left; assumption).
    all: try (right; assumption).
  - apply alpha_equiv_rel_cat; [
      apply IHalpha_equiv_rel1; intros;
      [apply H | apply H0] |
      apply IHalpha_equiv_rel2; intros;
      [apply H | apply H0]
    ].
    all: simpl; unfold unionSet; apply orb_true_iff.
    all: try (left; assumption).
    all: try (right; assumption).
  - simpl in H. simpl in H0.
    apply alpha_equiv_rel_len.
    apply IHalpha_equiv_rel.
    all: assumption.
Qed.

(** Alpha equivalence is preserved by substitution *)
Theorem substitutivity : forall e e' e'' e''' x,
  alpha_equiv_rel e e' ->
  alpha_equiv_rel e'' e''' ->
  alpha_equiv_rel (subst e'' x e) (subst e''' x e').
Proof.
  intros. unfold subst.
  remember (max (get_fresh_var e) (get_fresh_var e'')) as o.
  remember (max (get_fresh_var e') (get_fresh_var e''')) as o'.
  apply substitutivity_aux.
  intros.
  assert (T := fresh_rename_new_bounds e emptySet o v H1).
  apply not_in_conj_not_in_free.
  apply fresh_var_not_in_conj_vars. lia.
  intros.
  assert (T := fresh_rename_new_bounds e' emptySet o' v H1).
  apply not_in_conj_not_in_free.
  apply fresh_var_not_in_conj_vars. lia.
  apply fresh_rename_keeps_alpha_equiv_2.
  intros.
  apply fresh_var_not_in_conj_vars. lia.
  intros.
  apply fresh_var_not_in_conj_vars. lia.
  assumption.
  assumption.
Qed.

(*Definition subst2 x e' e := subst e' x e.

Theorem substitutivity_proper (x : nat) :
  Proper (alpha_equiv_rel ==> alpha_equiv_rel ==> alpha_equiv_rel) (subst2 x).
Proof.
  intros e e' H e'' e''' H2.
  unfold subst2.
  apply substitutivity; assumption.
Qed.*)
