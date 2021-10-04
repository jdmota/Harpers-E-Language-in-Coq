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

Lemma substitutivity_aux_1 : forall e e' e'' x,
  (forall v, bound_vars e v = true -> free_vars e'' v = false) ->
  (forall v, bound_vars e' v = true -> free_vars e'' v = false) ->
  alpha_equiv_rel e e' ->
  alpha_equiv_rel (subst' e'' x e) (subst' e'' x e').
Proof.
  intros.
  generalize dependent H0.
  generalize dependent H.
  generalize dependent x.
  generalize dependent e''.
  induction H1; intros; simpl.
  - apply alpha_equiv_refl.
  - case_eq (x0 =? x); case_eq (x0 =? x'); intros X1 X2.
    all:
      apply alpha_equiv_rel_let; [
        apply IHalpha_equiv_rel; [
          intros; apply H2; simpl; unfold unionSet;
          apply orb_true_iff; left; assumption |
          intros; apply H3; simpl; unfold unionSet;
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
      cut (free_vars e2' x0 = false). intro FV.
      rewrite <- subst_non_free_var; [ | assumption].
      rewrite <- subst_non_free_var in H5; [ | assumption].
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
      cut (free_vars e2 x0 = false). intro FV.
      rewrite <- subst_non_free_var; [ | assumption].
      rewrite <- subst_non_free_var in H4; [ | assumption].
      apply H; assumption.
      apply Nat.eqb_eq in X1. subst x0.
      assert (T1 := alpha_equiv_same_free_vars (rename e2 x newX) (rename e2' x' newX) (H newX M5 M6)).
      assert (T2 := rename_removes_free_vars e2' x' newX M2).
      rewrite <- T1 in T2.
      assert (T3 := rename_keeps_other_free_vars e2 x newX x' X2 M2).
      rewrite T3. assumption.
    + intros.
      remember (
        max
          (max
            (max (get_fresh_var e2) (get_fresh_var e2'))
            (max (get_fresh_var (subst' e'' x0 e2)) (get_fresh_var (subst' e'' x0 e2')))
          )
          (max (max (S x) (S x')) (max (S x0) (S z)))
      ) as newX.
      assert (M := complex_max_2 e2 e2' (subst' e'' x0 e2) (subst' e'' x0 e2') x x' x0 z newX HeqnewX).
      destruct M as [M1 [M2 [M3 [M4 [M5 [M6 [M7 M8]]]]]]].
      apply (alpha_equiv_renamed _ _ _ _ newX _ M7 M8 H4 H5).
      rewrite rename_vs_subst.
      rewrite rename_vs_subst.
      all: try assumption.
      apply H0. assumption. assumption.
      intros.
      rewrite <- rename_keeps_bound_vars in H6.
      apply H2. simpl. unfold unionSet.
      apply orb_true_iff. right.
      unfold updateSet. rewrite H6.
      destruct (x =? v); reflexivity.
      intros.
      rewrite <- rename_keeps_bound_vars in H6.
      apply H3. simpl. unfold unionSet.
      apply orb_true_iff. right.
      unfold updateSet. rewrite H6.
      destruct (x' =? v); reflexivity.
      apply H3. simpl. unfold unionSet.
      apply orb_true_iff. right.
      unfold updateSet. rewrite Nat.eqb_refl. reflexivity.
      apply H2. simpl. unfold unionSet.
      apply orb_true_iff. right.
      unfold updateSet. rewrite Nat.eqb_refl. reflexivity.
  - apply alpha_equiv_rel_num.
  - apply alpha_equiv_rel_str. assumption.
  - apply alpha_equiv_rel_plus; [
      apply IHalpha_equiv_rel1 | apply IHalpha_equiv_rel2
    ].
    all: intros.
    apply H; simpl; unfold unionSet;
    apply orb_true_iff; left; assumption.
    apply H0; simpl; unfold unionSet;
    apply orb_true_iff; left; assumption.
    apply H; simpl; unfold unionSet;
    apply orb_true_iff; right; assumption.
    apply H0; simpl; unfold unionSet;
    apply orb_true_iff; right; assumption.
  - apply alpha_equiv_rel_times; [
      apply IHalpha_equiv_rel1 | apply IHalpha_equiv_rel2
    ].
    all: intros.
    apply H; simpl; unfold unionSet;
    apply orb_true_iff; left; assumption.
    apply H0; simpl; unfold unionSet;
    apply orb_true_iff; left; assumption.
    apply H; simpl; unfold unionSet;
    apply orb_true_iff; right; assumption.
    apply H0; simpl; unfold unionSet;
    apply orb_true_iff; right; assumption.
  - apply alpha_equiv_rel_cat; [
      apply IHalpha_equiv_rel1 | apply IHalpha_equiv_rel2
    ].
    all: intros.
    apply H; simpl; unfold unionSet;
    apply orb_true_iff; left; assumption.
    apply H0; simpl; unfold unionSet;
    apply orb_true_iff; left; assumption.
    apply H; simpl; unfold unionSet;
    apply orb_true_iff; right; assumption.
    apply H0; simpl; unfold unionSet;
    apply orb_true_iff; right; assumption.
  - simpl in H. simpl in H0.
    apply alpha_equiv_rel_len.
    apply IHalpha_equiv_rel.
    all: assumption.
Qed.

Lemma substitutivity_aux_2 : forall e e' e'' x o o',
  (forall v, conj_vars e v = true -> conj_vars e (o + v) = false) ->
  (forall v, conj_vars e' v = true -> conj_vars e' (o' + v) = false) ->
  get_fresh_var e'' <= o ->
  get_fresh_var e'' <= o' ->
  alpha_equiv_rel e e' ->
  alpha_equiv_rel (subst' e'' x (fresh_rename e emptySet o)) (subst' e'' x (fresh_rename e' emptySet o')).
Proof.
  intros. apply substitutivity_aux_1.
  intros.
  assert (T := fresh_rename_new_bounds e emptySet o v H4).
  apply not_in_conj_not_in_free.
  apply fresh_var_not_in_conj_vars.
  apply (le_trans _ o _); assumption.
  intros.
  assert (T := fresh_rename_new_bounds e' emptySet o' v H4).
  apply not_in_conj_not_in_free.
  apply fresh_var_not_in_conj_vars.
  apply (le_trans _ o' _); assumption.
  apply fresh_rename_keeps_alpha_equiv_2; assumption.
Qed.

Lemma substitutivity_aux_3 : forall e e' e'' x,
  (forall v, bound_vars e v = true -> free_vars e'' v = false) ->
  alpha_equiv_rel e' e'' ->
  alpha_equiv_rel (subst' e' x e) (subst' e'' x e).
Proof.
  induction e using expr_ind; intros; simpl.
  - destruct (x0 =? x).
    assumption. reflexivity.
  - destruct (x0 =? x).
    + apply alpha_equiv_rel_let.
      apply H. apply same_structure_refl.
      intros. apply H1. simpl.
      unfold unionSet. rewrite H3. apply orb_true_l.
      assumption.
      intros. reflexivity.
    + apply alpha_equiv_rel_let.
      apply H. apply same_structure_refl.
      intros. apply H1. simpl.
      unfold unionSet. rewrite H3. apply orb_true_l.
      assumption.
      intros. apply rename_keeps_alpha_equiv.
      assumption. assumption.
      apply H0. apply same_structure_refl.
      intros. apply H1. simpl.
      unfold unionSet. unfold updateSet.
      rewrite H5. destruct (x =? v); apply orb_true_r.
      assumption.
  - reflexivity.
  - reflexivity.
  - apply alpha_equiv_rel_plus.
    apply H. apply same_structure_refl.
    intros. apply H1. simpl.
    unfold unionSet. rewrite H3. apply orb_true_l.
    assumption.
    apply H0. apply same_structure_refl.
    intros. apply H1. simpl.
    unfold unionSet.
    rewrite H3. apply orb_true_r.
    assumption.
  - apply alpha_equiv_rel_times.
    apply H. apply same_structure_refl.
    intros. apply H1. simpl.
    unfold unionSet. rewrite H3. apply orb_true_l.
    assumption.
    apply H0. apply same_structure_refl.
    intros. apply H1. simpl.
    unfold unionSet.
    rewrite H3. apply orb_true_r.
    assumption.
  - apply alpha_equiv_rel_cat.
    apply H. apply same_structure_refl.
    intros. apply H1. simpl.
    unfold unionSet. rewrite H3. apply orb_true_l.
    assumption.
    apply H0. apply same_structure_refl.
    intros. apply H1. simpl.
    unfold unionSet.
    rewrite H3. apply orb_true_r.
    assumption.
  - apply alpha_equiv_rel_len.
    apply H. apply same_structure_refl.
    intros. apply H0. simpl. assumption. assumption.
Qed.

Lemma substitutivity_aux_4 : forall e e' e'' x o,
  (forall v, conj_vars e v = true -> conj_vars e (o + v) = false) ->
  get_fresh_var e' <= o ->
  get_fresh_var e'' <= o ->
  alpha_equiv_rel e' e'' ->
  alpha_equiv_rel (subst' e' x (fresh_rename e emptySet o)) (subst' e'' x (fresh_rename e emptySet o)).
Proof.
  intros.
  apply substitutivity_aux_3.
  intros.
  assert (T := fresh_rename_new_bounds e emptySet o v H3).
  apply not_in_conj_not_in_free.
  apply fresh_var_not_in_conj_vars.
  apply (le_trans _ o _); assumption.
  assumption.
Qed.

Lemma substitutivity_aux_5 : forall e e' e'' x o o',
  get_fresh_var e <= o ->
  get_fresh_var e <= o' ->
  get_fresh_var e' <= o ->
  get_fresh_var e'' <= o' ->
  alpha_equiv_rel e' e'' ->
  alpha_equiv_rel (subst' e' x (fresh_rename e emptySet o)) (subst' e'' x (fresh_rename e emptySet o')).
Proof.
  intros.
  apply (alpha_equiv_trans _ (subst' e' x (fresh_rename e emptySet (o + o'))) _).
  apply (substitutivity_aux_2 e e e' x o (o + o')).
  intros. apply fresh_var_not_in_conj_vars. apply le_plus_trans. assumption.
  intros. apply fresh_var_not_in_conj_vars. apply le_plus_trans. apply le_plus_trans. assumption.
  assumption. apply le_plus_trans. assumption.
  reflexivity.
  apply (alpha_equiv_trans _ (subst' e'' x (fresh_rename e emptySet (o + o'))) _).
  apply substitutivity_aux_4.
  intros.
  apply fresh_var_not_in_conj_vars.
  apply le_plus_trans. apply le_plus_trans. assumption.
  apply le_plus_trans. assumption.
  rewrite add_comm. apply le_plus_trans. assumption.
  assumption.
  apply substitutivity_aux_2.
  intros.
  apply fresh_var_not_in_conj_vars.
  apply le_plus_trans. apply le_plus_trans. assumption.
  intros.
  apply fresh_var_not_in_conj_vars.
  apply le_plus_trans. assumption.
  rewrite add_comm. apply le_plus_trans. assumption.
  assumption.
  reflexivity.
Qed.

Lemma substitutivity_1 : forall e e' e'' x,
  alpha_equiv_rel e e' ->
  alpha_equiv_rel (subst e'' x e) (subst e'' x e').
Proof.
  intros.
  unfold subst.
  apply substitutivity_aux_2.
  intros. apply fresh_var_not_in_conj_vars.
  apply le_plus_trans.
  apply le_max_l.
  intros. apply fresh_var_not_in_conj_vars.
  apply le_plus_trans.
  apply le_max_l.
  apply le_max_r.
  apply le_max_r.
  assumption.
Qed.

Lemma substitutivity_2 : forall e e' e'' x,
  alpha_equiv_rel e' e'' ->
  alpha_equiv_rel (subst e' x e) (subst e'' x e).
Proof.
  intros.
  unfold subst.
  apply substitutivity_aux_5.
  intros.
  apply le_max_l.
  apply le_max_l.
  apply le_max_r.
  apply le_max_r.
  assumption.
Qed.

(** Alpha equivalence is preserved by substitution *)
Theorem substitutivity : forall e e' e'' e''' x,
  alpha_equiv_rel e e' ->
  alpha_equiv_rel e'' e''' ->
  alpha_equiv_rel (subst e x e'') (subst e' x e''').
Proof.
  intros.
  assert (T1 := substitutivity_1 e'' e''' e x H0).
  apply (alpha_equiv_trans _ (subst e x e''') _).
  apply substitutivity_1.
  assumption.
  apply substitutivity_2.
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
