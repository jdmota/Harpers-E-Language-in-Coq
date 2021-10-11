Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Strings.String.
From Coq Require Import Logic.Eqdep_dec.
From PFPL Require Import PartialMap_Set.
From PFPL Require Import Definitions.
From PFPL Require Import Lemmas_Vars.
From PFPL Require Import Lemmas_Rename.
From PFPL Require Import Lemmas_Same_Structure.
From PFPL Require Import Induction_Expr.
From PFPL Require Import Lemmas_AlphaEquiv.
From PFPL Require Import Lemmas_Rename_AlphaEquiv.
From PFPL Require Import Lemmas_FreshRename.
From PFPL Require Import Lemmas_FreshRename_AlphaEquiv.
From PFPL Require Import Lemmas_Rename_FreshRename.
From PFPL Require Import Lemmas_Subst.
From PFPL Require Import Lemmas_Rename_Subst.
From PFPL Require Import Theorems_AlphaEquiv.
From PFPL Require Import Theorems_Eval.

(** At most one type for each expression (In Harper's book) *)
Lemma unicity: forall Gamma e t t',
  hastype Gamma e t -> hastype Gamma e t' -> t = t'.
Proof.
  intros Gamma e t t' H1. generalize dependent t'.
  induction H1; intros t' H2; inversion H2; subst.
  all: try reflexivity.
  rewrite H in H3. inversion H3. reflexivity.
  apply IHhastype1 in H5. subst. apply IHhastype2. assumption.
Qed.

(** Typing rules are syntax-directed (In Harper's book) *)
Lemma inversion : forall Gamma e t,
  hastype Gamma e t -> (
    (forall (x: nat), e = EId x -> Gamma x = Some(t)) /\
    (forall (s: string), e = EStr s -> t = TStr) /\
    (forall (n: nat), e = ENum n -> t = TNum) /\
    (forall e1 e2, e = EPlus e1 e2 -> t = TNum /\ hastype Gamma e1 TNum /\ hastype Gamma e2 TNum) /\
    (forall e1 e2, e = ETimes e1 e2 -> t = TNum /\ hastype Gamma e1 TNum /\ hastype Gamma e2 TNum) /\
    (forall e1 e2, e = ECat e1 e2 -> t = TStr /\ hastype Gamma e1 TStr /\ hastype Gamma e2 TStr) /\
    (forall e1, e = ELen e1 -> t = TNum /\ hastype Gamma e1 TStr) /\
    (forall e1 x e2, e = ELet e1 x e2 -> (exists t1 t2, t = t2 /\ hastype Gamma e1 t1 /\ hastype (update Gamma x t1) e2 t2))
  ).
Proof.
  intros Gamma e t H. induction H.
  - repeat split; intros; inversion H0.
    subst. assumption.
  - repeat split; intros; inversion H.
  - repeat split; intros; inversion H.
  - repeat split; intros; inversion H1.
    subst. assumption. subst. assumption.
  - repeat split; intros; inversion H1.
    subst. assumption. subst. assumption.
  - repeat split; intros; inversion H1.
    subst. assumption. subst. assumption.
  - repeat split; intros; inversion H0.
    subst. assumption.
  - repeat split; intros; inversion H1.
    subst. exists t1. exists t2.
    repeat split; assumption.
Qed.

(** Weakening (In Harper's book) *)
Lemma weakening : forall Gamma e t,
  hastype Gamma e t -> (forall x t', Gamma x = None -> hastype (x |-> t'; Gamma) e t).
Proof.
  intros Gamma e t H1 y t' H2. induction H1.
  - apply T_Var. rewrite <- H. apply (update_neq _ Gamma x y t').
    unfold not. intros H4. subst. rewrite H2 in H. inversion H.
  - apply T_Str.
  - apply T_Num.
  - apply T_Plus. apply IHhastype1. assumption. apply IHhastype2. assumption.
  - apply T_Times. apply IHhastype1. assumption. apply IHhastype2. assumption.
  - apply T_Cat. apply IHhastype1. assumption. apply IHhastype2. assumption.
  - apply T_Len. apply IHhastype. assumption.
  - assert (H2' := H2). apply IHhastype1 in H2.
    clear IHhastype1. apply (T_Let _ _ t1).
    + assumption.
    + case_eq (x =? y).
      * intros. apply Nat.eqb_eq in H. subst. rewrite (update_shadow EType Gamma y). assumption.
      * intros. apply Nat.eqb_neq in H. rewrite update_permute.
        apply IHhastype2. rewrite <- H2'. apply (update_neq _ Gamma). assumption.
        apply not_eq_sym. assumption.
Qed.

(** Different enunciation of the weakening property *)
Lemma weakening_2 : forall Gamma e t,
  hastype Gamma e t -> (forall x t', free_vars e x = false -> hastype (x |-> t'; Gamma) e t).
Proof.
  intros Gamma e t H1 y t' H2. induction H1.
  - apply T_Var. rewrite <- H. apply (update_neq _ Gamma x y t').
    unfold not. intros. subst. simpl in H2. unfold singletonSet in H2.
    rewrite Nat.eqb_refl in H2. discriminate.
  - apply T_Str.
  - apply T_Num.
  - simpl in H2. unfold unionSet in H2. apply orb_false_iff in H2. destruct H2.
    apply T_Plus. apply IHhastype1. assumption. apply IHhastype2. assumption.
  - simpl in H2. unfold unionSet in H2. apply orb_false_iff in H2. destruct H2.
    apply T_Times. apply IHhastype1. assumption. apply IHhastype2. assumption.
  - simpl in H2. unfold unionSet in H2. apply orb_false_iff in H2. destruct H2.
    apply T_Cat. apply IHhastype1. assumption. apply IHhastype2. assumption.
  - simpl in H2.
    apply T_Len. apply IHhastype. assumption.
  - simpl in H2. unfold unionSet in H2. apply orb_false_iff in H2. destruct H2.
    unfold removeFromSet in H0.
    apply (T_Let _ _ t1).
    + apply IHhastype1. assumption.
    + case_eq (x =? y); intros.
      * apply Nat.eqb_eq in H1. subst. rewrite (update_shadow EType Gamma y). assumption.
      * rewrite H1 in H0. apply Nat.eqb_neq in H1.
        rewrite update_permute. apply IHhastype2.
        assumption. apply not_eq_sym. assumption.
Qed.

(** Different enunciation of the weakening property *)
Lemma weakening_3 : forall Gamma e t x t',
  hastype (update Gamma x t') e t -> free_vars e x = false -> hastype Gamma e t.
Proof.
  intros Gamma e t y t' H H0. remember (y |-> t'; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction H; intros; subst.
  - simpl in H0. unfold singletonSet in H0.
    case_eq (x =? y); intro XY.
    rewrite XY in H0. discriminate.
    unfold update in H. rewrite Nat.eqb_sym in XY. rewrite XY in H.
    apply T_Var. assumption.
  - apply T_Str.
  - apply T_Num.
  - simpl in H0. unfold unionSet in H0. apply orb_false_iff in H0. destruct H0.
    apply T_Plus. apply IHhastype1. assumption. reflexivity.
    apply IHhastype2. assumption. reflexivity.
  - simpl in H0. unfold unionSet in H0. apply orb_false_iff in H0. destruct H0.
    apply T_Times. apply IHhastype1. assumption. reflexivity.
    apply IHhastype2. assumption. reflexivity.
  - simpl in H0. unfold unionSet in H0. apply orb_false_iff in H0. destruct H0.
    apply T_Cat. apply IHhastype1. assumption. reflexivity.
    apply IHhastype2. assumption. reflexivity.
  - simpl in H.
    apply T_Len. apply IHhastype. assumption. reflexivity.
  - simpl in H0. unfold unionSet in H0. apply orb_false_iff in H0. destruct H0.
    unfold removeFromSet in H2.
    apply (T_Let _ _ t1).
    + apply IHhastype1. assumption. reflexivity.
    + case_eq (x =? y); intros.
      * apply Nat.eqb_eq in H3. subst.
        rewrite (update_shadow EType Gamma0 y) in H1. assumption.
      * rewrite H3 in H2. apply Nat.eqb_neq in H3.
        apply IHhastype2. assumption.
        rewrite update_permute. reflexivity.
        apply not_eq_sym. assumption.
Qed.

(** Auxiliary lemma to prove that typing is preserved by alpha equivalence *)
Lemma same_type_with_renamed : forall Gamma e t x x' t',
  conj_vars e x' = false ->
  hastype (x |-> t'; Gamma) e t <->
  hastype (x' |-> t'; Gamma) (rename e x x') t.
Proof.
  intros. split; intro.
  {
    remember (x |-> t'; Gamma) as Gamma'.
    generalize dependent Gamma.
    induction H0; intros; simpl; simpl in H; subst.
    - unfold update in H0.
      case_eq (x =? x0); intro XX0; rewrite XX0 in H0.
      inversion H0. subst.
      constructor. unfold update.
      rewrite Nat.eqb_refl. reflexivity.
      constructor. unfold update.
      unfold singletonSet in H. rewrite Nat.eqb_sym.
      destruct (x0 =? x'). discriminate. assumption.
    - constructor.
    - constructor.
    - unfold unionSet in H. apply orb_false_iff in H. destruct H as [H H'].
      constructor.
      apply IHhastype1; auto.
      apply IHhastype2; auto.
    - unfold unionSet in H. apply orb_false_iff in H. destruct H as [H H'].
      constructor.
      apply IHhastype1; auto.
      apply IHhastype2; auto.
    - unfold unionSet in H. apply orb_false_iff in H. destruct H as [H H'].
      constructor.
      apply IHhastype1; auto.
      apply IHhastype2; auto.
    - constructor.
      apply IHhastype; auto.
    - unfold unionSet in H. apply orb_false_iff in H. destruct H as [H H'].
      unfold updateSet in H'.
      case_eq (x0 =? x'); intro X0X'; rewrite X0X' in H'.
      discriminate.
      case_eq (x =? x0); intro XX0.
      + apply Nat.eqb_eq in XX0. subst.
        apply (T_Let _ _ t1). apply IHhastype1.
        assumption. reflexivity.
        rewrite update_shadow in H0_0.
        rewrite update_permute.
        apply weakening_2. assumption.
        apply not_in_conj_not_in_free. assumption.
        apply Nat.eqb_neq. rewrite Nat.eqb_sym. assumption.
      + apply (T_Let _ _ t1). apply IHhastype1.
        assumption. reflexivity.
        rewrite update_permute.
        apply IHhastype2. assumption.
        rewrite update_permute. reflexivity.
        apply Nat.eqb_neq. assumption.
        apply Nat.eqb_neq. rewrite Nat.eqb_sym. assumption.
  }
  {
    generalize dependent H0.
    generalize dependent H.
    generalize dependent t'.
    generalize dependent t0.
    generalize dependent Gamma.
    induction e; intros; simpl; simpl in H;
    simpl in H0; subst.
    - inversion H0. constructor.
    - inversion H0. constructor.
    - case_eq (x =? x0); intro X0X; rewrite X0X in H0.
      apply Nat.eqb_eq in X0X. subst.
      inversion H0. subst. constructor.
      unfold update in H3. rewrite Nat.eqb_refl in H3.
      inversion H3. subst.
      unfold update. rewrite Nat.eqb_refl. reflexivity.
      inversion H0. subst. constructor.
      unfold update in H3.
      unfold singletonSet in H. rewrite Nat.eqb_sym in H.
      case_eq (x' =? x0); intro X'X0; rewrite X'X0 in H.
      discriminate. rewrite X'X0 in H3.
      unfold update. rewrite X0X. assumption.
    - unfold unionSet in H. apply orb_false_iff in H. destruct H as [H H'].
      inversion H0. subst. constructor.
      apply IHe1; auto.
      apply IHe2; auto.
    - unfold unionSet in H. apply orb_false_iff in H. destruct H as [H H'].
      inversion H0. subst. constructor.
      apply IHe1; auto.
      apply IHe2; auto.
    - unfold unionSet in H. apply orb_false_iff in H. destruct H as [H H'].
      inversion H0. subst. constructor.
      apply IHe1; auto.
      apply IHe2; auto.
    - inversion H0. subst. constructor.
      apply IHe; auto.
    - unfold unionSet in H. apply orb_false_iff in H. destruct H as [H H'].
      unfold updateSet in H'. case_eq (x0 =? x'); intro X0X'; rewrite X0X' in H'.
      discriminate.
      case_eq (x =? x0); intro XX0; rewrite XX0 in H0.
      apply Nat.eqb_eq in XX0. subst. inversion H0. subst.
      apply (T_Let _ _ t1).
      apply IHe1; auto.
      rewrite update_shadow.
      rewrite update_permute in H7.
      apply (weakening_3 (x0 |-> t1; Gamma) e2 t0 x' t').
      assumption. apply not_in_conj_not_in_free. assumption.
      rewrite Nat.eqb_sym in X0X'. apply Nat.eqb_neq. assumption.
      inversion H0. subst.
      apply (T_Let _ _ t1).
      apply IHe1; auto.
      rewrite update_permute.
      apply IHe2. assumption.
      rewrite update_permute. assumption.
      apply Nat.eqb_neq. assumption.
      apply Nat.eqb_neq. assumption.
  }
Qed.

(** Typing is preserved by alpha equivalence *)
Lemma alpha_variants_have_same_type : forall e e' Gamma t,
  alpha_equiv_rel e e' -> hastype Gamma e t -> hastype Gamma e' t.
Proof.
  intros e e' Gamma t H.
  generalize dependent t.
  generalize dependent Gamma.
  induction H; intros.
  - assumption.
  - inversion H2. subst.
    apply (T_Let _ _ t1).
    apply IHalpha_equiv_rel. assumption.
    remember (max (get_fresh_var e2) (get_fresh_var e2')) as newX.
    assert (C1 : conj_vars e2 newX = false).
    rewrite HeqnewX. apply fresh_var_not_in_conj_vars_left.
    assert (C2 : conj_vars e2' newX = false).
    rewrite HeqnewX. apply fresh_var_not_in_conj_vars_right.
    apply (same_type_with_renamed Gamma e2' t0 x' newX t1 C2).
    apply (H1 newX C1 C2).
    apply (same_type_with_renamed Gamma e2 t0 x newX t1 C1).
    assumption.
  - assumption.
  - apply eqb_eq in H. subst. assumption.
  - inversion H1. subst. apply T_Plus.
    apply IHalpha_equiv_rel1; assumption.
    apply IHalpha_equiv_rel2; assumption.
  - inversion H1. subst. apply T_Times.
    apply IHalpha_equiv_rel1; assumption.
    apply IHalpha_equiv_rel2; assumption.
  - inversion H1. subst. apply T_Cat.
    apply IHalpha_equiv_rel1; assumption.
    apply IHalpha_equiv_rel2; assumption.
  - inversion H0. subst. apply T_Len.
    apply IHalpha_equiv_rel; assumption.
Qed.

(** Substitution property assuming no capture of variables *)
Lemma substitution_aux : forall Gamma x t e t' e',
  (forall v, bound_vars e v = true -> free_vars e' v = false) ->
  hastype (x |-> t'; Gamma) e t -> hastype Gamma e' t' -> hastype Gamma (subst' e' x e) t.
Proof.
  intros Gamma x t e t' e' H1 H2 H3.
  remember (x |-> t'; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction H2; intros Gamma' G H3; simpl.
  - case_eq (x =? x0); intros.
    * apply Nat.eqb_eq in H0. subst. unfold update in H.
      rewrite Nat.eqb_refl in H. inversion H. subst. assumption.
    * apply Nat.eqb_neq in H0. apply T_Var. rewrite <- H.
      rewrite G. symmetry. apply update_neq. assumption.
  - apply T_Str.
  - apply T_Num.
  - simpl in H1. unfold unionSet in H1.
    apply T_Plus.
    + apply IHhastype1. intros.
      apply H1. apply orb_true_iff. left. assumption.
      assumption. assumption.
    + apply IHhastype2. intros.
      apply H1. apply orb_true_iff. right. assumption.
      assumption. assumption.
  - simpl in H1. unfold unionSet in H1.
    apply T_Times.
    + apply IHhastype1. intros.
      apply H1. apply orb_true_iff. left. assumption.
      assumption. assumption.
    + apply IHhastype2. intros.
      apply H1. apply orb_true_iff. right. assumption.
      assumption. assumption.
  - simpl in H1. unfold unionSet in H1.
    apply T_Cat.
    + apply IHhastype1. intros.
      apply H1. apply orb_true_iff. left. assumption.
      assumption. assumption.
    + apply IHhastype2. intros.
      apply H1. apply orb_true_iff. right. assumption.
      assumption. assumption.
  - simpl in H1.
    apply T_Len.
    apply IHhastype. intros.
    apply H1. assumption.
    assumption. assumption.
  - simpl in H1. unfold unionSet in H1. unfold updateSet in H1.
    case_eq (x =? x0); intro XX0.
    + apply Nat.eqb_eq in XX0. subst x0.
      apply (T_Let _ _ t1).
      * apply IHhastype1. intros.
        apply H1. apply orb_true_iff. left. assumption.
        assumption. assumption.
      * rewrite G in H2_0.
        rewrite update_shadow in H2_0. assumption.
    + apply (T_Let _ _ t1).
      * apply IHhastype1. intros.
        apply H1. apply orb_true_iff. left. assumption.
        assumption. assumption.
      * rewrite G in H2_0.
        apply IHhastype2. intros.
        apply H1. apply orb_true_iff. right.
        rewrite H. case_eq (x0 =? v); reflexivity.
        rewrite G.
        apply update_permute. apply Nat.eqb_neq. assumption.
        apply weakening_2. assumption.
        apply H1. rewrite Nat.eqb_refl.
        apply orb_true_r.
Qed.

(** Substitution (In Harper's book) *)
Lemma substitution : forall Gamma x t e t' e',
  hastype (x |-> t'; Gamma) e t -> hastype Gamma e' t' -> hastype Gamma (subst e' x e) t.
Proof.
  intros.
  unfold subst.
  remember (max (get_fresh_var e) (get_fresh_var e')) as o.
  apply (substitution_aux Gamma _ _ _ t').
  apply fresh_rename_removes_conflicts.
  assumption.
  apply (alpha_variants_have_same_type e).
  apply fresh_rename_keeps_alpha_equiv.
  rewrite Heqo.
  apply le_max_l.
  all: assumption.
Qed.

(** Decomposition property assuming no capture of variables *)
Lemma decomposition_aux : forall Gamma e x e' t,
  (forall v, bound_vars e v = true -> free_vars e' v = false) ->
  hastype Gamma (subst' e' x e) t -> (forall t', hastype Gamma e' t' -> hastype (x |-> t'; Gamma) e t).
Proof.
  intros Gamma e x. generalize dependent Gamma.
  induction e; intros; simpl in H0.
  - inversion H0. subst. apply T_Num.
  - inversion H0. subst. apply T_Str.
  - case_eq (x =? x0); intros.
    * rewrite H2 in H0. apply T_Var.
      unfold update. rewrite H2.
      apply (unicity Gamma e' t0 t' H0) in H1.
      subst. reflexivity.
    * rewrite H2 in H0. inversion H0. subst.
      apply T_Var. unfold update.
      rewrite H2. assumption.
  - simpl in H. unfold unionSet in H.
    inversion H0. subst.
    apply T_Plus; [apply (IHe1 _ e') | apply (IHe2 _ e')].
    all: try assumption.
    all: intros; apply H; rewrite H2.
    apply orb_true_l. apply orb_true_r.
  - simpl in H. unfold unionSet in H.
    inversion H0. subst.
    apply T_Times; [apply (IHe1 _ e') | apply (IHe2 _ e')].
    all: try assumption.
    all: intros; apply H; rewrite H2.
    apply orb_true_l. apply orb_true_r.
  - simpl in H. unfold unionSet in H.
    inversion H0. subst.
    apply T_Cat; [apply (IHe1 _ e') | apply (IHe2 _ e')].
    all: try assumption.
    all: intros; apply H; rewrite H2.
    apply orb_true_l. apply orb_true_r.
  - simpl in H. inversion H0. subst.
    apply T_Len. apply (IHe _ e'); assumption.
  - simpl in H. unfold unionSet in H. unfold updateSet in H.
    case_eq (x =? x0); intro.
    + apply Nat.eqb_eq in H2. subst x0.
      rewrite Nat.eqb_refl in H0. inversion H0. subst.
      apply (T_Let _ _ t1).
      * apply (IHe1 _ e').
        all: try assumption.
        intros; apply H; rewrite H2.
        apply orb_true_l.
      * rewrite update_shadow. assumption.
    + rewrite H2 in H0. inversion H0. subst.
      apply (T_Let _ _ t1).
      * apply (IHe1 _ e').
        all: try assumption.
        intros; apply H; rewrite H3.
        apply orb_true_l.
      * rewrite update_permute.
        apply (IHe2 _ e').
        all: try assumption.
        intros; apply H; rewrite H3.
        destruct (x0 =? v); apply orb_true_r.
        apply weakening_2. assumption.
        apply H. rewrite Nat.eqb_refl.
        apply orb_true_r.
        apply Nat.eqb_neq. assumption.
Qed.

(** Decomposition (In Harper's book) *)
Lemma decomposition : forall Gamma e x e' t,
  hastype Gamma (subst e' x e) t -> (forall t', hastype Gamma e' t' -> hastype (x |-> t'; Gamma) e t).
Proof.
  intros.
  unfold subst in H.
  remember (max (get_fresh_var e) (get_fresh_var e')) as o.
  apply (alpha_variants_have_same_type (fresh_rename e emptySet o)).
  apply alpha_equiv_sym.
  apply fresh_rename_keeps_alpha_equiv.
  rewrite Heqo. apply le_max_l.
  apply (decomposition_aux Gamma _ _ e').
  apply fresh_rename_removes_conflicts.
  all: assumption.
Qed.

(** Steps of evaluation preserve typing (In Harper's book) *)
Theorem preservation : forall Gamma e t e',
  hastype Gamma e t -> Eval e e' -> hastype Gamma e' t.
Proof.
  intros Gamma e t e' H1 H2. generalize dependent t. induction H2; intros t H1.
  - inversion H1. subst. apply T_Num.
  - inversion H1. subst. apply T_Plus. apply IHEval. assumption. assumption.
  - inversion H1. subst. apply T_Plus. assumption. apply IHEval. assumption.
  - inversion H1. subst. apply T_Num.
  - inversion H1. subst. apply T_Times. apply IHEval. assumption. assumption.
  - inversion H1. subst. apply T_Times. assumption. apply IHEval. assumption.
  - inversion H1. subst. apply T_Str.
  - inversion H1. subst. apply T_Cat. apply IHEval. assumption. assumption.
  - inversion H1. subst. apply T_Cat. assumption. apply IHEval. assumption.
  - inversion H1. subst. apply T_Num.
  - inversion H1. subst. apply T_Len. apply IHEval. assumption.
  - inversion H1. subst. apply (T_Let _ _ t1).
    + apply IHEval. assumption.
    + assumption.
  - inversion H1. subst. apply (substitution Gamma x t e2 t1).
    all: assumption.
Qed.

(** Canonical Forms (In Harper's book) *)
Lemma canonical_forms : forall Gamma e t,
  Val e -> hastype Gamma e t -> (
    (t = TNum -> exists n, e = ENum n) /\
    (t = TStr -> exists s, e = EStr s)
  ).
Proof.
  intros Gamma e t H1.
  induction H1; intros; split; intros; subst.
  exists n. reflexivity.
  inversion H.
  inversion H.
  exists s. reflexivity.
Qed.

(** Well-typed programs cannot get stuck (In Harper's book) *)
Theorem progress : forall e t,
  hastype empty_ctx e t -> Val e \/ exists e', Eval e e'.
Proof.
  intros e t H.
  remember empty_ctx as Gamma.
  induction H; subst.
  - subst. discriminate H.
  - left. apply valStr.
  - left. apply valNum.
  - right.
    assert (IHhastype1 := IHhastype1 Logic.eq_refl).
    assert (IHhastype2 := IHhastype2 Logic.eq_refl).
    destruct IHhastype1; destruct IHhastype2.
    + apply (canonical_forms empty_ctx e1 TNum) in H1.
      apply (canonical_forms empty_ctx e2 TNum) in H2.
      destruct H1. destruct H2.
      assert (H1 := H1 Logic.eq_refl).
      assert (H2 := H2 Logic.eq_refl).
      destruct H1. destruct H2. subst.
      exists (ENum (x + x0)). constructor. reflexivity.
      assumption. assumption.
    + destruct H2. exists (EPlus e1 x). constructor; assumption.
    + destruct H1. exists (EPlus x e2). constructor; assumption.
    + destruct H1. exists (EPlus x e2). constructor; assumption.
  - right.
    assert (IHhastype1 := IHhastype1 Logic.eq_refl).
    assert (IHhastype2 := IHhastype2 Logic.eq_refl).
    destruct IHhastype1; destruct IHhastype2.
    + apply (canonical_forms empty_ctx e1 TNum) in H1.
      apply (canonical_forms empty_ctx e2 TNum) in H2.
      destruct H1. destruct H2.
      assert (H1 := H1 Logic.eq_refl).
      assert (H2 := H2 Logic.eq_refl).
      destruct H1. destruct H2. subst.
      exists (ENum (x * x0)). constructor. reflexivity.
      assumption. assumption.
    + destruct H2. exists (ETimes e1 x). constructor; assumption.
    + destruct H1. exists (ETimes x e2). constructor; assumption.
    + destruct H1. exists (ETimes x e2). constructor; assumption.
  - right.
    assert (IHhastype1 := IHhastype1 Logic.eq_refl).
    assert (IHhastype2 := IHhastype2 Logic.eq_refl).
    destruct IHhastype1; destruct IHhastype2.
    + apply (canonical_forms empty_ctx e1 TStr) in H1.
      apply (canonical_forms empty_ctx e2 TStr) in H2.
      destruct H1. destruct H2.
      assert (H3 := H3 Logic.eq_refl).
      assert (H4 := H4 Logic.eq_refl).
      destruct H3. destruct H4. subst.
      exists (EStr (append x x0)). constructor. reflexivity.
      assumption. assumption.
    + destruct H2. exists (ECat e1 x). constructor; assumption.
    + destruct H1. exists (ECat x e2). constructor; assumption.
    + destruct H1. exists (ECat x e2). constructor; assumption.
  - right.
    assert (IHhastype := IHhastype Logic.eq_refl).
    destruct IHhastype.
    + apply (canonical_forms empty_ctx e TStr) in H0.
      destruct H0.
      assert (H1 := H1 Logic.eq_refl).
      destruct H1. subst.
      exists (ENum (length x)). constructor. reflexivity.
      assumption.
    + destruct H0. exists (ELen x). constructor; assumption.
  - right.
    assert (IHhastype1 := IHhastype1 Logic.eq_refl).
    destruct IHhastype1.
    + exists (subst e1 x e2). constructor; assumption.
    + destruct H1. exists (ELet x0 x e2). constructor; assumption.
Qed.

(** Based on https://softwarefoundations.cis.upenn.edu/plf-current/StlcProp.html#lab244 *)
Theorem type_safety : forall e e' t,
  hastype empty_ctx e t -> EvalStar e e' -> Val e' \/ exists e'', Eval e' e''.
Proof.
  intros e e' t H1 H2. induction H2.
  - apply progress in H1. assumption.
  - apply IHEvalStar. apply (preservation _ _ _ _ H1 H).
Qed.

(** Proof of termination of well-typed programs *)
Theorem well_typed_programs_terminate : forall e t,
  hastype empty_ctx e t -> exists e', EvalBig e e'.
Proof.
  intro e. remember (subexprs_count e) as c.
  generalize dependent e.
  generalize dependent c.
  induction c using lt_wf_ind; intros.
  assert (T := progress e t0 H0).
  destruct T.
  - inversion H1; subst.
    exists (ENum n). constructor.
    exists (EStr s). constructor.
  - destruct H1.
    assert (T1 := preservation empty_ctx e t0 x H0 H1).
    assert (T2 := progress x t0 T1).
    remember (subexprs_count x) as c2.
    cut (c2 < c). intro C.
    assert (T3 := H c2 C x Heqc2 t0 T1).
    destruct T3 as [e' T3]. exists e'.
    apply eval_big_equiv_eval_star.
    apply eval_big_equiv_eval_star in T3.
    destruct T3 as [T3 T4]. split.
    apply (starN _ _ x); assumption.
    assumption.
    subst. apply eval_reduces. assumption.
Qed.
