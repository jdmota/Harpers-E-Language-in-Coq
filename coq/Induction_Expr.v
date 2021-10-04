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
From PFPL Require Import Lemmas_Same_Structure.

Lemma expr_pair_ind_simple :
  forall P : EExp -> EExp -> Prop,
  (forall x x', P (EId x) (EId x')) ->
  (forall e1 x e2 e1' x' e2',
    P e1 e1' -> P e2 e2' -> P (ELet e1 x e2) (ELet e1' x' e2')) ->
  (forall n n', P (ENum n) (ENum n')) ->
  (forall s s', P (EStr s) (EStr s')) ->
  (forall e1 e2 e1' e2',
    P e1 e1' -> P e2 e2' -> P (EPlus e1 e2) (EPlus e1' e2')) ->
  (forall e1 e2 e1' e2',
    P e1 e1' -> P e2 e2' -> P (ETimes e1 e2) (ETimes e1' e2')) ->
  (forall e1 e2 e1' e2',
    P e1 e1' -> P e2 e2' -> P (ECat e1 e2) (ECat e1' e2')) ->
  (forall e1 e1',
    P e1 e1' -> P (ELen e1) (ELen e1')) ->
  (forall e e',
    (match e, e' with
    | ENum _, ENum _ => False
    | EStr _, EStr _ => False
    | EId _, EId _ => False
    | EPlus _ _, EPlus _ _ => False
    | ETimes _ _, ETimes _ _ => False
    | ECat _ _, ECat _ _ => False
    | ELen _, ELen _ => False
    | ELet _ _ _, ELet _ _ _ => False
    | _, _ => True
    end) -> P e e') ->
  (forall e e', P e e').
Proof.
  intros P HId HLet HNum HStr HPlus HTimes HCat HLen HF.
  induction e.
  - induction e'.
    apply HNum.
    all: apply HF; trivial.
  - induction e'.
    apply HF; trivial.
    apply HStr.
    all: apply HF; trivial.
  - induction e'.
    apply HF; trivial.
    apply HF; trivial.
    apply HId.
    all: apply HF; trivial.
  - induction e'.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HPlus. apply IHe1. apply IHe2.
    all: apply HF; trivial.
  - induction e'.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HTimes. apply IHe1. apply IHe2.
    all: apply HF; trivial.
  - induction e'.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HCat. apply IHe1. apply IHe2.
    all: apply HF; trivial.
  - induction e'.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HLen. apply IHe.
    all: apply HF; trivial.
  - induction e'.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HF; trivial.
    apply HLet. apply IHe1. apply IHe2.
Qed.

Definition strengthen :=
  fun (P: EExp -> EExp -> Prop) (e e' : EExp) =>
    (forall e'' e''',
      same_structure e e'' ->
      same_structure e' e''' ->
      P e'' e'''
    ).

Lemma expr_pair_ind_same_structure :
  forall P : EExp -> EExp -> Prop,
  forall e e', strengthen P e e' -> P e e'.
Proof.
  intros. apply H.
  apply same_structure_refl.
  apply same_structure_refl.
Qed.

Definition strengthen_one :=
  fun (P: EExp -> Prop) (e : EExp) =>
    (forall e', same_structure e e' -> P e').

Lemma expr_ind_aux :
  forall P : EExp -> Prop,
  (forall x, strengthen_one P (EId x)) ->
  (forall e1 x e2,
    strengthen_one P e1 -> strengthen_one P e2 ->
    strengthen_one P (ELet e1 x e2)) ->
  (forall n, strengthen_one P (ENum n)) ->
  (forall s, strengthen_one P (EStr s)) ->
  (forall e1 e2,
    strengthen_one P e1 ->
    strengthen_one P e2 ->
    strengthen_one P (EPlus e1 e2)) ->
  (forall e1 e2,
    strengthen_one P e1 ->
    strengthen_one P e2 ->
    strengthen_one P (ETimes e1 e2)) ->
  (forall e1 e2,
    strengthen_one P e1 ->
    strengthen_one P e2 ->
    strengthen_one P (ECat e1 e2)) ->
  (forall e1,
    strengthen_one P e1 -> strengthen_one P (ELen e1)) ->
  (forall e, P e).
Proof.
  intros P HId HLet HNum HStr HPlus HTimes HCat HLen.
  assert (G : (forall e : EExp, strengthen_one P e) -> (forall e : EExp, P e)).
  intros. assert (H0 := H e). unfold strengthen_one in H0.
  assert (H1 := H0 e). apply H1. apply same_structure_refl.
  apply G. clear G.
  induction e.
  - apply HNum.
  - apply HStr.
  - apply HId.
  - apply HPlus. assumption. assumption.
  - apply HTimes. assumption. assumption.
  - apply HCat. assumption. assumption.
  - apply HLen. assumption.
  - apply HLet. assumption. assumption.
Qed.

Lemma strengthen_one_same_structure :
  forall (P : EExp -> Prop) e e',
    same_structure e e' ->
    strengthen_one P e ->
    strengthen_one P e'.
Proof.
  intros.
  unfold strengthen_one in H0.
  unfold strengthen_one.
  intros.
  apply H0. apply (same_structure_trans e e' e'0).
  assumption. assumption.
Qed.

Lemma expr_ind :
  forall P : EExp -> Prop,
  (forall x, P (EId x)) ->
  (forall e1 x e2,
    strengthen_one P e1 -> strengthen_one P e2 ->
    P (ELet e1 x e2)) ->
  (forall n, P (ENum n)) ->
  (forall s, P (EStr s)) ->
  (forall e1 e2,
    strengthen_one P e1 ->
    strengthen_one P e2 ->
    P (EPlus e1 e2)) ->
  (forall e1 e2,
    strengthen_one P e1 ->
    strengthen_one P e2 ->
    P (ETimes e1 e2)) ->
  (forall e1 e2,
    strengthen_one P e1 ->
    strengthen_one P e2 ->
    P (ECat e1 e2)) ->
  (forall e1,
    strengthen_one P e1 -> P (ELen e1)) ->
  (forall e, P e).
Proof.
  intros P HId HLet HNum HStr HPlus HTimes HCat HLen.
  apply expr_ind_aux.
  all: intros; unfold strengthen_one; intros.
  - inversion H; subst. apply HId.
  - inversion H1; subst. apply HLet.
    apply (strengthen_one_same_structure _ e1 e1').
    assumption. assumption.
    apply (strengthen_one_same_structure _ e2 e2').
    assumption. assumption.
  - inversion H; subst. apply HNum.
  - inversion H; subst. apply HStr.
  - inversion H1; subst. apply HPlus.
    apply (strengthen_one_same_structure _ e1 e1').
    assumption. assumption.
    apply (strengthen_one_same_structure _ e2 e2').
    assumption. assumption.
  - inversion H1; subst. apply HTimes.
    apply (strengthen_one_same_structure _ e1 e1').
    assumption. assumption.
    apply (strengthen_one_same_structure _ e2 e2').
    assumption. assumption.
  - inversion H1; subst. apply HCat.
    apply (strengthen_one_same_structure _ e1 e1').
    assumption. assumption.
    apply (strengthen_one_same_structure _ e2 e2').
    assumption. assumption.
  - inversion H0; subst. apply HLen.
    apply (strengthen_one_same_structure _ e1 e1').
    assumption. assumption.
Qed.

Lemma expr_pair_ind_aux :
  forall P : EExp -> EExp -> Prop,
  (forall x x', strengthen P (EId x) (EId x')) ->
  (forall e1 x e2 e1' x' e2',
    strengthen P e1 e1' -> strengthen P e2 e2' ->
    strengthen P (ELet e1 x e2) (ELet e1' x' e2')) ->
  (forall n n', strengthen P (ENum n) (ENum n')) ->
  (forall s s', strengthen P (EStr s) (EStr s')) ->
  (forall e1 e2 e1' e2',
    strengthen P e1 e1' ->
    strengthen P e2 e2' ->
    strengthen P (EPlus e1 e2) (EPlus e1' e2')) ->
  (forall e1 e2 e1' e2',
    strengthen P e1 e1' ->
    strengthen P e2 e2' ->
    strengthen P (ETimes e1 e2) (ETimes e1' e2')) ->
  (forall e1 e2 e1' e2',
    strengthen P e1 e1' ->
    strengthen P e2 e2' ->
    strengthen P (ECat e1 e2) (ECat e1' e2')) ->
  (forall e1 e1',
    strengthen P e1 e1' -> strengthen P (ELen e1) (ELen e1')) ->
  (forall e e',
    diff_constructor e e' -> strengthen P e e') ->
  (forall e e', P e e').
Proof.
  intros P HId HLet HNum HStr HPlus HTimes HCat HLen HF.
  intros e e'.
  apply expr_pair_ind_same_structure.
  induction e, e' using expr_pair_ind_simple.
  apply HId.
  apply HLet. assumption. assumption.
  apply HNum.
  apply HStr.
  apply HPlus. assumption. assumption.
  apply HTimes. assumption. assumption.
  apply HCat. assumption. assumption.
  apply HLen. assumption.
  apply HF. assumption.
Qed.

Lemma expr_pair_ind :
  forall P : EExp -> EExp -> Prop,
  (forall x x', P (EId x) (EId x')) ->
  (forall e1 x e2 e1' x' e2',
    strengthen P e1 e1' -> strengthen P e2 e2' ->
    P (ELet e1 x e2) (ELet e1' x' e2')) ->
  (forall n n', P (ENum n) (ENum n')) ->
  (forall s s', P (EStr s) (EStr s')) ->
  (forall e1 e2 e1' e2',
    strengthen P e1 e1' ->
    strengthen P e2 e2' ->
    P (EPlus e1 e2) (EPlus e1' e2')) ->
  (forall e1 e2 e1' e2',
    strengthen P e1 e1' ->
    strengthen P e2 e2' ->
    P (ETimes e1 e2) (ETimes e1' e2')) ->
  (forall e1 e2 e1' e2',
    strengthen P e1 e1' ->
    strengthen P e2 e2' ->
    P (ECat e1 e2) (ECat e1' e2')) ->
  (forall e1 e1',
    strengthen P e1 e1' -> P (ELen e1) (ELen e1')) ->
  (forall e e',
    diff_constructor e e' -> P e e') ->
  (forall e e', P e e').
Proof.
  intros P HId HLet HNum HStr HPlus HTimes HCat HLen HF.
  apply expr_pair_ind_aux.
  - intros. unfold strengthen. intros.
    inversion H. inversion H0. subst. apply HId.
  - intros. unfold strengthen. intros.
    inversion H1. inversion H2. subst.
    apply HLet.
    all:
      unfold strengthen in H;
      unfold strengthen in H0;
      unfold strengthen;
      intros.
    apply H.
    apply (same_structure_trans e1 e1'0 e'').
    assumption. assumption.
    apply (same_structure_trans e1' e1'1 e''').
    assumption. assumption.
    apply H0.
    apply (same_structure_trans e2 e2'0 e'').
    assumption. assumption.
    apply (same_structure_trans e2' e2'1 e''').
    assumption. assumption.
  - intros. unfold strengthen. intros.
    inversion H. inversion H0. subst. apply HNum.
  - intros. unfold strengthen. intros.
    inversion H. inversion H0. subst. apply HStr.
  - intros. unfold strengthen. intros.
    inversion H1. inversion H2. subst.
    apply HPlus.
    all:
      unfold strengthen in H;
      unfold strengthen in H0;
      unfold strengthen;
      intros.
    apply H.
    apply (same_structure_trans e1 e1'0 e'').
    assumption. assumption.
    apply (same_structure_trans e1' e1'1 e''').
    assumption. assumption.
    apply H0.
    apply (same_structure_trans e2 e2'0 e'').
    assumption. assumption.
    apply (same_structure_trans e2' e2'1 e''').
    assumption. assumption.
  - intros. unfold strengthen. intros.
    inversion H1. inversion H2. subst.
    apply HTimes.
    all:
      unfold strengthen in H;
      unfold strengthen in H0;
      unfold strengthen;
      intros.
    apply H.
    apply (same_structure_trans e1 e1'0 e'').
    assumption. assumption.
    apply (same_structure_trans e1' e1'1 e''').
    assumption. assumption.
    apply H0.
    apply (same_structure_trans e2 e2'0 e'').
    assumption. assumption.
    apply (same_structure_trans e2' e2'1 e''').
    assumption. assumption.
  - intros. unfold strengthen. intros.
    inversion H1. inversion H2. subst.
    apply HCat.
    all:
      unfold strengthen in H;
      unfold strengthen in H0;
      unfold strengthen;
      intros.
    apply H.
    apply (same_structure_trans e1 e1'0 e'').
    assumption. assumption.
    apply (same_structure_trans e1' e1'1 e''').
    assumption. assumption.
    apply H0.
    apply (same_structure_trans e2 e2'0 e'').
    assumption. assumption.
    apply (same_structure_trans e2' e2'1 e''').
    assumption. assumption.
  - intros. unfold strengthen. intros.
    inversion H0. inversion H1. subst.
    apply HLen.
    all:
      unfold strengthen in H;
      unfold strengthen;
      intros.
    apply H.
    apply (same_structure_trans e1 e1'0 e'').
    assumption. assumption.
    apply (same_structure_trans e1' e1'1 e''').
    assumption. assumption.
  - intros. unfold strengthen. intros.
    destruct e.
    all: try (apply same_structure_num in H0; destruct H0; subst).
    all: try (apply same_structure_str in H0; destruct H0; subst).
    all: try (apply same_structure_id in H0; destruct H0; subst).
    all: try (apply same_structure_plus in H0; destruct H0; destruct H0; subst).
    all: try (apply same_structure_times in H0; destruct H0; destruct H0; subst).
    all: try (apply same_structure_cat in H0; destruct H0; destruct H0; subst).
    all: try (apply same_structure_len in H0; destruct H0; subst).
    all: try (apply same_structure_let in H0; destruct H0; destruct H0; destruct H0; subst).
    all: destruct e'.
    all: simpl in H; try contradiction; clear H.
    all: try (apply same_structure_num in H1; destruct H1; subst; simpl; trivial).
    all: try (apply same_structure_str in H1; destruct H1; subst; simpl; trivial).
    all: try (apply same_structure_id in H1; destruct H1; subst; simpl; trivial).
    all: try (apply same_structure_plus in H1; destruct H1; destruct H; subst; simpl; trivial).
    all: try (apply same_structure_times in H1; destruct H1; destruct H; subst; simpl; trivial).
    all: try (apply same_structure_cat in H1; destruct H1; destruct H; subst; simpl; trivial).
    all: try (apply same_structure_len in H1; destruct H1; subst; simpl; trivial).
    all: try (apply same_structure_let in H1; destruct H1; destruct H; destruct H; subst; simpl; trivial).
    all: apply HF; simpl; auto.
Qed.
