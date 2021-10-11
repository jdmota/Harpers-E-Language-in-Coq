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
From PFPL Require Import Lemmas_FreshRename_AlphaEquiv.
From PFPL Require Import Lemmas_Rename_FreshRename.
From PFPL Require Import Lemmas_Subst.
From PFPL Require Import Lemmas_Rename_Subst.
From PFPL Require Import Theorems_AlphaEquiv.

(** Finality of values (In Harper's book) *)
Lemma finality_of_values : forall e,
  Val e /\ (exists e', Eval e e') -> False.
Proof.
  intros. destruct H.
  induction H; destruct H0; inversion H.
Qed.

(** Determinacy (In Harper's book) *)
Lemma determinacy : forall e e' e'',
  Eval e e' -> Eval e e'' -> e' = e''.
Proof.
  intros e e' e'' H1. generalize dependent e''.
  induction H1; intros e'' H2.
  - inversion H2; subst. reflexivity.
    inversion H4.
    inversion H5.
  - inversion H2; subst.
    inversion H1.
    apply IHEval in H4. subst. reflexivity.
    inversion H3; subst; inversion H1.
  - inversion H2; subst.
    inversion H1.
    inversion H; subst; inversion H5.
    apply IHEval in H6. subst. reflexivity.
  - inversion H2; subst. reflexivity.
    inversion H4.
    inversion H5.
  - inversion H2; subst.
    inversion H1.
    apply IHEval in H4. subst. reflexivity.
    inversion H3; subst; inversion H1.
  - inversion H2; subst.
    inversion H1.
    inversion H; subst; inversion H5.
    apply IHEval in H6. subst. reflexivity.
  - inversion H2; subst. reflexivity.
    inversion H4.
    inversion H5.
  - inversion H2; subst.
    inversion H1.
    apply IHEval in H4. subst. reflexivity.
    inversion H3; subst; inversion H1.
  - inversion H2; subst.
    inversion H1.
    inversion H; subst; inversion H5.
    apply IHEval in H6. subst. reflexivity.
  - inversion H2; subst. reflexivity.
    inversion H1.
  - inversion H2; subst.
    inversion H1.
    apply IHEval in H0. subst. reflexivity.
  - inversion H2; subst.
    apply IHEval in H5. subst. reflexivity.
    inversion H5; subst; inversion H1.
  - inversion H2; subst.
    inversion H; subst; inversion H5.
    reflexivity.
Qed.

(** A value does not evaluate *)
Lemma values_do_not_evaluate_1 : forall e,
  Val e -> eval e = None.
Proof.
  destruct e; intro.
  all: inversion H.
  all: subst.
  all: simpl.
  all: reflexivity.
Qed.

(** An evaluation is possible only to non-values *)
Lemma values_do_not_evaluate_2 : forall e e',
  eval e = Some e' -> is_val e = false.
Proof.
  intros. case_eq (is_val e); intro.
  - rewrite <- val_rel_equiv_is_val in H0.
    apply values_do_not_evaluate_1 in H0.
    rewrite H in H0. discriminate.
  - reflexivity.
Qed.

(** Correcteness of the small-step implementation (part 1) *)
Lemma eval_correct_1 : forall e e',
  eval e = Some e' -> Eval e e'.
Proof.
  induction e; intros; simpl in H.
  - discriminate.
  - discriminate.
  - discriminate.
  - case_eq (eval e1); intros; rewrite H0 in H.
    + assert (T := values_do_not_evaluate_2 e1 e H0).
      rewrite T in H.
      destruct e1; simpl in T; try discriminate.
      all: inversion H; subst.
      all: apply evalPlus2; apply IHe1; assumption.
    + case_eq (eval e2); intros; rewrite H1 in H.
      * case_eq (is_val e1); intros; rewrite H2 in H.
        {
          rewrite <- val_rel_equiv_is_val in H2.
          cut (e' = (EPlus e1 e)). intro. subst e'.
          apply evalPlus3. assumption.
          apply IHe2. assumption.
          assert (T := values_do_not_evaluate_2 e2 e H1).
          destruct e2; simpl in T; try discriminate.
          all: destruct e1; inversion H; reflexivity.
        }
        {
          destruct e1; simpl in H2; discriminate.
        }
      * destruct e1; unfold is_val in H.
        all: destruct e2; try discriminate.
        inversion H. subst. apply evalPlus1. reflexivity.
  - case_eq (eval e1); intros; rewrite H0 in H.
    + assert (T := values_do_not_evaluate_2 e1 e H0).
      rewrite T in H.
      destruct e1; simpl in T; try discriminate.
      all: inversion H; subst.
      all: apply evalTimes2; apply IHe1; assumption.
    + case_eq (eval e2); intros; rewrite H1 in H.
      * case_eq (is_val e1); intros; rewrite H2 in H.
        {
          rewrite <- val_rel_equiv_is_val in H2.
          cut (e' = (ETimes e1 e)). intro. subst e'.
          apply evalTimes3. assumption.
          apply IHe2. assumption.
          assert (T := values_do_not_evaluate_2 e2 e H1).
          destruct e2; simpl in T; try discriminate.
          all: destruct e1; inversion H; reflexivity.
        }
        {
          destruct e1; simpl in H2; discriminate.
        }
      * destruct e1; unfold is_val in H.
        all: destruct e2; try discriminate.
        inversion H. subst. apply evalTimes1. reflexivity.
  - case_eq (eval e1); intros; rewrite H0 in H.
    + assert (T := values_do_not_evaluate_2 e1 e H0).
      rewrite T in H.
      destruct e1; simpl in T; try discriminate.
      all: inversion H; subst.
      all: apply evalCat2; apply IHe1; assumption.
    + case_eq (eval e2); intros; rewrite H1 in H.
      * case_eq (is_val e1); intros; rewrite H2 in H.
        {
          rewrite <- val_rel_equiv_is_val in H2.
          cut (e' = (ECat e1 e)). intro. subst e'.
          apply evalCat3. assumption.
          apply IHe2. assumption.
          assert (T := values_do_not_evaluate_2 e2 e H1).
          destruct e2; simpl in T; try discriminate.
          all: destruct e1; inversion H; reflexivity.
        }
        {
          destruct e1; simpl in H2; discriminate.
        }
      * destruct e1; unfold is_val in H.
        all: destruct e2; try discriminate.
        inversion H. subst. apply evalCat1. reflexivity.
  - case_eq (eval e); intros; rewrite H0 in H.
    + destruct e.
      all: inversion H; subst.
      all: try (simpl in H; discriminate).
      all: apply evalLen2; apply IHe; assumption.
    + destruct e; try discriminate.
      inversion H. subst.
      apply evalLen1. reflexivity.
  - case_eq (is_val e1); intros; rewrite H0 in H.
    + rewrite <- val_rel_equiv_is_val in H0.
      inversion H. subst.
      apply evalLet2; assumption.
    + case_eq (eval e1); intros; rewrite H1 in H.
      inversion H. subst.
      apply evalLet1. apply IHe1. assumption.
      discriminate.
Qed.

(** Correcteness of the small-step implementation (part 2) *)
Lemma eval_correct_2 : forall e e',
  Eval e e' -> eval e = Some e'.
Proof.
  intros e e' H. induction H; subst; simpl.
  - reflexivity.
  - rewrite IHEval.
    rewrite (values_do_not_evaluate_2 e1 e1' IHEval).
    destruct e1; try (simpl in IHEval; discriminate).
    all: reflexivity.
  - rewrite IHEval.
    rewrite val_rel_equiv_is_val in H. rewrite H.
    assert (T := values_do_not_evaluate_2 e2 e2' IHEval).
    destruct e2; try (simpl in T; discriminate).
    all: destruct e1; reflexivity.
  - reflexivity.
  - rewrite IHEval.
    rewrite (values_do_not_evaluate_2 e1 e1' IHEval).
    destruct e1; try (simpl in IHEval; discriminate).
    all: reflexivity.
  - rewrite IHEval.
    rewrite val_rel_equiv_is_val in H. rewrite H.
    assert (T := values_do_not_evaluate_2 e2 e2' IHEval).
    destruct e2; try (simpl in T; discriminate).
    all: destruct e1; reflexivity.
  - reflexivity.
  - rewrite IHEval.
    rewrite (values_do_not_evaluate_2 e1 e1' IHEval).
    destruct e1; try (simpl in IHEval; discriminate).
    all: reflexivity.
  - rewrite IHEval.
    rewrite val_rel_equiv_is_val in H. rewrite H.
    assert (T := values_do_not_evaluate_2 e2 e2' IHEval).
    destruct e2; try (simpl in T; discriminate).
    all: destruct e1; reflexivity.
  - reflexivity.
  - rewrite IHEval.
    destruct e1; try (simpl in IHEval; discriminate).
    all: reflexivity.
  - rewrite IHEval.
    rewrite (values_do_not_evaluate_2 e1 e1' IHEval).
    reflexivity.
  - rewrite val_rel_equiv_is_val in H. rewrite H.
    reflexivity.
Qed.

(** Correcteness of the small-step implementation *)
Theorem eval_correct : forall e e',
  Eval e e' <-> eval e = Some e'.
Proof.
  intros. split.
  apply eval_correct_2.
  apply eval_correct_1.
Qed.

(** Substitution is able to reduce the number of subexpressions (auxiliary) *)
Lemma subst'_reduces_aux : forall e1 x e2 e2',
  subexprs_count e1 = 1 ->
  subexprs_count e2 = subexprs_count e2' ->
  subexprs_count (subst' e1 x e2) = subexprs_count e2'.
Proof.
  intros e1 x. induction e2; intros; simpl.
  - simpl in H0. assumption.
  - simpl in H0. assumption.
  - simpl in H0. destruct (x =? x0); simpl.
    rewrite H. all: assumption.
  - rewrite <- H0. simpl.
    assert(IHe2_1 := IHe2_1 e2_1 H). assert(IHe2_2 := IHe2_2 e2_2 H).
    rewrite IHe2_1. rewrite IHe2_2. all: reflexivity.
  - rewrite <- H0. simpl.
    assert(IHe2_1 := IHe2_1 e2_1 H). assert(IHe2_2 := IHe2_2 e2_2 H).
    rewrite IHe2_1. rewrite IHe2_2. all: reflexivity.
  - rewrite <- H0. simpl.
    assert(IHe2_1 := IHe2_1 e2_1 H). assert(IHe2_2 := IHe2_2 e2_2 H).
    rewrite IHe2_1. rewrite IHe2_2. all: reflexivity.
  - rewrite <- H0. simpl.
    assert(IHe2 := IHe2 e2 H).
    rewrite IHe2. all: reflexivity.
  - rewrite <- H0. simpl.
    assert(IHe2_1 := IHe2_1 e2_1 H). assert(IHe2_2 := IHe2_2 e2_2 H).
    destruct (x =? x0); simpl; rewrite IHe2_1;
    try rewrite IHe2_2; reflexivity.
Qed.

(** Substitution is able to reduce the number of subexpressions *)
Lemma subst'_reduces : forall e1 x e2 e2',
  subexprs_count e1 = 1 ->
  subexprs_count e2 = subexprs_count e2' ->
  subexprs_count (subst' e1 x e2) < subexprs_count (ELet e1 x e2').
Proof.
  intros. rewrite (subst'_reduces_aux _ _ _ e2').
  simpl. apply le_lt_n_Sm. apply le_plus_r.
  assumption. assumption.
Qed.

(** Fresh renamings keep the number of subexpressions *)
Lemma fresh_rename_keeps_count : forall e bv o,
  subexprs_count e = subexprs_count (fresh_rename e bv o).
Proof.
  induction e; intros; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (bv x); reflexivity.
  - assert(IHe1 := IHe1 bv o). assert(IHe2 := IHe2 bv o).
    rewrite IHe1. rewrite IHe2. reflexivity.
  - assert(IHe1 := IHe1 bv o). assert(IHe2 := IHe2 bv o).
    rewrite IHe1. rewrite IHe2. reflexivity.
  - assert(IHe1 := IHe1 bv o). assert(IHe2 := IHe2 bv o).
    rewrite IHe1. rewrite IHe2. reflexivity.
  - assert(IHe := IHe bv o).
    rewrite IHe. reflexivity.
  - assert(IHe1 := IHe1 bv o). assert(IHe2 := IHe2 (updateSet bv x) o).
    rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

(** Substitution with capture-avoidance is able to reduce the number of subexpressions *)
Lemma subst_reduces : forall e1 x e2,
  subexprs_count e1 = 1 ->
  subexprs_count (subst e1 x e2) < subexprs_count (ELet e1 x e2).
Proof.
  intros. unfold subst.
  apply subst'_reduces. assumption.
  symmetry. apply fresh_rename_keeps_count.
Qed.

(** Evaluation produces an expression with less subexpressions *)
Lemma eval_reduces : forall e e',
  Eval e e' -> subexprs_count e' < subexprs_count e.
Proof.
  intros e e' H. induction H; simpl; try lia.
  inversion H; subst; simpl.
  assert (T := subst_reduces (ENum n) x e2).
  simpl in T. assert (T := T Logic.eq_refl). assumption.
  assert (T := subst_reduces (EStr s) x e2).
  simpl in T. assert (T := T Logic.eq_refl). assumption.
Qed.

(** Evaluation function produces an expression with less subexpressions *)
Corollary eval_func_reduces : forall e e',
  eval e = Some e' -> subexprs_count e' < subexprs_count e.
Proof.
  intros. apply eval_correct in H.
  apply eval_reduces. assumption.
Qed.

(** Big-step implementation *)
Function eval_big (e : EExp) {measure subexprs_count e} : option EExp :=
  match e with
  | ENum n => Some (ENum n)
  | EStr s => Some (EStr s)
  | _ =>
    match eval e with
    | Some e' => eval_big e'
    | None => None
    end
  end.
Proof.
all: intros; subst.
inversion teq0.
all: apply eval_func_reduces; assumption.
Qed.

(** Big-step implementation returns some value or none *)
Lemma eval_big_returns_value_or_none : forall e e',
  eval_big e = Some e' -> Val e'.
Proof.
  intros e e'.
  apply eval_big_ind; intros; subst.
  inversion H; subst. constructor.
  inversion H; subst. constructor.
  apply H. assumption.
  discriminate.
Qed.

(** Big-step evaluation returns a value *)
Lemma eval_big_gives_value : forall e e',
  EvalBig e e' -> Val e'.
Proof.
  intros. induction H.
  all: try constructor.
  assumption.
Qed.

(** Star evaluation to n-times evaluation (In Harper's book) *)
Lemma EvalStarToEvalN : forall e e',
  EvalStar e e' -> exists n, EvalN e e' n.
Proof.
  intros. induction H.
  - exists 0. apply eval0.
  - destruct IHEvalStar. exists (S x).
    apply (evalN _ e'' e'); assumption.
Qed.

(** N-times evaluation to star evaluation (In Harper's book) *)
Lemma EvalNToEvalStar : forall e e',
  (exists n, EvalN e e' n) -> EvalStar e e'.
Proof.
  intros. destruct H. induction H.
  - constructor.
  - apply (starN _ _ e'); assumption.
Qed.

(** The big-step evaluation is deterministic *)
Lemma eval_big_deterministic : forall e e' e'',
  EvalBig e e' -> EvalBig e e'' -> e' = e''.
Proof.
  intros e e' e'' H. generalize dependent e''.
  induction H; subst; intros.
  - inversion H; subst. reflexivity.
  - inversion H; subst. reflexivity.
  - inversion H1; subst.
    assert (IHEvalBig1 := IHEvalBig1 (ENum n0) H4).
    assert (IHEvalBig2 := IHEvalBig2 (ENum n3) H6).
    inversion IHEvalBig1. inversion IHEvalBig2. subst. reflexivity.
  - inversion H1; subst.
    assert (IHEvalBig1 := IHEvalBig1 (ENum n0) H4).
    assert (IHEvalBig2 := IHEvalBig2 (ENum n3) H6).
    inversion IHEvalBig1. inversion IHEvalBig2. subst. reflexivity.
  - inversion H1; subst.
    assert (IHEvalBig1 := IHEvalBig1 (EStr s0) H4).
    assert (IHEvalBig2 := IHEvalBig2 (EStr s3) H6).
    inversion IHEvalBig1. inversion IHEvalBig2. subst. reflexivity.
  - inversion H0; subst.
    assert (IHEvalBig := IHEvalBig (EStr s0) H2).
    inversion IHEvalBig. subst. reflexivity.
  - inversion H1; subst.
    assert (IHEvalBig1 := IHEvalBig1 e1'0 H6). subst.
    apply IHEvalBig2. assumption.
Qed.

(** Split [EPlus] evaluation (part 1) *)
Lemma plus_seq : forall n e1 e2 x,
  (EvalN (EPlus e1 e2) (ENum x) n) ->
  (exists x1 x2 n0 n1,
    EvalN e1 (ENum x1) n0 /\ EvalN e2 (ENum x2) n1 /\ x = x1 + x2 /\ n = 1 + n0 + n1
  ).
Proof.
  induction n; intros; inversion H; subst.
  inversion H1; subst.
  - inversion H4; subst.
    exists n1. exists n2.
    exists 0. exists 0. repeat split.
    apply eval0.
    apply eval0.
    inversion H0.
  - apply IHn in H4.
    destruct H4 as [x1 [x2 [n0 [n1 [H4 [H4' [H4'' H4''']]]]]]].
    exists x1. exists x2. exists (S n0). exists n1.
    repeat split.
    apply (evalN _ e1'); assumption.
    assumption. assumption.
    simpl. f_equal. simpl in H4'''. assumption.
  - apply IHn in H4.
    destruct H4 as [x1 [x2 [n0 [n1 [H4 [H4' [H4'' H4''']]]]]]].
    exists x1. exists x2. exists n0. exists (S n1).
    repeat split.
    assumption. apply (evalN _ e2'); assumption.
    assumption.
    simpl. f_equal. simpl in H4'''.
    rewrite add_comm. simpl. rewrite add_comm. assumption.
Qed.

(** Split [ETimes] evaluation (part 1) *)
Lemma times_seq : forall n e1 e2 x,
  (EvalN (ETimes e1 e2) (ENum x) n) ->
  (exists x1 x2 n0 n1,
    EvalN e1 (ENum x1) n0 /\ EvalN e2 (ENum x2) n1 /\ x = x1 * x2 /\ n = 1 + n0 + n1
  ).
Proof.
  induction n; intros; inversion H; subst.
  inversion H1; subst.
  - inversion H4; subst.
    exists n1. exists n2.
    exists 0. exists 0. repeat split.
    apply eval0.
    apply eval0.
    inversion H0.
  - apply IHn in H4.
    destruct H4 as [x1 [x2 [n0 [n1 [H4 [H4' [H4'' H4''']]]]]]].
    exists x1. exists x2. exists (S n0). exists n1.
    repeat split.
    apply (evalN _ e1'); assumption.
    assumption. assumption.
    simpl. f_equal. simpl in H4'''. assumption.
  - apply IHn in H4.
    destruct H4 as [x1 [x2 [n0 [n1 [H4 [H4' [H4'' H4''']]]]]]].
    exists x1. exists x2. exists n0. exists (S n1).
    repeat split.
    assumption. apply (evalN _ e2'); assumption.
    assumption.
    simpl. f_equal. simpl in H4'''.
    rewrite add_comm. simpl. rewrite add_comm. assumption.
Qed.

(** Split [ECat] evaluation (part 1) *)
Lemma cat_seq : forall n e1 e2 x,
  (EvalN (ECat e1 e2) (EStr x) n) ->
  (exists x1 x2 n0 n1,
    EvalN e1 (EStr x1) n0 /\ EvalN e2 (EStr x2) n1 /\ x = append x1 x2 /\ n = 1 + n0 + n1
  ).
Proof.
  induction n; intros; inversion H; subst.
  inversion H1; subst.
  - inversion H4; subst.
    exists s1. exists s2.
    exists 0. exists 0. repeat split.
    apply eval0.
    apply eval0.
    inversion H0.
  - apply IHn in H4.
    destruct H4 as [x1 [x2 [n0 [n1 [H4 [H4' [H4'' H4''']]]]]]].
    exists x1. exists x2. exists (S n0). exists n1.
    repeat split.
    apply (evalN _ e1'); assumption.
    assumption. assumption.
    simpl. f_equal. simpl in H4'''. assumption.
  - apply IHn in H4.
    destruct H4 as [x1 [x2 [n0 [n1 [H4 [H4' [H4'' H4''']]]]]]].
    exists x1. exists x2. exists n0. exists (S n1).
    repeat split.
    assumption. apply (evalN _ e2'); assumption.
    assumption.
    simpl. f_equal. simpl in H4'''.
    rewrite add_comm. simpl. rewrite add_comm. assumption.
Qed.

(** Split [ELen] evaluation (part 1) *)
Lemma len_seq : forall n e1 x,
  (EvalN (ELen e1) (ENum x) n) ->
  (exists x1 n0,
    EvalN e1 (EStr x1) n0 /\ x = length x1 /\ n = 1 + n0
  ).
Proof.
  induction n; intros; inversion H; subst.
  inversion H1; subst.
  - exists s1. exists 0.
    inversion H4; subst.
    repeat split. constructor.
    inversion H0.
  - apply IHn in H4.
    destruct H4 as [x1 [n0 [H4 [H4' H4'']]]].
    exists x1. exists (S n0).
    repeat split.
    apply (evalN _ e1'); assumption.
    assumption. lia.
Qed.

(** Split [ELet] evaluation (part 1) *)
Lemma let_seq : forall n e1 x e2 e',
  Val e' ->
  (EvalN (ELet e1 x e2) e' n) ->
  (exists e1' n0 n1,
    Val e1' /\ EvalN e1 e1' n0 /\ EvalN (subst e1' x e2) e' n1 /\ n = 1 + n0 + n1
  ).
Proof.
  induction n; intros; inversion H; subst;
  inversion H0; subst.
  - inversion H5; subst.
    * inversion H2; subst.
      exists e1. exists 0. exists 0.
      repeat split. assumption. constructor. constructor.
    * inversion H2; subst.
      apply IHn in H5.
      destruct H5 as [e1'0 [n2 [n3 [H5 [H5' [H5'' H5''']]]]]].
      exists e1'0. exists (S n2). exists n3. repeat split.
      assumption. apply (evalN _ e1'); assumption.
      assumption. lia. assumption.
      exists e1. exists 0. exists (S n1). repeat split.
      assumption. constructor. assumption.
  - inversion H5; subst.
    * inversion H2; subst.
      exists e1. exists 0. exists 0.
      repeat split. assumption. constructor. constructor.
    * inversion H2; subst.
      apply IHn in H5.
      destruct H5 as [e1'0 [n2 [n3 [H5 [H5' [H5'' H5''']]]]]].
      exists e1'0. exists (S n2). exists n3. repeat split.
      assumption. apply (evalN _ e1'); assumption.
      assumption. lia. assumption.
      exists e1. exists 0. exists (S n0). repeat split.
      assumption. constructor. assumption.
Qed.

(** Equivalence of the small-step and big-step semantics (part 1) *)
Lemma eval_big_equiv_eval_star_1 : forall e e',
  EvalStar e e' /\ Val e' -> EvalBig e e'.
Proof.
  intros. destruct H. apply EvalStarToEvalN in H. destruct H.
  generalize dependent e'. generalize dependent e.
  induction x using lt_wf_ind; intros.
  inversion H0; subst.
  - inversion H1; subst.
    apply evalBigNum. apply evalBigStr.
  - assert (H4 := H3). apply H in H3. inversion H2; subst.
    + inversion H3; subst. apply evalBigPlus; apply evalBigNum.
    + inversion H3; subst. apply evalBigPlus; [| assumption].
      apply plus_seq in H4.
      destruct H4 as [x1 [x2 [n0 [n3 [H4 [H4' [H4'' H4''']]]]]]].
      assert (T1 := H4). apply H in T1.
      assert (T2 := eval_big_deterministic e1' (ENum x1) (ENum n1) T1 H8).
      inversion T2. subst x1. clear T1 T2. subst n.
      apply (H (S n0)). lia.
      apply (evalN _ e1'); assumption. constructor.
      lia. constructor.
    + inversion H3; subst. apply evalBigPlus; [assumption |].
      apply plus_seq in H4.
      destruct H4 as [x1 [x2 [n0 [n3 [H4 [H4' [H4'' H4''']]]]]]].
      assert (T1 := H4'). apply H in T1.
      assert (T2 := eval_big_deterministic e2' (ENum x2) (ENum n2) T1 H11).
      inversion T2. subst x2. clear T1 T2. subst n.
      apply (H (S n3)). lia.
      apply (evalN _ e2'); assumption. constructor.
      lia. constructor.
    + inversion H3; subst. apply evalBigTimes; apply evalBigNum.
    + inversion H3; subst. apply evalBigTimes; [| assumption].
      apply times_seq in H4.
      destruct H4 as [x1 [x2 [n0 [n3 [H4 [H4' [H4'' H4''']]]]]]].
      assert (T1 := H4). apply H in T1.
      assert (T2 := eval_big_deterministic e1' (ENum x1) (ENum n1) T1 H8).
      inversion T2. subst x1. clear T1 T2. subst n.
      apply (H (S n0)). lia.
      apply (evalN _ e1'); assumption. constructor.
      lia. constructor.
    + inversion H3; subst. apply evalBigTimes; [assumption |].
      apply times_seq in H4.
      destruct H4 as [x1 [x2 [n0 [n3 [H4 [H4' [H4'' H4''']]]]]]].
      assert (T1 := H4'). apply H in T1.
      assert (T2 := eval_big_deterministic e2' (ENum x2) (ENum n2) T1 H11).
      inversion T2. subst x2. clear T1 T2. subst n.
      apply (H (S n3)). lia.
      apply (evalN _ e2'); assumption. constructor.
      lia. constructor.
    + inversion H3; subst. apply evalBigCat; apply evalBigStr.
    + inversion H3; subst. apply evalBigCat; [| assumption].
      apply cat_seq in H4.
      destruct H4 as [x1 [x2 [n0 [n3 [H4 [H4' [H4'' H4''']]]]]]].
      assert (T1 := H4). apply H in T1.
      assert (T2 := eval_big_deterministic e1' (EStr x1) (EStr s1) T1 H8).
      inversion T2. subst x1. clear T1 T2. subst n.
      apply (H (S n0)). lia.
      apply (evalN _ e1'); assumption. constructor.
      lia. constructor.
    + inversion H3; subst. apply evalBigCat; [assumption |].
      apply cat_seq in H4.
      destruct H4 as [x1 [x2 [n0 [n3 [H4 [H4' [H4'' H4''']]]]]]].
      assert (T1 := H4'). apply H in T1.
      assert (T2 := eval_big_deterministic e2' (EStr x2) (EStr s2) T1 H11).
      inversion T2. subst x2. clear T1 T2. subst n.
      apply (H (S n3)). lia.
      apply (evalN _ e2'); assumption. constructor.
      lia. constructor.
    + inversion H3; subst. apply evalBigLen; apply evalBigStr.
    + inversion H3; subst. apply evalBigLen.
      apply len_seq in H4.
      destruct H4 as [x1 [n0 [H4 [H4' H4'']]]].
      assert (T1 := H4). apply H in T1.
      assert (T2 := eval_big_deterministic e1' (EStr x1) (EStr s1) T1 H7).
      inversion T2. subst x1. clear T1 T2. subst n.
      apply (H (S n0)). lia.
      apply (evalN _ e1'); assumption. constructor.
      lia. constructor.
    + inversion H3; subst. apply (evalBigLet _ _ _ e1'0); [| assumption].
      apply let_seq in H4.
      destruct H4 as [e1'1 [n0 [n1 [H4 [H4' [H4'' H4''']]]]]].
      assert (T1 := H4'). apply H in T1.
      assert (T2 := eval_big_deterministic e1' e1'0 e1'1 H10 T1).
      subst e1'1. clear T1.
      apply (H (S n0)). lia.
      apply (evalN _ e1'); assumption. assumption.
      lia. assumption. assumption.
    + apply (evalBigLet e1 e2 x e1 e').
      inversion H5; subst; constructor.
      assumption.
    + lia.
    + assumption.
Qed.

(** Split [EPlus] evaluation (part 2) *)
Lemma plus_seq_2 : forall n1 n2 e1 x1 e2 x2,
  EvalN e1 (ENum x1) n1 ->
  EvalN e2 (ENum x2) n2 ->
  EvalN (EPlus e1 e2) (ENum (x1 + x2)) (1 + n1 + n2).
Proof.
  induction n1; induction n2; intros; simpl.
  - inversion H; subst. inversion H0; subst.
    apply (evalN _ (ENum (x1 + x2))).
    constructor. reflexivity.
    constructor.
  - inversion H; subst. inversion H0; subst.
    apply (IHn2 (ENum x1) x1) in H5. simpl in H5.
    apply (evalN _ (EPlus (ENum x1) e')).
    constructor. constructor. assumption.
    assumption. constructor.
  - inversion H; subst. inversion H0; subst.
    apply (IHn1 0 e' x1 (ENum x2) x2) in H5. simpl in H5.
    apply (evalN _ (EPlus e' (ENum x2))).
    constructor. assumption. assumption. assumption.
  - inversion H; subst.
    apply (IHn1 (S n2) e' x1 e2 x2) in H5. simpl in H5.
    apply (evalN _ (EPlus e' e2)).
    constructor. assumption. assumption. assumption.
Qed.

(** Split [ETimes] evaluation (part 2) *)
Lemma times_seq_2 : forall n1 n2 e1 x1 e2 x2,
  EvalN e1 (ENum x1) n1 ->
  EvalN e2 (ENum x2) n2 ->
  EvalN (ETimes e1 e2) (ENum (x1 * x2)) (1 + n1 + n2).
Proof.
  induction n1; induction n2; intros; simpl.
  - inversion H; subst. inversion H0; subst.
    apply (evalN _ (ENum (x1 * x2))).
    constructor. reflexivity.
    constructor.
  - inversion H; subst. inversion H0; subst.
    apply (IHn2 (ENum x1) x1) in H5. simpl in H5.
    apply (evalN _ (ETimes (ENum x1) e')).
    constructor. constructor. assumption.
    assumption. constructor.
  - inversion H; subst. inversion H0; subst.
    apply (IHn1 0 e' x1 (ENum x2) x2) in H5. simpl in H5.
    apply (evalN _ (ETimes e' (ENum x2))).
    constructor. assumption. assumption. assumption.
  - inversion H; subst.
    apply (IHn1 (S n2) e' x1 e2 x2) in H5. simpl in H5.
    apply (evalN _ (ETimes e' e2)).
    constructor. assumption. assumption. assumption.
Qed.

(** Split [ECat] evaluation (part 2) *)
Lemma cat_seq_2 : forall n1 n2 e1 x1 e2 x2,
  EvalN e1 (EStr x1) n1 ->
  EvalN e2 (EStr x2) n2 ->
  EvalN (ECat e1 e2) (EStr (append x1 x2)) (1 + n1 + n2).
Proof.
  induction n1; induction n2; intros; simpl.
  - inversion H; subst. inversion H0; subst.
    apply (evalN _ (EStr (append x1 x2))).
    constructor. reflexivity.
    constructor.
  - inversion H; subst. inversion H0; subst.
    apply (IHn2 (EStr x1) x1) in H5. simpl in H5.
    apply (evalN _ (ECat (EStr x1) e')).
    constructor. constructor. assumption.
    assumption. constructor.
  - inversion H; subst. inversion H0; subst.
    apply (IHn1 0 e' x1 (EStr x2) x2) in H5. simpl in H5.
    apply (evalN _ (ECat e' (EStr x2))).
    constructor. assumption. assumption. assumption.
  - inversion H; subst.
    apply (IHn1 (S n2) e' x1 e2 x2) in H5. simpl in H5.
    apply (evalN _ (ECat e' e2)).
    constructor. assumption. assumption. assumption.
Qed.

(** Split [ELen] evaluation (part 2) *)
Lemma len_seq_2 : forall n1 e1 x1,
  EvalN e1 (EStr x1) n1 ->
  EvalN (ELen e1) (ENum (length x1)) (1 + n1).
Proof.
  induction n1; intros; simpl.
  - inversion H; subst.
    apply (evalN _ (ENum (length x1))).
    constructor. reflexivity.
    constructor.
  - inversion H; subst.
    apply (IHn1 e' x1) in H4. simpl in H4.
    apply (evalN _ (ELen e')).
    constructor. assumption. assumption.
Qed.

(** Split [ELet] evaluation (part 2) *)
Lemma let_seq_2 : forall n1 n2 e1 x e2 e1' e2',
  Val e1' ->
  Val e2' ->
  EvalN e1 e1' n1 ->
  EvalN (subst e1' x e2) e2' n2 ->
  EvalN (ELet e1 x e2) e2' (1 + n1 + n2).
Proof.
  induction n1; induction n2; intros; simpl.
  - inversion H1; subst.
    apply (evalN _ (subst e1' x e2)).
    constructor. assumption. assumption.
  - inversion H1; subst.
    apply (evalN _ (subst e1' x e2)).
    constructor. assumption. assumption.
  - inversion H1; subst. inversion H2; subst.
    apply (IHn1 0 e' x e2 e1' (subst e1' x e2)) in H2. simpl in H2.
    apply (evalN _ (ELet e' x e2)).
    constructor. assumption. assumption.
    assumption. assumption. assumption.
  - inversion H1; subst.
    apply (IHn1 (S n2) e' x e2 e1' e2') in H7. simpl in H7.
    apply (evalN _ (ELet e' x e2)).
    constructor. all: assumption.
Qed.

(** Equivalence of the small-step and big-step semantics (part 2) *)
Lemma eval_big_equiv_eval_star_2 : forall e e',
  EvalBig e e' -> EvalStar e e' /\ Val e'.
Proof.
  intros. split. apply EvalNToEvalStar.
  induction H.
  - exists 0. constructor.
  - exists 0. constructor.
  - destruct IHEvalBig1. destruct IHEvalBig2.
    exists (1 + x + x0).
    apply plus_seq_2; assumption.
  - destruct IHEvalBig1. destruct IHEvalBig2.
    exists (1 + x + x0).
    apply times_seq_2; assumption.
  - destruct IHEvalBig1. destruct IHEvalBig2.
    exists (1 + x + x0).
    apply cat_seq_2; assumption.
  - destruct IHEvalBig.
    exists (1 + x).
    apply len_seq_2; assumption.
  - destruct IHEvalBig1. destruct IHEvalBig2.
    exists (1 + x0 + x1).
    apply (let_seq_2 _ _ _ _ _ e1').
    apply (eval_big_gives_value e1); assumption.
    apply (eval_big_gives_value (subst e1' x e2)); assumption.
    all: assumption.
  - apply (eval_big_gives_value e); assumption.
Qed.

(** Equivalence of the small-step and big-step semantics *)
Theorem eval_big_equiv_eval_star : forall e e',
  EvalBig e e' <-> EvalStar e e' /\ Val e'.
Proof.
  intros. split.
  apply eval_big_equiv_eval_star_2.
  apply eval_big_equiv_eval_star_1.
Qed.

(** Correcteness of the big-step implementation (part 1) *)
Lemma eval_big_correct_1 : forall e e',
  EvalBig e e' -> eval_big e = Some e'.
Proof.
  intros. apply eval_big_equiv_eval_star in H. destruct H.
  apply EvalStarToEvalN in H. destruct H.
  generalize dependent e'. generalize dependent e.
  induction x; intros.
  - inversion H; subst. inversion H0; subst.
    rewrite eval_big_equation; reflexivity.
    rewrite eval_big_equation; reflexivity.
  - inversion H; subst. assert (H2' := H2).
    apply eval_correct in H2'.
    rewrite eval_big_equation.
    rewrite H2'. clear H2'.
    apply IHx in H5.
    destruct e; inversion H2; subst; assumption.
    assumption.
Qed.

(** Correcteness of the big-step implementation (auxiliary of part 2) *)
Lemma eval_big_correct_2_aux : forall e e',
  eval_big e = Some e' -> exists n, EvalN e e' n /\ Val e'.
Proof.
  intros e e'.
  apply eval_big_ind; intros; subst.
  - inversion H; subst. exists 0. split; constructor.
  - inversion H; subst. exists 0. split; constructor.
  - apply H in H0. destruct H0. destruct H0. exists (S x).
    split. apply (evalN _ e'0). apply eval_correct.
    all: assumption.
  - discriminate.
Qed.

(** Correcteness of the big-step implementation (part 2) *)
Lemma eval_big_correct_2 : forall e e',
  eval_big e = Some e' -> EvalBig e e'.
Proof.
  intros.
  assert (T := eval_big_correct_2_aux e e' H).
  destruct T. destruct H0.
  apply eval_big_equiv_eval_star. split.
  apply EvalNToEvalStar. exists x.
  all: assumption.
Qed.

(** Correcteness of the big-step implementation *)
Theorem eval_big_correct : forall e e',
  EvalBig e e' <-> eval_big e = Some e'.
Proof.
  intros. split.
  apply eval_big_correct_1.
  apply eval_big_correct_2.
Qed.
