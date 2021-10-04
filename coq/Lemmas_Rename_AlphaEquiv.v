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

Lemma alpha_equiv_renamed_1 : forall e e' x z,
  free_vars e z = false -> conj_vars e' z = false ->
  alpha_equiv_rel e (rename e' x z) ->
  e' = (rename e' x z).
Proof.
  intros e e'.
  induction e, e' using expr_pair_ind; intros.
  - simpl. simpl in H1.
    destruct (x0 =? x').
    inversion H1. subst.
    simpl in H. unfold singletonSet in H.
    rewrite Nat.eqb_refl in H. discriminate.
    reflexivity.
  - simpl. simpl in H3.
    simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1.
    unfold removeFromSet in H4.
    simpl in H2. unfold unionSet in H2.
    apply orb_false_iff in H2. destruct H2.
    unfold updateSet in H5.
    case_eq (x' =? z); intros X'Z.
    rewrite X'Z in H5. discriminate.
    case_eq (x0 =? x'); intros.
    + rewrite H6 in H3.
      apply Nat.eqb_eq in H6. subst.
      inversion H3. subst.
      assert (T :=
        H e'1 e'3
        (same_structure_refl e'1)
        (same_structure_refl e'3)
        x' z H1 H2 H8
      ).
      rewrite <- T. reflexivity.
    + rewrite H6 in H3. rewrite X'Z in H5.
      inversion H3. subst.
      assert (T :=
        H e'1 e'3
        (same_structure_refl e'1)
        (same_structure_refl e'3)
        x0 z H1 H2 H9
      ).
      rewrite <- T.
      remember (max (get_fresh_var e'2) (get_fresh_var (rename e'4 x0 z))) as newX.
      remember (max (S z) newX) as newX2.
      assert (T2 : (z =? newX2) = false).
      {
        assert (T2 := le_max_l (S z) newX).
        assert (T3 := lt_n_Sn z).
        rewrite <- HeqnewX2 in T2.
        assert (T4 := lt_le_trans z (S z) newX2 T3 T2).
        assert (T5 := lt_neq z newX2 T4).
        case_eq (z =? newX2); intros.
        rewrite Nat.eqb_eq in H7. subst. rewrite <- H7 in T5.
        unfold not in T5. assert (T5 := T5 Logic.eq_refl).
        contradiction.
        reflexivity.
      }
      assert (T3 : alpha_equiv_rel (rename e'2 x newX2) (rename (rename e'4 x0 z) x' newX2)).
      {
        assert (T3 := max_id (S z)).
        apply H14.
        apply fresh_var_not_in_conj_vars. lia.
        apply fresh_var_not_in_conj_vars. lia.
      }
      assert (T4 := alpha_equiv_same_free_vars (rename e'2 x newX2) (rename (rename e'4 x0 z) x' newX2) T3).
      assert (T5 : free_vars e'4 x0 = false).
      {
        case_eq (free_vars e'4 x0); intros.
        assert (T5 := rename_the_free_var e'4 x0 z H7 H5).
        rewrite Nat.eqb_sym in X'Z.
        assert (T6 := rename_keeps_other_free_vars (rename e'4 x0 z) x' newX2 z X'Z).
        assert (T6 := T6 T2).
        rewrite <- T4 in T6.
        rewrite T5 in T6.
        case_eq (x =? z); intros XZ.
        apply Nat.eqb_eq in XZ. rewrite XZ in T6.
        assert (T7 := rename_removes_free_vars e'2 z newX2 T2).
        rewrite T7 in T6. discriminate.
        rewrite XZ in H4.
        rewrite Nat.eqb_sym in XZ.
        assert (T7 := rename_keeps_other_free_vars e'2 x newX2 z XZ T2).
        rewrite <- T6 in T7.
        rewrite H4 in T7. discriminate.
        reflexivity.
      }
      f_equal.
      apply rename_non_existant_free.
      assumption.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. simpl in H3.
    inversion H3. subst.
    simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1.
    simpl in H2. unfold unionSet in H2.
    apply orb_false_iff in H2. destruct H2.
    f_equal.
    apply (H e'1 e'3
      (same_structure_refl e'1)
      (same_structure_refl e'3)
      x z H1 H2 H7
    ).
    apply (H0 e'2 e'4
      (same_structure_refl e'2)
      (same_structure_refl e'4)
      x z H4 H5 H9
    ).
  - simpl. simpl in H3.
    inversion H3. subst.
    simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1.
    simpl in H2. unfold unionSet in H2.
    apply orb_false_iff in H2. destruct H2.
    f_equal.
    apply (H e'1 e'3
      (same_structure_refl e'1)
      (same_structure_refl e'3)
      x z H1 H2 H7
    ).
    apply (H0 e'2 e'4
      (same_structure_refl e'2)
      (same_structure_refl e'4)
      x z H4 H5 H9
    ).
  - simpl. simpl in H3.
    inversion H3. subst.
    simpl in H1. unfold unionSet in H1.
    apply orb_false_iff in H1. destruct H1.
    simpl in H2. unfold unionSet in H2.
    apply orb_false_iff in H2. destruct H2.
    f_equal.
    apply (H e'1 e'3
      (same_structure_refl e'1)
      (same_structure_refl e'3)
      x z H1 H2 H7
    ).
    apply (H0 e'2 e'4
      (same_structure_refl e'2)
      (same_structure_refl e'4)
      x z H4 H5 H9
    ).
  - simpl. simpl in H2.
    inversion H2. subst.
    simpl in H0.
    simpl in H1.
    f_equal.
    apply (H e'1 e'2
      (same_structure_refl e'1)
      (same_structure_refl e'2)
      x z H0 H1 H5
    ).
  - destruct e'1.
    all: destruct e'2.
    all: simpl in H; try contradiction.
    all: simpl in H2.
    all: inversion H2; subst.
    all: destruct (x =? x0).
    all: inversion H2.
    all: destruct (x =? x1).
    all: inversion H2.
Qed.

Lemma complex : forall e e' x x' x'' z,
  conj_vars e z = false ->
  conj_vars e' z = false ->
  (x' =? z) = false ->
  (x'' =? x') = false ->
  (forall newX : nat,
    conj_vars e newX = false ->
    conj_vars (rename e' x'' z) newX = false ->
    alpha_equiv_rel (rename e x newX) (rename (rename e' x'' z) x' newX)
  ) ->
  free_vars e' x'' = false.
Proof.
  intros.
  case_eq (x'' =? z); intros X''Z.

  apply Nat.eqb_eq in X''Z. subst x''.
  apply not_in_conj_not_in_free; assumption.

  case_eq (x' =? z); intro X'Z.
  rewrite X'Z in H1. symmetry in H1.
  apply Nat.eqb_eq in X'Z. subst.
  discriminate.

  remember (max
    (max (get_fresh_var e) (get_fresh_var e'))
    (max (max (S x'') (S 0)) (max (S z) (S z)))
  ) as newX.
  assert (T := complex_max e e' x'' 0 z z newX HeqnewX).
  destruct T as [T' [_ [T'' [_ [T''' T'''']]]]].
  assert (T3 : free_vars (rename e x newX) z = false). {
    case_eq (x =? z); intros.
    apply Nat.eqb_eq in H4. rewrite H4.
    apply rename_removes_free_vars.
    assumption.
    rewrite Nat.eqb_sym in H4.
    assert (T3 := rename_keeps_other_free_vars e x newX z H4 T'').
    rewrite <- T3. apply not_in_conj_not_in_free. assumption.
  }
  assert (T4 : conj_vars (rename e' x' newX) z = false). {
    rewrite Nat.eqb_sym in X'Z.
    assert (T4 := rename_keeps_other_vars e' x' newX z X'Z T'').
    rewrite H0 in T4. symmetry. assumption.
  }
  assert (T6 : conj_vars (rename e' x'' newX) z = false). {
    case_eq (x'' =? z); intros.
    apply Nat.eqb_eq in H4. rewrite H4.
    assert (T6 := rename_non_existant e' z newX H0).
    rewrite <- T6. assumption.
    rewrite Nat.eqb_sym in H4.
    assert (T6 := rename_keeps_other_vars e' x'' newX z H4 T'').
    rewrite H0 in T6. symmetry. assumption.
  }
  assert (T8 : conj_vars (rename e' x'' z) newX = false). {
    rewrite Nat.eqb_sym in T'.
    rewrite Nat.eqb_sym in T''.
    assert (T8 := rename_keeps_other_vars e' x'' z newX T' T'').
    rewrite <- T8.
    assumption.
  }
  assert (T9 := H3 newX T''' T8).
  assert (C : (rename (rename e' x'' z) x' newX) = (rename (rename e' x' newX) x'' z)).
  {
    apply rename_commu. assumption.
    assumption. rewrite Nat.eqb_sym.
    assumption. assumption.
  }
  assert (T10 := T9).
  rewrite C in T10.
  assert (T11 := alpha_equiv_renamed_1
    (rename e x newX)
    (rename e' x' newX)
    x'' z T3 T4 T10
  ).
  assert (T12 := rename_non_existant_free_2
    (rename e' x' newX)
    x'' z X''Z T11
  ).
  rewrite X'Z in H1. symmetry in H1.
  assert (T13 := rename_keeps_other_free_vars e' x' newX x'' H2 T').
  rewrite <- T13 in T12.
  assumption.
Qed.

Lemma alpha_equiv_renamed : forall e e' x x' z z',
  conj_vars e z = false -> conj_vars e' z = false ->
  conj_vars e z' = false -> conj_vars e' z' = false ->
  alpha_equiv_rel (rename e x z) (rename e' x' z) ->
  alpha_equiv_rel (rename e x z') (rename e' x' z').
Proof.
  intros e e'.
  induction e, e' using expr_pair_ind;
  intros y y' z z' C1 C2 C3 C4 A1; simpl in A1; simpl.
  - case_eq (y =? x); case_eq (y' =? x'); intros X X';
    rewrite X in A1; rewrite X' in A1.
    constructor.
    apply Nat.eqb_eq in X'. inversion A1. subst.
    simpl in C2. unfold singletonSet in C2.
    rewrite Nat.eqb_refl in C2. discriminate.
    apply Nat.eqb_eq in X. inversion A1. subst.
    simpl in C1. unfold singletonSet in C1.
    rewrite Nat.eqb_refl in C1. discriminate.
    assumption.
  - simpl in C1. unfold unionSet in C1.
    rewrite orb_false_iff in C1. destruct C1 as [C1 C1'].
    simpl in C2. unfold unionSet in C2.
    rewrite orb_false_iff in C2. destruct C2 as [C2 C2'].
    simpl in C3. unfold unionSet in C3.
    rewrite orb_false_iff in C3. destruct C3 as [C3 C3'].
    simpl in C4. unfold unionSet in C4.
    rewrite orb_false_iff in C4. destruct C4 as [C4 C4'].
    unfold updateSet in C1'.
    case_eq (x =? z); intro XZ; rewrite XZ in C1'. discriminate.
    unfold updateSet in C2'.
    case_eq (x' =? z); intro X'Z; rewrite X'Z in C2'. discriminate.
    unfold updateSet in C3'.
    case_eq (x =? z'); intro XZ'; rewrite XZ' in C3'. discriminate.
    unfold updateSet in C4'.
    case_eq (x' =? z'); intro X'Z'; rewrite X'Z' in C4'. discriminate.
    case_eq (y =? x); case_eq (y' =? x'); intros Y'X' YX;
    rewrite YX in A1; rewrite Y'X' in A1.
    + apply Nat.eqb_eq in YX. apply Nat.eqb_eq in Y'X'.
      inversion A1. subst. constructor.
      apply (H _ _ (same_structure_refl e'1) (same_structure_refl e'3) x x' z).
      all: assumption.
    + apply Nat.eqb_eq in YX.
      inversion A1. subst. constructor.
      apply (H _ _ (same_structure_refl e'1) (same_structure_refl e'3) x y' z).
      all: try assumption.
      intros.
      assert (T := complex e'2 e'4 x x' y' z C1' C2' X'Z Y'X' H8).
      rewrite <- (rename_non_existant_free e'4 y' z' T).
      rewrite <- (rename_non_existant_free e'4 y' z' T) in H2.
      rewrite <- (rename_non_existant_free e'4 y' z T) in H8.
      apply (H8 z0 H1 H2).
    + apply Nat.eqb_eq in Y'X'.
      inversion A1. subst. constructor.
      apply (H _ _ (same_structure_refl e'1) (same_structure_refl e'3) y x' z).
      all: try assumption.
      assert (H8' : (forall z0 : nat,
        conj_vars e'4 z0 = false ->
        conj_vars (rename e'2 y z) z0 = false ->
        alpha_equiv_rel (rename e'4 x' z0) (rename (rename e'2 y z) x z0))
      ). {
        intros. apply alpha_equiv_sym. apply H8; assumption.
      }
      intros.
      apply alpha_equiv_sym.
      assert (T := complex e'4 e'2 x' x y z C2' C1' XZ YX H8').
      rewrite <- (rename_non_existant_free e'2 y z' T).
      rewrite <- (rename_non_existant_free e'2 y z' T) in H1.
      rewrite <- (rename_non_existant_free e'2 y z T) in H8'.
      apply (H8' z0 H2 H1).
    + inversion A1. subst. constructor.
      apply (H _ _ (same_structure_refl e'1) (same_structure_refl e'3) y y' z).
      all: try assumption.
      intros.
      remember (max (max
        (max (get_fresh_var (rename e'2 y z)) (get_fresh_var (rename e'4 y' z)))
        (max (get_fresh_var (rename e'2 y z')) (get_fresh_var (rename e'4 y' z')))
      ) (max (max (S y) (S y')) (max (S z) (S z')))) as newX.
      assert (T1 := complex_max_2
        (rename e'2 y z) (rename e'4 y' z)
        (rename e'2 y z') (rename e'4 y' z')
        y y' z z' newX HeqnewX
      ).
      destruct T1 as [YnewX [Y'newX [ZnewX [Z'newX [T1 [T2 [T3 T4]]]]]]].
      clear HeqnewX.
      assert (T5 := H8 newX T1 T2).
      rewrite Nat.eqb_sym in XZ.
      rewrite (rename_commu e'2 y z x newX YX YnewX XZ ZnewX) in T5.
      rewrite Nat.eqb_sym in X'Z.
      rewrite (rename_commu e'4 y' z x' newX Y'X' Y'newX X'Z ZnewX) in T5.
      assert (T6 : conj_vars (rename e'2 x newX) z = false). {
        assert (T6 := rename_keeps_other_vars e'2 x newX z XZ ZnewX).
        rewrite <- T6. assumption.
      }
      assert (T7 : conj_vars (rename e'4 x' newX) z = false). {
        assert (T7 := rename_keeps_other_vars e'4 x' newX z X'Z ZnewX).
        rewrite <- T7. assumption.
      }
      assert (T8 : conj_vars (rename e'2 x newX) z' = false). {
        rewrite Nat.eqb_sym in XZ'.
        assert (T8 := rename_keeps_other_vars e'2 x newX z' XZ' Z'newX).
        rewrite <- T8. assumption.
      }
      assert (T9 : conj_vars (rename e'4 x' newX) z' = false). {
        rewrite Nat.eqb_sym in X'Z'.
        assert (T9 := rename_keeps_other_vars e'4 x' newX z' X'Z' Z'newX).
        rewrite <- T9. assumption.
      }
      assert (T10 := H0 (rename e'2 x newX) (rename e'4 x' newX)
        (rename_keeps_structure e'2 x newX)
        (rename_keeps_structure e'4 x' newX)
        y y' z z' T6 T7 T8 T9 T5
      ).
      rewrite Nat.eqb_sym in YX.
      rewrite Nat.eqb_sym in YnewX.
      rewrite Nat.eqb_sym in Z'newX.
      rewrite (rename_commu e'2 x newX y z' YX XZ' YnewX Z'newX) in T10.
      rewrite Nat.eqb_sym in Y'X'.
      rewrite Nat.eqb_sym in Y'newX.
      rewrite (rename_commu e'4 x' newX y' z' Y'X' X'Z' Y'newX Z'newX) in T10.
      apply (H0
        (rename e'2 y z')
        (rename e'4 y' z')
        (rename_keeps_structure e'2 y z')
        (rename_keeps_structure e'4 y' z')
        x x' newX z0 T3 T4 H1 H2 T10
      ).
  - assumption.
  - assumption.
  - simpl in C1. unfold unionSet in C1.
    rewrite orb_false_iff in C1. destruct C1 as [C1 C1'].
    simpl in C2. unfold unionSet in C2.
    rewrite orb_false_iff in C2. destruct C2 as [C2 C2'].
    simpl in C3. unfold unionSet in C3.
    rewrite orb_false_iff in C3. destruct C3 as [C3 C3'].
    simpl in C4. unfold unionSet in C4.
    rewrite orb_false_iff in C4. destruct C4 as [C4 C4'].
    inversion A1. subst.
    constructor.
    apply (H e'1 e'3 (same_structure_refl e'1) (same_structure_refl e'3) y y' z).
    all: try assumption.
    apply (H0 e'2 e'4 (same_structure_refl e'2) (same_structure_refl e'4) y y' z).
    all: assumption.
  - simpl in C1. unfold unionSet in C1.
    rewrite orb_false_iff in C1. destruct C1 as [C1 C1'].
    simpl in C2. unfold unionSet in C2.
    rewrite orb_false_iff in C2. destruct C2 as [C2 C2'].
    simpl in C3. unfold unionSet in C3.
    rewrite orb_false_iff in C3. destruct C3 as [C3 C3'].
    simpl in C4. unfold unionSet in C4.
    rewrite orb_false_iff in C4. destruct C4 as [C4 C4'].
    inversion A1. subst.
    constructor.
    apply (H e'1 e'3 (same_structure_refl e'1) (same_structure_refl e'3) y y' z).
    all: try assumption.
    apply (H0 e'2 e'4 (same_structure_refl e'2) (same_structure_refl e'4) y y' z).
    all: assumption.
  - simpl in C1. unfold unionSet in C1.
    rewrite orb_false_iff in C1. destruct C1 as [C1 C1'].
    simpl in C2. unfold unionSet in C2.
    rewrite orb_false_iff in C2. destruct C2 as [C2 C2'].
    simpl in C3. unfold unionSet in C3.
    rewrite orb_false_iff in C3. destruct C3 as [C3 C3'].
    simpl in C4. unfold unionSet in C4.
    rewrite orb_false_iff in C4. destruct C4 as [C4 C4'].
    inversion A1. subst.
    constructor.
    apply (H e'1 e'3 (same_structure_refl e'1) (same_structure_refl e'3) y y' z).
    all: try assumption.
    apply (H0 e'2 e'4 (same_structure_refl e'2) (same_structure_refl e'4) y y' z).
    all: assumption.
  - simpl in C1.
    simpl in C2.
    simpl in C3.
    simpl in C4.
    inversion A1. subst.
    constructor.
    apply (H e'1 e'2 (same_structure_refl e'1) (same_structure_refl e'2) y y' z).
    all: assumption.
  - assert (T := diff_constructor_not_alpha e'1 e'2 H
      (rename e'1 y z) (rename e'2 y' z)
      (rename_keeps_structure e'1 y z)
      (rename_keeps_structure e'2 y' z)
      A1
    ).
    contradiction.
Qed.

Lemma rename_keeps_alpha_equiv : forall e e' x z,
  conj_vars e z = false -> conj_vars e' z = false ->
  alpha_equiv_rel e e' ->
  alpha_equiv_rel (rename e x z) (rename e' x z).
Proof.
  intros.
  generalize dependent H0.
  generalize dependent H.
  generalize dependent z.
  generalize dependent x.
  induction H1; intros; simpl.
  - apply alpha_equiv_refl.
  - simpl in H2. unfold unionSet in H2.
    apply orb_false_iff in H2. destruct H2 as [H2 H2'].
    unfold updateSet in H2'. case_eq (x =? z); intro XZ.
    all: rewrite XZ in H2'. discriminate.
    simpl in H3. unfold unionSet in H3.
    apply orb_false_iff in H3. destruct H3 as [H3 H3'].
    unfold updateSet in H3'. case_eq (x' =? z); intro X'Z.
    all: rewrite X'Z in H3'. discriminate.
    case_eq (x0 =? x); intro X0X;
    case_eq (x0 =? x'); intro X0X'.
    + apply Nat.eqb_eq in X0X. apply Nat.eqb_eq in X0X'. subst.
      apply alpha_equiv_rel_let.
      apply IHalpha_equiv_rel; assumption.
      assumption.
    + apply Nat.eqb_eq in X0X. subst.
      apply alpha_equiv_rel_let.
      apply IHalpha_equiv_rel; assumption.
      intros.
      remember (max
        (max
          (max (get_fresh_var e2) (get_fresh_var e2'))
          (max (get_fresh_var e2) (get_fresh_var (rename e2' x z)))
        )
        (max (max (S x) (S x')) (max (S z) (S z0)))) as newX.
      assert (M := complex_max_2 e2 e2' e2 (rename e2' x z)
        x x' z z0 newX HeqnewX
      ).
      destruct M as [M1 [M2 [M3 [M4 [M5 [M6 [M7 M8]]]]]]].
      apply (alpha_equiv_renamed e2 (rename e2' x z)
        x x' newX z0 M5 M8 H4 H5
      ).
      rewrite Nat.eqb_sym in X'Z.
      rewrite (rename_commu _ _ _ _ _ X0X' M1 X'Z M3).
      rewrite (rename_twice e2 x newX z M1 M5).
      apply H0; try assumption.
      apply rename_does_not_add_new_var.
      rewrite Nat.eqb_sym. assumption. assumption.
      apply rename_does_not_add_new_var.
      rewrite Nat.eqb_sym. assumption. assumption.
    + apply Nat.eqb_eq in X0X'. subst.
      apply alpha_equiv_rel_let.
      apply IHalpha_equiv_rel; assumption.
      intros.
      remember (max
        (max
          (max (get_fresh_var e2) (get_fresh_var e2'))
          (max (get_fresh_var (rename e2 x' z)) (get_fresh_var e2'))
        )
        (max (max (S x) (S x')) (max (S z) (S z0)))) as newX.
      assert (M := complex_max_2 e2 e2' (rename e2 x' z) e2'
        x x' z z0 newX HeqnewX
      ).
      destruct M as [M1 [M2 [M3 [M4 [M5 [M6 [M7 M8]]]]]]].
      apply (alpha_equiv_renamed (rename e2 x' z) e2'
        x x' newX z0 M7 M8 H4 H5
      ).
      rewrite Nat.eqb_sym in XZ.
      rewrite (rename_commu _ _ _ _ _ X0X M2 XZ M3).
      rewrite (rename_twice e2' x' newX z M2 M6).
      apply H0; try assumption.
      apply rename_does_not_add_new_var.
      rewrite Nat.eqb_sym. assumption. assumption.
      apply rename_does_not_add_new_var.
      rewrite Nat.eqb_sym. assumption. assumption.
    + apply alpha_equiv_rel_let.
      apply IHalpha_equiv_rel; assumption.
      intros.
      remember (max
        (max
          (max (get_fresh_var e2) (get_fresh_var e2'))
          (max (get_fresh_var (rename e2 x0 z)) (get_fresh_var (rename e2' x0 z)))
        )
        (max (max (S x0) (S x')) (max (S z) (S z0)))) as newX.
      assert (M := complex_max_2 e2 e2' (rename e2 x0 z) (rename e2' x0 z)
        x0 x' z z0 newX HeqnewX
      ).
      destruct M as [M1 [M2 [M3 [M4 [M5 [M6 [M7 M8]]]]]]].
      apply (alpha_equiv_renamed (rename e2 x0 z) (rename e2' x0 z)
        x x' newX z0 M7 M8 H4 H5
      ).
      rewrite Nat.eqb_sym in XZ.
      rewrite (rename_commu e2 _ _ _ _ X0X M1 XZ M3).
      rewrite Nat.eqb_sym in X'Z.
      rewrite (rename_commu e2' _ _ _ _ X0X' M1 X'Z M3).
      apply H0; try assumption.
      apply rename_does_not_add_new_var.
      rewrite Nat.eqb_sym. assumption. assumption.
      apply rename_does_not_add_new_var.
      rewrite Nat.eqb_sym. assumption. assumption.
  - apply alpha_equiv_rel_num.
  - apply alpha_equiv_rel_str. assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H as [H H'].
    simpl in H0. unfold unionSet in H0.
    apply orb_false_iff in H0. destruct H0 as [H0 H0'].
    apply alpha_equiv_rel_plus; [apply IHalpha_equiv_rel1 | apply IHalpha_equiv_rel2].
    all: assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H as [H H'].
    simpl in H0. unfold unionSet in H0.
    apply orb_false_iff in H0. destruct H0 as [H0 H0'].
    apply alpha_equiv_rel_times; [apply IHalpha_equiv_rel1 | apply IHalpha_equiv_rel2].
    all: assumption.
  - simpl in H. unfold unionSet in H.
    apply orb_false_iff in H. destruct H as [H H'].
    simpl in H0. unfold unionSet in H0.
    apply orb_false_iff in H0. destruct H0 as [H0 H0'].
    apply alpha_equiv_rel_cat; [apply IHalpha_equiv_rel1 | apply IHalpha_equiv_rel2].
    all: assumption.
  - simpl in H. simpl in H0.
    apply alpha_equiv_rel_len. apply IHalpha_equiv_rel.
    all: assumption.
Qed.
