(* Elementary Row Operation definitions *)
Require Import MatrixDef.
Require Import VST.floyd.functional_base.
Require Import Coq.setoid_ring.Field_theory.
Require Import Field.
Require Import MatrixFacts.


Module FieldFacts(A: FieldMod).

Definition A := A.A.
Infix "*" := A.mult.
Infix "+" := A.plus.
Infix "-" := A.sub.
Notation "0" := A.zero.
Notation "1" := A.one.
Notation "- x" := (A.opp x).
Infix "/" := A.div.

Add Field field : A.Fth.

Lemma mult_assoc: forall a b c : A,
  a * (b * c) = (a * b) * c.
Proof.
  intros. ring.
Qed.

Lemma inv_mult: forall a : A,
  a <> 0 ->
  a * (A.inv a) = 1.
Proof.
  intros. field. assumption.
Qed.

Lemma mult_comm: forall a b : A,
  a * b = b * a.
Proof.
  intros. ring.
Qed. 

Lemma mult_1_l: forall a,
  1 * a = a.
Proof.
  intros. ring.
Qed.

Lemma mult_0_r: forall a,
  a * 0 = 0.
Proof.
  intros. ring.
Qed.

Lemma inv_nonzero: forall a,
  a <> 0 ->
  A.inv a <> 0.
Proof.
  intros. intro. assert (a * A.inv a = 1) by (field; assumption). 
  rewrite H0 in H1. rewrite mult_0_r in H1. pose proof (F_1_neq_0 (A.Fth)). rewrite H1 in H2.
  contradiction.
Qed. 

Lemma sub_add: forall a b c,
  a - b = c -> a = c + b.
Proof.
  intros. rewrite <- H. ring.
Qed.

Lemma one_not_zero : 1 <> 0.
Proof.
  pose proof (F_1_neq_0 (A.Fth)). assumption.
Qed.

Lemma add_0_l: forall a,
  0 + a = a.
Proof.
  intros. ring.
Qed.

Lemma add_0_r: forall a,
  a + 0 = a.
Proof.
  intros. ring.
Qed.

Notation "-1" := (0 - 1).

Lemma minus_one_not_zero : -1 <> 0.
Proof.
  intro. apply sub_add in H. rewrite add_0_l in H. apply one_not_zero. auto.
Qed.

Lemma minus_one_inv: -1 * -1 = 1.
Proof.
  ring.
Qed.

Lemma minus_one_times: forall a,
  -1 * a = -a.
Proof.
  intros. ring.
Qed.

Lemma inv_inv: forall a b,
  b -(-a) = b + a.
Proof.
  intros. ring.
Qed.

Lemma inv_def: forall a,
  -a + a = 0.
Proof.
  intros. ring.
Qed.

Lemma minus_add: forall a b,
  a - b = a + (-b).
Proof.
  intros. ring.
Qed.

Lemma add_assoc: forall a b c,
  a + (b + c) = (a + b) + c.
Proof.
  intros. ring.
Qed.

End FieldFacts.

Module RowOps(A: FieldMod)(M: Matrix A).

Definition A := A.A.
Infix "*" := A.mult.
Infix "+" := A.plus.
Infix "-" := A.sub.
Notation "0" := A.zero.
Notation "1" := A.one.
Notation "- x" := (A.opp x).
Infix "/" := A.div.

Import M.
Module F := FieldFacts A.
Module P := MatrixFacts.MatrixFacts A M.
Import P.
Import F.

Section Defs.

Variable m : nat.
Variable n : nat.

(*Inductive definition of ERO *)
Inductive ERO : matrix m n -> matrix m n -> Prop :=
  | ero_swap: forall mx r1 r2,
    (r1 < m)%nat ->
    (r2 < m)%nat ->
    ERO mx (swap_rows mx r1 r2)
  | ero_scalar: forall mx i c,
    (i < m)%nat ->
    c <> 0 ->
    ERO mx (scalar_mul_row mx i c)
  | ero_sub: forall mx r1 r2,
    (r1 < m)%nat ->
    (r2 < m)%nat ->
    r1 <> r2 ->
    ERO mx (subtract_rows mx r1 r2).

(*two matrices are row equivalent if one can be transformed to another via a sequence of EROs*)
Inductive row_equivalent: matrix m n -> matrix m n -> Prop :=
  | row_same: forall mx,
    row_equivalent mx mx
  | row_ero: forall mx mx' mx'',
    ERO mx mx' ->
    row_equivalent mx' mx'' ->
    row_equivalent mx mx''.

Lemma row_equivalent_refl: forall m1 m2,
  m1 = m2 ->
  row_equivalent m1 m2.
Proof.
  intros. subst. apply row_same.
Qed.

Lemma row_equivalent_trans: forall m1 m2 m3,
  row_equivalent m1 m2 ->
  row_equivalent m2 m3 ->
  row_equivalent m1 m3.
Proof.
  intros. induction H.
  - assumption.
  - eapply row_ero. apply H. auto.
Qed.

Lemma row_equivalent_ero: forall m1 m2,
  ERO m1 m2 ->
  row_equivalent m1 m2.
Proof.
  intros. eapply row_ero. apply H. apply row_same.
Qed.


(*A surprisingly complicated lemma - row_equivalence is symmetric *)
Lemma row_equivalence_sym: forall m1 m2,
  row_equivalent m1 m2 -> row_equivalent m2 m1.
Proof.
  intros. induction H.
  - constructor.
  - inversion H; subst.
    + eapply row_equivalent_trans. apply IHrow_equivalent. erewrite <- swap_twice. apply row_equivalent_ero.
      eapply ero_swap. all: lia.
    + eapply row_equivalent_trans. apply IHrow_equivalent.
      eapply row_equivalent_trans. apply row_equivalent_ero.  apply (ero_scalar _ i (A.inv c)).
      lia. apply inv_nonzero. assumption. 
      assert ((scalar_mul_row (scalar_mul_row mx i c) i (A.inv c)) = mx). { apply matrix_equiv.
      intros. rewrite scalar_mul_row_spec; try lia.
      if_tac. subst. rewrite scalar_mul_row_spec; try lia. if_tac. rewrite mult_assoc. 
      rewrite (mult_comm _ c). rewrite inv_mult. rewrite mult_1_l. reflexivity.
      assumption. contradiction. rewrite scalar_mul_row_spec; try lia. if_tac. contradiction. reflexivity. }
      rewrite H3. apply row_equivalent_refl. reflexivity.
    + eapply row_equivalent_trans. apply IHrow_equivalent.
      eapply row_equivalent_trans. (*this is actually quite involved: we need to multiply r2 = by -1,
      subtract r2 from r1, then multiply r2 by -1 again*)
      eapply row_equivalent_trans. apply row_equivalent_ero. apply (ero_scalar _ r2 -1); try lia.
      apply minus_one_not_zero.
      eapply row_equivalent_trans. apply row_equivalent_ero. apply (ero_sub _ r1 r2); try lia.
      apply row_equivalent_ero. apply (ero_scalar _ r2 -1); try lia.
      apply minus_one_not_zero.
      apply row_equivalent_refl. apply matrix_equiv. intros.
      rewrite scalar_mul_row_spec; try lia. if_tac.
      * rewrite subtract_rows_spec; try lia. if_tac. subst. contradiction.
        rewrite scalar_mul_row_spec; try lia. if_tac. 2 : contradiction.
        rewrite subtract_rows_spec; try lia. if_tac. subst. contradiction.
        rewrite mult_assoc. rewrite minus_one_inv. rewrite mult_1_l. reflexivity.
      * rewrite subtract_rows_spec; try lia. if_tac. 
        -- subst. rewrite? scalar_mul_row_spec; try lia. if_tac. contradiction. if_tac. 2 : contradiction.
           rewrite? subtract_rows_spec; try lia. if_tac. 2 : contradiction.
           if_tac. subst; contradiction. rewrite minus_one_times. rewrite inv_inv.
           rewrite minus_add. rewrite <- add_assoc. rewrite inv_def. rewrite add_0_r. reflexivity.
        -- rewrite scalar_mul_row_spec; try lia. if_tac. contradiction. rewrite subtract_rows_spec; try lia.
           if_tac. contradiction. reflexivity.
Qed. 



End Defs.
End RowOps.