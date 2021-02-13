(*We have the listMatrix version of Vandermonde matrices, rather than in [ListMatrix], so that we use the same field
  as in [Common]. Otherwise there are dependent type errors. We have it in a separate file so we can use
  ssreflect while still using results in Common*)

Require Import VST.floyd.functional_base.

Require Import Vandermonde.
From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import PropList.
Require Import Poly.
Require Import Common.

(*Weight matrix definition*)
Section WeightMx.

Definition weight_mx_list (m n : Z) : matrix (Common.F) :=
  prop_list (fun i => (prop_list (fun j => (poly_to_qpoly mod_poly (monomial (Z.to_nat (i * (n - j - 1)))))) n)) m.

Lemma weight_matrix_wf: forall m n, 0 <= n -> 0 <= m -> wf_matrix (weight_mx_list m n) m n.
Proof.
  move => m n Hn Hm. rewrite /wf_matrix /weight_mx_list. repeat(split).
  - rewrite prop_list_length; lia.
  - by [].
  - move => x. rewrite In_Znth_iff. move => [i [Hilen Hith]].
    rewrite <- Hith. rewrite prop_list_Znth. rewrite prop_list_length; lia.
    rewrite prop_list_length in Hilen; lia.
Qed.

Lemma weight_mx_list_spec: forall m n, 
  0 <= m ->
  0 <= n ->
  matrix_to_mx m n (weight_mx_list m n) = vandermonde_powers (Z.to_nat m) (Z.to_nat n).
Proof.
  move => m n Hm Hn. rewrite -matrixP /eqrel. move => x y. rewrite mxE vandermonde_powers_val /get /weight_mx_list.
  have /ltP Hynat: (y < Z.to_nat n)%N by [].
  have Hyn: 0 <= Z.of_nat y < n by split; lia.
  rewrite !prop_list_Znth. rewrite exp_monomial. f_equal. f_equal. 
  have->: (x * (Z.to_nat n - y - 1))%N = (x * (Z.to_nat n - y - 1))%coq_nat by [].
  rewrite Z2Nat.inj_mul; try lia. rewrite Nat2Z.id. rewrite Z2Nat.inj_sub; try lia.
  rewrite Z2Nat.inj_sub; try lia. rewrite Nat2Z.id. by rewrite Nat.mul_sub_distr_l.
  by [].
  split; try lia. have /ltP Hx: (x < Z.to_nat m)%N by []. lia.
Qed. 

Definition weight_mx := (gauss_restrict_rows 
            (weight_mx_list fec_max_h  (fec_n - 1)) fec_max_h).

End WeightMx.

Require Import ListMatrix.
Require Import ReedSolomon.
Section Encoder.

(* The ListMatrix version of the encoder*)
Definition encode_list_mx (h k c : Z) (packets : list (list Z)) : matrix (Common.F) :=
  list_matrix_multiply h k c (submatrix weight_mx h k) (extend_mx (int_to_poly_mx packets) c).

(*Lift the above into ssreflect matrices and operations*)
Lemma encoder_spec : forall (h k c : Z) (packets: list (list Z)) (Hh: h <= fec_max_h) (Hk: k <= fec_n - 1),
  0 <= h ->
  0 <= k ->
  0 <= c ->
  Zlength packets = k ->
  Forall (fun x => Zlength x <= c) packets ->
  matrix_to_mx h c (encode_list_mx h k c packets) = encoder   (le_Z_N Hh) (le_Z_N Hk)
    (matrix_to_mx fec_max_h (fec_n - 1) weight_mx) 
    (matrix_to_mx k c (extend_mx (int_to_poly_mx packets) c)).
Proof.
  move => h k c packets Hh Hk Hn0 Hk0 Hc0 Hlen Hin. rewrite /encode_list_mx /encoder.
  have Hwf: wf_matrix weight_mx fec_max_h (fec_n - 1). apply gauss_restrict_rows_wf.
    apply weight_matrix_wf; rep_lia.
  rewrite list_matrix_multiply_correct.
  by rewrite (@submatrix_to_mx _ (fec_max_h) (fec_n - 1) _ _ _ Hh Hk).
  apply (submatrix_wf Hwf); rep_lia.
  apply extend_mx_wf. by []. by rewrite int_to_poly_mx_length1. move: Hin.
  rewrite !Forall_forall => Hin l. rewrite In_Znth_iff => [[x [Hxlen Hznth]]].
  subst. rewrite int_to_poly_mx_length2. apply Hin. apply Znth_In; try lia.
  by rewrite int_to_poly_mx_length1 in Hxlen.
Qed.

End Encoder.
