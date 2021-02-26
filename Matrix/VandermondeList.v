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
  mk_matrix m n (fun i j => (poly_to_qpoly mod_poly (monomial (Z.to_nat (i * (n - j - 1)))))).

Lemma weight_matrix_wf: forall m n, 0 <= n -> 0 <= m -> wf_matrix (weight_mx_list m n) m n.
Proof.
  move => m n Hn Hm. by apply mk_matrix_wf.
Qed.

Lemma weight_mx_list_spec: forall m n, 
  0 <= m ->
  0 <= n ->
  matrix_to_mx m n (weight_mx_list m n) = vandermonde_powers (Z.to_nat m) (Z.to_nat n).
Proof.
  move => m n Hm Hn. rewrite -matrixP => x y. 
  have Hx: 0 <= Z.of_nat x < m by apply (Z_ord_bound).
  have Hy: 0 <= Z.of_nat y < n by apply (Z_ord_bound). 
  rewrite vandermonde_powers_val mxE mk_matrix_get //= exp_monomial //. f_equal. f_equal. 
  have->: (x * (Z.to_nat n - y - 1))%N = (x * (Z.to_nat n - y - 1))%coq_nat by []. (*lia and nia not enough*)
  rewrite Z2Nat.inj_mul; try lia. rewrite Nat2Z.id Z2Nat.inj_sub; try lia.
  rewrite Z2Nat.inj_sub; try lia. by rewrite Nat2Z.id Nat.mul_sub_distr_l.
Qed. 

Definition weight_mx := (gauss_restrict_rows fec_max_h (fec_n -1)
            (weight_mx_list fec_max_h  (fec_n - 1))).

Lemma weight_mx_wf: wf_matrix weight_mx (fec_max_h) (fec_n - 1).
Proof.
  apply gauss_restrict_rows_wf. apply weight_matrix_wf; rep_lia.
Qed.

End WeightMx.

Require Import ListMatrix.
Require Import ReedSolomon.
Section Encoder.

(* The ListMatrix version of the encoder*)
Definition encode_list_mx (h k c : Z) (packets : list (list Z)) : matrix (Common.F) :=
  list_matrix_multiply h k c (submatrix (fec_n - 1) weight_mx h k) 
      (extend_mx k c (int_to_poly_mx packets)).

(*Lift the above into ssreflect matrices and operations*)
Lemma encoder_spec : forall (h k c : Z) (packets: list (list Z)) (Hh: h <= fec_max_h) (Hk: k <= fec_n - 1),
  0 <= h ->
  0 <= k ->
  0 <= c ->
  Zlength packets = k ->
  Forall (fun x => Zlength x <= c) packets ->
  matrix_to_mx h c (encode_list_mx h k c packets) = encoder (le_Z_N Hh) (le_Z_N Hk)
    (matrix_to_mx fec_max_h (fec_n - 1) weight_mx) 
    (matrix_to_mx k c (extend_mx k c (int_to_poly_mx packets))).
Proof.
  move => h k c packets Hh Hk Hn0 Hk0 Hc0 Hlen Hin. rewrite /encode_list_mx /encoder.
  have Hwf: wf_matrix weight_mx fec_max_h (fec_n - 1). apply weight_mx_wf. 
  rewrite list_matrix_multiply_correct.
  by rewrite (@submatrix_to_mx _ (fec_max_h) (fec_n - 1) _ _ _ Hh Hk).
  by apply submatrix_wf.
  by apply extend_mx_wf. 
Qed.

End Encoder.
