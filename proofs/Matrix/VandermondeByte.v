(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

(*The results we need about the specific Vandermonde matrix over the field of bytes (really, these results hold over
  any field generated by a primitive element, but we only need (and prove) the results for the byte field.
  We use a separate file because we need to very careful about the order of imports between VST and ssreflect*)
Require Import VST.floyd.functional_base.
From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.poly.
Require Import mathcomp.algebra.polydiv.
Require Import mathcomp.algebra.qpoly.
Require Import mathcomp.field.qfpoly.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import ByteField.
Require Import ListPoly.
Require Import CommonSSR.
Require Import BoolField.
Require Import Vandermonde.
Require Import ByteFacts.
Require Import Gaussian.
Require Import GaussRestrict.

(** Results about the Weight Matrix*)

Notation B := byte_fieldType.


Section PrimitiveVandermonde.

Local Open Scope ring_scope.

(*Because the C code actually reverses the rows, we need rev of the natural choice 1, x, x^2, etc*)
Definition vandermonde_powers m n : 'M[B]_(m, n) :=
  vandermonde m n (rev (map (fun i => (bx ^+ i)) (iota 0 n))).

(*Alternate definition, useful for rewriting*)
Lemma vandermonde_powers_val (m n : nat) (i : 'I_m) (j: 'I_n) :
  vandermonde_powers m n i j = (bx ^+ (i * (n - j - 1))).
Proof.
  rewrite /vandermonde_powers /vandermonde mxE.
  have Hjsz: (nat_of_ord j < size (iota 0 n))%nat by rewrite size_iota.
  rewrite -map_rev.
  have->: [seq bx ^+ i0 | i0 <- rev(iota 0 n)]`_j = bx ^+ (n - j - 1). {
  rewrite (nth_map 0%nat) => [|//]. rewrite nth_rev=>[|//].
  rewrite size_iota nth_iota.
  by rewrite add0n -subnDA addn1. apply rev_ord_proof. by rewrite size_rev. }  
  by rewrite GRing.exprAC GRing.exprM.
Qed.

Notation p256_irred := (primitive_mi p256_primitive).
Notation Q256 := {poly %/ p256 with p256_irred}.

(*Now we need to prove [strong_inv] for this matrix*)

Lemma qpoly_to_byte_mul (q1 q2 : Q256) :
  qpoly_to_byte (q1 * q2)  = (qpoly_to_byte q1) * (qpoly_to_byte q2).
Proof.
  have->:(qpoly_to_byte q1 * qpoly_to_byte q2) =
     byte_mul (qpoly_to_byte q1) (qpoly_to_byte q2) by [].
  by rewrite /byte_mul !qpoly_byte_cancel.
Qed. 

Lemma qpoly_to_byte_pow (q: Q256) i :
  qpoly_to_byte (q ^+ i) = (qpoly_to_byte q) ^+ i.
Proof.
  elim : i => [| n IH /=].
  - rewrite !GRing.expr0. apply byte_to_qpoly_inj.
    by rewrite qpoly_byte_cancel byte_one_qpoly.
  - rewrite !GRing.exprS. by rewrite -IH qpoly_to_byte_mul.
Qed.

(*To reduce duplication. This is a straightforward application of the 
  injectivity of [qpow_map] by requires work to construct and unwrap the 
  ordinals*)

Lemma qpow_map_nonzero_inj x y :
  (x < 255)%N -> (y < 255)%N -> 
  x != 0%N -> 'qX ^+ x = 'qX ^+ y :> Q256 -> x = y.
Proof.
  move => Hx Hy Hx0.
  have Hxbound: (x < (#|bool_finType| ^ (size p256).-1).-1)%N.
    by rewrite card_bool size_p256.
  have Hybound: (y < (#|bool_finType| ^ (size p256).-1).-1)%N by
    rewrite card_bool size_p256.
  by apply: qX_exp_inj.
Qed.

Lemma bx_pows_inj i j :
  (i < 255)%N ->  (j < 255)%N -> bx ^+ i = bx ^+ j -> i = j.
Proof.
  move => Hi Hj. rewrite /bx => Heq.
  apply (congr1 byte_to_qpoly) in Heq.
  move: Heq. rewrite -!qpoly_to_byte_pow !qpoly_byte_cancel.
  case Hi0: (i == 0%N).
  - apply (elimT eqP) in Hi0. subst.
    case Hj0: (j == 0%N).
    + apply (elimT eqP) in Hj0. by subst.
    + move => Hij. apply esym in Hij.
      apply qpow_map_nonzero_inj in Hij; try by []. by rewrite Hj0.
  - move => Hij. apply qpow_map_nonzero_inj in Hij; try by []. by rewrite Hi0.
Qed.

(*We need the above in order to prove our lists are uniq for proving the 
  variable vandermonde submatrices invertible*)
Lemma power_list_uniq (n : nat) :
  (n < 256)%N -> uniq (map (fun i => (bx ^+ i)) (iota 0 n)).
Proof.
  move => Hn. rewrite map_inj_in_uniq. by rewrite iota_uniq.
  move => x y. rewrite !mem_iota !add0n => /andP[Hxgt Hxn] /andP[Hygt Hyn].
  have Hyup: (y < 255)%N by apply (ltn_leq_trans Hyn).
  have Hxup: (x < 255)%N by apply (ltn_leq_trans Hxn).
  by apply bx_pows_inj.
Qed. 

(*Now we deal with the matrices more directly*)

Lemma vandermonde_remove_col_list m n (Hmn : (m <= n)%N) l 
                                 (r :'I_m) (j : 'I_m) :
  submx_remove_col (@vandermonde B m n l) Hmn r j =
   vandermonde r r (rem_nth (take (r.+1) l) j).
Proof.
  rewrite /submx_remove_col /vandermonde -matrixP /eqrel => x y.
  rewrite !mxE. rewrite rem_nth_nth /=. case Hyj: (y < j)%N.
  - rewrite /=. rewrite nth_take. by []. have Hyr: (y < r)%N by [].
    by apply (ltn_trans Hyr).
  - rewrite /=. rewrite nth_take. by [].
    by rewrite -(addn1 y) -(addn1 r) ltn_add2r.
Qed.

Lemma vandermonde_remove_col_unitmx m n (Hmn : (m <= n)%N) 
                                   (r : 'I_m) (j: 'I_m) :
  (j < r)%N -> (n < 256)%N ->
  submx_remove_col (vandermonde_powers m n) Hmn r j \in unitmx.
Proof.
  move => Hjr Hnbound.
  rewrite vandermonde_remove_col_list. apply vandermonde_unitmx.
  - apply rem_nth_uniq. apply 0. apply take_uniq.
    rewrite rev_uniq. by apply power_list_uniq.
  - have Hsz: size (take r.+1 (rev 
        [seq (@GRing.exp _ bx i) | i <- iota 0 n])) = r.+1. {
    rewrite size_take size_rev size_map size_iota.
    have Hrm: (r.+1 <= m)%N by []. have: (r.+1 <= n)%N.
      by apply (leq_trans Hrm Hmn).
    rewrite leq_eqVlt => /orP[/eqP Hr1n | Hr1n].
    + rewrite Hr1n. rewrite ltnn -Hr1n. apply pred_Sn.
    + rewrite Hr1n. apply pred_Sn. }
    rewrite rem_nth_size; rewrite Hsz. apply pred_Sn. by apply (ltn_trans Hjr).
Qed.

(* The row matrix is much more complicated.
  Let P be the original powers matrix. Then p_ij = x^i(n-j-1).
  So row i consists of x^i(n-1), x^i(n-2),..., x^i(n-r). We cannot simply 
  take the transpose, because this is the reverse of a vandermonde matrix - 
  every column goes in decreasing powers of x. So we proved a result that we 
  can flip all the rows while preserving invertibility, allowing us to get 
  x^i(n-r), x^i(n-r+1),... in each column (after transpose). But this is still 
  not good enough, since we start with some extra powers of x (ie, a column 
  might be x^4, x^6, x^8,...). So before doing the above,
  we first scalar multiply each row i by p_ir^-1 = x^-(i(n-r-1)).
  So the transformations are as follows:
  p_{ij} = x^{i(n-j-1)}
  p1_{ij} = x^{i(r-j)} (scalar multiply)
  p2_{ij} = x^{j(r-i)} (transpose)
  p3_{ij} = x^{ji} (flip all rows (i -> r.+1 - i - 1)
  Finally, p3 is a vandermonde matrix, so it is invertible. Since all of these 
  transformations preserve invertibility, p is also invertible. *)



Definition scalar_mult_last_inv {m n} (Hn : (0 < n)%N) (A : 'M[B]_(m, n)) : 
      'M[B]_(m, n) :=
  foldr (fun (r: 'I_m) acc => sc_mul acc (A r (pred_ord Hn))^-1 r) 
     A (ord_enum m).

Lemma scalar_mult_last_inv_val {m n} (Hn : (0 < n)%N) (A : 'M[B]_(m, n)) i j :
  scalar_mult_last_inv Hn A i j = (A i j) * (A i (pred_ord Hn))^-1.
Proof.
  rewrite mx_row_transform.
  - by rewrite /sc_mul mxE eq_refl GRing.mulrC.
  - move => A' i' j' r Hir'. rewrite /sc_mul mxE. 
    by have->:(i' == r = false) by move: Hir'; case (i' == r).
  - move => A' B r Hin Hout j'. by rewrite /sc_mul !mxE eq_refl Hin.
  - apply ord_enum_uniq.
  - apply mem_ord_enum.
Qed.

Lemma qx_not_zero: bx != 0%R.
Proof.
  case: (bx == 0) /eqP => [ |//].
  rewrite /bx. have->:0%R = Byte.zero by []. move => Hx.
  apply (congr1 byte_to_qpoly) in Hx. move: Hx.
  rewrite qpoly_byte_cancel byte_zero_qpoly => Hx0.
  by have /eqP[] := (qX_neq0 (isT : 2 < size p256)%N _ : _ != 0 :> Q256).
Qed. 

(*This is the big lemma that will allow us to prove the transpose of 
  this matrix equivalent to a vandermonde mx*)
Lemma scalar_mult_last_inv_vandermonde_powers {m n} (Hmn: (m <= n)%N) 
        (r  y : 'I_m) i j :
  (r <= y)%N ->
  (scalar_mult_last_inv (ltn0Sn r) (submx_add_row
     (@vandermonde_powers m n) Hmn r y)) i j = 
    bx^+ ((if (i < r)%N then (i : nat) else y) * (r-j)).
Proof.
  move => Hry. rewrite scalar_mult_last_inv_val !mxE.
  have /eqP Hord: (widen_ord (leq_trans (ltn_ord r) Hmn) j) == j :> nat by []. 
  rewrite !Hord.
  have /eqP Hord' : 
    (widen_ord (leq_trans (ltn_ord r) Hmn) (pred_ord (ltn0Sn r))) == r :> nat.
      by [].
  rewrite {Hord} !Hord' {Hord'} !nth_rev; rewrite !size_map size_iota.
  have Hnsub: forall p, (n - p.+1 < n)%N. { move => p.
     rewrite ltn_subrL ltn0Sn /=.
  have: (0 <= n)%N by []. rewrite leq_eqVlt => /orP[Hn0 | //]. eq_subst Hn0.
  have Hrm: (r < m)%N by []. rewrite leqn0 in Hmn. eq_subst Hmn. by []. }
  rewrite !(nth_map 0%nat); try (by rewrite size_iota).
  rewrite !nth_iota; try (by rewrite Hnsub).
  rewrite !add0n.
  have Hsimpl z : 
    (bx ^+ (n - j.+1)) ^+ z / bx ^+ (n - r.+1) ^+ z = bx ^+ (z * (r - j)). {
  have: (0 <= z)%N by []. rewrite leq_eqVlt => /orP[Hz0 | Hz].
  + eq_subst Hz0. rewrite -!GRing.exprM !muln0 mul0n !GRing.expr0.
    apply GRing.mulfV.
    apply GRing.oner_neq0.
  + have: (j <= r)%N by rewrite ltnSE. rewrite leq_eqVlt => /orP[Hjreq | Hlt].
    - eq_subst Hjreq. rewrite Hjreq subnn muln0 GRing.expr0. apply GRing.mulfV.
      rewrite -GRing.exprM. rewrite GRing.expf_neq0. by []. apply qx_not_zero.
    - rewrite -!GRing.exprM. rewrite -!GRing.Theory.expfB.
      2: { have Hjr1: (j.+1 < r.+1)%N by []. rewrite ltn_mul2r Hz /=.
        apply ltn_sub2l.
        have Hrm: (r.+1 <= m)%N by [].
        have Hjm: (j.+1 < m)%N by apply (ltn_leq_trans Hjr1 Hrm).
        apply (ltn_leq_trans Hjm Hmn). by []. }
      rewrite -mulnBl subnBA. rewrite -addnABC. rewrite addnC -subnBA. 
      by rewrite subnn subn0 subSS mulnC. by rewrite leqnn.
      have Hjm: (j < m)%N by apply (ltn_trans Hlt).
      by apply (ltn_leq_trans Hjm Hmn). by [].
      have Hrm: (r < m)%N by []. by apply (ltn_leq_trans Hrm). }
  have: (i <= r)%N by rewrite ltnSE. rewrite leq_eqVlt => /orP[Hireq | Hlt].
  - eq_subst Hireq. rewrite Hireq ltnn. apply Hsimpl.
  - rewrite Hlt /=. apply Hsimpl.
  - have Hrm: (r < m)%N by []. by apply (ltn_leq_trans Hrm).
  - have Hjr: (j <= r)%N by rewrite -ltnS. have Hrm : (r < m)%N by [].
    have Hjm: (j < m)%N by apply (leq_ltn_trans Hjr Hrm).
    by apply (ltn_leq_trans Hjm).
Qed. 


(*The row matrix is a bit more complicated. The resulting matrix isn't 
  Vandermonde, but if we transpose it and then flip all the rows, then it is.
  So we use the [flip_rows] result as well*)

Lemma vandermonde_powers_add_row_list m n (Hmn : (m <= n)%N) (r j :'I_m) :
  (r <= j)%N ->
  flip_rows ((scalar_mult_last_inv (ltn0Sn r) 
    (submx_add_row (@vandermonde_powers m n) Hmn r j))^T) =
    vandermonde (r.+1) (r.+1) 
      ((map (fun i => (bx ^+ i)) (iota 0 r)) ++ (bx ^+ j :: nil)).
Proof.
  move => Hrj. rewrite /flip_rows /vandermonde -matrixP /eqrel => x y.
  rewrite mxE mxE scalar_mult_last_inv_vandermonde_powers. 2: by [].
  rewrite  !mxE.
  have Hxn: (x < n)%N. have Hxr: (x < r.+1)%N by []. rewrite ltnS in Hxr.
    have Hrm: (r < m)%N by [].
    have Hxm: (x < m)%N by apply (leq_ltn_trans Hxr Hrm).
    by apply (ltn_leq_trans Hxm Hmn).
  have Hx: (r - (r.+1 - x.+1))%nat = x by rewrite subSS subKn // -ltnS. 
  have: (y < r.+1)%N by []. rewrite ltnS leq_eqVlt => /orP[/eqP Hyr | Hyr].
  - rewrite Hyr ltnn. rewrite nth_cat.
    rewrite size_map size_iota ltnn subnn /=. by rewrite Hx -GRing.exprM.
  - rewrite Hyr /=. rewrite nth_cat size_map size_iota Hyr.
    rewrite !(nth_map 0%nat) /=. rewrite !nth_iota.
    rewrite !add0n. by rewrite Hx -GRing.exprM. by []. by rewrite size_iota.
Qed.

Lemma vandermonde_add_row_unitmx m n (Hmn : (m <= n)%N) (r j : 'I_m) :
  (r <= j)%N -> (n < 256)%N ->
  submx_add_row (vandermonde_powers m n) Hmn r j \in unitmx.
Proof.
  move => Hrj Hn.
  (*lots of layers to show*)
  have Hinv: row_equivalent (submx_add_row (vandermonde_powers m n) Hmn r j)
    (scalar_mult_last_inv (ltn0Sn r)
      (submx_add_row (vandermonde_powers m n) Hmn r j)). {
  apply mx_row_transform_equiv. move => A' r'. apply ero_row_equiv.
  apply ero_sc_mul.
  rewrite !mxE /=. (*need to do it here to show that not zero*)
  have Hnr: (n - r.+1 < n)%N.  rewrite ltn_subrL ltn0Sn /=.
  have: (0 <= n)%N by []. 
  rewrite leq_eqVlt => /orP[Hn0 | //]. eq_subst Hn0.
  have Hrm: (r < m)%N by []. rewrite leqn0 in Hmn. eq_subst Hmn. by [].
  rewrite nth_rev size_map size_iota. rewrite (nth_map 0%nat). rewrite nth_iota.
  rewrite add0n -!GRing.exprVn -GRing.exprM GRing.expf_neq0. by [].
  apply GRing.invr_neq0. apply qx_not_zero. by []. by rewrite size_iota.
  have Hrm: (r < m)%N by []. by apply (ltn_leq_trans Hrm). }
  apply row_equivalent_unitmx_iff in Hinv. rewrite Hinv {Hinv}.
  rewrite -unitmx_tr flip_rows_unitmx vandermonde_powers_add_row_list =>[|//].
  apply vandermonde_unitmx.
  - rewrite cats1 rcons_uniq.
    have->: (bx ^+ j \notin [seq (bx ^+ i) | i <- iota 0 r]). {
      case: (bx ^+ j \in [seq bx ^+ i | i <- iota 0 r]) /mapP =>[[i Hi Heq]|//]. 
      move : Hi; rewrite mem_iota add0n => /andP[H{H} Hir].
      have Hjbound: (j < 255)%N. have Hjm: (j < m)%N by [].
      have Hjn: (j < n)%N by apply (ltn_leq_trans Hjm Hmn).
        apply (ltn_leq_trans Hjn Hn).
      apply bx_pows_inj in Heq.
      + subst. have: (r < r)%N by apply (leq_ltn_trans Hrj). by rewrite ltnn.
      + by []. 
      + have Hij: (i < j)%N by apply (ltn_leq_trans Hir Hrj).
        apply (ltn_trans Hij Hjbound). }
    rewrite /=. apply power_list_uniq.
    apply (leq_ltn_trans Hrj).  have Hjm: (j < m)%N by [].
    apply (ltn_trans Hjm).
    by apply (leq_ltn_trans Hmn).
  - by rewrite size_cat /= size_map size_iota addn1.
Qed.

(*Finally, the result we want: The Vandermonde matrix consisting of powers of 
  the primitive element satisfied [strong_inv 0]*)
Lemma vandermonde_strong_inv : forall m n (Hmn : (m <= n)%N) (Hm : (0 < m)%N),
  (n < 256)%N ->
  strong_inv (vandermonde_powers m n) Hm Hmn.
Proof.
  move => m n Hmn Hm Hn. rewrite /strong_inv => r' H{H}.
  split; move => j Hrj.
  - by apply vandermonde_remove_col_unitmx.
  - by apply vandermonde_add_row_unitmx.
Qed.

End PrimitiveVandermonde.

Require Import ListMatrix.
Require Import ZSeq.
Require Import MatrixTransform.

(*Weight matrix definition*)
Section WeightMx.

Local Open Scope ring_scope.

Definition weight_mx_list (m n : Z) : lmatrix B :=
  mk_lmatrix m n (fun i j => bx ^+  Z.to_nat (i * (n - j - 1))).

Lemma weight_matrix_wf m n :
  0 <= n -> 0 <= m -> wf_lmatrix (weight_mx_list m n) m n.
Proof. move => Hn Hm. by apply mk_lmatrix_wf. Qed.

Lemma weight_mx_list_spec m n : 
  0 <= m -> 0 <= n ->
  lmatrix_to_mx m n (weight_mx_list m n) = 
  vandermonde_powers (Z.to_nat m) (Z.to_nat n).
Proof.
  move => Hm Hn. rewrite -matrixP => x y. 
  have Hx: 0 <= Z.of_nat x < m by apply (Z_ord_bound).
  have Hy: 0 <= Z.of_nat y < n by apply (Z_ord_bound). 
  rewrite vandermonde_powers_val mxE mk_lmatrix_get //=. f_equal.
  have->: (x * (Z.to_nat n - y - 1))%N = (x * (Z.to_nat n - y - 1))%coq_nat.
    by []. (*lia and nia not enough*)
  rewrite Z2Nat.inj_mul; try lia. rewrite Nat2Z.id Z2Nat.inj_sub; try lia.
  rewrite Z2Nat.inj_sub; try lia. by rewrite Nat2Z.id Nat.mul_sub_distr_l.
Qed. 

Definition weight_mx := (gauss_restrict_list fec_max_h (fec_n -1)
            (weight_mx_list fec_max_h  (fec_n - 1))).

Lemma weight_mx_wf: wf_lmatrix weight_mx (fec_max_h) (fec_n - 1).
Proof.
  apply gauss_restrict_list_wf. apply weight_matrix_wf; rep_lia.
Qed.
 
End WeightMx.