Require Import VST.floyd.functional_base.

From mathcomp Require Import all_ssreflect.
(*Require Import mathcomp.algebra.matrix.*)
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import ListMatrix.
Require Import ZSeq.
Require Import ReedSolomonList.
Require Import VandermondeByte.
Require Import MatrixTransform.
Require Import CommonSSR.
  
Section PopArr.

(*We define a more general version, where we only populate up to m' and n' (such that m' <= m, n' <= n)
  and the rest has a default element. We need this more general version for the decoder, then we define
  the primary array populating in terms of this*)
Definition pop_partial {A}  m' n' m n (f: Z -> Z -> A) (d: A) (i j : Z) :=
  mkseqZ (fun x => mkseqZ (fun y => if Z_le_lt_dec n' y then d else
                                    if Z_le_lt_dec m' x then d else 
                                    if Z_lt_le_dec x i then f x y else 
                                    if Z.eq_dec x i then if Z_lt_le_dec y j then f x y else d 
                                    else d) n) m.

Lemma pop_partial_rect: forall {A: Type} (m' n' m n : Z) (f: Z -> Z -> A) (d: A) (i j : Z),
  0 <= m ->
  0 <= n ->
  rect (pop_partial m' n' m n f d i j) m n.
Proof.
  move => A m' n' m n f d i j Hm Hn.
  have Hlen1: Zlength (pop_partial m' n' m n f d i j) = m by rewrite mkseqZ_Zlength.
  rewrite /rect; split; [| split]; try by [].
  rewrite Forall_Znth Hlen1 // => x Hx. by rewrite mkseqZ_Znth // mkseqZ_Zlength.
Qed.

(*At the start, this is the 2D array with all d's*)
Lemma pop_partial_zero: forall {A} m' n' m n f (d : A),
  0 <= m ->
  0 <= n ->
  pop_partial m' n' m n f d 0 0 = zseq m (zseq n d).
Proof.
  move => A m' n' m n f d Hm Hn. have Hinhab: Inhabitant A. apply d. apply (@rect_eq_ext _ _ m n).
  - by apply pop_partial_rect.
  - by apply zseq_rect.
  - move => i j Hi Hj. rewrite /get !mkseqZ_Znth // !zseq_Znth //.
    case :  (Z_lt_le_dec i 0) => [| /= _]; try rep_lia.
    case : (Z_le_lt_dec n' j) => [//=| /= Hjn ].
    case : (Z_le_lt_dec m' i) => [//=| /= Him].
    case : (Z.eq_dec i 0) => [/= Hi0 | //]. subst. 
    by case : (Z_lt_le_dec j 0); try rep_lia.
Qed.

(*Finish a row*)
Lemma pop_partial_row_finish: forall {A} m' n' m n f (d: A) i,
  0 <= m ->
  0 <= n ->
  pop_partial m' n' m n f d i n' = pop_partial m' n' m n f d (i+1) 0.
Proof.
  move => A m' n' m n f d i Hm Hn. have Hinhab: Inhabitant A. apply d.
  apply (rect_eq_ext (pop_partial_rect _ _ _ _ _ _ Hm Hn)  (pop_partial_rect  _ _ _ _ _ _ Hm Hn) ).
  move => i' j' Hi' Hj'. rewrite /get !mkseqZ_Znth //.
  case : (Z_le_lt_dec n' j') => [// | /= Hjn'].
  case : (Z_le_lt_dec m' i') => [// | /=Him'].
  case :  (Z_lt_le_dec i' i) => [Hii' /= | Hii' /=].
  - by case : (Z_lt_le_dec i' (i + 1)); try rep_lia. 
  - case : (Z.eq_dec i' i) => [Hiieq /= | Hiineq /=].
    + subst. case : (Z_lt_le_dec i (i + 1)) => [ /=_ | ]; try rep_lia.
      case : (Z_lt_le_dec j' n') => [//|]; lia. 
    + case : (Z_lt_le_dec i' (i + 1)) => [| /= _]; try rep_lia.
      case : (Z.eq_dec i' (i + 1)) => [Hi1 /= | //].
      by case : (Z_lt_le_dec j' 0); try rep_lia.
Qed.

Lemma pop_partial_set: forall {A} `{Inhabitant A} m' n' m n f (d: A) i j,
  m' <= m ->
  n' <= n ->
  0 <= i < m' ->
  0 <= j < n' ->
  pop_partial m' n' m n f d i (j+1) =
    set (pop_partial m' n' m n f d i j) i j (f i j).
Proof.
  move => A Hinhab m' n' m n f d i j Hm Hn Hi Hj. apply (@rect_eq_ext _ _ m n).
  - apply pop_partial_rect; lia.
  - apply set_rect; apply pop_partial_rect; lia.
  - move => i' j' Hi' Hj'. rewrite (@get_set _ _ _ m n); try rep_lia; last first.
    apply pop_partial_rect; lia. rewrite /get !mkseqZ_Znth; try lia.
    case : (Z_le_lt_dec n' j') => [/= Hnj' | /= Hnj']. have->: j =? j' = false.
      apply /Z.eqb_spec. lia. by rewrite andbF.
    case : (Z_le_lt_dec m' i') => [/= Hmi' | /= Hmi']. have->//: i =? i' = false.
      apply /Z.eqb_spec. lia.
    case: (i =? i') /(Z.eqb_spec _ _) => [ Hiieq /= | Hiineq /=].
    + subst. case : (Z_lt_le_dec i' i') => [| /= _]; try rep_lia.
      case : (Z.eq_dec i' i') => [/= _|]; try rep_lia.
      case: (j =? j') /(Z.eqb_spec _ _) => [Hjjeq //= | Hjjeq //=].
      * subst. by case : (Z_lt_le_dec j' (j' + 1)); try rep_lia.
      * case : (Z_lt_le_dec j' j) => [Hjj' /= | Hjj/=];  by case : (Z_lt_le_dec j' (j + 1)); try rep_lia.
    + case : (Z_lt_le_dec i' i) => [// | Hii' /=].
      by case : (Z.eq_dec i' i); try rep_lia.
Qed.

Lemma pop_partial_done: forall {A} `{Inhabitant A} m' n' m n f (d: A) j x y,
  m' <= m ->
  n' <= n ->
  0 <= x < m' ->
  0 <= y < n' ->
  get (pop_partial m' n' m n f d m j) x y = f x y.
Proof.
  move => A Hinhab m' n' m n f d j x y Hm Hn Hx Hy. rewrite /get !mkseqZ_Znth //; try lia.
  case : (Z_le_lt_dec n' y) => [|/= _]; try lia.
  case : (Z_le_lt_dec m' x) => [|/=_]; try lia.
  by case : (Z_lt_le_dec x m) => [_ // |]; try lia.
Qed.

(*Now we can define the version that uses the full array. We repeat a lot of the theorems because
  they were done before; we don't have to change the downstream proofs*)
Definition pop_2d_arr {A: Type} m n (f: Z -> Z -> A) (d: A) (i j : Z) : list (list A) :=
  pop_partial m n m n f d i j.

Lemma pop_2d_arr_rect:forall {A: Type} (m n : Z) (f: Z -> Z -> A) (d: A) (i j : Z),
  0 <= m ->
  0 <= n ->
  rect (pop_2d_arr m n f d i j) m n.
Proof.
  move => A m n f d i j Hm Hn. by apply pop_partial_rect.
Qed.

Lemma pop_2d_arr_zero: forall {A} m n f (d : A),
  0 <= m ->
  0 <= n ->
  pop_2d_arr m n f d 0 0 = zseq m (zseq n d).
Proof.
  move => A m n f d Hm Hn. by apply pop_partial_zero.
Qed.

Lemma pop_2d_arr_row_finish: forall {A} m n f (d: A) i,
  0 <= m ->
  0 <= n ->
  pop_2d_arr m n f d i n = pop_2d_arr m n f d (i+1) 0.
Proof.
  move => A m n f d i Hm Hn. by apply pop_partial_row_finish.
Qed.

Lemma pop_2d_arr_set: forall {A} `{Inhabitant A} m n f (d: A) i j,
  0 <= i < m ->
  0 <= j < n ->
  pop_2d_arr m n f d i (j+1) =
    set (pop_2d_arr m n f d i j) i j (f i j).
Proof.
   move => A Hinhab m n f d i j Hi Hj. apply pop_partial_set; lia.
Qed.

Lemma pop_2d_arr_done: forall {A} `{Inhabitant A} m n f (d : A) j x y,
  0 <= x < m ->
  0 <= y < n ->
  get (pop_2d_arr m n f d m j) x y = f x y.
Proof.
  move => A Hinhab m n f d j x y Hx Hy. apply pop_partial_done; lia.
Qed.

End PopArr.

(*

Local Open Scope ring_scope.

Variable F : fieldType.

(*At several places in the C code, a 2d array is populated by filling in each element, in order. We abstract that out
  to make the VST proof simpler and to reduce duplication*)
(*This is a matrix where the first i rows are filled, and the (i+1)st row is filled up to j*)
Definition pop_2d_mx m n (f: Z -> Z -> F) (i j : Z) : lmatrix F :=
  mk_lmatrix m n (fun x y => if Z_lt_le_dec x i then f x y
                    else if Z.eq_dec x i then if Z_lt_le_dec y j then f x y
                    else 0 else 0).

Lemma pop_2d_mx_wf: forall m n f i j,
  0 <= m ->
  0 <= n ->
  wf_lmatrix (pop_2d_mx m n f i j) m n.
Proof.
  move => m n f i j Hm Hn. by apply mk_lmatrix_wf.
Qed. 

(*At the start, this is the zero 2D array*)
Lemma pop_2d_mx_zero: forall m n f,
  0 <= m ->
  0 <= n ->
  pop_2d_mx m n f 0 0 = (zseq m (zseq n 0)).
Proof.
  move => m n f Hm Hn. apply (@lmatrix_ext_eq _ m n).
  - by apply pop_2d_mx_wf.
  - rewrite /wf_lmatrix; repeat split; [| rep_lia |].
    + rewrite zseq_Zlength; rep_lia.
    + rewrite Forall_Znth => i. rewrite zseq_Zlength; try rep_lia. move => Hi.
      rewrite zseq_Znth; try rep_lia. rewrite zseq_Zlength; rep_lia.
  - move => i' j' Hi' Hj'.
    rewrite mk_lmatrix_get; try rep_lia. rewrite /get !zseq_Znth; try rep_lia.
    case :  (Z_lt_le_dec i' 0) => [| /= _]; try rep_lia.
    case : (Z.eq_dec i' 0) => [/= Hi0 | //]. subst. 
    by case : (Z_lt_le_dec j' 0); try rep_lia.
Qed.

(*Finishing a row*)
Lemma pop_2d_mx_row_finish: forall m n f i,
  0 <= m ->
  0 <= n ->
  pop_2d_mx m n f i n = pop_2d_mx m n f (i+1) 0.
Proof.
  move => m n f i Hm Hn. apply (lmatrix_ext_eq (pop_2d_mx_wf _ _ _ Hm Hn) (pop_2d_mx_wf _ _ _ Hm Hn)).
  move => i' j' Hi' Hj'.
  rewrite !mk_lmatrix_get; try rep_lia.
  case :  (Z_lt_le_dec i' i) => [Hii' /= | Hii' /=].
  - by case : (Z_lt_le_dec i' (i + 1)); try rep_lia. 
  - case : (Z.eq_dec i' i) => [Hiieq /= | Hiineq /=].
    + subst. case : (Z_lt_le_dec i (i + 1)) => [ /=_ | ]; try rep_lia.
      case : (Z_lt_le_dec j' n) => [//|]. lia. 
    + case : (Z_lt_le_dec i' (i + 1)) => [| /= _]; try rep_lia.
      case : (Z.eq_dec i' (i + 1)) => [Hi1 /= | //].
      by case : (Z_lt_le_dec j' 0); try rep_lia.
Qed.

(*Update an element*)
Lemma pop_2d_mx_set: forall m n f i j,
  0 <= i < m ->
  0 <= j < n ->
  set (pop_2d_mx m n f i j) i j (f i j) = pop_2d_mx m n f i (j + 1).
Proof.
  move => m n f i j Hi Hj. apply (@lmatrix_ext_eq _ m n).
  - apply set_wf. apply pop_2d_mx_wf; lia.
  - apply pop_2d_mx_wf; lia.
  - move => i' j' Hi' Hj'. rewrite (@get_set _ m n); try rep_lia; last first.
    apply pop_2d_mx_wf; lia. rewrite !mk_lmatrix_get; try rep_lia. 
    case: (i' =? i) /(Z.eqb_spec _ _) => [ Hiieq /= | Hiineq /=].
    + subst. case : (Z_lt_le_dec i i) => [| /= _]; try rep_lia.
      case : (Z.eq_dec i i) => [/= _|]; try rep_lia.
      case: (j' =? j) /(Z.eqb_spec _ _) => [Hjjeq //= | Hjjeq //=].
      * subst. by case : (Z_lt_le_dec j (j + 1)); try rep_lia.
      * case : (Z_lt_le_dec j' j) => [Hjj' /= | Hjj/=];  by case : (Z_lt_le_dec j' (j + 1)); try rep_lia.
    + case : (Z_lt_le_dec i' i) => [// | Hii' /=].
      by case : (Z.eq_dec i' i); try rep_lia.
Qed.

(*Finish - prove a postcondition*)
Lemma pop_2d_mx_done: forall m n f j x y,
  0 <= x < m ->
  0 <= y < n ->
  get (pop_2d_mx m n f m j) x y = f x y.
Proof.
  move => m n f j x y Hx Hy. rewrite mk_lmatrix_get //.
  by case : (Z_lt_le_dec x m) => [_ // |]; try lia.
Qed.

*)
Section PopMult.

Variable F : fieldType.

Local Open Scope ring_scope.

(*Fill in a matrix for matrix multiplication*)

(*Input matrices are m x k and k x n, so output is m x n*)
Definition pop_mx_mult m n k (mx1 mx2: lmatrix F) (i j: Z): lmatrix F :=
  pop_2d_arr m n (fun x y => dot_prod mx1 mx2 x y k) 0 i j.

Lemma pop_mx_mult_wf: forall m n k mx1 mx2 i j,
  0 <= m ->
  0 <= n ->
  wf_lmatrix (pop_mx_mult m n k mx1 mx2 i j) m n.
Proof. 
  move => m n k mx1 mx2 i j. apply pop_2d_arr_rect.
Qed.

Lemma pop_mx_mult_row_finish: forall m n k mx1 mx2 i,
  0 <= m ->
  0 <= n ->
  pop_mx_mult m n k mx1 mx2 i n = pop_mx_mult m n k mx1 mx2 (i+1) 0.
Proof. 
  move => m n k mx1 mx2 i. apply pop_2d_arr_row_finish. 
Qed.

Lemma pop_mx_mult_zero: forall m n k mx1 mx2,
  0 <= m ->
  0 <= n ->
  pop_mx_mult m n k mx1 mx2 0 0 = zseq m (zseq n 0).
Proof.
  move => m n k mx1 mx2. apply pop_2d_arr_zero.
Qed.

Lemma pop_mx_mult_set: forall m n k mx1 mx2 i j,
  0 <= i < m ->
  0 <= j < n ->
  @set _ 0 (pop_mx_mult m n k mx1 mx2 i j) i j (dot_prod mx1 mx2 i j k) =
  pop_mx_mult m n k mx1 mx2 i (j+1).
Proof.
  move => m n k mx1 mx2 i j Hi Hj. by rewrite -pop_2d_arr_set.
Qed. 

Lemma pop_mx_mult_done: forall m n k mx1 mx2 j,
  0 <= m ->
  0 <= n ->
  pop_mx_mult m n k mx1 mx2 m j = list_lmatrix_multiply m k n mx1 mx2.
Proof.
  move => m n k mx1 mx2 j Hm Hn. apply (@lmatrix_ext_eq _ m n).
  - by apply pop_mx_mult_wf.
  - by apply list_lmatrix_multiply_wf.
  - move => x y Hx Hy. by rewrite pop_2d_arr_done // mk_lmatrix_get.
Qed.

End PopMult.

(*We also need a partial version for the decoder, since the whole array is not filled in*)
(*The original matrices have dimensions m' x k' and k' x n'*)
Definition pop_mx_mult_part m' n' k' m n (mx1 mx2: lmatrix B) (i j : Z) : list (list Values.val) :=
  pop_partial m' n' m n (fun x y => Vubyte (dot_prod mx1 mx2 x y k')) Vundef i j.


Lemma pop_mx_mult_part_wf: forall m' n' k' m n mx1 mx2 i j,
  0 <= m ->
  0 <= n ->
  rect (pop_mx_mult_part m' n' k' m n mx1 mx2 i j) m n.
Proof. 
  move => m n k mx1 mx2 i j. apply pop_partial_rect.
Qed.

(*Don't want to use wf lemma directly bc the matrices involved have very long names*)
Lemma pop_mx_mult_part_Zlength: forall m' n' k' m n mx1 mx2 i j,
  0 <= m -> 0 <= n -> Zlength (pop_mx_mult_part m' n' k' m n mx1 mx2 i j) = m.
Proof.
  move => m' n' k' m n mx1 mx2 x y Hm Hn. by apply pop_mx_mult_part_wf.
Qed. 

Lemma pop_mx_mult_part_row_finish: forall m' n' k' m n mx1 mx2 i,
  0 <= m ->
  0 <= n ->
  pop_mx_mult_part m' n' k' m n mx1 mx2 i n' = pop_mx_mult_part m' n' k' m n mx1 mx2 (i+1) 0.
Proof. 
  move => m' n' k' m n mx1 mx2 i. apply pop_partial_row_finish. 
Qed.

Lemma pop_mx_mult_part_zero: forall m' n' k' m n mx1 mx2,
  0 <= m ->
  0 <= n ->
  pop_mx_mult_part m' n' k' m n mx1 mx2 0 0 = zseq m (zseq n Vundef).
Proof.
  move => m' n' k' m n mx1 mx2. apply pop_partial_zero.
Qed.

Lemma pop_mx_mult_part_set: forall m' n' k' m n mx1 mx2 i j,
   m' <= m ->
  n' <= n ->
  0 <= i < m' ->
  0 <= j < n' ->
  @set _ Vundef (pop_mx_mult_part m' n' k' m n mx1 mx2 i j) i j (Vubyte (dot_prod mx1 mx2 i j k')) =
  pop_mx_mult_part m' n' k' m n mx1 mx2 i (j+1).
Proof.
  move => m' n' k' m n mx1 mx2 i j Hm Hn Hi Hj. by rewrite -pop_partial_set.
Qed. 

(*We can't say anything about the list as a whole, but the part we care about has entries equivalent to
  matrix multiplication*)
Lemma pop_mx_mult_part_done: forall m' n' k' m n mx1 mx2 j x y,
  m' <= m ->
  n' <= n ->
  0 <= x < m' ->
  0 <= y < n' ->
  Znth y (Znth x (pop_mx_mult_part m' n' k' m n mx1 mx2 m j)) = 
    Vubyte (get (list_lmatrix_multiply m' k' n' mx1 mx2) x y).
Proof.
  move => m' n' k' m n mx1 mx2 j x y Hm Hn Hx Hy. rewrite mk_lmatrix_get //.
  pose proof (@pop_partial_done  _ _ m' n' m n (fun x y => Vubyte (dot_prod mx1 mx2 x y k')) Vundef) as Hdone.
  rewrite /get in Hdone. by apply Hdone.
Qed. 

Require Import ByteField.
Require Import PolyField.
Require Import ByteFacts.

(*Fill in the weight matrix in order, using [pop_2d_arr]*)
Definition pop_weight_mx (i j : Z) : lmatrix B := pop_2d_arr fec_max_h (fec_n -1) 
  (fun x y => (byte_pow_map (Byte.repr ((x * y) mod 255)))) 0%R i j.

Lemma pop_weight_mx_wf: forall i j,
  wf_lmatrix (pop_weight_mx i j) fec_max_h (fec_n - 1).
Proof.
  move => i j. apply pop_2d_arr_rect; rep_lia.
Qed.

Lemma pop_weight_mx_row_finish: forall i,
  pop_weight_mx i (fec_n - 1) = pop_weight_mx (i+1) 0.
Proof.
  move => i. apply pop_2d_arr_row_finish; rep_lia.
Qed.

Lemma pop_weight_mx_zero:
  pop_weight_mx 0 0 = (zseq fec_max_h (zseq (fec_n - 1) Byte.zero)).
Proof.
  apply pop_2d_arr_zero; rep_lia.
Qed.

Lemma pop_weight_mx_set: forall i j,
  0 <= i < fec_max_h ->
  0 <= j < fec_n - 1 ->
  set (pop_weight_mx i j) i j (byte_pow_map (Byte.repr ((i * j) mod 255))) =
  pop_weight_mx i (j + 1).
Proof.
  move => i j Hi Hj. by rewrite -pop_2d_arr_set.
Qed.

(*Relate [modn] to Z.modulo*)

Lemma modn_mod_nat: forall (n1 n2 : nat),
  (0 < n2)%N ->
  (n1 %% n2)%N = (n1 mod n2)%N.
Proof.
  move => n1 n2 Hn2. apply (Nat.mod_unique _ _ (n1 %/ n2)).
  - apply /ltP. by rewrite ltn_mod.
  - have->:(n2 * (n1 %/ n2))%coq_nat = (n2 * (n1 %/ n2))%N by [].
    have->:(n2 * (n1 %/ n2) + n1 %% n2)%coq_nat = (n2 * (n1 %/ n2) + n1 %% n2)%N by [].
    by rewrite mulnC -divn_eq.
Qed.

Lemma modn_mod_Z: forall (z1 z2: Z),
  0 <= z1 ->
  0 < z2 ->
  Z.to_nat (z1 mod z2) = ((Z.to_nat z1) %% (Z.to_nat z2))%N.
Proof.
  move => z1 z2 Hz1 Hz2. rewrite modn_mod_nat; last first. apply /ltP; lia.
  apply Nat2Z.inj. rewrite mod_Zmod; try lia. rewrite !Z2Nat.id; try lia.
  by apply Z.mod_pos_bound.
Qed.

Lemma pop_weight_weight_done: forall j,
  mx_val (pop_weight_mx fec_max_h j) = rev_mx_val (weight_mx_list fec_max_h  (fec_n - 1)).
Proof.
  move => j. apply (map_2d_rev_equiv fec_max_h (fec_n - 1)).
  - apply pop_weight_mx_wf.
  - apply weight_matrix_wf; rep_lia.
  - move => i' j' Hi' Hj'. rewrite pop_2d_arr_done //.
    rewrite mk_lmatrix_get; try lia. rewrite /byte_pow_map /bx -qpoly_to_byte_pow. f_equal.
    rewrite /qpow_map_full /=. apply powX_eq_mod. rewrite Byte.unsigned_repr; last first.
    pose proof (Z.mod_pos_bound (i' * j') 255); rep_lia. rewrite modn_mod_Z; try lia.
    have->: Z.to_nat 255 = 255%N by [].
    have->: (fec_n - 1 - (fec_n - 1 - j' - 1) - 1)%Z = j' by lia.
    by rewrite modn_mod.
Qed.

(*Populate [find_lost] in the VST proof*)
Definition pop_find_lost l k len : list Values.val :=
  map Vubyte (find_lost l k) ++ zseq (len - Zlength (find_lost l k)) Vundef.

Lemma pop_find_lost_0: forall l len,
  pop_find_lost l 0 len = zseq len Vundef.
Proof.
  move => l len. rewrite /pop_find_lost /= /find_lost /=. f_equal. list_solve.
Qed.

Lemma cat_app: forall {A: Type} (l1 l2: list A),
  (l1 ++ l2)%list = l1 ++ l2.
Proof.
  by [].
Qed.

Lemma pop_find_lost_plus_1: forall l k len,
  0 <= k < len ->
  pop_find_lost l (k+1) len = if (Z.eq_dec (Byte.signed (Znth k l)) 1%Z) then
    upd_Znth (Zlength (find_lost l k)) (pop_find_lost l k len) (Vubyte (Byte.repr k))
    else (pop_find_lost l k len).
Proof.
  move => l k len Hk.
  rewrite /pop_find_lost find_lost_plus_1; try lia.
  case: (Z.eq_dec (Byte.signed (Znth k l)) 1) => [/= Hk1 | //= Hk1]; try lia.
  rewrite map_cat /= Zlength_app Zlength_cons Zlength_nil /=.
  rewrite upd_Znth_app2.
  - rewrite !Zlength_map Z.sub_diag. rewrite (@zseq_hd _ (len - Zlength _)).
    + rewrite upd_Znth0 /= -!catA cat_app /=. f_equal. f_equal. f_equal. lia.
    + pose proof (@find_lost_found_aux_Zlength (fun x : byte => Z.eq_dec (Byte.signed x) 1) Byte.repr l (Ziota 0 k)) as Hlen.
      rewrite Zlength_Ziota in Hlen; rewrite /find_lost; lia.
  - rewrite !Zlength_map. list_solve.
Qed.

(*TODO: see if we need anything else for done - maybe something about Znth*)
Lemma pop_find_lost_Znth: forall l k len i,
  0 <= i < Zlength (find_lost l k) ->
  Znth i (pop_find_lost l k len) = Vubyte (Znth i (find_lost l k)).
Proof.
  move => l k len i Hi. rewrite /pop_find_lost. rewrite Znth_app1; last first.
  by rewrite Zlength_map; lia. by rewrite Znth_map.
Qed.

(*TODO: can we generalize this to reduce duplication?*)


(*Populate [find_found] in the VST proof*)
Definition pop_find_found l k len : list Values.val :=
  map Vubyte (find_found l k) ++ zseq (len - Zlength (find_found l k)) Vundef.

Lemma pop_find_found_0: forall l len,
  pop_find_found l 0 len = zseq len Vundef.
Proof.
  move => l len. rewrite /pop_find_found /= /find_found /=. f_equal. list_solve.
Qed.

Lemma pop_find_found_plus_1: forall l k len,
  0 <= k < len ->
  pop_find_found l (k+1) len = if (Z.eq_dec (Byte.signed (Znth k l)) 1%Z) then (pop_find_found l k len) else
    upd_Znth (Zlength (find_found l k)) (pop_find_found l k len) (Vubyte (Byte.repr k)).
Proof.
  move => l k len Hk. (*remember (pop_find_lost l k len) as pop.*)
  rewrite /pop_find_found /find_found find_lost_found_aux_plus_1; try lia.
  case: (Z.eq_dec (Byte.signed (Znth k l)) 1) => [//= Hk1 | //= Hk1]; try lia.
  (*rewrite upd_Znth_map.
  rewrite map_cat /= Zlength_app Zlength_cons Zlength_nil /=.*)
  rewrite upd_Znth_app2.
  - rewrite !Zlength_map Z.sub_diag. symmetry. rewrite (@zseq_hd _ (len - Zlength _)).
    + rewrite map_cat upd_Znth0 /= cat_app -!catA /=. f_equal. f_equal. f_equal. 
      rewrite Zlength_app; list_solve.
    + pose proof (@find_lost_found_aux_Zlength (fun x : byte => ~~ Z.eq_dec (Byte.signed x) 1) Byte.repr l (Ziota 0 k)) as Hlen.
      rewrite Zlength_Ziota in Hlen; lia.
  - rewrite !Zlength_map. list_solve.
Qed.

(*TODO: see if we need anything else for done - maybe something about Znth*)
Lemma pop_find_found_Znth: forall l k len i,
  0 <= i < Zlength (find_found l k) ->
  Znth i (pop_find_found l k len) = Vubyte (Znth i (find_found l k)).
Proof.
  move => l k len i Hi. rewrite /pop_find_found. rewrite Znth_app1; last first.
  by rewrite Zlength_map; lia. by rewrite Znth_map.
Qed.


(*Populate [find_parity_rows] - this is basically the same as [pop_find_lost] and [pop_find_found]*)
Definition pop_find_parity_rows l k len : list Values.val :=
  map Vubyte (find_parity_rows l k) ++ zseq (len - Zlength (find_parity_rows l k)) Vundef.

Lemma pop_find_parity_rows_0: forall l len,
  pop_find_parity_rows l 0 len = zseq len Vundef.
Proof.
  move => l len. rewrite /pop_find_parity_rows /= /find_parity_rows /=. f_equal. list_solve.
Qed.

Lemma pop_find_parity_rows_plus_1: forall l k len,
  0 <= k < len ->
  pop_find_parity_rows l (k+1) len = 
  match (Znth k l) with
  | None => pop_find_parity_rows l k len
  | Some _ => upd_Znth (Zlength (find_parity_rows l k)) (pop_find_parity_rows l k len) (Vubyte (Byte.repr k))
  end.
Proof.
  move => l k len Hk. rewrite /pop_find_parity_rows find_parity_rows_plus_1; try lia.
  case : (Znth k l) => [//= Hnth | //= Hnth].
  pose proof (@find_parity_rows_Zlength l k (proj1 Hk)) as Hlenbound.
  rewrite map_cat -catA /= upd_Znth_app2; rewrite !Zlength_map; [| list_solve].
  rewrite Z.sub_diag. symmetry. rewrite zseq_hd; try lia.
  rewrite cat_app upd_Znth0. f_equal. f_equal. f_equal. rewrite Zlength_app; list_solve.
Qed.

Lemma pop_find_parity_rows_Znth: forall l k len i,
  0 <= i < Zlength (find_parity_rows l k) ->
  Znth i (pop_find_parity_rows l k len) = Vubyte (Znth i (find_parity_rows l k)).
Proof.
  move => l k len i Hi. rewrite /pop_find_parity_rows Znth_app1; last first.
  by rewrite Zlength_map; lia. by rewrite Znth_map.
Qed.

(*Populate the [find_parity_found] array - this is a bit trickier because it is populated after the [find_found]
  array in memory*)
Definition pop_find_parity_found pack pars k len found max_n : list Values.val :=
  map Vubyte (find_found pack found) ++ map Vubyte (find_parity_found pars max_n k) ++
  zseq (len - Zlength (find_found pack found) - Zlength (find_parity_found pars max_n k)) Vundef.

Lemma pop_find_parity_found_0: forall pack pars len found max_n,
  pop_find_parity_found pack pars 0 len found max_n =
  pop_find_found pack found len.
Proof.
  move => pack pars len found max_n. rewrite /pop_find_parity_found /pop_find_found /find_parity_found /=.
  f_equal. f_equal. list_solve.
Qed.

Lemma pop_find_parity_found_plus_1: forall pack pars k len found max_n,
  0 <= k ->
  Zlength (find_found pack found) + Zlength (find_parity_found pars max_n k) < len ->
  0 <= found ->
  pop_find_parity_found pack pars (k+1) len found max_n =
  match Znth k pars with
  | None => pop_find_parity_found pack pars k len found max_n
  | Some _ => upd_Znth (Zlength (find_found pack found) + Zlength (find_parity_found pars max_n k))
                (pop_find_parity_found pack pars k len found max_n) (Vubyte (Byte.repr (max_n - 1 - k)))
  end.
Proof.
  move => pack pars k len found max_n Hk Hlen Hf.
  rewrite /pop_find_parity_found find_parity_found_plus_1; try lia.
  case : (Znth k pars) => [// Hnth | //= Hnth].
  pose proof (@find_parity_found_Zlength pars k max_n Hk) as Hlenbound.
  rewrite map_cat -catA /= upd_Znth_app2; rewrite !Zlength_map.
  - rewrite upd_Znth_app2; rewrite !Zlength_map; [| list_solve].
    have->: (Zlength (find_found pack found) + Zlength (find_parity_found pars max_n k) -
    Zlength (find_found pack found) - Zlength (find_parity_found pars max_n k)) = 0%Z by lia.
    symmetry. rewrite zseq_hd. rewrite upd_Znth0 !cat_app Zlength_app. f_equal. f_equal. f_equal. f_equal.
    list_solve. list_solve.
  - rewrite Zlength_app Zlength_map. list_solve.
Qed.

Lemma pop_find_parity_found_Znth: forall pack pars k len found max_n i,
  0 <= i < (Zlength (find_found pack found) + Zlength (find_parity_found pars max_n k)) ->
  Znth i (pop_find_parity_found pack pars k len found max_n) =
  Vubyte (if range_le_lt_dec 0 i (Zlength (find_found pack found)) then
          Znth i (find_found pack found)
          else (Znth (i - (Zlength (find_found pack found))) (find_parity_found pars max_n k))).
Proof.
  move => pack pars k len found max_n i Hi.
  rewrite /pop_find_parity_found. case : (range_le_lt_dec 0 i (Zlength (find_found pack found))) => [/= Hi' | /= Hi'].
  - rewrite Znth_app1.
    + by rewrite Znth_map.
    + rewrite Zlength_map; lia.
  - rewrite Znth_app2 !Zlength_map; [|lia]. rewrite Znth_app1.
    + rewrite Znth_map; list_solve.
    + rewrite Zlength_map; lia.
Qed.

(*
Lemma pop_find_parity_found_Znth1: forall pack pars k len found max_n i,
  0 <= i < Zlength (find_found pack found) ->
  Znth i (pop_find_parity_found pack pars k len found max_n) = Vubyte (Znth i (find_found pack found)).
Proof.
  move => pack pars k len found max_n i Hi.
  rewrite /pop_find_parity_found. rewrite Znth_app1.
  - by rewrite Znth_map.
  - rewrite Zlength_map; lia.
Qed.

Lemma pop_find_parity_found_Znth2: forall pack pars k len found max_n i,
  Zlength (find_found pack found) <= i < Zlength (find_found pack found) + Zlength (find_parity_found pars max_n k) ->
  Znth i (pop_find_parity_found pack pars k len found max_n) = 
  Vubyte (Znth (i - (Zlength (find_found pack found))) (find_parity_found pars max_n k)).
Proof.
  move => pack pars k len found max_n i Hi. rewrite /pop_find_parity_found Znth_app2 !Zlength_map; [|lia].
  rewrite Znth_app1. rewrite Znth_map; list_solve.
  rewrite Zlength_map; lia.
Qed. *)

(*Populating the matrix to be inverted is quite nontrivial, for 4 reasons
  1. It is essentially represented as a 1D, rather than 2D array, so we need some arithmetic
     to get the right indexing
  2. It may not fill up the whole memory location
  3. Everything is reversed
  4. We fill up multiple nonconsecutive cells at a time*)


(*For the inverse operation, populating is nontrivial because the entire matrix has to be reversed.
  Also, it is treated as a 1-D array for all intents and purposes, so we do that here*)

(*want to say in memory: flatten_mx ... ++ zseq Vundef (3 * fec_max_h - 3 * xh)*)

(*This means we have filled up the first i rows are the first j entries of row i*)

(*The first part (the rest is just Vundef)*)
Definition pop_find_inv_fst (xh: Z) (weights: lmatrix B) (row lost : seq byte) i j : seq Values.val :=
   mkseqZ (fun z =>
                 let r := z / (2 * xh) in
                 let c := z mod (2 * xh) in
                 if (r <? i) || ((r =? i) && ((c <? j) || ((xh <=? c) && (c <? j + xh)))) then
                    if (c <? xh) then if (r + c + 1 =? xh) then Vubyte Byte.one else Vubyte Byte.zero
                    else Vubyte (get weights (Byte.unsigned (Znth r row)) (Byte.unsigned (Znth (c - xh) lost)))
                 else Vundef) (2 * xh * xh).

Definition pop_find_inv (xh: Z) (weights: lmatrix B) (row lost : seq byte) i j : seq Values.val :=
  pop_find_inv_fst xh weights row lost i j ++ 
  zseq (2 * fec_max_h * fec_max_h - 2 * xh * xh) Vundef.

Lemma pop_find_inv_fst_Zlength: forall xh weights row lost i j,
  0 <= xh ->
  Zlength (pop_find_inv_fst xh weights row lost i j) = 2 * xh * xh.
Proof.
  move => xh weights row lost i j. rewrite /pop_find_inv_fst.
  rewrite mkseqZ_Zlength //. nia.
Qed.

Lemma pop_find_inv_fst_0: forall xh weights row lost,
  0 < xh ->
  pop_find_inv_fst xh weights row lost 0 0 = zseq (2 * xh * xh) Vundef.
Proof.
  move => xh weights row lost Hxh. have Hxh': 0 <= xh by lia. apply Znth_eq_ext.
  - rewrite pop_find_inv_fst_Zlength // zseq_Zlength; nia.
  - move => i. rewrite pop_find_inv_fst_Zlength // => Hi.
    rewrite /pop_find_inv_fst mkseqZ_Znth //.
    case : (i / (2 * xh) <? 0) /Z.ltb_spec0 => [Hi0 | Hi0].
    * have: 0 <= i / (2 * xh). apply Z_div_pos; lia. lia.
    * have->: (xh <=? i mod (2 * xh)) && (i mod (2 * xh) <? 0 + xh) = false. {
        case : (xh <=? i mod (2 * xh)) /Z.leb_spec => [Hmod /=|//]. apply /Z.ltb_spec0. lia. }
      rewrite /=. case : (i / (2 * xh) =? 0) /Z.eqb_spec => [Hi0' | Hi0'].
      -- case : (i mod (2 * xh) <? 0) /Z.ltb_spec0 => [Himod | Himod].
         ++ have: 0 <= i mod (2 * xh) < 2 * xh. apply Z.mod_pos_bound; lia. lia.
         ++ rewrite /= zseq_Znth //. lia.
      -- rewrite /= zseq_Znth //. lia.
Qed.

(*Finish a row*)
Lemma pop_find_inv_fst_finish: forall xh weights row lost i,
  0 <= xh ->
  pop_find_inv_fst xh weights row lost i xh = pop_find_inv_fst xh weights row lost (i+1) 0.
Proof.
  move => xh weights row lost i Hxh. apply Znth_eq_ext.
  - by rewrite !pop_find_inv_fst_Zlength.
  - rewrite pop_find_inv_fst_Zlength // => x Hx.
    rewrite /pop_find_inv_fst !mkseqZ_Znth //.
    case : (x / (2 * xh) <? i) /Z.ltb_spec0 => [Hdiv /= | Hdiv /=].
    + have-> //: (x / (2 * xh) <? i + 1) = true. apply /Z.ltb_spec0. lia.
    + case : (x / (2 * xh) <? i + 1) /Z.ltb_spec0 => [Hdiv' /= | Hdiv' /=].
      * have-> //=: (x / (2 * xh) =? i). apply /Z.eqb_spec. lia.
        case : (x mod (2 * xh) <? xh) /Z.ltb_spec0 => [//=|/= Hmodxh].
        have-> /=:(xh <=? x mod (2 * xh)) = true. apply /Z.leb_spec0. lia.
        have->//: x mod (2 * xh) <? xh + xh. apply /Z.ltb_spec0. 
        have:  0 <= x mod (2 * xh) < 2 * xh. apply Z.mod_pos_bound; lia. lia.
      * have->/=:(x / (2 * xh) =? i) = false. apply /Z.eqb_spec. lia.
        case : (x / (2 * xh) =? i + 1) /Z.eqb_spec => [Hi1 /= | //].
        have->//: (x mod (2 * xh) <? 0) || (xh <=? x mod (2 * xh)) && (x mod (2 * xh) <? 0 + xh) = false.
        have Hmodbound:  0 <= x mod (2 * xh) < 2 * xh by apply Z.mod_pos_bound; lia.
        apply orb_false_intro. apply /Z.ltb_spec0. lia. 
        case : (xh <=? x mod (2 * xh)) /Z.leb_spec0 => [Hmodxh /=|//].
        apply /Z.ltb_spec0. lia.
Qed.

(*This is not a good name*)
Lemma idx_div: forall i j k,
  0 <= i < k ->
  0 <= j < k ->
  (i * k + j) / k = i.
Proof.
  move => i j k Hi Hj. rewrite Z.add_comm Z_div_plus; try lia.
  rewrite Zdiv_small; lia.
Qed.

Lemma idx_mod: forall i j k,
  0 <= i < k ->
  0 <= j < k ->
  (i * k + j) mod k = j.
Proof.
  move => i j k Hi Hj. by rewrite Z.add_comm Z_mod_plus_full Z.mod_small.
Qed.

(*Set the element(s) in the update. This is quite complicated because of
  all the cases, setting multiple elements, and some div/mod math*)
Lemma pop_find_inv_fst_set: forall xh weights row lost i j,
  0 <= xh ->
  0 <= i < xh ->
  0 <= j < xh ->
  pop_find_inv_fst xh weights row lost i (j+1) =
  upd_Znth (i * xh * 2 + j + xh) (upd_Znth (i * xh * 2 + j) (pop_find_inv_fst xh weights row lost i j) 
      (if Z.eq_dec (i + j + 1) xh then Vubyte Byte.one else Vubyte Byte.zero))
    (Vubyte (get weights (Byte.unsigned (Znth i row)) (Byte.unsigned (Znth j lost)))).
Proof.
  move => xh weights row lost i j Hxh Hi Hj. apply Znth_eq_ext.
  - rewrite !Zlength_upd_Znth !pop_find_inv_fst_Zlength; lia.
  - rewrite pop_find_inv_fst_Zlength; try lia. move => x Hx.
    case (Z.eq_dec x (i * xh * 2 + j)) => [Hnew /= | Hnew /=].
    + rewrite Hnew Znth_upd_Znth_diff; [| nia]. rewrite Znth_upd_Znth_same; try nia; last first.
      rewrite pop_find_inv_fst_Zlength; lia. 
      rewrite /pop_find_inv_fst mkseqZ_Znth; try nia.
      have Hdiv : (i * xh * 2 + j) / (2 * xh) = i by rewrite -Z.mul_assoc (Z.mul_comm 2) idx_div //; nia.
      have Hmod: (i * xh * 2 + j) mod (2 * xh) = j by rewrite -Z.mul_assoc (Z.mul_comm 2) idx_mod; nia.
      rewrite Hdiv Hmod Z.ltb_irrefl Z.eqb_refl /=.
      have->/=:(j <? j + 1). apply /Z.ltb_spec0. lia.
      have->/=:j <? xh. apply /Z.ltb_spec0. lia.
      case : (Z.eq_dec (i + j + 1) xh) => [Heq /= | Hneq /=].
      by rewrite Heq Z.eqb_refl. have->//: i + j + 1 =? xh = false.
      by apply /Z.eqb_spec.
    + case (Z.eq_dec x (i * xh * 2 + j + xh)) => [Hnew' /= | Hnew' /=].
      * rewrite Hnew' Znth_upd_Znth_same; try nia; last first. rewrite Zlength_upd_Znth
        pop_find_inv_fst_Zlength; lia.
        rewrite /pop_find_inv_fst mkseqZ_Znth; try nia.
        have Hdiv: (i * xh * 2 + j + xh) / (2 * xh) = i
          by rewrite -Z.add_assoc -Z.mul_assoc (Z.mul_comm 2) idx_div //; nia.
        have Hmod: (i * xh * 2 + j + xh) mod (2 * xh) = j + xh by
          by rewrite -Z.add_assoc -Z.mul_assoc (Z.mul_comm 2) idx_mod; nia.
        rewrite Hdiv Hmod Z.ltb_irrefl Z.eqb_refl /=.
        have->/=: (xh <=? j + xh) && (j + xh <? j + 1 + xh). {
          apply andb_true_intro; split. apply /Z.leb_spec0; lia. apply /Z.ltb_spec0; lia. }
        rewrite orbT. have->//:j + xh <? xh = false. apply /Z.ltb_spec0; lia. repeat f_equal; lia.
      * (*Finally, we are not updating anything new. This is still annoying, since we need to prove
          nothing else changed*)
        rewrite upd_Znth_diff//; last first; try (rewrite Zlength_upd_Znth pop_find_inv_fst_Zlength; nia).
        rewrite upd_Znth_diff//; last first; try (rewrite pop_find_inv_fst_Zlength; nia).
        rewrite /pop_find_inv_fst !mkseqZ_Znth; try lia.
        case : (x / (2 * xh) <? i) /Z.ltb_spec0 => [Hidiv // | Hidiv//=].
        case : (x / (2 * xh) =? i) /Z.eqb_spec => [Hieq /= | //].
        case : (x mod (2 * xh) <? j) /Z.ltb_spec0 => [Hmod /= | Hmod /=].
        -- have->//:(x mod (2 * xh) <? j + 1). apply /Z.ltb_spec0. lia.
        -- case : (x mod (2 * xh) <? j + 1) /Z.ltb_spec0 => [Hmod' //=| Hmod' //=].
          ++ have Hxj: x mod (2 * xh) = j by lia.
             have Hxcon: x = i * xh * 2 + j by rewrite (Z_div_mod_eq x (2 * xh)); lia. by [].
          ++ case : (xh <=? x mod (2 * xh)) /Z.leb_spec0 => [Hxmod/=|//].
             case : (x mod (2 * xh) <? j + xh) /Z.ltb_spec0 => [Hxjmod /= | Hxjmod /=].
            ** have->//: x mod (2 * xh) <? j + 1 + xh. apply /Z.ltb_spec0; lia.
            ** case : (x mod (2 * xh) <? j + 1 + xh) /Z.ltb_spec0 => [Hxjmod' /= | //].
               have Hjeq: x mod (2 * xh) = j + xh by lia.
               have Hxcon: x = i * xh * 2 + j + xh by rewrite (Z_div_mod_eq x (2 * xh)); lia. by [].
Qed.


(*I think the 2nd weights should be reversed. Because the first weights refers to the weights
  literally in the C code, which is the reverse of the weight mx that we actually care about in the
  functional model [weight_mx]*)
Lemma pop_find_inv_fst_post: forall xh weights row lost,
  0 <= xh ->
  wf_lmatrix weights fec_max_h (fec_n - 1) ->
  Forall (fun x => 0 <= Byte.unsigned x < fec_max_h) row ->
  Forall (fun x => 0 <= Byte.unsigned x < fec_n - 1) lost ->
  Zlength row = xh ->
  Zlength lost = xh ->
   pop_find_inv_fst xh (map_2d_rev id weights) row lost xh 0 =
   map Vubyte (flatten_mx (concat_mx_id (
       submx_rows_cols_rev_list weights xh xh (fec_n - 1) (map Byte.unsigned row) (map Byte.unsigned (rev lost))) xh)).
Proof.
  move => xh weights row lost Hxh [Hwh [_ Hweights]] Hrow Hlost Hrowlen Hlostlen.
  have Hflatlen: Zlength (flatten_mx (concat_mx_id
        (submx_rows_cols_rev_list weights xh xh (fec_n - 1) [seq Byte.unsigned i | i <- row]
         [seq Byte.unsigned i | i <- rev lost]) xh)) = 2 * xh * xh. {
    rewrite (@flatten_mx_Zlength _ xh (xh + xh)) //. lia.
    by apply row_mx_list_wf. }
 apply Znth_eq_ext.
  - by rewrite pop_find_inv_fst_Zlength // Zlength_map Hflatlen. 
  - rewrite pop_find_inv_fst_Zlength // => i Hi. rewrite /pop_find_inv_fst mkseqZ_Znth //.
    rewrite Znth_map; last first. by rewrite Hflatlen.
    rewrite (@flatten_mx_Znth' xh (2 * xh)); try lia; last first.
    have->:2 * xh = xh + xh by lia.
    by apply row_mx_list_wf.
    have Hxhpos: 0 < 2 * xh by nia. have Hi': 0 <= i < xh * (2 * xh) by lia.
    pose proof (find_indices_correct xh (2* xh) i Hxhpos Hi') as [Hidiv [Himod Hieq]].
    rewrite mk_lmatrix_get; try lia. 
    have->/=: i / (2 * xh) <? xh = true. apply /Z.ltb_spec0. lia.
    case : (Z_lt_ge_dec (2 * xh - 1 - i mod (2 * xh)) xh) => [/= Hfst | /=Hsnd]. 
    + have->/=: i mod (2 * xh) <? xh = false. apply /Z.ltb_spec0. lia.
      rewrite mk_lmatrix_get; try lia. f_equal.
      rewrite !Znth_map; try lia; last first. rewrite Zlength_map rev_rev Zlength_rev; lia.
      rewrite rev_rev Zlength_rev; lia.
      have Hdivbound: 0 <= Byte.unsigned (Znth (i / (2 * xh)) row) < Zlength weights. {
        move: Hrow. by rewrite Hwh Forall_Znth Hrowlen => /(_ (i / (2 * xh)) Hidiv). }
      have Hnthlen:Zlength (Znth (Byte.unsigned (Znth (i / (2 * xh)) row)) weights) = fec_n - 1. move: Hweights.
        rewrite Forall_Znth => /(_ (Byte.unsigned (Znth (i / (2 * xh)) row))) ->//.
      rewrite /get map_2d_rev_Znth //.
      * rewrite Hnthlen. rewrite /=. f_equal. f_equal. f_equal. f_equal.
        rewrite rev_rev Znth_rev; try lia. rewrite Hlostlen. f_equal. lia.
      * rewrite Hnthlen. move: Hlost.
        have Hbound: 0 <= (i mod (2 * xh) - xh) < Zlength lost by lia.
        by rewrite Forall_Znth => /(_ _ Hbound).
    + have->/=: i mod (2 * xh) <? xh = true. apply /Z.ltb_spec0. lia.
      rewrite mk_lmatrix_get; try lia.
      case : (Z.eq_dec (i / (2 * xh)) (2 * xh - 1 - i mod (2 * xh) - xh)) => [Hone /= | Hzero /=].
      * by have->: i / (2 * xh) + i mod (2 * xh) + 1 =? xh = true by apply /Z.eqb_spec; lia.
      * by have->:i / (2 * xh) + i mod (2 * xh) + 1 =? xh = false by apply /Z.eqb_spec; lia.
Qed.

(*The actual array may be longer. All of these lemmas are simple extensions of the above*)

Lemma pop_find_inv_Zlength: forall xh weights row lost i j,
  0 <= xh <= fec_max_h ->
  Zlength(pop_find_inv xh weights row lost i j) = 2 * fec_max_h * fec_max_h.
Proof.
  move => xh i j weights row lost Hxh. rewrite /pop_find_inv Zlength_app zseq_Zlength; try nia.
  rewrite pop_find_inv_fst_Zlength; nia.
Qed.

Lemma pop_find_inv_0: forall xh weights row lost,
  0 < xh <= fec_max_h ->
  pop_find_inv xh weights row lost 0 0 = zseq (2 * fec_max_h * fec_max_h) Vundef.
Proof.
  move => xh weights row lost Hxh. rewrite /pop_find_inv pop_find_inv_fst_0; try lia.
  rewrite -zseq_app; try nia. f_equal. nia.
Qed.

Lemma pop_find_inv_finish: forall xh weights row lost i,
  0 <= xh ->
  pop_find_inv xh weights row lost i xh = pop_find_inv xh weights row lost (i+1) 0.
Proof.
  move => xh weights row lost i Hxh. rewrite /pop_find_inv. f_equal.
  by apply pop_find_inv_fst_finish.
Qed.

Lemma pop_find_inv_set: forall xh weights row lost i j,
  0 <= xh ->
  0 <= i < xh ->
  0 <= j < xh ->
  pop_find_inv xh weights row lost i (j+1) =
  upd_Znth (i * xh * 2 + j + xh) (upd_Znth (i * xh * 2 + j) (pop_find_inv xh weights row lost i j) 
      (if Z.eq_dec (i + j + 1) xh then Vubyte Byte.one else Vubyte Byte.zero))
    (Vubyte (get weights (Byte.unsigned (Znth i row)) (Byte.unsigned (Znth j lost)))).
Proof.
  move => xh weights row lost i j Hxh Hi Hj. rewrite /pop_find_inv.
  rewrite !upd_Znth_app1.
  - by rewrite pop_find_inv_fst_set.
  - rewrite Zlength_upd_Znth pop_find_inv_fst_Zlength; nia.
  - rewrite pop_find_inv_fst_Zlength; nia.
Qed. 

Lemma pop_find_inv_post: forall xh weights row lost,
  0 <= xh ->
  wf_lmatrix weights fec_max_h (fec_n - 1) ->
  Forall (fun x => 0 <= Byte.unsigned x < fec_max_h) row ->
  Forall (fun x => 0 <= Byte.unsigned x < fec_n - 1) lost ->
  Zlength row = xh ->
  Zlength lost = xh ->
   pop_find_inv xh (map_2d_rev id weights) row lost xh 0 =
   map Vubyte (flatten_mx (concat_mx_id (
       submx_rows_cols_rev_list weights xh xh (fec_n - 1) (map Byte.unsigned row) (map Byte.unsigned (rev lost))) xh))
  ++ zseq (2 * fec_max_h * fec_max_h - 2 * xh * xh) Vundef.
Proof.
  move => xh weights row lost Hxh Hwf Hrowb Hlostb Hrowlen Hlostlen.
  rewrite /pop_find_inv. f_equal. by apply pop_find_inv_fst_post.
Qed.

(*Populate the stats array. This is a bit complicated because we index in using lost*)
Definition pop_stats (stats: list byte) (to_fill : list Z) i :=
  mkseqZ (fun x => if (Zindex x to_fill) <? Zlength to_fill then 
                      if ((Zindex x to_fill) <? i) then Byte.zero else Znth x stats
                   else Znth x stats) (Zlength stats).

Lemma pop_stats_Zlength: forall stats to_fill i,
  Zlength (pop_stats stats to_fill i) = Zlength stats.
Proof.
  move => stats to_fill i. rewrite mkseqZ_Zlength //; list_solve.
Qed.

Lemma pop_stats_0: forall stats to_fill,
  pop_stats stats to_fill 0 = stats.
Proof.
  move => stats to_fill. apply Znth_eq_ext; rewrite pop_stats_Zlength //.
  move => i Hi. rewrite mkseqZ_Znth //. case : (Zindex i to_fill <? Zlength to_fill) => [|//].
  case : (Zindex i to_fill <? 0) /Z.ltb_spec0 => [|//]. rewrite /Zindex. lia.
Qed.

Lemma pop_stats_plus_1: forall stats to_fill i,
  NoDup to_fill ->
  Forall (fun x => 0 <= x < Zlength stats) to_fill ->
  0 <= i < Zlength to_fill ->
  pop_stats stats to_fill (i + 1) = upd_Znth (Znth i to_fill) (pop_stats stats to_fill i) Byte.zero.
Proof.
  move => stats to_fill i Hnodup Hall Hi. apply Znth_eq_ext.
  - by rewrite Zlength_upd_Znth !pop_stats_Zlength.
  - rewrite pop_stats_Zlength => x Hx. rewrite !mkseqZ_Znth //.
    have [Hix | Hix]: (x = Znth i to_fill) \/ (x <> Znth i to_fill) by lia.
    + subst. rewrite upd_Znth_same //; last first. by rewrite pop_stats_Zlength.
      rewrite !Zindex_Znth //. have->/=: (i <? Zlength to_fill) = true by lia.
      have->//: i <? i + 1 = true by lia.
    + rewrite upd_Znth_diff //; try rewrite pop_stats_Zlength; try lia; last first.
      move: Hall. by rewrite Forall_Znth => /(_ _ Hi).
      rewrite !mkseqZ_Znth //.
      case : (Zindex x to_fill <? Zlength to_fill) => [|//].
      case : (Zindex x to_fill <? i ) /Z.ltb_spec0 => [/= Hxi | /= Hxi].
      * have->//: (Zindex x to_fill <? i + 1) = true by lia.
      * case : (Zindex x to_fill <? i + 1) /Z.ltb_spec0 => [/= Hxi' | //].
        have Hieq: Zindex x to_fill = i by lia. subst. 
        move: Hix. rewrite Znth_Zindex //. apply Zindex_In. lia.
Qed.

Lemma pop_stats_done: forall stats to_fill,
  (forall i, ~ In i to_fill -> Znth i stats = Byte.zero) ->
  pop_stats stats to_fill (Zlength to_fill) = zseq (Zlength stats) Byte.zero.
Proof.
  move => stats to_fill Hinfill.
  apply Znth_eq_ext.
  - rewrite pop_stats_Zlength zseq_Zlength //. list_solve.
  - rewrite pop_stats_Zlength => i Hi. rewrite mkseqZ_Znth // zseq_Znth //; [| list_solve].
    case : (Zindex i to_fill <? Zlength to_fill) /Z.ltb_spec0 => [// | /= Hnotin].
    apply Hinfill. by rewrite -Zindex_In.
Qed.

(* Populate (and trim) [fill_rows_list]*)
(*NOTE: input is NOT necessarily a filled matrix - it has length m and each row has length <= n*)
(*This definition does not use mk_lmatrix, because it is not a well formed matrix. We only fill in where needed*)
Definition pop_fill_rows_list (input : list (list byte)) rec rows i j :=
  mkseqZ (fun x => mkseqZ (fun y => if (Zindex x rows) <? (Zlength rows) then
                                      if ((Zindex x rows) <? i) || (((Zindex x rows) =? i) && (y <? j)) 
                                      then get rec (Zindex x rows) y
                                      else get input x y
                                    else get input x y)
  (Zlength (Znth x input))) (Zlength input).

Lemma pop_fill_rows_list_0: forall input rec rows,
  pop_fill_rows_list input rec rows 0 0 = input.
Proof.
  move => input rec rows. apply Znth_eq_ext; rewrite mkseqZ_Zlength; [by [] | list_solve | move =>i Hi | list_solve].
  apply Znth_eq_ext; rewrite !mkseqZ_Znth // mkseqZ_Zlength //; [list_solve | | list_solve].
  move => j Hj. rewrite mkseqZ_Znth //.
  case : (Zindex i rows <? Zlength rows) => [/=|//].
  case : (Zindex i rows <? 0) /Z.ltb_spec0. rewrite /Zindex; lia. move => _ /=.
  case : (j <? 0) /Z.ltb_spec0; try lia. move => _ /=. by rewrite andbF.
Qed.

Lemma z_leb_split: forall z1 z2,
  (z1 <? z2 + 1) = (z1 <? z2) || (z1 =? z2).
Proof.
  move => z1 z2. lia.
Qed. 

(*Actually may go further, C code does not stop once we reach length*)
(*Finish a row*)
Lemma pop_fill_rows_list_finish: forall input rec rows i c,
  Forall (fun l => Zlength l <= c) input ->
  pop_fill_rows_list input rec rows i c = pop_fill_rows_list input rec rows (i+1) 0.
Proof.
  move => input rec rows i c Hall.
  have Hlenin: 0 <= Zlength input by list_solve.
  apply Znth_eq_ext; rewrite !mkseqZ_Zlength // => x Hx.
  have Hlennth: 0 <= Zlength (Znth x input) by list_solve.
  apply Znth_eq_ext; rewrite !mkseqZ_Znth // !mkseqZ_Zlength // => y Hy.
  rewrite !mkseqZ_Znth //.
  case : (Zindex x rows <? Zlength rows) => [|//].
  have->: (y <? c) = true. apply /Z.ltb_spec0. have: Zlength (Znth x input) <= c; try lia.
    move: Hall. by rewrite Forall_Znth => /(_ _ Hx). rewrite andbT.
  have->:(y <? 0) = false. apply /Z.ltb_spec0. lia. by rewrite andbF orbF z_leb_split.
Qed.

(*TODO: move*)
Lemma set_Zlength1: forall {A} `{Inhabitant A} (s: seq (seq A)) i j x,
  Zlength (set s i j x) = Zlength s.
Proof.
  move => A Hinhab s i j x. rewrite /set. list_solve.
Qed.

Lemma set_Zlength2: forall {A} `{Inhabitant A} (s: seq (seq A)) i j x y,
  Zlength (Znth y (set s i j x)) = Zlength (Znth y s).
Proof.
  move => A Hinhab s i j x y. rewrite /set.
  have [Hylo | [Hyhi | Hyin]]: (y < 0 \/ Zlength s <= y \/ 0 <= y < Zlength s) by lia.
  - by rewrite !Znth_underflow.
  - rewrite !(Znth_overflow y) //. lia. list_solve.
  - have [Hiy | Hiy]: i = y \/ i <> y by lia.
    + subst. rewrite upd_Znth_same //. list_solve.
    + have [Hiout | Hiin]: ~ (0 <= i < Zlength s) \/ 0 <= i < Zlength s by lia.
      * rewrite upd_Znth_out_of_range //. lia.
      * rewrite upd_Znth_diff //. lia.
Qed.

(*update an element - this is a bit more complicated than above bc we dont update elt (i, j)*)
Lemma pop_fill_rows_list_set: forall input rec rows i j,
  NoDup rows ->
  Forall (fun x => 0 <= x < Zlength input) rows ->
  0 <= i < Zlength rows ->
  0 <= j < Zlength (Znth (Znth i rows) input) ->
  pop_fill_rows_list input rec rows i (j+1) =
    set (pop_fill_rows_list input rec rows i j) (Znth i rows) j (get rec i j).
Proof.
  move => input rec rows i j Hnodup Hinrows Hi Hj. 
  have Hlenin: 0 <= Zlength input by list_solve.
  apply Znth_eq_ext; rewrite !mkseqZ_Zlength //.
  by rewrite set_Zlength1 mkseqZ_Zlength.
  move => x Hx. have Hlennth: 0 <= Zlength (Znth x input) by list_solve.
  apply Znth_eq_ext; rewrite !mkseqZ_Znth // !mkseqZ_Zlength //.
  by rewrite set_Zlength2 mkseqZ_Znth // mkseqZ_Zlength.
  move => y Hy. rewrite mkseqZ_Znth // /set mkseqZ_Znth //; last first.
  move: Hinrows. by rewrite Forall_Znth => /(_ _ Hi).
  case : (Z.eq_dec x (Znth i rows)) => [Hxi | Hxi].
  - subst. rewrite upd_Znth_same; last first. rewrite mkseqZ_Zlength //.
    case : (Z.eq_dec y j) => [Hyj | Hyj].
    + subst. rewrite upd_Znth_same; last first. by rewrite mkseqZ_Zlength.
      rewrite !Zindex_Znth //. have->:i <? Zlength rows = true by lia.
      by have->:(i <? i) || (i =? i) && (j <? j + 1) = true by lia.
    + rewrite upd_Znth_diff; try lia; try rewrite mkseqZ_Zlength //.
      rewrite mkseqZ_Znth //.
      by have->: (y <? j) = (y <? j + 1) by lia.
  - rewrite upd_Znth_diff; try lia; try rewrite mkseqZ_Zlength //; last first.
    move: Hinrows. by rewrite Forall_Znth => /(_ _ Hi).
    rewrite !mkseqZ_Znth //.
    have->//=:(Zindex x rows =? i) = false. case : (Z.eq_dec (Zindex x rows) i); try lia.
    move => Hieq. subst. rewrite Znth_Zindex in Hxi. by []. 
    apply Zindex_In. lia.
Qed.

Lemma pop_fill_rows_list_done: forall input rec rows lens j k c xh,
  0 <= c ->
  Zlength input = k ->
  Zlength lens = k ->
  Zlength rec = xh ->
  Zlength rows = xh ->
  xh <= k ->
  Forall (fun x => Zlength x <= c) input ->  
  (forall i, 0 <= i < Zlength input -> Znth i lens = Zlength (Znth i input)) ->
  pop_fill_rows_list input rec rows (Zlength input) j =
  crop_mx (fill_rows_list k c xh input rec rows) lens.
Proof.
  move => input rec rows lens j k c xh Hc Hinlen Hlenlen Hreclen Hrowlen Hxhk Hinbound Hlenspec.
  have Hlenin: 0 <= Zlength input by list_solve.
  have Hk: 0 <= k by list_solve.
  pose proof (fill_rows_list_wf xh input rec rows Hk Hc) as [Hfillen [_ Hfillin]].
  apply Znth_eq_ext; rewrite mkseqZ_Zlength //.
  - rewrite Zlength_map Zlength_Ziota; lia. 
  - move => i Hi.
    have Hlennth: 0 <= Zlength (Znth i input) by list_solve.
    apply Znth_eq_ext; rewrite !mkseqZ_Znth // !mkseqZ_Zlength //.
    + rewrite Znth_map; last first. rewrite Zlength_Ziota; lia.
      rewrite Zlength_sublist Znth_Ziota; try lia; rewrite Hlenspec //=; try lia;
      have->: 0 + i = i by lia. lia.
      move: Hfillin. rewrite Forall_Znth Hfillen. move: Hi. rewrite Hinlen => Hi.
      move => /(_ _ Hi) ->. move: Hinbound. by rewrite Forall_Znth Hinlen => /(_ _ Hi).
    + move => y Hy. rewrite mkseqZ_Znth //.
      rewrite Znth_map; last first. rewrite Zlength_Ziota; lia.
      rewrite Znth_Ziota; try lia. have->: (0 + i) = i by lia.
      rewrite Hlenspec // Znth_sublist; try lia.
      have->:(y+0) = y by lia.
      have->:Znth y (Znth i (fill_rows_list k c xh input rec rows)) = get (fill_rows_list k c xh input rec rows) i y.
        by rewrite /get.
      rewrite mk_lmatrix_get; try lia; last first.
      have: Zlength (Znth i input) <= c; try lia. move: Hinbound. by rewrite Forall_Znth => /(_ _ Hi).
      rewrite Hrowlen. case : (Zindex i rows <? xh) /Z.ltb_spec0 => [Hidxh | Hidxh].
      * case : (Z_lt_le_dec (Zindex i rows) xh); try lia. move => /= _.
        have->//:(Zindex i rows <? Zlength input). apply /Z.ltb_spec0. lia.
      * case : (Z_lt_le_dec (Zindex i rows) xh) => [|//]; try lia.
Qed.


