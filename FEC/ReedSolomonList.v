Require Import VST.floyd.functional_base.

From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import Vandermonde.
Require Import Common.
Require Import ListMatrix.
Require Import ReedSolomon.
Require Import VandermondeList.
Require Import Gaussian.
Require Import CommonSSR.


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

Section Decoder.

(*Intermediate functions*)

(*Get lost and found packets*)
Definition find_lost_found_aux (f: Z -> bool) (g: Z -> Z) base l (k: Z) : list Z :=
  fold_left (fun acc x => if f (Znth x l) then acc ++ [:: g x] else acc) (Ziota 0 k) base.

Lemma find_lost_found_aux_bound: forall f g base l k b,
  0 <= k ->
  (forall x, 0 <= x < k -> 0 <= g x < b) ->
  (forall x, In x base -> 0 <= x < b) ->
  Forall (fun x : Z => 0 <= x < b) (find_lost_found_aux f g base l k).
Proof.
  move => f g base l k b Hk Hg Hbase. rewrite /find_lost_found_aux Forall_forall. move: Hbase.
  have: forall x, In x (Ziota 0 k) -> 0 <= x < k. move => y. by rewrite Zseq_In. move : base.
  elim : (Ziota 0 k) => [//= | h t /= IH base Hall Hbase x].
  apply IH. move => y Hin. apply Hall. by right.
  move => y.
  case Hfh: (f (Znth h l)); move => Hin.
  - apply in_app_or in Hin. case: Hin => [Hyb | Hyh]. by apply Hbase.
    case : Hyh => [Hyh | Hfalse ]; rewrite //=. subst. apply Hg. apply Hall. by left.
  - by apply Hbase.
Qed. 

(*First, get the lost packets*)
Definition find_lost (stats: list Z) (k: Z) : list Z :=
  find_lost_found_aux (fun x => Z.eq_dec x 1%Z) id nil stats k.

Lemma find_lost_bound: forall l k,
  0 <= k ->
  Forall (fun x : Z => 0 <= x < k) (find_lost l k).
Proof.
  move => l k Hk. by apply find_lost_found_aux_bound.
Qed.

(*the first part of the found array*)
Definition find_found (stats: list Z) (k: Z) : list Z :=
  find_lost_found_aux (fun x => negb (Z.eq_dec x 1%Z)) id nil stats k.

Lemma find_found_bound: forall l k,
  0 <= k ->
  Forall (fun x : Z => 0 <= x < k) (find_found l k).
Proof.
  move => l k Hk. by apply find_lost_found_aux_bound.
Qed.

Instance Inhabitant_option: forall {A: Type}, Inhabitant (option A).
intros A. apply None.
Defined.

(*Parities are represented as a list (option (list Z)), representing whether the parity packet is there
  or not. We will translate this into Vundef or Vptr as needed*)
Definition find_parities (par: list (option (list Z))) (c: Z) (max_n : Z) : (list Z * list Z) :=
  fold_left (fun (acc: seq Z * seq Z) (x : Z) => let (rows, found) := acc in match (Znth x par) with
                                       | None => (rows, found)
                                       | _ => (rows ++ [:: x], found ++ [:: max_n - 1 - x])
                                        end) (Ziota 0 c) (nil, nil).


(*Bounds - TODO: can we abstract this*)
Lemma find_parities_bound_fst: forall par c max_n,
  0 <= c ->
  Forall (fun x => 0 <= x < c) (fst (find_parities par c max_n)).
Proof.
  move => par c max_n Hc. rewrite /find_parities Forall_forall. remember [::] as s. rewrite {1}Heqs {1}Heqs {2}Heqs.
  have: forall x, In x (Ziota 0 c) -> 0 <= x < c by (move => y; rewrite Zseq_In).
  have: forall x, In x s -> 0 <= x < c by rewrite Heqs. 
  rewrite {Heqs}. remember [::] as s'. rewrite {1}Heqs' {1}Heqs' {Heqs'}. (*need generic base cases*) 
  move: s s'. elim : (Ziota 0 c) => [//= | h t /= IH s s' Hs Hall x].
  case : (Znth h par) => [ l /= | /=].
  - apply IH. move => y Hin. apply in_app_or in Hin. case : Hin => [Hys | Hyh].
    + by apply Hs.
    + case : Hyh => [Hyh | Hf]; rewrite //=. subst. apply Hall. by left.
    + move => y Hin. apply Hall. by right.
  - apply IH. by []. move => y Hy. apply Hall. by right.
Qed.

Lemma find_parities_bound_snd: forall par c max_n,
  0 <= c < max_n ->
  Forall (fun x => 0 <= x < max_n) (snd (find_parities par c max_n)).
Proof.
  move => par c max_n Hc. rewrite /find_parities Forall_forall. remember [::] as s. rewrite {1}Heqs {1}Heqs {1}Heqs.
  have: forall x, In x (Ziota 0 c) -> 0 <= x < c by move => y; rewrite Zseq_In; lia.
  have: forall x, In x s -> 0 <= x < max_n by rewrite Heqs. 
  rewrite {Heqs}. remember [::] as s'. rewrite {1}Heqs' {1}Heqs' {Heqs'}. (*need generic base cases*) 
  move: s s'. elim : (Ziota 0 c) => [//= | h t /= IH s s' Hs Hall x].
  case : (Znth h par) => [ l /= | /=].
  - apply IH. move => y Hin. apply in_app_or in Hin. case : Hin => [Hys | Hyh].
    + by apply Hs.
    + case : Hyh => [Hyh | Hf]; rewrite //=. subst. have Hh: 0 <= h < c by (apply Hall; left). lia.
    + move => y Hin. apply Hall. by right.
  - apply IH. by []. move => y Hy. apply Hall. by right.
Qed.

(*TODO: move*)
Lemma forall_lt_leq_trans: forall n m (l: list Z),
  n <= m ->
  Forall (fun x : Z => 0 <= x < n) l ->
  Forall (fun x : Z => 0 <= x < m) l.
Proof.
  move => n m l Hnm. rewrite !Forall_forall => Hall x Hin.
  apply Hall in Hin. lia.
Qed. 


(*The ListMatrix version of [submx_rows_cols] TODO maybe move*)
Definition submx_rows_cols_list (mx: matrix F) m n (rows: list Z) (cols: list Z) : matrix F :=
  mk_matrix m n (fun x y => get mx (Znth x rows) (Znth y cols)) .

(*TODO: definition move*)
Lemma submx_rows_cols_list_wf: forall mx m n rows cols,
  0 <= m ->
  0 <= n ->
  wf_matrix (submx_rows_cols_list mx m n rows cols) m n.
Proof.
  move => mx m n rows cols. by apply mk_matrix_wf.
Qed.

Lemma ord_zero_proof n (H: 0 < n) : (0 < Z.to_nat n)%N.
Proof.
  apply /ltP. lia.
Qed.

Definition ord_zero n (H: 0 < n) : 'I_(Z.to_nat n) :=
  Ordinal (ord_zero_proof H).

(*Need to transform a list of Z into a list of 'I_m*)
Definition Z_ord_list (l: list Z) (n: Z) : seq 'I_(Z.to_nat n) :=
  pmap insub (map Z.to_nat l).

(*See what we need - will be something like this - maybe for Znth instead*)
Lemma Z_ord_list_spec: forall (l: seq Z) n,
  0 <= n ->
  Forall (fun x => 0 <= x < n) l ->
  map (fun i => Z.of_nat (nat_of_ord i)) (Z_ord_list l n) = l.
Proof.
  move => l n Hn. elim : l => [//| /= h t IH Hall].
  rewrite /Z_ord_list /=. have Hhn: 0 <= h < n. move: Hall; rewrite Forall_forall =>/(_ h) Hh.
  apply Hh. by left.
  rewrite insubT.  apply /ltP. lia.
  move => Hh. rewrite /= IH. by rewrite Z2Nat.id; try lia. by inversion Hall.
Qed.

Lemma nth_nth: forall {A: Type} (d: A) (l: seq A) (n: nat),
  nth d l n = List.nth n l d.
Proof.
  move => A d l. elim : l => [//= n | //= h t IH n].
  - by case : n.
  - case: n. by []. move => n. by rewrite /= IH.
Qed.

Lemma Z_ord_list_Znth: forall (l: seq Z) n i (Hn: 0 < n),
  0 <= i ->
  Forall (fun x => 0 <= x < n) l ->
  Znth i l = Z.of_nat (nth (ord_zero Hn) (Z_ord_list l n) (Z.to_nat i)).
Proof.
  move => l n i Hn Hi Hall. rewrite -{1}(@Z_ord_list_spec l n) //. 2: lia.
  rewrite /Znth. case : (zlt i 0); try lia. move =>H{H}.
  rewrite nth_nth.
  have <-: Z.of_nat (ord_zero Hn) = Inhabitant_Z by []. by rewrite map_nth.
Qed.

Lemma Z_list_bound: forall (l: seq Z) n i,
  Forall (fun x => 0 <= x < n) l ->
  0 <= i < Zlength l ->
  (Z.to_nat (Znth i l) < Z.to_nat n)%N.
Proof.
  move => l n i. rewrite Forall_Znth => /(_ i) Hin Hi. apply /ltP. lia.
Qed.

Lemma Z_ord_list_Zlength: forall n l,
  Forall (fun x : Z => 0 <= x < n) l ->
  Zlength (Z_ord_list l n) = Zlength l.
Proof.
  move => n l Hall. rewrite /Z_ord_list !Zlength_correct -!size_length. f_equal.
  rewrite size_pmap_sub. 
  have->: count (fun x : nat => (x < Z.to_nat n)%N) [seq Z.to_nat i | i <- l] = size [seq Z.to_nat i | i <- l].
  { apply /eqP. rewrite -all_count all_in => x Hin. apply in_mem_In in Hin. move: Hin; rewrite in_map_iff =>
    [[x' [Hx' Hin]]]. subst. move: Hall; rewrite Forall_forall => /(_ x' Hin) => Hx'. apply /ltP; lia. }
  by rewrite size_map.
Qed.

Lemma nth_pmap: forall (aT rT: eqType) (f: aT -> option rT) (s: seq aT) (i: nat) (a: aT) (r: rT),
  all f s ->
  (i < size s)%N ->
  Some (nth r (pmap f s) i) = f (nth a s i).
Proof.
  move => aT rT f s i a r. move: i. elim : s =>[//= | h t /= IH i /andP[Hh Hall]]. rewrite ltnS => Hi.
  move : Hh. case Hh: (f h) => [h' /= | //=]. move => Htriv. 
  have: (0 <= i)%N by []. rewrite leq_eqVlt => /orP[/eqP Hi0 | Hi'].
  - subst. by rewrite /= Hh.
  - have->: (i = (i.-1).+1)%N by rewrite (ltn_predK Hi'). rewrite /=. rewrite IH //.
    have Hi1: (i.-1 < i)%N by apply pred_lt. by apply (ltn_leq_trans Hi1).
Qed.

Lemma some_inj: forall {A: Type} (x y: A),
  Some x = Some y ->
  x = y.
Proof.
  move => A x y Hop. by case : Hop.
Qed.

Lemma Z_ord_list_Znth': forall (l: seq Z) n i `{Inhabitant 'I_(Z.to_nat n)} (Hi: 0 <= i < Zlength l)
  (Hall: Forall (fun x => 0 <= x < n) l),
  0 <= n ->
  Znth i (Z_ord_list l n) = Ordinal (Z_list_bound Hall Hi).
Proof.
  move => l n i Hinh Hi Hall Hn. have: n = 0%Z \/ 0 < n by lia. move => [Hn0 | {}Hn].
  + subst. case : Hinh. move => m Hm. have: (m < Z.to_nat 0)%coq_nat by apply /ltP. lia.
  + rewrite -nth_Znth. 2: by rewrite Z_ord_list_Zlength.
    rewrite -nth_nth /Z_ord_list. apply some_inj. rewrite (nth_pmap 0%N).
    * rewrite (nth_map 0%Z); last first. rewrite size_length -ZtoNat_Zlength. apply /ltP. lia.
      rewrite insubT.
      -- rewrite nth_nth nth_Znth. 2: lia. by apply Z_list_bound.
      -- move => Hord. rewrite /=. f_equal. apply ord_inj.
         by rewrite /= nth_nth nth_Znth.
    * rewrite all_in => x. rewrite in_mem_In in_map_iff => [[x' [Hx' Hin]]]. subst.
      rewrite insubT =>[|//]. apply /ltP. move: Hall; rewrite Forall_forall => /(_ x' Hin). lia.
    * rewrite size_map size_length -ZtoNat_Zlength. apply /ltP. lia.
Qed.

Lemma submx_rows_cols_list_equiv: forall mx m n m' n' rows cols (Hm: 0 < m) (Hn: 0 < n),
  0 <= m' ->
  0 <= n' ->
  Forall (fun x => 0 <= x < m) rows ->
  Forall (fun x => 0 <= x < n) cols ->
  matrix_to_mx m' n' (submx_rows_cols_list mx m' n' rows cols) = 
    submx_rows_cols (Z.to_nat m') (Z.to_nat n') (matrix_to_mx m n mx)
       (Z_ord_list rows m) (Z_ord_list cols n) (ord_zero Hm) (ord_zero Hn).
Proof.
  move => mx m n m' n' rows cols Hm Hn Hm' Hn' Hrows Hcols. apply mk_matrix_mx =>[//|//| x y Hx Hy].
  rewrite !mxE. f_equal.
  - rewrite (Z_ord_list_Znth Hm) =>[//| |//]. lia.
  - rewrite (Z_ord_list_Znth Hn) => [//||//]. lia.
Qed.

(*Take columns from end instead of beginning - large mx is m x n, submx is m' x n'*)
Definition submx_rows_cols_rev_list (mx: matrix F) m' n' n rows cols :=
  submx_rows_cols_list mx m' n' rows (map (fun x => n - x - 1) cols).

Lemma submx_rows_cols_rev_list_wf: forall mx m' n' n rows cols,
  0 <= m' ->
  0 <= n' ->
  wf_matrix (submx_rows_cols_rev_list mx m' n' n rows cols) m' n'.
Proof.
  move => mx m' n' n rows cols.
  apply submx_rows_cols_list_wf.
Qed.

Lemma Z_ord_list_rev: forall n cols,
 Forall (fun x : Z => 0 <= x < n) cols ->
  Z_ord_list [seq n - x0 - 1 | x0 <- cols] n = [seq rev_ord x0 | x0 <- Z_ord_list cols n].
Proof.
  move => n cols Hall.
  have Hn: n <= 0 \/ 0 < n by lia. case : Hn => [H0n | Hn].
  - move : Hall; case : cols =>[// | h t /=].
    rewrite Forall_forall => /( _ h) Hin.
    have Hh: 0 <= h < n. apply Hin; by left. lia.
  - have Hinh: Inhabitant 'I_(Z.to_nat n). have H0n: (0 < Z.to_nat n)%N by (apply /ltP; lia).
      apply (Ordinal H0n).
    have Hall': Forall (fun x : Z => 0 <= x < n) [seq n - x0 - 1 | x0 <- cols]. {
      move : Hall. rewrite !Forall_forall => Hall x. rewrite in_map_iff => [[x' [Hx' Hin]]].
      subst. apply Hall in Hin. lia. }
    apply Znth_eq_ext.
    + by rewrite Zlength_map !Z_ord_list_Zlength // Zlength_map.
    + move => i. rewrite Z_ord_list_Zlength // Zlength_map => Hi.
      rewrite Znth_map. 2: by rewrite Z_ord_list_Zlength.
      rewrite !Z_ord_list_Znth'; try lia. rewrite Zlength_map; lia.
      move => Hi'. apply ord_inj. rewrite /=.
      rewrite Znth_map //.
      have Hnth: 0 <= Znth i cols < n. by move : Hall; rewrite Forall_Znth => /(_ i Hi).
      have->: (Z.to_nat n - (Z.to_nat (Znth i cols)).+1)%N = (Z.to_nat n - (Z.to_nat (Znth i cols)).+1)%coq_nat by [].
      lia.
Qed.

(*m and n are dimensions of the whole matrix, m' and n' are the new dimensions of the submatrix*)
Lemma submx_rows_cols_rev_list_spec: forall mx m n m' n' rows cols (Hm: 0 < m) (Hn: 0 < n),
  0 <= m'->
  0 <= n'->
  Forall (fun x => 0 <= x < m) rows ->
  Forall (fun x => 0 <= x < n) cols ->
  matrix_to_mx m' n' (submx_rows_cols_rev_list mx m' n' n rows cols) =
  submx_rows_cols_rev (Z.to_nat m') (Z.to_nat n') (matrix_to_mx m n mx)
    (Z_ord_list rows m) (Z_ord_list cols n) (ord_zero Hm) (ord_zero Hn).
Proof.
  move => mx m n m' n' rows cols Hm Hn Hm' Hn' Hrows Hcols.
  rewrite /submx_rows_cols_rev_list /submx_rows_cols_rev.
  apply mk_matrix_mx; try lia. move => x y Hx Hy.
  rewrite mxE /=. f_equal.
  - rewrite (Z_ord_list_Znth Hm) =>[//| |//]. lia.
  - rewrite (Z_ord_list_Znth Hn); try lia. 
    + f_equal. f_equal. f_equal. by apply Z_ord_list_rev.
    + move: Hcols. rewrite !Forall_forall => Hcols i. rewrite in_map_iff => [[x' [Hx' Hin]]].
      subst. apply Hcols in Hin. lia.
Qed.


(*Concatenate two matrices*)
Definition row_mx_list (left: matrix F) (right: matrix F) m n1 n2 : matrix F :=
  mk_matrix m (n1 + n2) (fun x y => if Z_lt_ge_dec y n1 then get left x y else get right x (y - n1)).

Lemma row_mx_list_wf: forall left right m n1 n2,
  0 <= m ->
  0 <= n1 ->
  0 <= n2 ->
  wf_matrix (row_mx_list left right m n1 n2) m (n1 + n2).
Proof.
  move => l r m n1 n2 Hm Hn1 H2. apply mk_matrix_wf; lia.
Qed.

(*Need a cast bc it cannot unify Z.to_nat n + Z.to_nat m with Z.to_nat (n + m)*)
Lemma row_mx_list_spec: forall left right m n1 n2 (Hn1: 0 <= n1) (Hn2: 0 <= n2),
  0 <= m ->
  matrix_to_mx m (n1 + n2) (row_mx_list left right m n1 n2) =
    castmx (Logic.eq_refl _, Logic.eq_sym (Z2Nat.inj_add n1 n2 Hn1 Hn2))
    (row_mx (matrix_to_mx m n1 left) (matrix_to_mx m n2 right)).
Proof.
  move => l r m n1 n2 Hn1 Hn2 Hm. rewrite -matrixP => x y.
  rewrite castmxE !mxE /= mk_matrix_get.
  - case: (Z_lt_ge_dec (Z.of_nat y) n1) =>[ Hy /=|Hy  /=].
    + pose proof (splitP (cast_ord (esym (Logic.eq_sym (Z2Nat.inj_add n1 n2 Hn1 Hn2))) y)).
      case : X =>[j /= Hyj | k /= Hyk]. by rewrite Hyj cast_ord_id mxE.
      rewrite Hyk in Hy. move: Hy. rewrite Nat2Z.inj_add Z2Nat.id; lia. (*Why can't lia do this automatically?*)
    + pose proof (splitP (cast_ord (esym (Logic.eq_sym (Z2Nat.inj_add n1 n2 Hn1 Hn2))) y)).
      case : X =>[j /= Hyj | k /= Hyk]. 
      * have: (j < Z.to_nat n1)%N by []. rewrite -Hyj => /ltP Hyn1. lia.
      * rewrite cast_ord_id mxE Hyk. f_equal. rewrite Nat2Z.inj_add. lia. (*again, why do I need to rewrite?*)
  - by apply Z_ord_bound.
  - apply Z_ord_bound. lia.
Qed.

(*Concatenate two matrices - up/down*)
Definition col_mx_list (top: matrix F) (bottom: matrix F) m1 m2 n : matrix F :=
  mk_matrix (m1 + m2) n (fun x y => if Z_lt_ge_dec x m1 then get top x y else get bottom (x - m1) y).

Lemma col_mx_list_wf: forall top bottom m1 m2 n,
  0 <= m1 ->
  0 <= m2 ->
  0 <= n ->
  wf_matrix (col_mx_list top bottom m1 m2 n) (m1 + m2) n.
Proof.
  move => t u m1 m2 n Hm1 Hm2 Hn. apply mk_matrix_wf; lia.
Qed.

(*Need a cast bc it cannot unify Z.to_nat n + Z.to_nat m with Z.to_nat (n + m)*)
Lemma col_mx_list_spec: forall top bottom m1 m2 n (Hm1: 0 <= m1) (Hm2: 0 <= m2),
  0 <= n ->
  matrix_to_mx (m1 + m2) n (col_mx_list top bottom m1 m2 n) =
    castmx (Logic.eq_sym (Z2Nat.inj_add m1 m2 Hm1 Hm2), Logic.eq_refl)
    (col_mx (matrix_to_mx m1 n top) (matrix_to_mx m2 n bottom)).
Proof.
  move => t u m1 m2 n Hm1 Hm2 Hn. rewrite -matrixP => x y.
  rewrite castmxE !mxE /= mk_matrix_get.
  - pose proof (splitP (cast_ord (esym (Logic.eq_sym (Z2Nat.inj_add m1 m2 Hm1 Hm2))) x)).
    case : X => [j /= Hj | k /= Hk]; rewrite !mxE.
    + case: (Z_lt_ge_dec (Z.of_nat x) m1) =>[ Hx /=|Hx  /=].
      * by rewrite Hj.
      * have: (0 <= Z.of_nat j < m1)%Z by apply Z_ord_bound. lia.
    + case: (Z_lt_ge_dec (Z.of_nat x) m1) =>[ Hx /=|Hx  /=].
      * rewrite Hk in Hx. rewrite Nat2Z.inj_add in Hx. lia.
      * rewrite Hk. f_equal. rewrite Nat2Z.inj_add. lia.
  - apply Z_ord_bound. lia.
  - by apply Z_ord_bound.
Qed.

(*The identity matrix*)
Definition id_list (n: Z) := mk_matrix n n (fun x y => if Z.eq_dec x y then (GRing.one F) else (GRing.zero F)).

Lemma id_list_wf: forall n,
  0 <= n ->
  wf_matrix (id_list n) n n.
Proof.
  move => n Hn. by apply mk_matrix_wf.
Qed.

Lemma id_list_spec: forall n,
  0 <= n ->
  matrix_to_mx n n (id_list n) = (1%:M)%R.
Proof.
  move => n Hn. rewrite -matrixP => x y.
  rewrite id_A mxE mk_matrix_get.
  - case : (Z.eq_dec (Z.of_nat x) (Z.of_nat y)) => [Hxy /= | Hxy /=].
    + have->: x == y. apply /eqP. apply ord_inj. lia. by [].
    + have->:x == y = false. apply /eqP. move => C. rewrite C in Hxy. lia. by [].
  - by apply Z_ord_bound.
  - by apply Z_ord_bound.
Qed.

(*We want to invert a matrix by concatenating it with the identity, then running gaussian elimination. We define
  each part separately to make the VST proof cleaner*)
Definition concat_mx_id (mx: matrix F) n :=
  row_mx_list mx (id_list n) n n n.

(*NOTE: (delete later) - dont need to worry about reversal here, everything will be
  wrapped in [rev_mx_val] or whatever - only place to worry about is with portion of weight mx, since
  that is actually reversed*)

(*Get the right submatrix of an n x (n + n) matrix*)
Definition right_submx n (mx: matrix F) :=
  mk_matrix n n (fun x y => get mx x (n + y)).

Lemma right_submx_wf: forall n mx,
  0 <= n ->
  wf_matrix (right_submx n mx) n n.
Proof.
  move => n mx Hn. by apply mk_matrix_wf.
Qed.

(*We again need a cast to unify (Z.to_nat (n + n)) and Z.to_nat n + Z.to_nat n*)
Lemma right_submx_spec: forall n mx (Hn: 0 <= n),
  matrix_to_mx n n (right_submx n mx) = 
  rsubmx (castmx (Logic.eq_refl _, (Z2Nat.inj_add n n Hn Hn)) (matrix_to_mx n (n + n) mx)).
Proof.
  move => n mx Hn. rewrite -matrixP => x y.
  rewrite !mxE castmxE mxE /= mk_matrix_get. f_equal; try lia. rewrite Nat2Z.inj_add; lia.
  by apply Z_ord_bound. by apply Z_ord_bound.
Qed.

Definition find_invmx_list (mx: matrix F) n :=
  right_submx n (gauss_restrict_rows n (n + n) (concat_mx_id mx n)).


Lemma cast_eq: forall m n m' n' (A: 'M[F]_(m, n)) (B: 'M[F]_(m', n')) (Heq: (m = m') * (n = n')),
  (forall (x: 'I_m) (y: 'I_n), A x y = B (cast_ord (fst Heq) x) (cast_ord (snd Heq) y)) ->
  castmx Heq A = B.
Proof.
  move => m n m' n' A B Heq Hab. rewrite -matrixP => x y.
  rewrite castmxE Hab /=. f_equal; by apply ord_inj.
Qed.

(*TODO: move to Gaussian*)

Definition cast_seq n n' (H: n = n') (s: seq 'I_n)  : seq 'I_n' :=
  map (cast_ord H) s.

Lemma foldr_castmx: forall m n m' n' (A: 'M[F]_(m, n)) (Heq: (m = m') * (n = n')) 
  (f: 'I_m -> 'M[F]_(m, n) -> 'M[F]_(m, n)) (g: 'I_m' -> 'M[F]_(m', n') -> 'M[F]_(m', n')) (l: seq 'I_m),
  (forall (x: 'I_m) (A: 'M[F]_(m, n)), castmx Heq (f x A) = g (cast_ord (fst Heq) x) (castmx Heq A)) ->
  castmx Heq (foldr f A l) = foldr g (castmx Heq A) (cast_seq (fst Heq) l).
Proof.
  move => m n m' n' A Heq f g l Hfg. elim : l => [//= | h t IH /=].
  by rewrite Hfg IH.
Qed.

(*Probably can abstract this as functor or monad or something*)
Definition cast_option n n' (H: n = n')  (o: option 'I_n) : option 'I_n' :=
  match o with
  | None => None
  | Some x => Some ((cast_ord H) x)
  end.

Lemma cast_option_none: forall n n' (H: n = n') (o: option 'I_n),
  (cast_option H o == None) = (o == None).
Proof.
  move => n n' H o. by case : o.
Qed.

Lemma cast_option_some: forall n n' (H: n = n') (o: option 'I_n) c,
  cast_option H o = Some c ->
  exists d, o = Some d /\ (cast_ord H) d = c.
Proof.
  move => n n' H o c. case : o =>[d //= Hsome | //=]. exists d. case: Hsome. by move ->.
Qed.

(*Working with casts is very annoying*)
Lemma lead_coef_cast: forall m n m' n' (H: (m = m') * (n = n')) (A: 'M[F]_(m, n)) (r: 'I_m),
  lead_coef A r = cast_option (esym (snd H)) (lead_coef (castmx H A) (cast_ord (fst H) r)).
Proof.
  move => m n m' n' H A r.
  case Hlc: (lead_coef A r) =>[c /= | //=].
  - move: Hlc. rewrite lead_coef_some_iff => [[Hrc Hbefore]].
    symmetry. case Hlc : (lead_coef (castmx H A) (cast_ord H.1 r)) => [d /= | //=].
    + move : Hlc. rewrite lead_coef_some_iff => [[Hrd Hbef]].
      move : Hrd; rewrite castmxE /= => Hrd.
      case (orP (ltn_total c  (cast_ord (esym (snd H)) d))).
      * move => /orP[Hlt | Heq].
        -- have: A r c == 0%R. apply /eqP.  move: Hbef => /(_ (cast_ord (snd H) c)).
           rewrite castmxE !cast_ordK => Hzero. by apply Hzero.
            move : Hrc; by case : (A r c == 0%R).
        -- apply (elimT eqP) in Heq. f_equal. by apply ord_inj.
      * move => Hdc. have:  A (cast_ord (esym H.1) (cast_ord H.1 r)) (cast_ord (esym H.2) d) == 0%R.
        apply /eqP. move : Hbefore => /(_ _ Hdc). by rewrite !cast_ordK.
        move: Hrd. by case : (A (cast_ord (esym H.1) (cast_ord H.1 r)) (cast_ord (esym H.2) d) == 0%R).
    + move: Hlc. rewrite lead_coef_none_iff => /(_ (cast_ord (snd H) c)). rewrite castmxE !cast_ordK => Hrc'. move: Hrc.
      by rewrite Hrc' eq_refl.
  - move: Hlc. rewrite lead_coef_none_iff => [Hall]. symmetry. apply /eqP. rewrite cast_option_none. apply /eqP.
    rewrite lead_coef_none_iff. move => x. rewrite castmxE !cast_ordK. apply Hall.
Qed.

Lemma cast_leq: forall m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N),
  (m' <= n')%N.
Proof.
  move => m n m' n' [Hm Hn]. by rewrite Hm Hn.
Qed.

Lemma cast_seq_pmap: forall n n' (H: n = n') (l: list nat),
  cast_seq H (pmap insub l) = pmap insub l.
Proof.
  move => n n' H l. elim : l => [//= | h t Ih /=].
  case Hh: (h < n)%N.
  - rewrite !insubT /=. by rewrite -H. move => Hn'. rewrite Ih /=. f_equal.
    by apply ord_inj.
  - by rewrite !insubF // -H.
Qed.  

Lemma cast_ord_enum: forall n n' (H: n = n'),
  cast_seq H (ord_enum n) = ord_enum n'.
Proof.
  move => n n' H. rewrite /ord_enum. by rewrite cast_seq_pmap H.
Qed.

Lemma cast_ord_switch: forall n n' (H: n = n') x y,
  (cast_ord (esym H) x == y) = (x == cast_ord H y).
Proof.
  move => n n' H x y.
  case Hx : (x == cast_ord H y).
  - apply /eqP. apply (elimT eqP) in Hx. rewrite Hx. apply cast_ordK.
  - apply /eqP. apply (elimF eqP) in Hx. move => C. move: Hx. by rewrite -C cast_ordKV.
Qed.

Lemma sc_mul_castmx: forall m n m' n' (Heq: (m = m') * (n = n')) (A: 'M[F]_(m, n)) c (r: 'I_m),
  castmx Heq (sc_mul A c r) = sc_mul (castmx Heq A) c (cast_ord (fst Heq) r).
Proof.
  move => m n m' n' Heq A c r. rewrite -matrixP => x y.
  by rewrite castmxE !mxE cast_ord_switch !castmxE.
Qed.

Lemma mk_identity_castmx: forall m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N) (A: 'M[F]_(m, n)) x,
  castmx Heq (mk_identity A Hmn x) = mk_identity (castmx Heq A) (cast_leq Heq Hmn) x.
Proof.
  move => m n m' n' Heq Hmn A x. rewrite /mk_identity -(cast_seq_pmap (fst Heq)).
  apply foldr_castmx. move => x' A'. rewrite sc_mul_castmx. f_equal.
  rewrite castmxE /= !cast_ordK. f_equal. f_equal. by apply ord_inj.
Qed.

Lemma add_mul_castmx: forall m n m' n' (Heq: (m = m') * (n = n'))
  (A: 'M[F]_(m, n)) c (r1 r2: 'I_m),
  castmx Heq (add_mul A c r1 r2) =
  add_mul (castmx Heq A) c (cast_ord Heq.1 r1) (cast_ord Heq.1 r2).
Proof.
  move => m n m' n' Heq A c r1 r2. rewrite -matrixP => x y.
  by rewrite castmxE !mxE cast_ord_switch !castmxE !cast_ordK.
Qed.

Lemma sub_all_rows_noif_castmx: forall  m n m' n' (Heq: (m = m') * (n = n'))
  (A: 'M[F]_(m, n)) (x: 'I_m),
  castmx Heq (sub_all_rows_noif A x) = sub_all_rows_noif (castmx Heq A) (cast_ord Heq.1 x).
Proof.
  move => m n m' n' Heq A x. rewrite /sub_all_rows_noif -(cast_ord_enum (fst Heq)).
  apply foldr_castmx => x' A'.
  case Hx: (x' == x).
  - apply (elimT eqP) in Hx. by have->: cast_ord Heq.1 x' == cast_ord Heq.1 x by rewrite Hx.
  - apply (elimF eqP) in Hx. have->: cast_ord Heq.1 x' == cast_ord Heq.1 x = false.
    case Hx': (cast_ord Heq.1 x' == cast_ord Heq.1 x) =>[|//]. apply (elimT eqP) in Hx'.
    by apply cast_ord_inj in Hx'.
    apply add_mul_castmx.
Qed.

Lemma all_cols_one_noif_castmx: forall  m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N) 
  (A: 'M[F]_(m, n)) (x: 'I_n),
  castmx Heq (all_cols_one_noif A x) =
  all_cols_one_noif (castmx Heq A) (cast_ord Heq.2 x).
Proof.
  move => m n m' n' Heq Hmn A x. rewrite /all_cols_one_noif -(cast_ord_enum (fst Heq)).
  apply foldr_castmx => x' A'. by rewrite sc_mul_castmx castmxE !cast_ordK.
Qed. 

Lemma gauss_one_step_restrict_castmx: forall  m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N) 
  (A: 'M[F]_(m, n)) (x: 'I_m),
  castmx Heq (gauss_one_step_restrict A x Hmn) =
  gauss_one_step_restrict (castmx Heq A) (cast_ord Heq.1 x) (cast_leq Heq Hmn).
Proof.
  move => m n m' n' Heq Hmn A x. rewrite /gauss_one_step_restrict sub_all_rows_noif_castmx
  all_cols_one_noif_castmx //=. f_equal. f_equal. by apply ord_inj.
Qed.
 

(*foldl version, this time with a nat function for [gauss_all_steps_restrict]*)
Lemma foldl_castmx: forall m n m' n' (A: 'M[F]_(m, n)) (Heq: (m = m') * (n = n')) 
  (f: 'M[F]_(m, n) -> nat -> 'M[F]_(m, n)) (g:  'M[F]_(m', n') -> nat -> 'M[F]_(m', n')) (l: seq nat),
  (forall (x: nat) (A: 'M[F]_(m, n)), castmx Heq (f A x) = g (castmx Heq A) x) ->
  castmx Heq (foldl f A l) = foldl g (castmx Heq A)  l.
Proof.
  move => m n m' n' A Heq f g l Hfg. move : A. elim : l => [//= | h t IH A /=].
  by rewrite IH Hfg. 
Qed.

Lemma gauss_all_steps_restrict_castmx: forall m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N) (A: 'M[F]_(m, n)) x y,
  castmx Heq (gauss_all_steps_restrict_aux A Hmn x y) =
  gauss_all_steps_restrict_aux (castmx Heq A) (cast_leq Heq Hmn) x y.
Proof.
  move => m n m' n' Heq Hmn A x y. apply foldl_castmx => x' A'.
  case Hx': (x' < m)%N.
  - rewrite !insubT. by rewrite -(fst Heq). move => Hxm'.
    rewrite gauss_one_step_restrict_castmx /=. f_equal. by apply ord_inj.
  - rewrite !insubF //. by rewrite -Heq.1.
Qed.


Lemma castmx_gaussian_restrict: forall m n m' n' (A: 'M[F]_(m, n)) (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N),
  castmx Heq (gaussian_elim_restrict A Hmn) = gaussian_elim_restrict (castmx Heq A) (cast_leq Heq Hmn).
Proof.
  move => m n m' n' A Heq Hmn. rewrite /gaussian_elim_restrict. rewrite -matrixP => x y.
  rewrite mk_identity_castmx. f_equal. f_equal. 2: by rewrite (fst Heq).
  rewrite /gauss_all_steps_restrict_end. rewrite gauss_all_steps_restrict_castmx. f_equal.
  by rewrite Heq.1.
Qed.

Lemma submx_remove_col_rowmx: forall m n (A B: 'M[F]_(m, n)) (Hmn: (m <= n)%N) (Hmn' : (m <= n + n)%N) r j,
  submx_remove_col A Hmn r j =
  submx_remove_col (row_mx A B) Hmn' r j.
Proof.
  move => m n A B Hmn Hmn' r j. rewrite -matrixP => x y.
  rewrite !mxE /=. case Hyj: (y < j)%N.
  - pose proof (splitP (widen_ord (ltnW (ltn_leq_trans (ltn_ord r) Hmn')) y)).
    case : X => [j' /= Hj' | k /= Hk].
    + f_equal. by apply ord_inj.
    + have Hny: (n <= y)%N by rewrite Hk leq_addr.
      have: (y < n)%N. have Hyr : (y < r)%N by [].
        have Hym: (y < m)%N by apply (ltn_trans Hyr). by apply (ltn_leq_trans Hym).
      by rewrite ltnNge Hny.
  - pose proof (splitP (ord_widen_succ (ltn_leq_trans (ltn_ord r) Hmn') y)).
    case : X => [j' /= Hj' | k /= Hk].
    + f_equal. by apply ord_inj.
    + have: (y.+1 < n)%N. have Hyr: (y < r)%N by [].
      have Hym: (y.+1 < m)%N by apply (leq_ltn_trans Hyr). by apply (ltn_leq_trans Hym).
      have: (n <= y.+1)%N. by rewrite Hk leq_addr. rewrite ltnNge. by move ->.
Qed. 

Lemma submx_add_row_rowmx: forall m n (A B: 'M[F]_(m, n)) (Hmn: (m <= n)%N) (Hmn' : (m <= n + n)%N) r j,
  submx_add_row A Hmn r j =
  submx_add_row (row_mx A B) Hmn' r j.
Proof.
  move => m n A B Hmn Hmn' r j. rewrite -matrixP => x y.
  rewrite !mxE /=. 
  pose proof (splitP (widen_ord (leq_trans (ltn_ord r) Hmn') y)).
  case : X => [j' /= Hj' | k /= Hk].
  - f_equal. by apply ord_inj.
  - have Hyr: (y < r.+1)%N by []. have Hrn : (r.+1 <= n)%N.
    have Hrm: (r.+1 <= m)%N by []. by apply (ltn_leq_trans Hrm).
    have Hyn: (y < n)%N. have Hyr': (y < r.+1)%N by []. by apply (ltn_leq_trans Hyr').
    have : (n <= y)%N by rewrite Hk leq_addr. by rewrite leqNgt Hyn.
Qed. 

Lemma strong_inv_row_mx: forall m n (A B: 'M[F]_(m, n)) (Hmn: (m <= n)%N) (Hmn' : (m <= n + n)%N) (r: 'I_m),
  strong_inv A Hmn r ->
  strong_inv (row_mx A B) Hmn' r.
Proof.
  move => m n A B Hmn Hmn' r. rewrite /strong_inv => Hstr r' Hr'. split.
  - move => j Hj. rewrite -submx_remove_col_rowmx. move : Hstr => /(_ r' Hr') => [[Hcol Hrow]].
    by apply Hcol.
  - move => j Hj. rewrite -submx_add_row_rowmx. move : Hstr => /(_ r' Hr') => [[Hcol Hrow]].
    by apply Hrow.
Qed.

Lemma mulmx_castmx: forall n n' (H: n = n') (A B: 'M[F]_n),
  castmx (H, H) (A *m B)%R = ((castmx (H, H) A) *m (castmx (H, H) B))%R.
Proof.
  move => n n' H A B. rewrite -matrixP => x y.
  rewrite castmxE !mxE. have Hn: (n <= n')%N by rewrite H leqnn.
  rewrite (big_nth x) (big_nth (cast_ord (esym H) x)) /=.
  rewrite !index_ord_enum !size_ord_enum.
  rewrite (big_nat_widen _ _ _ _ _ Hn) big_nat_cond (big_nat_cond _ _ _ _ (fun x => true)).
  apply eq_big.
  - move => i. by rewrite /= H andb_diag andbT.
  - rewrite /=. move => i /andP[Hi' Hi].
    rewrite !castmxE /=. 
    have Hii: i = nat_of_ord (Ordinal Hi) by []. 
    have Hii': i = nat_of_ord (Ordinal Hi') by []. 
    have->: (nth x (ord_enum n') i) = (nth x (ord_enum n') (Ordinal Hi')) by f_equal.
    have->: (nth (cast_ord (esym H) x) (ord_enum n) i) = (nth (cast_ord (esym H) x) (ord_enum n) (Ordinal Hi)) by f_equal.
    rewrite !nth_ord_enum. by f_equal; f_equal; apply ord_inj.
Qed.

Lemma id_castmx: forall n n' (H: n = n'),
  castmx (R:=F) (H, H) (1%:M)%R = (1%:M)%R.
Proof.
  move => n n' H. rewrite -matrixP => x y.
  by rewrite castmxE !id_A cast_ord_switch cast_ordKV.
Qed.

Lemma unitmx_castmx: forall n n' (H: n = n') (A: 'M[F]_n),
  ((castmx (H, H) A) \in unitmx) = (A \in unitmx).
Proof.
  move => n n' H A. case Hun: (A \in unitmx).
  - have Hmul: (A *m (invmx A))%R = (1%:M)%R by apply mulmxV.
    have: castmx (H, H) (A *m invmx A)%R = castmx (H, H) (1%:M)%R by rewrite Hmul.
    rewrite mulmx_castmx id_castmx => Hcast. apply mulmx1_unit in Hcast. apply Hcast.
  - case Hcastun: (castmx (H, H) A \in unitmx) => [|//].
    have Hmul: ((castmx (H, H) A) *m (invmx (castmx (H, H) A)))%R = (1%:M)%R by apply mulmxV.
    have: castmx (esym H, esym H) (castmx (H, H) A *m invmx (castmx (H, H) A))%R =
          castmx (esym H, esym H) (1%:M)%R by rewrite Hmul.
    rewrite mulmx_castmx castmxK id_castmx => Ha.
    apply mulmx1_unit in Ha. case : Ha => [Ha  Hc]. by rewrite Ha in Hun.
Qed.

Lemma lt_subst: forall (n m p: nat),
  (n < m)%N ->
  m = p ->
  (n < p)%N.
Proof.
  move => n m p Hn Hmp. by rewrite -Hmp.
Qed.

(*TODO: move this too*)
Lemma strong_inv_unitmx: forall {n} (A: 'M[F]_n) (H: (n <= n)%N) (r: 'I_n),
  strong_inv A H r ->
  A \in unitmx.
Proof.
  move => n A H r. rewrite /strong_inv.
  have: (0 <= n)%N by []. rewrite leq_eqVlt => /orP[/eqP H0n | Hn].
  -  move => Hstr. (*i guess the empty matrix is invertible?*)
     have->: A = (1%:M)%R. subst. apply matrix_zero_rows. apply unitmx1.
  - have Hr: (r <= (pred_ord Hn))%N by rewrite /= -ltn_pred. 
    move => /(_ (pred_ord Hn) Hr) => [[Hrow Hcol]].
    move : Hcol => /(_ (pred_ord Hn) (leqnn _)).
    have Hpred: n = (pred_ord Hn).+1 by rewrite /= (ltn_predK Hn).
    have->: submx_add_row A H (pred_ord Hn) (pred_ord Hn) = (castmx (Hpred, Hpred) A) .
    { rewrite -matrixP => x y. rewrite !mxE castmxE /=. f_equal. 2: by apply ord_inj.
      case Hx: (x < n.-1)%N.
      - by apply ord_inj.
      - have Hxn: (x < (pred_ord Hn).+1)%N by [].
        have {}Hxn: (x < n)%N. apply (lt_subst Hxn). by []. (*no idea why rewriting directly gives dep type error*)
        have: (x <= n.-1)%N by rewrite -ltn_pred. rewrite leq_eqVlt => /orP[/eqP Hxn1 | Hcon].
        + by apply ord_inj.
        + by rewrite Hcon in Hx. }
    by rewrite unitmx_castmx.
Qed.



(*The result we want: [find_invmx_list] computes the inverse. This is quite complicated to prove
  because of all the casting*)
Lemma find_invmx_list_spec: forall mx n,
  strong_inv_list n n mx 0 -> 
  matrix_to_mx n n (find_invmx_list mx n) = invmx (matrix_to_mx n n mx).
Proof.
  move => mx n. rewrite /strong_inv_list. case : (range_le_lt_dec 0 0 n) => [H0n /= | //].
  case : (Z_le_lt_dec n n) => [/= Htriv Hstr|//]. rewrite -gaussian_finds_invmx.
  - rewrite /find_invmx_list. have Hn: 0 <= n by lia. rewrite right_submx_spec /=.
    rewrite /find_invmx gauss_restrict_rows_equiv. lia. move => Hnn. 2: by apply row_mx_list_wf.
    rewrite castmx_gaussian_restrict gaussian_elim_equiv.
    + f_equal. f_equal. rewrite row_mx_list_spec; try lia. rewrite id_list_spec; try lia.
      rewrite -matrixP => x y. rewrite !castmxE /=. f_equal. by apply ord_inj. by apply ord_inj.
    + apply /ltP. lia.
    + move => Hn'. rewrite row_mx_list_spec; try lia. rewrite id_list_spec; try lia. rewrite castmxKV.
      apply (@strong_inv_row_mx _ _ (matrix_to_mx n n mx) 1%:M (le_Z_N Htriv)
              (cast_leq (erefl (Z.to_nat n), Z2Nat.inj_add n n Hn Hn) (le_Z_N Hnn))).
      by have ->: (Ordinal Hn') = Z_to_ord H0n by apply ord_inj.
  - by apply strong_inv_unitmx in Hstr.
Qed.

(*The parity packet is a list of option (list Z)'s, since some are lost in transit. We need to convert to 
  a matrix*)
Definition fill_missing (c: Z) (l: list (option (list Z))) : list (list Z) :=
  fold_left (fun acc x => match x with
                            | None => (list_repeat (Z.to_nat c) 0%Z) :: acc
                            | Some l => l :: acc
                            end) l nil.

(*Lastly, fill in the input matrix with the missing data*)
(*The first matrix is m x n, the second is some m' x n*)
Definition fill_row_list m n (d r: matrix F) row_d row_r :=
  mk_matrix m n (fun i j => if Z.eq_dec i row_d then get r row_r j else get d i j).

Definition fill_rows_list_aux m n (d r: matrix F) (to_fill: seq Z) (src_idx: list Z) :=
  fold_left (fun acc x => fill_row_list m n acc r (Znth x to_fill) x) src_idx d.

Definition fill_rows_list m n xh (d r: matrix F) (to_fill: seq Z) :=
  fill_rows_list_aux m n d r to_fill (Ziota 0 xh).

Lemma fill_row_list_spec: forall m1 m2 n d r row_d row_r (Hd: 0 <= row_d < m1) (Hr: 0 <= row_r < m2),
  0 <= n ->
  matrix_to_mx m1 n (fill_row_list m1 n d r row_d row_r) =
    fill_row (matrix_to_mx m1 n d) (matrix_to_mx m2 n r) (Z_to_ord Hd) (Z_to_ord Hr).
Proof.
  move => m1 m2 n d r row_d row_r Hd Hr Hn. apply mk_matrix_mx; try lia.
  move => x y Hx Hy. rewrite !mxE /= !Z2Nat.id; try lia.
  case: (Z.eq_dec x row_d) =>[//= Hxd | /= Hxd].
  - subst. by have->: Z_to_ord Hx == Z_to_ord Hd by (apply /eqP; apply ord_inj).
  - have->:Z_to_ord Hx == Z_to_ord Hd = false. rewrite -nat_of_ord_eq /=. apply /eqP. lia. by [].
Qed.

Lemma fill_rows_list_aux_spec: forall m1 m2 n d r to_fill src_idx (Hd: 0 < m1),
  0 <= n ->
  Forall (fun x => 0 <= x < m1) to_fill ->
  Forall (fun x => 0 <= x < m2) src_idx ->
  Zlength to_fill = m2 ->
  matrix_to_mx m1 n (fill_rows_list_aux m1 n d r to_fill src_idx) =
    fill_rows_aux (matrix_to_mx m1 n d) (matrix_to_mx m2 n r)
       (Z_ord_list to_fill m1) (ord_zero Hd) (Z_ord_list src_idx m2).
Proof.
  move => m1 m2 n d r to_fill src_idx Hd Hn Hfill Hsrc Hlen. rewrite /Z_ord_list. move : d Hsrc.
  elim : src_idx => [//= | h t IH d Hall /=].
  rewrite IH. 2: by apply Forall_inv_tail in Hall.
  have Hh: 0 <= h < m2 by apply Forall_inv in Hall. rewrite (@fill_row_list_spec m1 m2) //=.
  move: Hfill; rewrite Forall_Znth. by rewrite Hlen => /(_ h Hh).
  move => Hnth. rewrite insubT.
  apply /ltP; lia. move => Hhm. rewrite /=. f_equal. f_equal.
  2: by apply ord_inj.
  have->:(pmap insub [seq Z.to_nat i | i <- to_fill]) = Z_ord_list to_fill m1 by []. apply ord_inj.
  apply Nat2Z.inj. rewrite -Z_ord_list_Znth //. rewrite /= Z2Nat.id; lia. lia.
Qed.

Lemma Z_ord_list_iota: forall x,
  0 <= x ->
  Z_ord_list (Ziota 0 x) x = ord_enum (Z.to_nat x).
Proof.
  move => x Hx. rewrite /Ziota /ord_enum.
  have->: (Z.to_nat 0%Z) = 0%N by []. 
  have: forall i, i \in (iota 0 (Z.to_nat x)) -> (i < Z.to_nat x)%N. {
    move => i. by rewrite mem_iota add0n. }
  elim : (iota 0 (Z.to_nat x)) => [//= | h t /= IH Hin].
  rewrite /Z_ord_list /=.
  have Hhx: (h < Z.to_nat x)%coq_nat. apply /ltP. apply Hin. by rewrite in_cons eq_refl.
  rewrite !insubT; try( apply /ltP; lia). move => Hh' Hh''. rewrite /=.
  rewrite -IH.  rewrite /Z_ord_list. f_equal. apply ord_inj. by rewrite /= Nat2Z.id.
  move => i Hi. apply Hin. by rewrite in_cons Hi orbT.
Qed.

Lemma fill_rows_list_spec: forall m1 m2 n (d r: matrix F) to_fill (Hd: 0 < m1),
  0 <= n ->
  Forall (fun x => 0 <= x < m1) to_fill ->
  Zlength to_fill = m2 ->
  matrix_to_mx m1 n (fill_rows_list m1 n m2 d r to_fill) =
    fill_rows (matrix_to_mx m1 n d) (matrix_to_mx m2 n r)
       (Z_ord_list to_fill m1) (ord_zero Hd).
Proof.
  move => m1 m2 n d r to_fill Hd Hn Hfill Hlen.
  rewrite (@fill_rows_list_aux_spec m1 m2); try lia; try by [].
  rewrite /fill_rows. f_equal. apply Z_ord_list_iota. list_solve.
  rewrite Forall_forall=> x. rewrite Zseq_In; try lia. list_solve.
Qed.

(** The Decoder  *)

(*First, we will do everything in terms of list matrices, then bring back to Z*)
Definition decode_list_mx (k c : Z) (packets: list (list Z)) (parities: list (option (list Z))) 
  (stats: list Z) : matrix F :=
  (*populate all of the "arrays"*)
  let lost := find_lost stats k in
  let found1 := find_found stats k in 
  let (row, found2) := find_parities parities (Zlength parities) (fec_n - 1) in
  let found := found1 ++ found2 in
  let input := extend_mx k c (int_to_poly_mx packets) in
  let parmx := int_to_poly_mx (fill_missing c parities) in
  let xh := Zlength lost in
  (*step 1: find w' and v*)
  let w' := submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1) row lost in
  let v := find_invmx_list w' xh in
  (*step 2: find w'', d, and s*)
  let w'' := submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) row found in
  let d' := col_mx_list (submx_rows_cols_list input (k - xh) c found1 (Ziota 0 c))
              (submx_rows_cols_list parmx xh c found2 (Ziota 0 c)) (k-xh) xh c in
  let s := list_matrix_multiply xh k c w'' d' in
  (*step 3: find missing packets and fill in*)
  let d := list_matrix_multiply xh xh c v s in
  fill_rows_list k c xh input d lost.


Lemma max_h_n: ((Z.to_nat fec_max_h <= Z.to_nat (fec_n - 1)))%N.
Proof.
  apply /leP. rep_lia.
Qed.

Check decoder_mult.

Lemma k_bound_proof: forall k,
  (k <= (fec_n - 1) - fec_max_h) ->
  (Z.to_nat k <= Z.to_nat (fec_n - 1) - Z.to_nat fec_max_h)%N.
Proof.
  move => k Hk.  apply /leP.
  have->: (Z.to_nat (fec_n - 1) - Z.to_nat fec_max_h)%N = (Z.to_nat (fec_n - 1) - Z.to_nat fec_max_h)%coq_nat by [].
  rep_lia.
Qed.

(*We will need this a few times - the list of powers in the Vandermonde matrix*)
Definition weight_list := (rev [seq (qx (f:=mod_poly) ^+ i)%R | i <- iota 0 (Z.to_nat (fec_n - 1))]).

Lemma weight_list_size: size weight_list = Z.to_nat (fec_n - 1).
Proof.
  by rewrite /weight_list size_rev size_map size_iota.
Qed.

Lemma weight_mx_spec: matrix_to_mx fec_max_h (fec_n - 1) weight_mx =
   weights (Z.to_nat fec_max_h) (Z.to_nat (fec_n - 1)) weight_list.
Proof.
  rewrite /weight_mx /weight_list gauss_restrict_rows_equiv. rep_lia.
  move => Hhn. rewrite /weights gaussian_elim_equiv. f_equal. by rewrite weight_mx_list_spec; try rep_lia.
  apply /leP. rep_lia. move => Hh. rewrite weight_mx_list_spec; try rep_lia. apply vandermonde_strong_inv.
  rewrite mod_poly_deg_eq /=. apply /leP; rep_lia. 
  apply weight_matrix_wf; rep_lia.
Qed.

Print decoder_mult.

Print find_found.

Print find_parities.

Lemma h_pos: 0 < fec_max_h.
Proof.
  rep_lia.
Qed.

Lemma n_pos: 0 < fec_n - 1.
Proof.
  rep_lia.
Qed.

Print decoder_mult.

Print widen_ord_seq.

(*TODO: move to Z_ord_list stuff*)
Lemma Z_ord_list_widen: forall n m (H: (Z.to_nat n <= Z.to_nat m)%N) (l: list Z),
  Forall (fun x => 0 <= x < n) l ->
  Z_ord_list l m = widen_ord_seq H (Z_ord_list l n).
Proof.
  move => n m H l. rewrite /Z_ord_list. elim : l => [//= | h t /= IH Hforall].
  have Hhn: (Z.to_nat h < Z.to_nat n)%N. apply /ltP.
    have Hhn: (0 <= h < n) by apply (Forall_inv Hforall). lia. 
  rewrite !insubT. by apply (ltn_leq_trans Hhn). move => Hhm.
  rewrite /= IH. f_equal. by apply ord_inj. apply (Forall_inv_tail Hforall).
Qed.

(*TODO: move*)
Lemma Z_ord_list_app: forall n l1 l2,
  Z_ord_list (l1 ++ l2) n = Z_ord_list l1 n ++ Z_ord_list l2 n.
Proof.
  move => n l1 l2. rewrite /Z_ord_list. (*not just pmap, so need induction*)
  elim : l1 => [//= | h t /= IH].
  case Hh: (Z.to_nat h < Z.to_nat n)%N.
  - by rewrite !insubT /= IH.
  - by rewrite !insubF //= IH.
Qed.

(*TODO: move*)
(*
Lemma widen_ord_seq_eq: forall m n p (l1: seq 'I_m) (l2: seq 'I_n) (Hm: (m <= p)%N) (Hn: (n <= p)%N),
  map (fun x => nat_of_ord x) l1 = map (fun x => nat_of_ord x) l2 ->
  widen_ord_seq Hm l1 = widen_ord_seq Hn l2.
Proof.
  move => m n p l1 l2 Hm Hn. move: l2; elim : l1 => [//= l2 | h t /= IH l2].
  by case : l2.
  case : l2 => [ //= | h' t' /= [Hhh' Htt']].
  f_equal. by apply ord_inj. by apply IH.
Qed.

*)
(*TODO: see if we need*)
Lemma ord_seq_inj: forall n (l1 l2: seq 'I_n),
 map (fun x => nat_of_ord x) l1 = map (fun x => nat_of_ord x) l2 ->
  l1 = l2.
Proof.
  move => n l1. elim : l1 => [//= l2 | h t /= IH l2].
  by case : l2.
  case : l2 => [//= | h' t' /= [Hhh Htt]].
  f_equal. by apply ord_inj. by apply IH.
Qed.

Lemma Z_to_nat_eq: forall z1 z2,
  z1 = z2 ->
  Z.to_nat z1 = Z.to_nat z2.
Proof.
  move => z1 z2. by move ->.
Qed.


(*TODO: move*)
Lemma matrix_to_mx_cast: forall m1 m2 n1 n2 mx (Hm: m2 = m1) (Hn: n2 = n1),
  matrix_to_mx m1 n1 mx = castmx (Z_to_nat_eq Hm, Z_to_nat_eq Hn) (@matrix_to_mx F m2 n2 mx).
Proof.
  move => m1 m2 n1 n2 mx Hm Hn. rewrite -matrixP => x y.
  rewrite castmxE !mxE. f_equal.
Qed.

Search (?x = ?y -> ?y = ?z -> ?x = ?z).

(*TODO: move*)
Lemma castmx_twice: forall m1 m2 m3 n1 n2 n3 (A: 'M[F]_(m1, n1)) 
  (Hm12: m1 = m2) (Hm23: m2 = m3) (Hn12: n1 = n2) (Hn23: n2 = n3),
  castmx (Hm23, Hn23) (castmx (Hm12, Hn12) A) =
  castmx (etrans Hm12 Hm23, etrans Hn12 Hn23) A.
Proof.
  move => m1 m2 m3 n1 n2 n3 A Hm12 Hm23 Hn12 Hn23. rewrite -matrixP => x y.
  rewrite !castmxE /=. by f_equal; apply ord_inj.
Qed.


(*First, we prove that this is equivalent to the mathcomp decoder*)
(*LOTS of ordinals and dependent types in here, eventually we will be able to just have a few bounds hypotheses
  that can be solved with [lia]*)
Lemma decode_list_mx_equiv: forall k c h xh packets parities stats (Hk: 0 < k <= (fec_n - 1) - fec_max_h) (Hc: 0 < c)
  (Hh: 0 < h <= fec_max_h) (Hxh: xh <= k),
  let lost := find_lost stats k in
  let (row, foundp) := find_parities parities h (fec_n - 1) in
  Zlength lost = xh ->
  Zlength row = xh ->
  Zlength parities = h ->
  matrix_to_mx k c (decode_list_mx k c packets parities stats) = 
    decoder_mult (F:=F) max_h_n (k_bound_proof (proj2 Hk)) weight_list_size (ord_zero h_pos) (ord_zero n_pos)
      (ord_zero (proj1 Hk)) (ord_zero Hc) (matrix_to_mx k c (extend_mx k c (int_to_poly_mx packets)))
      (matrix_to_mx h c (int_to_poly_mx (fill_missing c parities)))
      (Z_ord_list lost k) (Z_ord_list row h)
      (le_Z_N (proj2 Hh)) (ord_zero (proj1 Hh)) (le_Z_N Hxh).
Proof.
  move => k c h xh packets parities stats Hk Hc Hh Hxh. rewrite /=.
  case Hpar : (find_parities parities h (fec_n -1)) => [ row foundp].
  move => Hlenlost Hlenfound Hlenpar.
  (*Things we will need to know about the lists*)
  have Hlostbound: Forall (fun x : Z => 0 <= x < k) (find_lost stats k) by (apply find_lost_bound; lia).
  have Hrowbound: Forall (fun x : Z => 0 <= x < h) row. {
    have->: row = (find_parities parities h (fec_n - 1)).1 by rewrite Hpar. 
    apply find_parities_bound_fst; lia. }
  have Hfoundbound: Forall (fun x : Z => 0 <= x < k) (find_found stats k). apply find_found_bound; lia.
  have Hfoundpbound: Forall (fun x : Z => 0 <= x < fec_n - 1) foundp. 
    have->:foundp = (find_parities parities h (fec_n - 1)).2 by rewrite Hpar. apply find_parities_bound_snd; lia. 
  have Hxh0: 0 <= xh by list_solve.
  rewrite /decode_list_mx Hlenpar Hlenlost Hpar /decoder_mult. rewrite fill_rows_list_spec //; try lia.
  move => Hk0. f_equal.
  rewrite list_matrix_multiply_correct. 2: { apply right_submx_wf; rep_lia. }
  2 : { apply list_matrix_multiply_wf; rep_lia. }
  2 : { by apply ord_inj. }
  rewrite find_invmx_list_spec. 2 : { (*TODO: I know we need this*) admit. }
  f_equal.
  - rewrite (@submx_rows_cols_rev_list_spec _ (fec_max_h) (fec_n - 1) xh xh) //; try lia.
    + move => Hh0 Hn0. f_equal. f_equal.
      * apply weight_mx_spec.
      * by apply Z_ord_list_widen.
      * by apply Z_ord_list_widen.
      * by apply ord_inj.
      * by apply ord_inj.
    + by apply (forall_lt_leq_trans (proj2 Hh)).
    + have Hkn: k <= fec_n - 1 by lia. by apply (forall_lt_leq_trans Hkn). 
  - rewrite list_matrix_multiply_correct. 2: { apply submx_rows_cols_rev_list_wf; lia. }
    2 : { have Hkxh: k = (k - xh) + xh by lia. rewrite {5}Hkxh. apply col_mx_list_wf; lia. }
    rewrite (@submx_rows_cols_rev_list_spec _ fec_max_h) //; try lia. (*TODO: make sure this should be h*)
    2 : { by apply (forall_lt_leq_trans (proj2 Hh)). }
    2 : { rewrite Forall_app. split =>[|//]. have Hkn: (k <= fec_n - 1) by lia. by apply (forall_lt_leq_trans Hkn). }
    move => Hh0 Hn0. f_equal.
    + f_equal.
      * apply weight_mx_spec.
      * by apply Z_ord_list_widen.
      * rewrite Z_ord_list_app. f_equal.
        -- (*will probably just prove this separately - need to prove w ord comp*)
           admit.
        -- (*also prove this separately*) admit.
      * by apply ord_inj.
      * by apply ord_inj.
    + rewrite (@matrix_to_mx_cast k ((k - xh) + xh) c c). lia. move => Hkxh.
      rewrite col_mx_list_spec. lia. move => Hkxh0. 2: lia. rewrite castmx_twice.
      (*TODO: deal with cast issue*)
      Check submx_rows_cols_list_equiv.
      rewrite (@submx_rows_cols_list_equiv _ k c (k-xh) c) //=; try lia.
      2: { rewrite Forall_forall => y. rewrite Zseq_In; lia. }
      (*Let's try, see if it works*)
      rewrite -matrixP => x y.
      rewrite !castmxE /= !mxE /=.
      pose proof (splitP (cast_ord (esym (etrans (Logic.eq_sym (Z2Nat.inj_add (k - xh) xh Hkxh0 Hxh0)) (Z_to_nat_eq Hkxh))) x)).
      case : X => [j /= Hj | k' /= Hk'].
      { rewrite !mxE /=. pose proof (splitP (cast_ord (esym (subnK (le_Z_N Hxh))) x)).
        case : X => [j' /= Hj' | k'' /= Hk''].
        { rewrite !mxE /=. f_equal; f_equal. (*again, need relation between find_found and find_lost w ord_comp*)
          admit. }
        { have /ltP Hx: (x < Z.to_nat (k - xh))%N by rewrite Hj.
          move: Hk''; have->: (Z.to_nat k - Z.to_nat xh + k'')%N = ((Z.to_nat k - Z.to_nat xh)%coq_nat + k'')%coq_nat by [] => Hk''. 
          lia. }
      }
      { pose proof (splitP (cast_ord (esym (subnK (le_Z_N Hxh))) x)).
        case : X => [j' /= Hj' | k'' /= Hk''].
        { have /ltP Hx: (x < (Z.to_nat k - Z.to_nat xh)%coq_nat)%N by rewrite Hj'.
          move: Hk'; have->:(Z.to_nat (k - xh) + k')%N = (Z.to_nat (k - xh) + k')%coq_nat by [] => Hk'. lia.
        }
        { rewrite !mxE /=. (*need relation between foundp and rows*) admit. }


(*TODO: go back and do these things, finish proofs*)


