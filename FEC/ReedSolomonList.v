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
Require Import List2D.
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
Definition find_lost_found_aux (f: Z -> bool) (g: Z -> Z) base pack l : list Z :=
  fold_left (fun acc x => if f (Znth x pack) then acc ++ [:: g x] else acc) l base.

Lemma find_lost_found_aux_bound: forall f g base pack l b,
  (forall x, In x l -> 0 <= g x < b) ->
  (forall x, In x base -> 0 <= x < b) ->
  Forall (fun x => 0 <= x < b) (find_lost_found_aux f g base pack l).
Proof.
  move => f g base pack l b Hg Hbase. 
  rewrite /find_lost_found_aux Forall_forall. move : base Hbase Hg.
  elim : l => [ //= | h t /= IH base Hbase Hg x].
  case Hh: (f (Znth h pack)); apply IH; rewrite //=.
  - move => z Hin. apply in_app_or in Hin. case : Hin => [Hin | [Hzh | Hfalse]]; rewrite //.
    + by apply Hbase.
    + subst. apply Hg. by left.
  - move => z Hin. apply Hg. by right.
  - move => z Hin. apply Hg. by right.
Qed. 

(*Almost exactly same as parities, is there some way to duplicate, like f is function from Z to
  some type w 2 constructors*)
Lemma find_lost_found_aux_NoDup: forall f g pack base l,
  NoDup base ->
  (forall x y, In x base -> In y l -> g y <> x) ->
  NoDup l ->
  (forall x y, In x l -> In y l -> g x = g y -> x = y) ->
  NoDup (find_lost_found_aux f g base pack l).
Proof.
  move => f g pack base l. move: base. elim : l => [//= | h t /= IH base Hnob Hbl Hnol Hinj].
  case Hfh : (f (Znth h pack)).
  - apply IH. apply Helper.NoDup_app. by []. constructor. by []. constructor.
    move => x Hinx. rewrite /= => Hinh. case : Hinh => [Hfh' | Hfalse]; rewrite //.
    have: g h <> x. apply Hbl. by []. by left. by rewrite Hfh'.
    move => x y Hinx Hiny.
    apply in_app_or in Hinx. case : Hinx => [Hinx | [Hxh | Hfalse]]; rewrite //.
    apply Hbl. by []. by right. subst. move => Hf. apply Hinj in Hf. 
    subst. by move: Hnol; rewrite NoDup_cons_iff => [[Hnotin H]]. by right. by left.
    by move: Hnol; rewrite NoDup_cons_iff => [[Hnotin Ht]].
    move => x y Hinx Hiny Hf. apply Hinj. by right. by right. by [].
  - apply IH. by []. move => x y Hinx Hiny. apply Hbl. by []. by right.
    by move: Hnol; rewrite NoDup_cons_iff => [[Hnotin H]].
    move => x y Hinx Hiny Hf. apply Hinj. by right. by right. by [].
Qed.

Lemma find_lost_found_aux_NoDup': forall f g pack l,
  NoDup l ->
  (forall x y, In x l -> In y l -> g x = g y -> x = y) ->
  NoDup (find_lost_found_aux f g nil pack l).
Proof.
  move => f g pack l Hno Hinj. apply find_lost_found_aux_NoDup; try by [].
  constructor.
Qed.

(*First, get the lost packets*)
Definition find_lost (stats: list Z) (k: Z) : list Z :=
  find_lost_found_aux (fun x => Z.eq_dec x 1%Z) id nil stats (Ziota 0 k).

Lemma find_lost_bound: forall l k,
  0 <= k ->
  Forall (fun x : Z => 0 <= x < k) (find_lost l k).
Proof.
  move => l k Hk. apply find_lost_found_aux_bound; try by [].
  move => x. rewrite Zseq_In; lia. 
Qed.

Lemma find_lost_NoDup: forall l k,
  NoDup (find_lost l k).
Proof.
  move => l k. apply find_lost_found_aux_NoDup'; try by [].
  apply Ziota_NoDup.
Qed.

(*the first part of the found array*)
Definition find_found (stats: list Z) (k: Z) : list Z :=
  find_lost_found_aux (fun x => negb (Z.eq_dec x 1%Z)) id nil stats (Ziota 0 k).

Lemma find_found_bound: forall l k,
  0 <= k ->
  Forall (fun x : Z => 0 <= x < k) (find_found l k).
Proof.
  move => l k Hk. apply find_lost_found_aux_bound; try by []. move => x. by rewrite Zseq_In; lia.
Qed.

Lemma find_found_NoDup: forall l k,
  NoDup (find_found l k).
Proof.
  move => l k. apply find_lost_found_aux_NoDup'; try by [].
  apply Ziota_NoDup.
Qed.


Instance Inhabitant_option: forall {A: Type}, Inhabitant (option A).
intros A. apply None.
Defined.

(*Parities are represented as a list (option (list Z)), representing whether the parity packet is there
  or not. We will translate this into Vundef or Vptr as needed*)

(* Definition remove_option {A: Type} (l: list (option A)) : list A :=
  fold_left (fun acc (x: option A) => match x with | None => acc | Some y => acc ++ [:: y] end ) l nil. *)

Definition find_parity_aux (f: Z -> Z) (par: list (option (list Z))) (base : list Z) (l: list Z) :=
  fold_left (fun acc x => match (Znth x par) with
                          | None => acc
                          | Some _ => acc ++ [:: f x]
                          end) l base.

Lemma find_parity_aux_base_Zlength: forall f par base l,
  Zlength (find_parity_aux f par base l) = Zlength base + Zlength (find_parity_aux f par [::] l).
Proof.
  move => f par base l. move: base. elim : l => [//= b | h t /= IH base].
  - list_solve.
  - case Hh: (Znth h par) => [o |].
    + rewrite IH. rewrite (IH [:: f h]). rewrite Zlength_app. lia.
    + apply IH.
Qed.

Lemma find_parity_aux_Zlength: forall f1 f2 par base l,
  Zlength (find_parity_aux f1 par base l) = Zlength (find_parity_aux f2 par base l).
Proof.
  move => f1 f2 par base l. move: base. elim : l => [//= | h t /= IH base].
  case Hh: (Znth h par) => [o |].
  - by rewrite /= find_parity_aux_base_Zlength (find_parity_aux_base_Zlength _ _ (base ++ [:: f2 h])) !Zlength_app 
    !Zlength_cons !Zlength_nil IH.
  - by apply IH.
Qed.

Lemma find_parity_aux_map: forall f par b1 b2 l,
  map f b1 = b2 ->
  map f (find_parity_aux id par b1 l) = find_parity_aux f par b2 l.
Proof.
  move => f par b1 b2 l. move: b1 b2. elim : l => [//= | h t /= IH b1 b2 Hb12].
  apply IH. case Hh : (Znth h par) => [o |].
  - by rewrite map_cat /= Hb12.
  - by [].
Qed.

Lemma find_parity_aux_map': forall f par l,
  map f (find_parity_aux id par nil l) = find_parity_aux f par nil l.
Proof.
  move => f par l. by apply find_parity_aux_map.
Qed.
  

Lemma find_parity_aux_bound: forall f pars base l b,
  (forall x, In x l -> 0 <= f x < b) ->
  (forall x, In x base -> 0 <= x < b) ->
  Forall (fun x : Z => 0 <= x < b) (find_parity_aux f pars base l).
Proof.
  move => f pars base l b Hf Hbase. rewrite /find_parity_aux Forall_forall. move : base Hbase Hf.
  elim : l => [ //= | h t /= IH base Hbase Hf x].
  case Hh: (Znth h pars) => [y /= | //=]; apply IH; rewrite //=.
  - move => z Hin. apply in_app_or in Hin. case : Hin => [Hin | Hzh].
    + by apply Hbase.
    + case : Hzh => [Hzh | Hfalse]; rewrite //. subst. apply Hf. by left.
  - move => z Hin. apply Hf. by right.
  - move => z Hin. apply Hf. by right.
Qed. 
(*maybe we don't need this*)
Lemma find_parity_aux_in: forall f par base l x,
  In x (find_parity_aux f par base l) ->
  In x base \/ exists y, f y = x /\ In y l.
Proof.
  move => f par base l x. move : base. elim : l => [//= base Hbase | h t /= IH base].
  by left. case Hh : (Znth h par) => [y /= | //=]. move => Hin. apply IH in Hin.
  case: Hin => [Hbaseh | Hxy].
  - apply in_app_or in Hbaseh. case : Hbaseh => [Hin | [Hxh | Hfalse]]; rewrite //.
    by left. right. exists h. split. by []. by left.
  - case Hxy => [y' [Hfxy' Hyt]]. right. exists y'. split. by []. by right.
  - move => Hin. apply IH in Hin. case : Hin => [Hin | [y [Hxy Hiny]]]. by left.
    right. exists y. split. by []. by right.
Qed.

Lemma find_parity_aux_NoDup: forall f par base l,
  NoDup base ->
  (forall x y, In x base -> In y l -> f y <> x) ->
  NoDup l ->
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup (find_parity_aux f par base l).
Proof.
  move => f par base l. move: base. elim : l => [//= | h t /= IH base Hnob Hbl Hnol Hinj].
  case : (Znth h par) => [a /= | //=].
  - apply IH. apply Helper.NoDup_app. by []. constructor. by []. constructor.
    move => x Hinx. rewrite /= => Hinh. case : Hinh => [Hfh | Hfalse]; rewrite //.
    have: f h <> x. apply Hbl. by []. by left. by rewrite Hfh.
    move => x y Hinx Hiny.
    apply in_app_or in Hinx. case : Hinx => [Hinx | [Hxh | Hfalse]]; rewrite //.
    apply Hbl. by []. by right. subst. move => Hf. apply Hinj in Hf. 
    subst. by move: Hnol; rewrite NoDup_cons_iff => [[Hnotin H]]. by right. by left.
    by move: Hnol; rewrite NoDup_cons_iff => [[Hnotin Ht]].
    move => x y Hinx Hiny Hf. apply Hinj. by right. by right. by [].
  - apply IH. by []. move => x y Hinx Hiny. apply Hbl. by []. by right.
    by move: Hnol; rewrite NoDup_cons_iff => [[Hnotin H]].
    move => x y Hinx Hiny Hf. apply Hinj. by right. by right. by [].
Qed.

(*The real result we wanted (we needed the stronger claim for the IH)*)
Lemma find_parity_aux_NoDup': forall f par l,
  NoDup l ->
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup (find_parity_aux f par nil l).
Proof.
  move => f par l Hno Hinj. apply find_parity_aux_NoDup; try by [].
  constructor.
Qed.

Definition find_parity_rows (par: list (option (list Z))) (c: Z) :=
  find_parity_aux id par nil (Ziota 0 c).

Lemma find_parity_rows_bound: forall par c,
  0 <= c ->
  Forall (fun x => 0 <= x < c) (find_parity_rows par c).
Proof.
  move => par c Hc.
  apply find_parity_aux_bound; rewrite //=.
  move => x. rewrite Zseq_In; lia.
Qed.

Lemma find_parity_rows_NoDup: forall par c,
  NoDup (find_parity_rows par c).
Proof.
  move => par c. apply find_parity_aux_NoDup'.
  apply Ziota_NoDup.
  by [].
Qed.

Definition find_parity_found (par: list (option (list Z))) (c: Z) (max_n : Z) :=
  find_parity_aux (fun x => max_n - 1 - x) par nil (Ziota 0 c).

(*TODO: see if we need better lower bound*)
Lemma find_parity_found_bound: forall par c max_n,
  0 <= c < max_n ->
  Forall (fun x => 0 <= x < max_n) (find_parity_found par c max_n).
Proof.
  move => par c max_n Hc. apply find_parity_aux_bound; try by [].
  move => x. rewrite Zseq_In; lia.
Qed.

Lemma find_parity_found_NoDup: forall par c max_n,
  0 <= c ->
  NoDup (find_parity_found par c max_n).
Proof.
  move => par c max_n Hc. apply find_parity_aux_NoDup'.
  apply Ziota_NoDup. move => x y. rewrite !Zseq_In; lia.
Qed.

(*The relationship between these two functions*)
Lemma find_parity_rows_found_Zlength: forall par c max_n,
  Zlength (find_parity_found par c max_n) = Zlength (find_parity_rows par c).
Proof.
  move => par c max_n.
  apply find_parity_aux_Zlength.
Qed.

Lemma find_parity_rows_found_map: forall par c max_n,
  map (fun x => max_n - 1 - x) (find_parity_rows par c) = find_parity_found par c max_n.
Proof.
  move => par c max_n. apply find_parity_aux_map'.
Qed.

Lemma find_parity_rows_found_Znth: forall par c max_n i,
  0 <= i < Zlength (find_parity_rows par c) ->
  Znth i (find_parity_found par c max_n) = max_n - 1 - Znth i (find_parity_rows par c).
Proof.
  move => par c max_n i Hi. by rewrite -find_parity_rows_found_map Znth_map.
Qed.


(*TODO: move*)
Lemma forall_lt_leq_trans: forall n m (l: list Z),
  n <= m ->
  Forall (fun x : Z => 0 <= x < n) l ->
  Forall (fun x : Z => 0 <= x < m) l.
Proof.
  move => n m l Hnm. apply Forall_impl. move => a Ha. lia. 
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
  map (fun x => match x with
                | None =>  (list_repeat (Z.to_nat c) 0%Z)
                | Some l => l
                end) l.

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
  let row := find_parity_rows parities (Zlength parities) in
  let found2 := find_parity_found parities (Zlength parities) (fec_n - 1) in
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
              (submx_rows_cols_list parmx xh c row (Ziota 0 c)) (k-xh) xh c in
  let s := list_matrix_multiply xh k c w'' d' in
  (*step 3: find missing packets and fill in*)
  let d := list_matrix_multiply xh xh c v s in
  fill_rows_list k c xh input d lost.


Lemma max_h_n: ((Z.to_nat fec_max_h <= Z.to_nat (fec_n - 1)))%N.
Proof.
  apply /leP. rep_lia.
Qed.

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

Lemma h_pos: 0 < fec_max_h.
Proof.
  rep_lia.
Qed.

Lemma n_pos: 0 < fec_n - 1.
Proof.
  rep_lia.
Qed.


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

(*TODO: move*)
Lemma castmx_twice: forall m1 m2 m3 n1 n2 n3 (A: 'M[F]_(m1, n1)) 
  (Hm12: m1 = m2) (Hm23: m2 = m3) (Hn12: n1 = n2) (Hn23: n2 = n3),
  castmx (Hm23, Hn23) (castmx (Hm12, Hn12) A) =
  castmx (etrans Hm12 Hm23, etrans Hn12 Hn23) A.
Proof.
  move => m1 m2 m3 n1 n2 n3 A Hm12 Hm23 Hn12 Hn23. rewrite -matrixP => x y.
  rewrite !castmxE /=. by f_equal; apply ord_inj.
Qed.

(*TODO: move*)
(*Need function to be injective only on domain of list, not in general*)
Lemma NoDup_map_inj: forall {A B: Type} (l: list A) (f: A -> B),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l ->
  NoDup (map f l).
Proof.
  move => A B l f. elim : l => [//= Hinj Hl | h t /= IH Hinj Hl].
  - constructor.
  - move: Hl; rewrite NoDup_cons_iff => [[Hnotin Hnodup]]. constructor. 
    move => C. apply list_in_map_inv in C. move : C => [x [Hfxh Hin]].
    apply Hinj in Hfxh. by subst. by left. by right.
    apply IH. move => x y Hinx Hiny. apply Hinj; by right.
    by [].
Qed. 

(*TODO: move*)
Lemma Z_ord_list_uniq: forall (z: seq Z) n,
  Forall (fun x => 0 <= x) z ->
  NoDup z ->
  uniq (Z_ord_list z n).
Proof.
  move => z n Hpos Hdup. rewrite /Z_ord_list pmap_sub_uniq //=.
  rewrite uniq_NoDup. apply NoDup_map_inj => [|//].
  move: Hpos; rewrite Forall_forall => Hall.
  move => x y Hinx Hinj Hnats.
  have: 0 <= x by apply Hall.
  have: 0 <= y by apply Hall. lia.
Qed.

Lemma Z_ord_list_In: forall (l: seq Z) n x,
  Forall (fun x => 0 <= x < n) l ->
  x \in (Z_ord_list l n) <->
  In (Z.of_nat x) l.
Proof.
  move => l n x. rewrite /Z_ord_list. elim : l => [//= | h t /= IH Hall].
  case Hh : (Z.to_nat h < Z.to_nat n)%N.
  - rewrite insubT /= in_cons. split.
    + move => /orP[/eqP Hxh | Hin].
      * subst. left. rewrite /= Z2Nat.id //. apply Forall_inv in Hall. lia.
      * right. apply IH. by apply Forall_inv_tail in Hall. by [].
    + move => [Hhx | Hint].
      * subst. have ->: (x == Ordinal Hh).  
        by apply /eqP; apply ord_inj; rewrite /= Nat2Z.id. by [].
      * have->: (x \in pmap insub [seq Z.to_nat i | i <- t]). apply IH. 
        by apply Forall_inv_tail in Hall. by []. by rewrite orbT.
  - rewrite insubF //=. rewrite IH. 2: by apply Forall_inv_tail in Hall. split.
    move => Hin. by right. move => [Hhx | Ht //]. subst.
    apply (Forall_inv) in Hall. move : Hh => /ltP Hh. lia.
Qed.

Lemma Z_ord_list_notin: forall (l: seq Z) n x,
  Forall (fun x => 0 <= x < n) l ->
  x \notin (Z_ord_list l n) <->
  ~ In (Z.of_nat x) l.
Proof.
  move => l n x Hall. split => Hnotin.
  - rewrite -Z_ord_list_In //. by apply /idP.
  - move: Hnotin; rewrite -Z_ord_list_In //=.
    by case : (x \in Z_ord_list l n).
Qed. 

(*old version TODO remove*)
(*
Lemma Z_ord_list_In: forall (l: seq Z) n x,
  Forall (fun x => 0 <= x) l ->
  x \in (Z_ord_list l n) ->
  In (Z.of_nat x) l.
Proof.
  move => l n x. rewrite /Z_ord_list. elim : l => [//= | h t /= IH Hall].
  case Hh : (Z.to_nat h < Z.to_nat n)%N.
  - rewrite insubT /= in_cons => /orP[/eqP Hxh | Hin].
    + subst. left. rewrite /= Z2Nat.id //. by apply Forall_inv in Hall.
    + right. apply IH. by apply Forall_inv_tail in Hall. by [].
  - rewrite insubF //=. move => Hin. right. apply IH. by apply Forall_inv_tail in Hall. by [].
Qed.*)

Lemma weight_list_uniq: uniq weight_list.
Proof.
  rewrite /weight_list rev_uniq power_list_uniq //=. apply /leP. 
  rewrite mod_poly_deg_eq /=. rep_lia.
Qed.

(*We need this both for correctness and for the the VST proof*)
Lemma strong_inv_list_partial: forall k xh h stats parities,
  0 < xh ->
  0 <= h ->
  h <= fec_max_h ->
  0 <= k <= (fec_n - 1) - fec_max_h ->
  Zlength (find_parity_rows parities h) = Zlength (find_lost stats k) ->
  Zlength (find_parity_rows parities h) = xh ->
  strong_inv_list xh xh (submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1) 
    (find_parity_rows parities h) (find_lost stats k)) 0%Z.
Proof.
  move => k xh h stats parities Hxh Hh Hhmax Hkn Hlens Hlenxh.
  rewrite /strong_inv_list. case : (range_le_lt_dec 0 0 xh); try lia.
  move => Hxh0. case : (Z_le_lt_dec xh xh); try lia. move => Hxhtriv.
  remember (find_parity_rows parities h) as row.
  have Hallrow: Forall (fun x => 0 <= x < h) row.
    rewrite Heqrow. by apply find_parity_rows_bound.
  have Hallrow': Forall (fun x => 0 <= x < fec_max_h) row.
    eapply Forall_impl. 2: apply Hallrow. rewrite /=. lia.
  have Halllost: Forall (fun x => 0 <= x < k) (find_lost stats k).
    apply find_lost_bound; lia.
  have Halllost': Forall (fun x => 0 <= x < fec_n - 1) (find_lost stats k).
    eapply Forall_impl. 2: apply Halllost. rewrite /=. lia.
  rewrite (@submx_rows_cols_rev_list_spec _ fec_max_h (fec_n - 1)) //=; try rep_lia.
  move => Hmaxh Hn. rewrite weight_mx_spec /weights /submx_rows_cols_rev. 
  have Hhnat: (0 < Z.to_nat fec_max_h)%N by (apply /ltP; rep_lia).
  have Hhn: (Z.to_nat fec_max_h <= Z.to_nat (fec_n - 1))%N by (apply /leP; rep_lia).
  (*Need to switch defaults for applying theorem*)
  rewrite (submx_rows_cols_default _ (ord_zero Hmaxh) (ord_zero Hn) (Ordinal Hhnat) ( widen_ord Hhn (Ordinal Hhnat))).
  + have->: (le_Z_N Hxhtriv) = (leqnn (Z.to_nat xh)) by apply ProofIrrelevance.proof_irrelevance.
    apply any_submx_strong_inv; rewrite //=.
    * by rewrite weight_list_uniq. 
    * apply weight_list_size.
    * apply Z_ord_list_uniq. eapply Forall_impl. 2: apply Hallrow. move => a; rewrite /=. lia.
      subst. apply find_parity_rows_NoDup.
    * rewrite map_inj_uniq. 2: { apply rev_ord_inj. }
      apply Z_ord_list_uniq. eapply Forall_impl. 2: apply find_lost_bound; lia. rewrite //=.
      lia. apply find_lost_NoDup.
    * by rewrite size_map !size_length -!ZtoNat_Zlength !Z_ord_list_Zlength // Hlens.
    * by rewrite size_length -ZtoNat_Zlength Z_ord_list_Zlength // Hlenxh.
    * move => x /mapP[y Hyin Hxy]. subst. rewrite /=. 
      apply Z_ord_list_In in Hyin. 2: eapply Forall_impl. 3: apply Halllost. 2: rewrite /=; lia.
      move: Halllost; rewrite Forall_forall => Hallost. apply Hallost in Hyin.
      rewrite leq_subRL. 2: apply /ltP; lia. rewrite addnC -leq_subRL. 2: apply /leP; lia. apply /ltP.
      have->:(Z.to_nat (fec_n - 1) - Z.to_nat fec_max_h)%N = (Z.to_nat (fec_n - 1) - Z.to_nat fec_max_h)%coq_nat by [].
      lia.
  + by rewrite size_length -ZtoNat_Zlength Z_ord_list_Zlength // Hlenxh.
  + by rewrite size_map size_length -ZtoNat_Zlength Z_ord_list_Zlength // -Hlens Hlenxh.
Qed.

(*Trivial case of xh = 0*)
Lemma decode_list_mx_zero: forall k c h packets parities stats,
  Zlength (find_lost stats k) = Zlength (find_parity_rows parities h) ->
  Zlength (find_lost stats k) = 0%Z ->
  matrix_to_mx k c (decode_list_mx k c packets parities stats) = 
  matrix_to_mx k c (extend_mx k c (int_to_poly_mx packets)).
Proof.
  move => k c h packets parities stats Hlens Hlen0.
  rewrite /decode_list_mx /=. rewrite !Hlen0 /=.
  by rewrite /fill_rows_list /=.
Qed.

Lemma find_lost_found_aux_app: forall f g base pack l1 l2,
  find_lost_found_aux f g base pack (l1 ++ l2) =
  find_lost_found_aux f g (find_lost_found_aux f g base pack l1) pack l2.
Proof.
  move => f g base pack l1 l2. by rewrite /find_lost_found_aux fold_left_app.
Qed.

Lemma nat_comp_app_notin: forall n l1 l2,
  (forall x, x \in l2 -> (n <= x)%N) ->
  nat_comp n l1 =
  nat_comp n (l1 ++ l2).
Proof.
  move => n l1 l2. elim : n => [//= | n /= IH Hin].
  rewrite !nat_comp_plus_one mem_cat.
  have->:n \in l2 = false. 
  case Hn: (n \in l2) =>[//|//]. apply Hin in Hn.
  by rewrite ltnn in Hn. rewrite orbF !IH //. move => x Hin'.
  apply ltnW. by apply Hin.
Qed.

Lemma nat_comp_app: forall n l1,
  nat_comp n (l1 ++ [:: n]) =
  nat_comp n l1.
Proof.
  move => n l1. rewrite -nat_comp_app_notin //. move => x. rewrite in_cons => /orP[/eqP Hxn | Hinf].
  subst. by rewrite leqnn. by [].
Qed.

(*TODO: may want to redefine [nat_comp] w foldl and iota instead, will make easier*)

(*TODO: move to above*)
Lemma find_lost_found_aux_in: forall f stats l x b,
  (forall x, In x l -> 0 <= x < b) ->
  In x (find_lost_found_aux f id [::] stats l) ->
  0 <= x < b.
Proof.
  move => f stats l x b Hl Hin.
  have Htriv: (forall x : Z, In x [::] -> 0 <= x < b) by [].
  pose proof (@find_lost_found_aux_bound f id [::] stats l b Hl Htriv) as Hall.
  by move: Hall; rewrite Forall_forall => /(_ _ Hin).
Qed.

(*TODO: move*)
(*Lost and found are complements*)
Lemma find_lost_found_comp_nat: forall stats k,
  map (Z.to_nat) (find_found stats k) =
  nat_comp (Z.to_nat k) (map Z.to_nat (find_lost stats k)).
Proof.
  move => stats k. rewrite /find_found /find_lost /Ziota /=.
  elim : (Z.to_nat k) => [//= | n IH]. rewrite nat_comp_plus_one !iota_plus_1 /= !map_cat /= !add0n !find_lost_found_aux_app /=.
  case: (Z.eq_dec (Znth (Z.of_nat n) stats) 1) => [/= Hn1 | /= Hn0].
  - have->:n
    \in [seq Z.to_nat i
           | i <- find_lost_found_aux (fun x : Z => Z.eq_dec x 1) id [::] stats
                    [seq Z.of_nat y | y <- iota 0 n] ++ [:: Z.of_nat n]]
    by rewrite map_cat /= mem_cat Nat2Z.id in_cons eq_refl orbT.
    rewrite map_cat /= Nat2Z.id nat_comp_app. apply IH.
  - have->:n
    \in [seq Z.to_nat i
           | i <- find_lost_found_aux (fun x : Z => Z.eq_dec x 1) id [::] stats
                    [seq Z.of_nat y | y <- iota 0 n]] = false. {
    apply /negPf /negP; rewrite in_mem_In in_map_iff => [[x [Hxn Hinx]]].
    subst. apply (@find_lost_found_aux_in _ _ _ _  x) in Hinx. lia.
    move => y. rewrite in_map_iff => [[x' [Hx' Hin]]]. subst. move: Hin.
    rewrite -in_mem_In mem_iota add0n => /andP[/leP Hx0 /ltP Hxx]. lia. }
    by rewrite map_cat /= Nat2Z.id IH.
Qed.

Lemma find_lost_found_comp: forall stats k,
  0 <= k ->
  Z_ord_list (find_found stats k) k =
  (ord_comp (Z_ord_list (find_lost stats k) k)).
Proof.
  (*do widen_ord stuff separately*)
  move => stats k Hk. rewrite {1}/Z_ord_list /ord_comp find_lost_found_comp_nat.
  f_equal. f_equal. pose proof (find_lost_bound stats Hk) as Hbound.
   have[H0k | H0k]: k = 0%Z \/ 0 < k by lia.
  - subst. by [].
  - apply Znth_eq_ext.
    + by rewrite !Zlength_map Z_ord_list_Zlength.
    + move => i. rewrite Zlength_map => Hi.
      have Hinhab: Inhabitant 'I_(Z.to_nat k). apply (ord_zero H0k).
      rewrite !Znth_map //=.
      * by rewrite Z_ord_list_Znth'.
      * by rewrite Z_ord_list_Zlength.
Qed.

(*TODO: move*)
Lemma Znth_Ziota: forall b x,
  0 <= x < b ->
  Znth x (Ziota 0 b) = x.
Proof.
  move => b x Hxb. rewrite /Ziota Znth_map. rewrite -nth_Znth. rewrite -nth_nth nth_iota //=.
  rewrite add0n. lia. apply /ltP; lia.
  all: rewrite Zlength_correct -size_length size_iota; lia.
Qed.

(*First, we prove that this is equivalent to the mathcomp decoder*)
(*LOTS of ordinals and dependent types in here, eventually we will be able to just have a few bounds hypotheses
  that can be solved with [lia]*)
Lemma decode_list_mx_equiv: forall k c h xh packets parities stats (Hk: 0 < k <= (fec_n - 1) - fec_max_h) (Hc: 0 < c)
  (Hh: 0 < h <= fec_max_h) (Hxh: xh <= k),
  let lost := find_lost stats k in
  let row := find_parity_rows parities h in
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
  remember (find_parity_rows parities h) as row.
  remember (find_parity_found parities h (fec_n - 1)) as foundp.
  move => Hlenlost Hlenfound Hlenpar.
  have: xh = 0%Z \/ 0 < xh by list_solve. move => [Hxh0 | Hxh0].
  - subst. rewrite (@decode_list_mx_zero k c (Zlength parities)) //.
    rewrite decoder_mult_0 //. rewrite size_length -ZtoNat_Zlength.
    rewrite Z_ord_list_Zlength. all: try (rewrite Hxh0; lia).
    apply find_lost_bound; lia.
  - (*Things we will need to know about the lists*)
    have Hlostbound: Forall (fun x : Z => 0 <= x < k) (find_lost stats k) by (apply find_lost_bound; lia).
    have Hrowbound: Forall (fun x : Z => 0 <= x < h) row. {
      subst. apply find_parity_rows_bound. lia. }
    have Hfoundbound: Forall (fun x : Z => 0 <= x < k) (find_found stats k). apply find_found_bound; lia.
    have Hfoundpbound: Forall (fun x : Z => 0 <= x < fec_n - 1) foundp.
      subst. apply find_parity_found_bound. lia. 
    (*have Hxh0: 0 <= xh by list_solve.*)
    rewrite /decode_list_mx Hlenpar Hlenlost /decoder_mult fill_rows_list_spec //; try lia.
    move => Hk0. f_equal.
    rewrite list_matrix_multiply_correct. 2: { apply right_submx_wf; rep_lia. }
    2 : { apply list_matrix_multiply_wf; rep_lia. }
    2 : { by apply ord_inj. }
    rewrite find_invmx_list_spec. 2 : {
      apply strong_inv_list_partial; try lia. by subst. by subst. } 
    f_equal.
    + rewrite (@submx_rows_cols_rev_list_spec _ (fec_max_h) (fec_n - 1) xh xh) //; try lia.
      * move => Hh0 Hn0. f_equal. f_equal.
        -- apply weight_mx_spec.
        -- subst; by apply Z_ord_list_widen.
        -- by apply Z_ord_list_widen.
        -- by apply ord_inj.
        -- by apply ord_inj.
      * subst. by apply (forall_lt_leq_trans (proj2 Hh)).
      * have Hkn: k <= fec_n - 1 by lia. by apply (forall_lt_leq_trans Hkn). 
    + rewrite list_matrix_multiply_correct. 2: { apply submx_rows_cols_rev_list_wf; lia. }
      2 : { have Hkxh: k = (k - xh) + xh by lia. rewrite {5}Hkxh. apply col_mx_list_wf; lia. }
      rewrite (@submx_rows_cols_rev_list_spec _ fec_max_h) //; try lia.
      2 : {  subst; by apply (forall_lt_leq_trans (proj2 Hh)). }
      2 : { subst. rewrite Forall_app. split =>[|//]. have Hkn: (k <= fec_n - 1) by lia. by apply (forall_lt_leq_trans Hkn). }
      move => Hh0 Hn0. f_equal.
      * f_equal.
        -- apply weight_mx_spec.
        -- subst; by apply Z_ord_list_widen.
        -- rewrite Z_ord_list_app. f_equal.
          ++ rewrite (Z_ord_list_widen (k_leq_n (k_bound_proof (proj2 Hk)))) // find_lost_found_comp //. lia.
          ++ have Hinhab: Inhabitant 'I_(Z.to_nat (fec_n - 1)) by apply (ord_zero Hn0).
             have Hfoundpbound': Forall (fun x : Z => 0 <= x < fec_n - 1) (find_parity_found parities h (fec_n - 1)) by subst.
             apply Znth_eq_ext. 
             ** rewrite Zlength_map !Z_ord_list_Zlength //. subst. by rewrite find_parity_rows_found_Zlength.
             ** move => i. rewrite !Z_ord_list_Zlength //  => Hi.
                have Hinhabh: Inhabitant 'I_(Z.to_nat h). apply (ord_zero (proj1 Hh)).
                rewrite Znth_map //.
                { have Hilen: 0 <= i < Zlength row. subst. by rewrite find_parity_rows_found_Zlength in Hi.
                  rewrite !Z_ord_list_Znth' //; try lia. apply ord_inj. subst. rewrite /= find_parity_rows_found_Znth //=.
                  have->: (Z.to_nat (fec_n - 1) - 1 - Z.to_nat (Znth i (find_parity_rows parities (Zlength parities))))%N =
                        ((Z.to_nat (fec_n - 1) - 1)%coq_nat - Z.to_nat (Znth i (find_parity_rows parities (Zlength parities))))%coq_nat by [].
                  rewrite !Z2Nat.inj_sub; try lia. move: Hrowbound; rewrite Forall_Znth => /(_ i Hilen). lia.
                }
                { subst. rewrite Z_ord_list_Zlength //. by rewrite find_parity_rows_found_Zlength in Hi.
                }
        -- by apply ord_inj.
        -- by apply ord_inj.
      * rewrite (@matrix_to_mx_cast k ((k - xh) + xh) c c). lia. move => Hkxh.
        rewrite col_mx_list_spec; try lia. move => Hkxh0 Hxh0'. rewrite castmx_twice.
        rewrite (@submx_rows_cols_list_equiv _ k c (k-xh) c) //=; try lia.
        2: { rewrite Forall_forall => y. rewrite Zseq_In; lia. }
        rewrite -matrixP => x y.
        rewrite !castmxE /= !mxE /=.
        pose proof (splitP (cast_ord (esym (etrans (Logic.eq_sym (Z2Nat.inj_add (k - xh) xh Hkxh0 Hxh0')) (Z_to_nat_eq Hkxh))) x)).
        case : X => [j /= Hj | k' /= Hk'].
        { rewrite !mxE /=. pose proof (splitP (cast_ord (esym (subnK (le_Z_N Hxh))) x)).
          case : X => [j' /= Hj' | k'' /= Hk''].
          { rewrite !mxE /=. f_equal; f_equal. rewrite find_lost_found_comp //.
            rewrite -Hj Hj' /=. have->:(ord_zero Hk0 = (ord_zero (proj1 Hk))) by apply ord_inj. by []. lia.
            rewrite Z_ord_list_iota //. lia. }
          { have /ltP Hx: (x < Z.to_nat (k - xh))%N by rewrite Hj.
            move: Hk''; have->: (Z.to_nat k - Z.to_nat xh + k'')%N = ((Z.to_nat k - Z.to_nat xh)%coq_nat + k'')%coq_nat by [] => Hk''. 
            lia. }
        }
        { pose proof (splitP (cast_ord (esym (subnK (le_Z_N Hxh))) x)).
          case : X => [j' /= Hj' | k'' /= Hk''].
          { have /ltP Hx: (x < (Z.to_nat k - Z.to_nat xh)%coq_nat)%N by rewrite Hj'.
            move: Hk'; have->:(Z.to_nat (k - xh) + k')%N = (Z.to_nat (k - xh) + k')%coq_nat by [] => Hk'. lia.
          }
          { rewrite !mxE /=. rewrite !mk_matrix_get; try lia. f_equal.
            have->:(nat_of_ord k'') = Z.to_nat (Z.of_nat k'') by rewrite Nat2Z.id.
            have->: k' = k''. move: Hk'' => /eqP Hx. move: Hx. rewrite Hk' Z2Nat.inj_sub; try lia.
            have->: (Z.to_nat k - Z.to_nat xh)%coq_nat = (Z.to_nat k - Z.to_nat xh)%N by [].
            rewrite eqn_add2l => /eqP Hx. by apply ord_inj.
            rewrite -Z_ord_list_Znth //. by subst. lia. rewrite nth_ord_enum Znth_Ziota //=.
            apply Z_ord_bound; lia. apply Z_ord_bound; lia. apply Z_ord_bound; lia. }
        }
Qed.

(*TODO: move to common and use in [int_to_poly_mx]*)
Definition Z_to_F (z: Z) : F :=
  exist (fun x => deg x < deg mod_poly) (poly_of_int z %~ mod_poly) (pmod_lt_deg _ _).


(*Are the parity packets valid? To be valid, we require that all the "Some" entries are the actual rows produced
  by the encoder. It's a bit awkward to state this in Coq*)
(*TODO: see whether to use this or "fill_missing"*)

(*
Definition parities_valid h k c parities data :=
  forall i j, 0 <= i < h -> 0 <= j < c ->
    match (Znth i parities) with
      | Some par => Z_to_F (Znth j par) = get (encode_list_mx h k c data) i j
      | None => True
    end.

*)

Definition parities_valid k c parities data :=
  forall i j, 0 <= i < Zlength parities -> 0 <= j < c ->
    match (Znth i parities) with
      | Some par => Znth j par = Znth j (Znth i (norev_mx (encode_list_mx (Zlength parities) k c data)))
      | _ => True
    end.

(*
(*TODO: MOVE, only one direction exists in stnd library, this is In version of [mem_map]*)
Lemma in_map_iff_inj: forall {A B} (f: A -> B) l x,
  (forall (x y : A), {x = y} + {x <> y}) ->
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  In x l <-> In (f x) (map f l).
Proof.
  move => A B f l x Heq. elim : l => [//= | h t /= IH Hinj].
  move: Heq => /(_ h x) [Heq | Hneq].
  - subst. split

 split.
  - by apply in_map.
  - rewrite in_map_iff => [[x' [Hxx' Hinx']]]. apply Hinj in Hxx'. by subst. 
Qed. *)

(*TODO: move*)
Lemma find_lost_found_aux_in_spec: forall f base pack l x,
  In x (find_lost_found_aux f id base pack l) <-> In x base \/ (In x l /\ f (Znth x pack)).
Proof.
  move => f base pack l x. move : base. elim : l => [//= base | h t /= IH base].
  - by split => [Hin | [Hin | [Hfalse Hf]]]; try left.
  - case Hfh : (f (Znth h pack)).
    + rewrite IH in_app_iff /= binop_lemmas2.or_False or_assoc. apply or_iff_compat_l.
      split.
      * move => [Hxh | [Hin Hh]].
        -- subst. split. by left. by [].
        -- split. by right. by [].
      * move => [[Hxh | Hin] Hf].
        -- subst. by left.
        -- right. by split.
    + rewrite IH. apply or_iff_compat_l. split.
      * move => [Hin Hf]. split. by right. by [].
      * move => [[Hhx | Hin] Hf]. subst. by rewrite Hf in Hfh. by split.
Qed.  

Lemma and_true_l: forall (P Q: Prop),
  P ->
  ((P /\ Q) <-> Q).
Proof.
  tauto.
Qed.
    
(*TODO: move*)
Lemma find_lost_found_in: forall l k x,
  0 <= x < k ->
  In x (find_found l k) <-> ~ In x (find_lost l k).
Proof.
  move => l k x Hxk. rewrite !find_lost_found_aux_in_spec /= !binop_lemmas2.False_or.
  have Hin: In x (Ziota 0 k) by rewrite Zseq_In; lia.
  rewrite !and_true_l //. symmetry. apply rwN. apply idP.
Qed.

(*TODO: move to map2d*)

Lemma map2d_Znth_eq: forall {A B} (l1 l2: list (list A)) (f: A -> B) i,
  Znth i l1 = Znth i l2 ->
  0 <= i < Zlength l1 ->
  0 <= i < Zlength l2 ->
  Znth i (map_2d f l1) = Znth i (map_2d f l2).
Proof.
  move => A B l1 l2 f i Hnth Hil1 Hil2. by rewrite /map_2d !Znth_map // Hnth.
Qed.

(*Or else things get unfolded a lot*)
Lemma int_to_poly_mx_Znth_eq: forall (l1 l2: list (list Z)) i,
  Znth i l1 = Znth i l2 ->
  0 <= i < Zlength l1 ->
  0 <= i < Zlength l2 ->
  Znth i (int_to_poly_mx l1) = Znth i (int_to_poly_mx l2).
Proof.
  move => l1 l2 i Hnth Hil1 Hil2. by apply map2d_Znth_eq.
Qed.

(*TODO: move*)
(*TODO: maybe combine w other one*)
Lemma find_parity_aux_in_iff: forall par base l x,
  In x (find_parity_aux id par base l) <-> In x base \/ (In x l /\ exists p, Znth x par = Some p).
Proof.
  move => par base l x. move: base. elim : l => [//= base | h t /= IH base].
  - by split => [ Hin //| [Hin // | [Hfalse Hex //]]]; left.
  - case Hnth : (Znth h par) => [c |]; rewrite IH /=.
    + rewrite in_app_iff /= or_assoc binop_lemmas2.or_False. apply or_iff_compat_l. split.
      * move => [Hxh | [Hint Hex]]. 
        -- subst. split. by left. by exists c.
        -- split. by right. by [].
      * move => [[Hxh | Hin] Hex].
        -- subst. by left.
        -- right. by split.
    + apply or_iff_compat_l. split.
      * move => [Hin Hex]. split. by right. by [].
      * move => [[Hhx | Hin] [p Hex]]. subst. by rewrite Hex in Hnth. split. by []. by exists p.
Qed. 

Lemma fill_missing_some: forall c l i p,
  0 <= i < Zlength l ->
  Znth i l = Some p ->
  Znth i (fill_missing c l) = p.
Proof.
  move => c l i p Hlen Hith. by rewrite Znth_map // Hith.
Qed. 

Lemma fill_missing_mx_some: forall c l i j p,
  Znth i l = Some p ->
  0 <= j < c ->
  0 <= i < Zlength l ->
  Zlength p = c ->
  get (int_to_poly_mx (fill_missing c l)) i j = Z_to_F (Znth j p).
Proof.
  move => c l i j p Hith Hj Hilen Hlenp.
  rewrite /get. rewrite map_2d_Znth /= /Z_to_F. by rewrite !(fill_missing_some _ Hilen Hith).
  by rewrite Zlength_map. by rewrite (fill_missing_some _ Hilen Hith) Hlenp.
Qed.

Lemma matrix_to_mx_get : forall m n (l: matrix F) mx (i: 'I_(Z.to_nat m)) (j: 'I_(Z.to_nat n)),
  matrix_to_mx m n l = mx ->
  get l (Z.of_nat i) (Z.of_nat j) = mx i j.
Proof.
  move => m n l mx i j. move <-. by rewrite mxE.
Qed.

Lemma poly_to_int_Z_F: forall f,
  Z_to_F (poly_to_int (f_to_poly f)) = f.
Proof.
  move => f. rewrite /f_to_poly/ Z_to_F poly_of_int_inv //=. case : f => p Hp. exist_eq.
  rewrite /=. apply pmod_refl => [// | //]. apply mod_poly_PosPoly.
Qed. 

(*The correctness theorem for the decoder, at the matrix level. We will convert this back to list(list Z) and give
  more convenient preconditions for clients of the VST code*)
Lemma decoder_list_mx_correct:forall k c h xh data packets parities stats,
  0 < k <= fec_n - 1 - fec_max_h ->
  0 < c ->
  0 < h <= fec_max_h ->
  xh <= h ->
  xh <= k ->
  Zlength (find_lost stats k) = xh ->
  Zlength (find_parity_rows parities h) = xh ->
  Zlength parities = h ->
  Zlength stats = k ->
  Zlength packets = k ->
  Zlength data = k ->
  Forall (fun l => Zlength l <= c) data ->
  (forall l, In (Some l) parities -> Zlength l = c) ->
  (forall i, 0 <= i < k -> Znth i stats <> 1%Z -> Znth i packets = Znth i data) ->
  parities_valid k c parities data ->
  matrix_to_mx k c (decode_list_mx k c packets parities stats) = (matrix_to_mx k c (extend_mx k c (int_to_poly_mx data))).
Proof.
  move => k c h xh data packets parities stats Hkn Hc Hhh Hxhh Hxhk Hlostlen Hrowslen Hparlen Hstatslen Hpacklen 
    Hdatalen Hdatalens Hparlens Hfound Hpars.
  (*Things we need multiple times*)
  have Hstatsun: uniq (Z_ord_list (find_lost stats k) k). { apply Z_ord_list_uniq. eapply Forall_impl.
    2: { apply find_lost_bound; lia. } move => a. rewrite /=. lia. apply find_lost_NoDup. }
  have Hrowsun : uniq (Z_ord_list (find_parity_rows parities h) h). { apply Z_ord_list_uniq. eapply Forall_impl.
    2: { apply find_parity_rows_bound; lia. } move => a. rewrite /=; lia. apply find_parity_rows_NoDup. }
  have Hstatssz: size (Z_ord_list (find_lost stats k) k) = Z.to_nat xh. { rewrite size_length -ZtoNat_Zlength Z_ord_list_Zlength //=.
    by rewrite Hlostlen. apply find_lost_bound; lia. }
  have Hrowssz: size (Z_ord_list (find_parity_rows parities h) h) = Z.to_nat xh. { rewrite size_length -ZtoNat_Zlength
    Z_ord_list_Zlength. by rewrite Hrowslen. apply find_parity_rows_bound; lia. }
  rewrite (@decode_list_mx_equiv _ _ _ _ packets parities stats Hkn Hc Hhh Hxhk) // decoder_equivalent //=.
  - rewrite (decoder_correct (data:=(matrix_to_mx k c (extend_mx k c (int_to_poly_mx data)))) max_h_n weight_list_uniq weight_list_size (ord_zero h_pos) (ord_zero n_pos) 
        (ord_zero (proj1 Hkn)) (ord_zero Hc) (le_Z_N Hxhh) ) //.
    + move => x y. rewrite !mxE !extend_mx_spec; try (apply Z_ord_bound; lia). 
      rewrite Z_ord_list_notin //=. 2: apply find_lost_bound; lia. rewrite -find_lost_found_in. 2: apply Z_ord_bound; lia.
      rewrite find_lost_found_aux_in_spec /= => [[Hfalse // | [Htriv Hstats]]].
      have Hstatsx: Znth (Z.of_nat x) stats <> 1%Z. by move : Hstats; case : (Z.eq_dec (Znth (Z.of_nat x) stats) 1%Z).
      apply Hfound in Hstatsx. 2: apply Z_ord_bound; lia. rewrite (int_to_poly_mx_Znth_eq Hstatsx) //.
      rewrite Hpacklen. apply Z_ord_bound; lia. rewrite Hdatalen. apply Z_ord_bound; lia.
    + move => x y. rewrite Z_ord_list_In. 2: apply find_parity_rows_bound; lia.
      rewrite find_parity_aux_in_iff /= => [[ Hfalse // | [Htriv [p Hnthx]]]].
      rewrite mxE. have Hx: (0 <= Z.of_nat x < h) by (apply Z_ord_bound; lia).
      have Hx': (0 <= Z.of_nat x < Zlength parities) by lia.
      have  Hy: (0 <= Z.of_nat y < c) by (apply Z_ord_bound; lia).
      move: Hpars; rewrite /parities_valid => /(_ (Z.of_nat x) (Z.of_nat y) Hx' Hy).
      rewrite Hnthx /= (fill_missing_mx_some Hnthx) //=.
      * move ->. have [Henc [ Hc0 Hinenc]]: wf_matrix (encode_list_mx (Zlength parities) k c data) (Zlength parities) c. {
          apply list_matrix_multiply_wf; lia. }
        rewrite -(@matrix_to_mx_get _ _ (encode_list_mx h k c data)) //=.
        rewrite /get norev_mx_Znth; try lia. by rewrite /= poly_to_int_Z_F Hparlen.
        rewrite -Henc in Hx'.
        move: Hinenc; rewrite Forall_Znth => /(_ (Z.of_nat x) Hx'); lia.
        have Hkn': k <= fec_n - 1  by lia. 
        have->: (k_leq_n (k_bound_proof (proj2 Hkn))) = le_Z_N Hkn'. 
          apply ProofIrrelevance.proof_irrelevance. rewrite -weight_mx_spec. 
        apply encoder_spec; try lia. by [].
      * apply Hparlens; rewrite -Hnthx. apply Znth_In. rewrite Hparlen. apply Z_ord_bound; lia.
  - apply weight_list_uniq.
  - apply F_char_2.
Qed.

(*Restore the packets to their original lengths*)
Definition crop_mx (mx: matrix F) (lens: list Z) :=
  map (fun x => sublist 0 (Znth x lens) (Znth x mx)) (Ziota 0 (Zlength mx)).

(*As long as the lengths array is correct and all lengths are bounded by c, [crop_mx] and [extend_mx] are
  inverses*) 
Lemma crop_extend: forall mx lens c,
  0 <= c ->
  Zlength mx = Zlength lens ->
  (forall i, 0 <= i < Zlength mx -> Znth i lens = Zlength (Znth i mx)) ->
  Forall (fun x => Zlength x <= c) mx ->
  crop_mx (extend_mx (Zlength mx) c mx) lens = mx.
Proof.
  move => mx lens c Hc Hlen Hlens Hcbound.
  have Hmxlen: 0 <= Zlength mx by list_solve. 
  pose proof (@extend_mx_wf _ (Zlength mx) c mx Hc Hmxlen) as [Hextlen [H0c Hall]].
  have Hcroplen: Zlength (crop_mx (extend_mx (Zlength mx) c mx) lens) = Zlength mx
    by rewrite Zlength_map Zlength_Ziota; try lia.
  apply Znth_eq_ext =>[//| i]. rewrite Hcroplen => Hi.
  rewrite Znth_map /=. rewrite !Znth_Ziota //; try lia. 2: by rewrite Hextlen.
  rewrite Hlens //. 2: rewrite Zlength_Ziota //; [rewrite Hextlen //| rewrite Hextlen; lia].
  have Hsublen: Zlength (sublist 0 (Zlength (Znth i mx)) (Znth i (extend_mx (Zlength mx) c mx))) = Zlength (Znth i mx). {
    rewrite Zlength_sublist; try lia. list_solve.
    have Hi': 0 <= i < Zlength (extend_mx (Zlength mx) c mx) by lia.
    move: Hall; rewrite Forall_Znth => /(_ i Hi'). move ->.
    by move: Hcbound; rewrite Forall_Znth => /(_ i Hi). }
  apply Znth_eq_ext =>[//| j]. rewrite Hsublen => Hj. rewrite Znth_sublist; try lia.
  rewrite Z.add_0_r. pose proof extend_mx_spec as Hextget. rewrite /get in Hextget; rewrite Hextget{Hextget} //.
  case : (Z_lt_le_dec j (Zlength (Znth i mx))) => [//= Hj' | /= Hj']. 
  have: j < j by apply (Z.lt_le_trans _ _ _ (proj2 Hj)).  (*lia doesnt work for some reason*)
  lia. move: Hcbound; rewrite Forall_Znth => /(_ i Hi). lia.
Qed.

(*For the decoder preconditions, we don't want to explicitly mention [find_lost] and [find_parity_rows], especially
  since only the length is important. So we will use [filter] instead, which should be easier to reason about*)


Lemma find_lost_found_aux_Zlength: forall f g base pack l,
  Zlength (find_lost_found_aux f g base pack l) = Zlength base + Zlength (find_lost_found_aux f g [::] pack l).
Proof.
  move => f g base pack l. move: base. elim : l => [//= base| h t /= IH base].
  - list_solve.
  - rewrite IH (IH (if f (Znth h pack) then [:: g h] else [::])). case Hf: (f (Znth h pack)).
    + rewrite Zlength_app. lia.
    + list_solve.
Qed.

(*Need a pretty strong IH, so use sublists*)
Lemma find_lost_found_aux_filter_sublist: forall f g pack (hi : nat),
  (Z.of_nat hi <= Zlength pack) ->
  Zlength (find_lost_found_aux f g [::] pack (Ziota 0 (Z.of_nat hi))) = 
  Zlength (filter f (sublist 0 (Z.of_nat hi) pack)).
Proof.
  move => f g pack hi. elim : hi => [//= | hi IH Hlen].
  have->: (Z.of_nat hi.+1) = (Z.of_nat hi + 1)%Z by lia. rewrite Ziota_plus_1; try lia.
  rewrite sublist_last_1; try lia. rewrite find_lost_found_aux_app find_lost_found_aux_Zlength /= filter_cat /=.
  rewrite IH //. rewrite Zlength_app !Z.add_0_l //.
  case Hf: (f (Znth (Z.of_nat hi) pack)); list_solve.
  lia.
Qed.

(*Now we can state the precondition in terms of filter, so a client doesn't need to know anything about
  [find_lost]*)
Lemma find_lost_filter: forall stats k,
  k = Zlength stats ->
  Zlength (find_lost stats k) = Zlength (filter (fun x => Z.eq_dec x 1) stats).
Proof.
  move => stats k Hk. have Hk0: 0 <= k by list_solve.
  have ->: k = Z.of_nat (Z.to_nat k) by lia. rewrite find_lost_found_aux_filter_sublist; try lia.
  rewrite sublist_same //. lia.
Qed.

(*Similar thing for parities*)

(*TODO: maybe can make generic with f : A -> Z -> bool, and ignore 1st argument for lost/found*)

Lemma find_parity_aux_app: forall f par base l1 l2,
  find_parity_aux f par base (l1 ++ l2) =
  find_parity_aux f par (find_parity_aux f par base l1) l2.
Proof.
  move => f par b l1 l2. by rewrite /find_parity_aux fold_left_app.
Qed.

Lemma find_parity_aux_filter_sublist: forall f (par : seq (option (seq Z))) (hi: nat),
  (Z.of_nat hi <= Zlength par) ->
  Zlength (find_parity_aux f par [::] (Ziota 0 (Z.of_nat hi))) = 
  Zlength (filter isSome (sublist 0 (Z.of_nat hi) par)).
Proof.
  move => f par hi. elim : hi => [//= | hi IH Hlen].
  have->: (Z.of_nat hi.+1) = (Z.of_nat hi + 1)%Z by lia. rewrite Ziota_plus_1; try lia.
  rewrite sublist_last_1; try lia. rewrite find_parity_aux_app find_parity_aux_base_Zlength /= filter_cat /=.
  rewrite IH //. 2: lia. rewrite Zlength_app !Z.add_0_l //.
  by case Hf: (Znth (Z.of_nat hi) par).
Qed.

(*Now we can state the precondition in terms of filter, so a client doesn't need to know anything about
  [find_parity_rows]*)
Lemma find_parity_rows_filter: forall parities h,
  Zlength parities = h ->
  Zlength (find_parity_rows parities h) = Zlength (filter isSome parities).
Proof.
  move => pars h Hh. have Hh0: 0 <= h by list_solve.
  have ->: h = Z.of_nat (Z.to_nat h) by lia. rewrite find_parity_aux_filter_sublist; try lia.
  rewrite sublist_same //. lia.
Qed.

Lemma matrix_to_mx_inj: forall (mx1 mx2 : matrix F) m n,
  wf_matrix mx1 m n ->
  wf_matrix mx2 m n ->
  matrix_to_mx m n mx1 = matrix_to_mx m n mx2 ->
  mx1 = mx2.
Proof.
  move => mx1 mx2 m n [Hlen1 [Hn Hall1]] [Hlen2 [Hn' Hall2]]. rewrite -matrixP /eqrel => Hmx.
  apply Znth_eq_ext. lia. move => i Hi. 
  have Hleni: Zlength (Znth i mx1) = n by move: Hall1; rewrite Forall_Znth => /(_ i Hi).
  have Hleni': Zlength (Znth i mx2) = n by move : Hall2; rewrite Hlen1 in Hi; rewrite -Hlen2 in Hi;
    rewrite Forall_Znth => /(_ i Hi).
  apply Znth_eq_ext. lia. move => j. rewrite Hleni => Hj.
  rewrite Hlen1 in Hi. move: Hmx => /(_ (Z_to_ord Hi) (Z_to_ord Hj)). by rewrite !mxE /get /= !Z2Nat.id; try lia.
Qed.

(*TODO: MOVE*)
Lemma map_2d_twice: forall {A B C: Type} (f: A -> B) (g: B -> C) (l: seq (seq A)),
  map_2d g (map_2d f l) = map_2d (fun x => g (f x)) l.
Proof.
  move => A B C f g l. rewrite /map_2d !map_map /=. apply map_ext.
  move => a. by rewrite map_map.
Qed. 

Lemma poly_of_int_byte: forall (z: Z),
  0 <= z < Byte.max_unsigned ->
  poly_of_int z %~ mod_poly = poly_of_int z.
Proof.
  move => z Hz. apply pmod_refl. apply mod_poly_PosPoly. apply polys_deg_bounded. rep_lia.
Qed.

(*TODO: move*)
Lemma poly_to_int_inv: forall z,
  0 <= z ->
  poly_to_int (poly_of_int z) = z.
Proof.
  move => z Hz. symmetry. by rewrite -poly_of_int_to_int.
Qed.

Lemma norev_mx_int_to_poly_mx: forall (l: list (list Z)),
  Forall2D (fun x => 0 <= x < Byte.max_unsigned) l ->
  norev_mx (int_to_poly_mx l) = l.
Proof.
  move => l Hall. rewrite /norev_mx /int_to_poly_mx map_2d_twice /=. 
  apply Znth_eq_ext; rewrite map_2d_Zlength1 //= => i Hi.
  apply Znth_eq_ext; rewrite map_2d_Zlength2 // => j Hj.
  move : Hall; rewrite Forall2D_Znth => /(_ i j Hi Hj) => Hij.
  rewrite map_2d_Znth // poly_of_int_byte // poly_to_int_inv //. lia.
Qed.

(*TODO: move*)
Print fill_row_list.
Lemma fill_row_list_wf: forall m n d r row_d row_r,
  0 <= m ->
  0 <= n ->
  wf_matrix (fill_row_list m n d r row_d row_r) m n.
Proof.
  move => m n d r row_d row_r. by apply mk_matrix_wf.
Qed.

Lemma fill_rows_list_aux_wf: forall m n d r to_fill l,
  wf_matrix d m n ->
  wf_matrix (fill_rows_list_aux m n d r to_fill l) m n.
Proof.
  move => m n d r to_fill l. apply mx_foldl_wf. move => mx' i Hwf'.
  apply fill_row_list_wf. apply (matrix_m_pos Hwf'). apply (matrix_n_pos Hwf').
Qed.

(** Final Definition of Decoder and Correctness*)

(*Our final decoder definition does everything in terms of lists and Z, making it useful for VST*)
Definition decoder_list k c packets parities stats lens :=
  norev_mx (crop_mx (decode_list_mx k c packets parities stats) lens).

Theorem decoder_list_correct: forall k c h xh (data packets : list (list Z)) 
  (parities : list (option (list Z))) (stats lens : list Z),
  0 < k <= fec_n - 1 - fec_max_h ->
  0 < c ->
  0 < h <= fec_max_h ->
  xh <= h ->
  xh <= k ->
  Zlength (filter (fun x => Z.eq_dec x 1) stats) = xh ->
  Zlength (filter isSome parities) = xh ->
  Zlength parities = h ->
  Zlength stats = k ->
  Zlength packets = k ->
  Zlength data = k ->
  Zlength lens = k ->
  (forall i, 0 <= i < k -> Znth i lens = Zlength (Znth i data)) ->
  Forall (fun l => Zlength l <= c) data ->
  Forall2D (fun x => 0 <= x < Byte.max_unsigned) data ->
  (forall i, 0 <= i < k -> Znth i stats <> 1%Z -> Znth i packets = Znth i data) ->
  (forall l, In (Some l) parities -> Zlength l = c) ->
  parities_valid k c parities data ->
  decoder_list k c packets parities stats lens = data.
Proof.
  move => k c h xh data packets parities stats lens Hknh Hc Hh Hxhh Hxhk Hstatsxh Hparsxh Hparlen
    Hstatlen Hpacklen Hdatalen Hlenslen Hlens Hdatac Hdatabound Hpackdata Hparlens Hparvalid.
  rewrite /decoder_list. 
  have Hmx: matrix_to_mx k c (decode_list_mx k c packets parities stats) = 
    (matrix_to_mx k c (extend_mx k c (int_to_poly_mx data))). { 
    apply (decoder_list_mx_correct Hknh Hc Hh Hxhh); try by [].
    - by rewrite find_lost_filter.
    - by rewrite find_parity_rows_filter. }
  apply matrix_to_mx_inj in Hmx. 
  - rewrite Hmx. have->: k = Zlength (int_to_poly_mx data) by rewrite int_to_poly_mx_length1 Hdatalen.
    rewrite crop_extend; try lia.
    + by apply norev_mx_int_to_poly_mx.
    + rewrite int_to_poly_mx_length1; lia.
    + move => i. rewrite int_to_poly_mx_length1 => Hi.
      rewrite int_to_poly_mx_length2. apply Hlens. lia.
    + move: Hdatac; rewrite !Forall_Znth => Hall x. rewrite int_to_poly_mx_length1 => Hx.
      rewrite int_to_poly_mx_length2. by apply Hall.
  - apply fill_rows_list_aux_wf. apply extend_mx_wf; lia.
  - apply extend_mx_wf; lia.
Qed.

End Decoder.
