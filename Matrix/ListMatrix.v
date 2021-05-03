(*Represent Matrices as 2D lists of elements in a field F, indexed by Z. This allows us to deal with all of the
  Ordinal and other dependent type proof obligations here, giving a nicer interface for the VST proofs that uses
  [Znth], [sublist], and Z, and lets us use lia for the resulting goals*)

Require Import VST.floyd.functional_base.

From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import Gaussian.
Require Import CommonSSR.
Require Import ZSeq.
Require Import Vandermonde. (*for [submx_rows_cols]*)
Require Import ReedSolomon. (*for [fill_row]*)
Require Import ByteFacts. (*for [byte_unsigned_inj]*)

(** Converting Between Z and Ordinals*)

(*Convert bounded Z to ordinal*)
Lemma Z_nat_bound: forall m x (Hx: 0 <= x < m),
  (Z.to_nat x < Z.to_nat m)%N.
Proof.
  intros m x Hxm. have Hcoqnat: (Z.to_nat x < Z.to_nat m)%coq_nat by apply Z2Nat.inj_lt; lia.
  by apply (introT ltP).
Qed.

Lemma Z_ord_bound: forall {m} (x : 'I_(Z.to_nat m)),
  0 <= m ->
  0 <= Z.of_nat x < m.
Proof.
  move => m x Hm. have HxmN: (x < Z.to_nat m)%N by [].
  have Hxm_nat : (x < Z.to_nat m)%coq_nat by apply (elimT ltP). by lia.
Qed.

Definition Z_to_ord {m} x (Hx: 0 <= x < m) : 'I_(Z.to_nat m) :=
  Ordinal (Z_nat_bound Hx).

Lemma le_Z_N: forall (m n: Z),
  m <= n ->
  (Z.to_nat m <= Z.to_nat n)%N.
Proof.
  move => m n Hmn. apply (introT leP). lia.
Qed.

Lemma Z_ord_bound_nat: forall {m} x (Hx: 0 <= x < m),
  nat_of_ord (Z_to_ord Hx) = Z.to_nat x.
Proof. by []. Qed.

Lemma eq_ord_int: forall {m} x y (Hx: 0 <= x < m) (Hy: 0 <= y < m),
  (Z_to_ord Hx == Z_to_ord Hy) = proj_sumbool (Z.eq_dec x y).
Proof.
  move => m x y Hx Hy.
  case: (Z.eq_dec x y) => [Hxy /= | Hxy /=].
  - apply /eqP. apply ord_inj. by subst.
  - apply /eqP. move => Ho. have: (Z.to_nat x = Z.to_nat y).
    by rewrite -!(@Z_ord_bound_nat m) Ho. lia.
Qed.

Lemma ord_zero_proof n (H: 0 < n) : (0 < Z.to_nat n)%N.
Proof.
  apply /ltP. lia.
Qed.

Definition ord_zero n (H: 0 < n) : 'I_(Z.to_nat n) :=
  Ordinal (ord_zero_proof H).

(** Z_ord_list - transform a list of Z into a list of 'I_n*)
Section ZOrdList.

Definition Z_ord_list (l: list Z) (n: Z) : seq 'I_(Z.to_nat n) :=
  pmap insub (map Z.to_nat l).

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

Lemma Z_ord_list_app: forall n l1 l2,
  Z_ord_list (l1 ++ l2) n = Z_ord_list l1 n ++ Z_ord_list l2 n.
Proof.
  move => n l1 l2. rewrite /Z_ord_list. (*not just pmap, so need induction*)
  elim : l1 => [//= | h t /= IH].
  case Hh: (Z.to_nat h < Z.to_nat n)%N.
  - by rewrite !insubT /= IH.
  - by rewrite !insubF //= IH.
Qed.

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

End ZOrdList. 

(*We also need a Byte version for the decoder.*)
Section ByteOrdList.

Lemma Z_byte_list_bound: forall l u s,
  Forall (fun x => l <= Byte.unsigned x < u) s ->
  Forall (fun x => l <= x < u) (map Byte.unsigned s).
Proof.
  move => l u s. rewrite !Forall_Znth => Hall i. rewrite Zlength_map => Hi.
  rewrite Znth_map //. by apply Hall.
Qed.

Definition byte_ord_list (l: list byte) (n: Z) : seq 'I_(Z.to_nat n) :=
  Z_ord_list (map Byte.unsigned l) n.

Lemma byte_ord_list_fold: forall l n,
  Z_ord_list (map Byte.unsigned l) n = byte_ord_list l n.
Proof.
  by [].
Qed.

Lemma byte_ord_list_Zlength: forall n l,
  Forall (fun x => 0 <= Byte.unsigned x < n) l ->
  Zlength (byte_ord_list l n) = Zlength l.
Proof.
  move => n l Hall. rewrite Z_ord_list_Zlength. by rewrite Zlength_map.
  by apply Z_byte_list_bound.
Qed.

Lemma byte_list_bound: forall (l: seq byte) n i,
  Forall (fun x => 0 <= Byte.unsigned x < n) l ->
  0 <= i < Zlength l ->
  (Z.to_nat (Byte.unsigned (Znth i l)) < Z.to_nat n)%N.
Proof.
  move => l n i. rewrite Forall_Znth => /(_ i) Hin Hi. apply /ltP. lia.
Qed.

Lemma byte_ord_list_Znth': forall (l: seq byte) n i `{Inhabitant 'I_(Z.to_nat n)} (Hi: 0 <= i < Zlength l)
  (Hall: Forall (fun x => 0 <= Byte.unsigned x < n) l),
  0 <= n ->
  Znth i (byte_ord_list l n) = Ordinal (byte_list_bound Hall Hi).
Proof.
  move => l n i Hinhab Hi Hall Hn. rewrite /byte_ord_list Z_ord_list_Znth'.
  - by apply Z_byte_list_bound.
  - by rewrite Zlength_map.
  - move => Hmap Hlen. apply ord_inj. by rewrite /= Znth_map.
  - by [].
Qed. 

Lemma byte_ord_list_uniq: forall (l: seq byte) n,
  NoDup l ->
  uniq (byte_ord_list l n).
Proof.
  move => l n Huniq. apply Z_ord_list_uniq.
  - rewrite Forall_Znth => i. rewrite Zlength_map => Hi. rewrite Znth_map //. rep_lia.
  - apply FinFun.Injective_map_NoDup => [|//]. move => x y. apply byte_unsigned_inj.
Qed.


Lemma byte_ord_list_widen: forall n m (H: (Z.to_nat n <= Z.to_nat m)%N) (l: list byte),
  Forall (fun x => 0 <= Byte.unsigned x < n) l ->
  byte_ord_list l m = widen_ord_seq H (byte_ord_list l n).
Proof.
  move => n m H l. rewrite /byte_ord_list /Z_ord_list. elim : l => [//= | h t /= IH Hforall].
  have Hhn: (Z.to_nat (Byte.unsigned h) < Z.to_nat n)%N. apply /ltP.
    have Hhn: (0 <= Byte.unsigned h < n) by apply (Forall_inv Hforall). lia. 
  rewrite !insubT. by apply (ltn_leq_trans Hhn). move => Hhm.
  rewrite /= IH. f_equal. by apply ord_inj. apply (Forall_inv_tail Hforall).
Qed.

Lemma byte_ord_list_app: forall n l1 l2,
  byte_ord_list (l1 ++ l2) n = byte_ord_list l1 n ++ byte_ord_list l2 n.
Proof.
  move => n l1 l2. by rewrite /byte_ord_list !map_cat Z_ord_list_app.
Qed.

Lemma byte_ord_list_In: forall (l: seq byte) n x,
  Forall (fun x => 0 <= Byte.unsigned x < n) l ->
  Z.of_nat (nat_of_ord x) <= Byte.max_unsigned ->
  x \in (byte_ord_list l n) <->
  In (Byte.repr (Z.of_nat x)) l.
Proof.
  move => l n x Hall Hx. rewrite /byte_ord_list. rewrite Z_ord_list_In; last first.
  by apply Z_byte_list_bound.  rewrite in_map_iff. split.
  - move => [y [Hxy Hiny]]. by rewrite -Hxy Byte.repr_unsigned.
  - move => Hin. exists (Byte.repr (Z.of_nat x)). split => [|//].
    rewrite Byte.unsigned_repr //. rep_lia. 
Qed.

Lemma byte_ord_list_notin: forall (l: seq byte) n x,
  Forall (fun x => 0 <= Byte.unsigned x < n) l ->
  Z.of_nat (nat_of_ord x) <= Byte.max_unsigned ->
  x \notin (byte_ord_list l n) <->
  ~  In (Byte.repr (Z.of_nat x)) l.
Proof.
  move => l n x Hall. split => Hnotin.
  - rewrite -byte_ord_list_In //. by apply /idP.
  - move: Hnotin; rewrite -byte_ord_list_In //=.
    by case : (x \in byte_ord_list l n).
Qed.


(*TODO: move to CommonSSR*)
Lemma rev_pmap: forall {aT rT} (f: aT -> option rT) (s: seq aT),
  rev (pmap f s) = pmap f (rev s).
Proof.
  move => aT rT f s. elim : s => [// | h t /= IH].
  rewrite rev_cons -cats1 pmap_cat /= -IH.
  case Hf: (f h) =>[/= u|/=].
  - by rewrite rev_cons -cats1.
  - by rewrite cats0.
Qed.

Lemma byte_ord_list_rev: forall l n,
  rev (byte_ord_list l n) = byte_ord_list (rev l) n.
Proof.
  move => l n. by rewrite /byte_ord_list /Z_ord_list rev_pmap !map_rev.
Qed.

End ByteOrdList.
  
Section ListMx.

Variable F : fieldType.

Local Open Scope ring_scope.

Instance inhabitant_F: Inhabitant F.
apply 0.
Defined.

(** ListMatrix definitions and constructors*)

Definition lmatrix := list (list F).

Definition wf_lmatrix (mx: lmatrix) (m n : Z) :=
  Zlength mx = m /\ 0 <= n /\ Forall (fun x => Zlength x = n) mx.

(*get the (i,j)th entry of a lmatrix*)
Definition get (mx: lmatrix) (i j : Z) :=
  let row := Znth i mx in
  Znth j row.

Definition set (mx: lmatrix) (i j : Z) (k: F) :=
  let row := Znth i mx in
  let new_row := upd_Znth j row k in
  upd_Znth i mx new_row.

Lemma set_wf: forall m n mx i j k,
  wf_lmatrix mx m n ->
  wf_lmatrix (set mx i j k) m n.
Proof.
  move => m n mx i j k [Hlen [Hn Hin]].
  move : Hin; rewrite Forall_Znth /wf_lmatrix /set => Hin.
  split. list_solve. split. by []. rewrite Forall_Znth Zlength_upd_Znth => i' Hi'.
  have [Hii' | Hii']: i = i' \/ i <> i' by lia.
  - subst. rewrite upd_Znth_same; list_solve.
  - list_solve.
Qed. 

Lemma get_set: forall m n mx i j i' j' k,
  wf_lmatrix mx m n ->
  0 <= i < m ->
  0 <= i' < m ->
  0 <= j < n ->
  0 <= j' < n -> 
  get (set mx i' j' k) i j = if (Z.eqb i i') && (Z.eqb j j') then k else get mx i j.
Proof.
  move => m n mx i j i' j' k [Hlen [ Hn Hin]] Hi Hi' Hj Hj'. rewrite /get /set.
  move : Hin; rewrite Forall_Znth => Hin. 
  case Hii' : (Z.eqb i i'); move : Hii' => /Z.eqb_spec Hii' /=.
  - subst. rewrite upd_Znth_same; [| lia].
    case Hjj' : (Z.eqb j j'); move : Hjj' => /Z.eqb_spec Hjj' /=.
    + subst. rewrite upd_Znth_same. by []. rewrite Hin; lia.
    + by rewrite upd_Znth_diff; try rewrite Hin; try lia.
  - by rewrite upd_Znth_diff; try lia.
Qed.

Lemma lmatrix_m_pos: forall {m n} (mx: lmatrix) (Hwf: wf_lmatrix mx m n),
  0 <= m.
Proof.
  move => m n mx. rewrite /wf_lmatrix => [[Hm Hn]]. list_solve.
Qed.

Lemma lmatrix_n_pos: forall {m n} (mx: lmatrix) (Hwf: wf_lmatrix mx m n),
  0 <= n.
Proof.
  move => m n mx. by rewrite /wf_lmatrix => [[Hm [Hn Hin]]].
Qed.

Definition lmatrix_to_mx m n (mx: lmatrix) : 'M[F]_(Z.to_nat m, Z.to_nat n) :=
  \matrix_(i < Z.to_nat m, j < Z.to_nat n) (get mx (Z.of_nat i) (Z.of_nat j)).

Lemma matrix_to_mx_get : forall m n (l: lmatrix) mx (i: 'I_(Z.to_nat m)) (j: 'I_(Z.to_nat n)),
  lmatrix_to_mx m n l = mx ->
  get l (Z.of_nat i) (Z.of_nat j) = mx i j.
Proof.
  move => m n l mx i j. move <-. by rewrite mxE.
Qed.

Lemma lmatrix_to_mx_inj: forall (mx1 mx2 : lmatrix) m n,
  wf_lmatrix mx1 m n ->
  wf_lmatrix mx2 m n ->
  lmatrix_to_mx m n mx1 = lmatrix_to_mx m n mx2 ->
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

Lemma lmatrix_ext_eq: forall m n mx1 mx2,
  wf_lmatrix mx1 m n ->
  wf_lmatrix mx2 m n ->
  (forall i j, 0 <= i < m -> 0 <= j < n -> get mx1 i j = get mx2 i j) -> 
  mx1 = mx2.
Proof.
  move => m n mx1 mx2 [Hm1 [Hn1 Hin1]] [Hm2 [Hn2 Hin2]] Hsame. apply Znth_eq_ext. lia.
  move => i Hi. move: Hin1 Hin2; rewrite !Forall_Znth => Hin1 Hin2.
  apply Znth_eq_ext. rewrite Hin1 =>[|//]. rewrite Hin2; lia.
  move => j Hj. rewrite Hin1 in Hj =>[|//]. apply Hsame; lia.
Qed.

(*Create a lmatrix by giving a function for the elements*)
Section GenMx.

Definition mk_lmatrix m n (f: Z -> Z -> F) : lmatrix :=
  mkseqZ (fun i => mkseqZ (fun j => f i j) n) m.

Lemma mk_lmatrix_wf: forall m n f,
  0 <= m ->
  0 <= n ->
  wf_lmatrix (mk_lmatrix m n f) m n.
Proof.
  move => m n f Hm Hn. rewrite /wf_lmatrix /mk_lmatrix mkseqZ_Zlength =>[|//].
  repeat split; try lia. rewrite Forall_Znth mkseqZ_Zlength =>[i Hi|//].
  rewrite mkseqZ_Znth; try lia. by rewrite mkseqZ_Zlength.
Qed.

Lemma mk_lmatrix_get: forall m n f i j,
  0 <= i < m ->
  0 <= j < n ->
  get (mk_lmatrix m n f) i j = f i j.
Proof.
  move => m n f i j Hi Hj. rewrite /mk_lmatrix /get mkseqZ_Znth => [|//].
  by rewrite mkseqZ_Znth.
Qed.

Lemma mk_lmatrix_mx:forall m n (f: Z -> Z -> F) (g: 'I_(Z.to_nat m) -> 'I_(Z.to_nat n) -> F),
  0 <= m ->
  0 <= n ->
  (forall x y (Hx: 0 <= x < m) (Hy: 0 <= y < n), f x y = g (Z_to_ord Hx) (Z_to_ord Hy)) ->
  lmatrix_to_mx m n (mk_lmatrix m n f) = \matrix_(i < Z.to_nat m, j < Z.to_nat n) g i j.
Proof.
  move => m n f g Hm Hn Hfg. rewrite /lmatrix_to_mx -matrixP => x y.
  rewrite !mxE.
  have Hxm: 0 <= Z.of_nat x < m. have /ltP: (x < Z.to_nat m)%N by []. lia.
  have Hyn: 0 <= Z.of_nat y < n. have /ltP: (y < Z.to_nat n)%N by []. lia.
  rewrite mk_lmatrix_get //=. rewrite Hfg. f_equal.
  - apply ord_inj. by rewrite Z_ord_bound_nat Nat2Z.id.
  - apply ord_inj. by rewrite Z_ord_bound_nat Nat2Z.id. 
Qed.

End GenMx.

(*So we don't have to repeat this every time. This is quite annoying with ssreflect for some reason*)

Ltac case_eqb x y H :=
  case_view (x =? y) (Z.eqb_spec x y) H.

Ltac case_ltb x y H :=
  case_view (x <? y) (Z.ltb_spec0 x y) H.

(*In some cases we want to apply a lmatrix up to a specific bound. So we abstract that out here, so we don't need
  to repeat the proofs for scalar multiplication and adding multiples*)
Section BoundMx.

Definition mk_bound_mx m n mx f b :=
  mk_lmatrix m n (fun i j => if (j <?b) then f i j else (get mx i j)).

Lemma mk_bound_mx_0: forall m n mx f,
  wf_lmatrix mx m n ->
  mk_bound_mx m n mx f 0 = mx.
Proof.
  move => m n mx f Hwf. apply (@lmatrix_ext_eq m n) =>[|//|].
  apply mk_lmatrix_wf. apply (lmatrix_m_pos Hwf). apply (lmatrix_n_pos Hwf).
  move => i j Hi Hj. rewrite mk_lmatrix_get //=.
  by case_ltb j 0%Z Hj0; try lia.
Qed.

Lemma mk_bound_mx_outside: forall m n mx f b i j,
  wf_lmatrix mx m n ->
  0 <= i < m ->
  0 <= j < n ->
  b <= j ->
  get (mk_bound_mx m n mx f b) i j = get mx i j.
Proof.
  move => m n mx f b i j Hwf Hi Hj Hb. rewrite mk_lmatrix_get //=.
  by case_ltb j b Hjb; try lia.
Qed.

Lemma mk_bound_mx_full: forall m n mx f i j,
  wf_lmatrix mx m n ->
  0 <= i < m ->
  0 <= j < n ->
  get (mk_bound_mx m n mx f n) i j = f i j.
Proof.
  move => m n mx f i j Hwf Hi Hj. rewrite mk_lmatrix_get //=.
  by case_ltb j n Hjn; try lia.
Qed. 

Lemma mk_bound_mx_plus_1: forall m n mx f b r,
  wf_lmatrix mx m n ->
  0 <= b < n ->
  0 <= r < m ->
  (forall i j, 0 <= i < m -> i <> r -> f i j = get mx i j) ->
  mk_bound_mx m n mx f (b+1)%Z = set (mk_bound_mx m n mx f b) r b (f r b).
Proof.
  move => m n mx f b r Hwf Hb Hr Hrow. have Hm: 0 <= m by apply (lmatrix_m_pos Hwf).
  have Hn: 0 <= n by apply (lmatrix_n_pos Hwf). apply (@lmatrix_ext_eq m n).
  - by apply mk_lmatrix_wf.
  - apply set_wf. by apply mk_lmatrix_wf.
  - move => i j Hi Hj. 
    rewrite (@get_set m n) //=. 2: by apply mk_lmatrix_wf.
    rewrite !mk_lmatrix_get //=.
    case_eqb i r Hir; rewrite /=.
    + subst. case_eqb j b Hjb; subst.
      * by case_ltb b (b+1)%Z Hbb; try lia.
      * case_ltb j b Hjblt; by case_ltb j (b+1)%Z Hjb1; try lia.
    + rewrite Hrow //=. by case_ltb j b Hjb; case_ltb j (b+1)%Z Hjb'.
Qed.

End BoundMx.

(** ListMatrix operations for Gaussian Elimination*)

Section ScMul.

(*For the row operations, it will help to define "partial" versions that operate on a sublist, since
  we need need a loop invariant for the operation*)

(*Really, this only makes sense if mx is a wf_lmatrix m n, but we want to avoid dependent types*)
Definition scalar_mul_row_partial m n (mx: lmatrix) (r: Z) (k: F) (bound: Z) :=
  mk_bound_mx m n mx (fun i j => if Z.eq_dec i r then k * (get mx i j) else (get mx i j)) bound.

Definition scalar_mul_row m n mx r k :=
  scalar_mul_row_partial m n mx r k n.

Lemma scalar_mul_row_partial_0: forall m n mx r k,
  wf_lmatrix mx m n ->
  scalar_mul_row_partial m n mx r k 0 = mx.
Proof.
  move => m n mx r k Hwf. by apply mk_bound_mx_0.
Qed.

Lemma scalar_mul_row_partial_wf: forall mx m n r k bound,
  0 <= m ->
  0 <= n ->
  wf_lmatrix (scalar_mul_row_partial m n mx r k bound) m n.
Proof.
  move => mx m n r k b Hm Hn. by apply mk_lmatrix_wf.
Qed.

Lemma scalar_mul_row_outside: forall m n mx r k b j,
  wf_lmatrix mx m n ->
  0 <= r < m ->
  0 <= j < n ->
  b <= j ->
  get (scalar_mul_row_partial m n mx r k b) r j = get mx r j.
Proof.
  move => m n mx r k b j Hwf Hr Hj Hbj. by apply mk_bound_mx_outside.
Qed.

Lemma scalar_mul_row_spec: forall mx m n r k i j,
  wf_lmatrix mx m n ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  get (scalar_mul_row m n mx r k) i j =
    if (Z.eq_dec i r) then k * (get mx i j) else get mx i j.
Proof.
  move => mx m n r k i j Hwf Hi Hj. by apply mk_bound_mx_full.
Qed.

Lemma scalar_mul_row_plus_1: forall mx m n r k b,
  wf_lmatrix mx m n ->
  0 <= r < m ->
  0 <= b < n ->
  scalar_mul_row_partial m n mx r k (b+1)%Z = set (scalar_mul_row_partial m n mx r k b) r b (k * (get mx r b)).
Proof.
  move => mx m n r k b Hwf Hr Hb. rewrite /scalar_mul_row_partial (mk_bound_mx_plus_1 (r:=r)) //=.
  - by case: (Z.eq_dec r r) =>[Hrr /= | Hrr]; try lia.
  - move => i j Hi Hir. by case (Z.eq_dec i r) =>[|Hneq /=]; try lia.
Qed.

Lemma scalar_mul_row_equiv: forall {m n} (mx: lmatrix) r k (Hr: 0 <= r < m),
  wf_lmatrix mx m n ->
  lmatrix_to_mx m n (scalar_mul_row m n mx r k) = sc_mul (lmatrix_to_mx m n mx) k (Z_to_ord Hr).
Proof.
  move => m n mx r k Hr Hwf. rewrite /sc_mul. apply mk_lmatrix_mx.
  - apply (lmatrix_m_pos Hwf).
  - apply (lmatrix_n_pos Hwf).
  - move => x y Hx Hy. rewrite eq_ord_int.
    case: (Z.eq_dec x r) => [Hxr /= | Hxr /=].
    + case_ltb y n Hyn; try lia. by rewrite /lmatrix_to_mx mxE /= !Z2Nat.id; try lia.
    + case_ltb y n Hyn; try lia. by rewrite /lmatrix_to_mx mxE /= !Z2Nat.id; try lia.
Qed.

End ScMul.


(*Generalized notion of repeated fold_left for row transformation (we have something similar in Gaussian for foldr*)

(*We need a function that a) only affects the row it is called on and b) preserves well-formedness*)
Definition fn_notin_conds m n (f: lmatrix -> Z -> lmatrix) :=
   (forall mx' i j r, wf_lmatrix mx' m n -> 0 <= i < m -> 0 <= j < n -> i <> r -> get mx' i j = get (f mx' r) i j)/\
  (forall mx' i, wf_lmatrix mx' m n -> wf_lmatrix (f mx' i) m n).
  

Lemma mx_foldl_notin: forall m n (mx: lmatrix) (f: lmatrix -> Z -> lmatrix) (l: list Z) i j,
  fn_notin_conds m n f ->
  0 <= i < m ->
  0 <= j < n ->
  ~In i l ->
  wf_lmatrix mx m n ->
  get (fold_left f l mx) i j = get mx i j.
Proof.
  move => m n mx f l i j [Hcond Hwfpres] Hi Hj. move : mx. elim : l => [//|h t IH /= mx Hin Hwf].
  rewrite IH. rewrite -Hcond; try by []. move => Heq. subst. apply Hin. by left.
  move => Hin'. apply Hin. by right. by apply Hwfpres.
Qed.

Definition fn_in_conds m n (f: lmatrix -> Z -> lmatrix) :=
  fn_notin_conds m n f /\
  (forall mx h i j, wf_lmatrix mx m n -> 0 <= i < m -> 0 <= j < n -> i <> h -> get (f (f mx h) i) i j = get (f mx i) i j).

Lemma mx_foldl_in: forall m n (mx: lmatrix) (f: lmatrix -> Z -> lmatrix) (l: list Z) i j,
  fn_in_conds m n f ->
  0 <= i < m ->
  0 <= j < n ->
  In i l ->
  NoDup l ->
  wf_lmatrix mx m n ->
  get (fold_left f l mx) i j = get (f mx i) i j.
Proof.
  move => m n mx f l i j [[Hcond Hwfpres] Htwice] Hi Hj. move : mx. elim : l => [//|h t IH /= mx Hin Hnodup Hwf].
  move: Hnodup; rewrite NoDup_cons_iff; move => [Hnotin  Hnodupt].
  case: Hin => [Hhi | Hin].
  - subst. rewrite (@mx_foldl_notin m n); try by []. by apply Hwfpres.
  - rewrite IH. apply Htwice; try by []. move => Heq. subst. by []. by []. by []. apply Hwfpres. by [].
Qed.

Lemma mx_foldl_wf: forall m n (mx: lmatrix) (f: lmatrix -> Z -> lmatrix) (l : list Z),
  (forall mx' i, wf_lmatrix mx' m n -> wf_lmatrix (f mx' i) m n) ->
  wf_lmatrix mx m n ->
  wf_lmatrix (fold_left f l mx) m n.
Proof.
  move => m n mx f l Hwfpres. move : mx. elim : l => [//|h t IH mx Hwf /=].
  apply IH. by apply Hwfpres.
Qed.

(*We need a slightly weaker version for when f only conditionally preserves wf*)
Lemma mx_foldl_wf': forall m n (mx: lmatrix) (f: lmatrix -> Z -> lmatrix) (l : list Z),
  (forall mx' i, 0 <= i < m -> wf_lmatrix mx' m n -> wf_lmatrix (f mx' i) m n) ->
  wf_lmatrix mx m n ->
  (forall x, In x l -> 0 <= x < m) ->
  wf_lmatrix (fold_left f l mx) m n.
Proof.
  move => m n mx f l Hwfpres. move : mx. elim : l => [//|h t IH mx Hwf Hin /=].
  apply IH. apply Hwfpres. apply Hin. by left. by []. move => x Hinx. apply Hin. by right.
Qed.

(*Now specialize this for functions operating on Ziota 0 b*)
Lemma foldl_ziota_get: forall m n (mx: lmatrix) (f: lmatrix -> Z -> lmatrix) (b: Z) i j,
  fn_in_conds m n f ->
  0 <= i < m ->
  0 <= j < n ->
  0 <= b ->
  wf_lmatrix mx m n ->
  get (fold_left f (Ziota 0 b) mx) i j = if (Z_lt_le_dec i b) then get (f mx i) i j else get mx i j.
Proof.
  move => m n mx f b i j Hconds Hi Hj Hb Hwf.
  case : (Z_lt_le_dec i b) => [Hin /= | Hout /=].
  - apply (mx_foldl_in Hconds); try by []. rewrite Ziota_In; lia. apply Ziota_NoDup.
  - apply (mx_foldl_notin (proj1 Hconds)); try by []. rewrite Ziota_In; lia.
Qed.

(*Convert any function of this form to a mathcomp matrix (so we only have to prove this once*)
Lemma foldl_ziota_to_mx: forall m n mx f b 
  (g: 'M[F]_(Z.to_nat m, Z.to_nat n) -> 'I_(Z.to_nat m) -> 'M[F]_(Z.to_nat m, Z.to_nat n)),
  (forall (r: Z) (Hr: 0 <= r < m) (mx: lmatrix), wf_lmatrix mx m n ->
      lmatrix_to_mx m n (f mx r) = g (lmatrix_to_mx m n mx) (Z_to_ord Hr)) ->
  fn_in_conds m n f ->
  0 <= b <= m ->
  wf_lmatrix mx m n ->
  lmatrix_to_mx m n (fold_left f (Ziota 0 b) mx) = foldl g (lmatrix_to_mx m n mx) (pmap insub (iota 0 (Z.to_nat b))).
Proof.
  move => m n mx f b g Hcompat Hconds Hb Hwf.
  rewrite /Ziota.   have ->: (Z.to_nat 0) = 0%N by lia.
  have: forall n, n \in (iota 0 (Z.to_nat b)) -> (n < Z.to_nat b)%N. { move => n'. by rewrite mem_iota. }
  move : mx Hwf.
  elim: (iota 0 (Z.to_nat b)) => [//| h t IH mx Hwf Hin /=].
  have Hh : (h < Z.to_nat m)%N. { apply /ltP. have: (h < Z.to_nat b)%coq_nat. apply /ltP. apply Hin.
   by rewrite in_cons eq_refl. lia. }
  rewrite insubT /=. rewrite IH //=.
  have Hhm: 0 <= Z.of_nat h < m. { apply (elimT ltP) in Hh. lia. }
  rewrite Hcompat /=. f_equal. f_equal.
  apply ord_inj. by rewrite Z_ord_bound_nat /= Nat2Z.id. by []. 
  by apply Hconds. move => n' Hn'. apply Hin. by rewrite in_cons Hn' orbT.
Qed.

(*We need another, similar, weaker for functions that just use [iota]*)
Lemma foldl_ziota_to_mx': forall m n mx f b 
  (g: 'M[F]_(Z.to_nat m, Z.to_nat n) -> nat -> 'M[F]_(Z.to_nat m, Z.to_nat n)),
  (forall (r: Z) (mx: lmatrix), 0 <= r < m -> wf_lmatrix mx m n ->
      lmatrix_to_mx m n (f mx r) = g (lmatrix_to_mx m n mx) (Z.to_nat r)) ->
  (forall mx' i, 0 <= i < m -> wf_lmatrix mx' m n -> wf_lmatrix (f mx' i) m n) ->
  0 <= b <= m ->
  wf_lmatrix mx m n ->
  lmatrix_to_mx m n (fold_left f (Ziota 0 b) mx) = foldl g (lmatrix_to_mx m n mx) (iota 0 (Z.to_nat b)).
Proof.
  move => m n mx f b g Hcompat Hwfpres Hb Hwf. rewrite /Ziota. have ->: (Z.to_nat 0) = 0%N by lia.
  have: forall n, n \in (iota 0 (Z.to_nat b)) -> (n < Z.to_nat b)%N. { move => n'. by rewrite mem_iota. }
  move : mx Hwf.
  elim: (iota 0 (Z.to_nat b)) => [//| h t IH mx Hwf Hin /=].
  have Hhm: 0 <= Z.of_nat h < m. have /ltP Hhb : (h < Z.to_nat b)%N. apply Hin. by rewrite in_cons eq_refl. lia.
  rewrite IH //. rewrite Hcompat //.
  by rewrite Nat2Z.id. by apply Hwfpres. 
  move => n' Hnin. apply Hin. by rewrite in_cons Hnin orbT.
Qed.

(*Corollaries and useful general results*)
Lemma foldl_ziota_plus_one: forall (mx: lmatrix) (f: lmatrix -> Z -> lmatrix) (b: Z),
  0 <= b ->
  fold_left f (Ziota 0 (b+1)%Z) mx = f (fold_left f (Ziota 0 b) mx) b.
Proof.
  move => mx f b Hb. rewrite Ziota_plus_1; try lia.
  by rewrite fold_left_app /=.
Qed.
 
(*easy corollary of [foldl_ziota_get]*)
Lemma foldl_ziota_outside: forall m n mx f b i j,
  fn_in_conds m n f ->
  0 <= i < m ->
  0 <= j < n ->
  0 <= b <= i ->
  wf_lmatrix mx m n ->
  get (fold_left f (Ziota 0 b) mx) i j = get mx i j.
Proof.
  move => m n mx f b i j Hcond Hi Hj Hb Hwf.
  rewrite (foldl_ziota_get Hcond); try by []; try lia.
  by case : (Z_lt_le_dec i b) => [Hin | Hout /=]; try lia.
Qed.

(*Make all cols one (scalar multiplication)*)

Section AllColsOne.

Definition all_cols_one_partial m n (mx: lmatrix) (c: Z) (bound: Z) :=
  fold_left (fun acc x => scalar_mul_row m n acc x (get mx x c)^-1 ) (Ziota 0 bound) mx.

Lemma all_cols_one_fn_in_conds: forall m n mx c,
  wf_lmatrix mx m n ->
  fn_in_conds m n (fun acc x => scalar_mul_row m n acc x (get mx x c)^-1 ).
Proof.
  move => m n mx c Hwf. rewrite /fn_in_conds /fn_notin_conds. split; [ split |]. 
  - move => mx' i j r Hwf' Hi Hj Hir. rewrite scalar_mul_row_spec; try by [].
    by case : (Z.eq_dec i r) => [Heq | Hneq /=]; try lia.
  - move => mx' i Hwf'. apply scalar_mul_row_partial_wf. apply (lmatrix_m_pos Hwf).
    apply (lmatrix_n_pos Hwf).
  - move => mx' h i j Hwf' Hi Hj Hih.
    rewrite !scalar_mul_row_spec //=. 
    case: (Z.eq_dec i i) => [Htriv {Htriv} /= | Hbad]; try lia.
    by case: (Z.eq_dec i h) => [Hbad | Htriv /=]; try lia.
    apply scalar_mul_row_partial_wf. apply (lmatrix_m_pos Hwf). apply (lmatrix_n_pos Hwf).
Qed.

(*Now all the results are easy corollaries*)
Lemma all_cols_one_plus_1: forall m n mx c b,
  0 <= b ->
  all_cols_one_partial m n mx c (b+1) = scalar_mul_row m n (all_cols_one_partial m n mx c b) b (get mx b c)^-1.
Proof.
  move => m n mx c b Hb. by apply foldl_ziota_plus_one.
Qed.

Lemma all_cols_one_outside: forall m n mx c bound i j,
  wf_lmatrix mx m n ->
  0 <= bound <= i ->
  0 <= i < m ->
  0 <= j < n ->
  get (all_cols_one_partial m n mx c bound) i j = get mx i j.
Proof.
  move => m n mx c b i j Hwf Hb Hi Hj. 
  by apply (foldl_ziota_outside (all_cols_one_fn_in_conds c Hwf)).
Qed.

Lemma all_cols_one_equiv_partial: forall {m n} (mx: lmatrix) (c: Z) (Hc: 0 <= c < n) bound,
  0 <= bound <= m ->
  wf_lmatrix mx m n ->
  lmatrix_to_mx m n (all_cols_one_partial m n mx c bound) = all_cols_one_noif_gen (lmatrix_to_mx m n mx) (Z_to_ord Hc)
  (pmap insub (iota 0 (Z.to_nat bound))).
Proof.
  move => m n mx c Hc b Hb Hwf. rewrite all_cols_one_noif_gen_foldl /all_cols_one_noif_l_gen /Ziota /ord_enum.
  apply foldl_ziota_to_mx; try by [].
  - move => r Hr mx' Hwf'. rewrite scalar_mul_row_equiv //=. f_equal.
    by rewrite /lmatrix_to_mx mxE /= !Z2Nat.id; try lia.
  - by apply all_cols_one_fn_in_conds.
  - apply pmap_sub_uniq. apply iota_uniq.
Qed.

Lemma all_cols_one_list_equiv: forall {m n} (mx: lmatrix) (c: Z) (Hc: 0 <= c < n),
  wf_lmatrix mx m n ->
  lmatrix_to_mx m n (all_cols_one_partial m n mx c m) = all_cols_one_noif (lmatrix_to_mx m n mx) (Z_to_ord Hc).
Proof.
  move => m n mx c Hc Hwf. apply all_cols_one_equiv_partial. split; try lia.
  apply (lmatrix_m_pos Hwf). by [].
Qed.

Lemma all_cols_one_partial_wf: forall {m n} mx c bound,
  wf_lmatrix mx m n ->
  wf_lmatrix (all_cols_one_partial m n mx c bound) m n.
Proof.
  move => m n mx c b Hwf. apply mx_foldl_wf =>[|//]. by apply all_cols_one_fn_in_conds.
Qed.

End AllColsOne.

Section AddRow.

Definition add_multiple_partial m n (mx: lmatrix) (r1 r2 : Z) (k: F) (bound : Z) : lmatrix :=
  mk_bound_mx m n mx (fun i j => if Z.eq_dec i r2 then (get mx r2 j) + k * (get mx r1 j) else (get mx i j)) bound.


Lemma add_multiple_partial_0: forall m n mx r1 r2 k,
  wf_lmatrix mx m n ->
  add_multiple_partial m n mx r1 r2 k 0 = mx.
Proof.
  move => m n mx r1 r2 k Hwf. by apply mk_bound_mx_0.
Qed.  

Lemma add_multiple_partial_plus_1: forall m n mx r1 r2 k b,
  wf_lmatrix mx m n ->
  0 <= r2 < m ->
  0 <= b < n ->
  add_multiple_partial m n mx r1 r2 k (b + 1) =
    set (add_multiple_partial m n mx r1 r2 k b) r2 b ((get mx r2 b) + (k * (get mx r1 b)))%R.
Proof.
  move => m n mx r1 r2 k b Hwf Hr2 Hb. rewrite /add_multiple_partial (mk_bound_mx_plus_1 (r:=r2)) //=.
  - by case: (Z.eq_dec r2 r2); try lia.
  - move => i j Hi Hir. by case : (Z.eq_dec i r2); try lia.
Qed.

Lemma add_multiple_partial_outside: forall m n mx r1 r2 k b j,
  wf_lmatrix mx m n ->
  0 <= r2 < m ->
  0 <= j < n ->
  b <= j ->
  get (add_multiple_partial m n mx r1 r2 k b) r2 j = get mx r2 j.
Proof.
  move => m n mx r1 r2 k b j Hwf Hr1 Hj Hb. by apply mk_bound_mx_outside.
Qed. 

Lemma add_multiple_partial_other_row: forall m n mx r1 r2 k b i j,
  wf_lmatrix mx m n ->
  0 <= j < n ->
  0 <= i < m ->
  i <> r2 ->
  get (add_multiple_partial m n mx r1 r2 k b) i j = get mx i j.
Proof.
  move => m n mx r1 r2 k b i j Hwf Hj Hi Hir2. rewrite mk_lmatrix_get //=.
  case (Z.eq_dec i r2); try lia; move => {}Hir2 /=.
  by case(j <? b).
Qed.

Definition add_multiple m n (mx: lmatrix) (r1 r2 : Z) (k: F) : lmatrix :=
  add_multiple_partial m n mx r1 r2 k n.

Lemma add_multiple_partial_wf: forall mx m n r1 r2 k bound,
  wf_lmatrix mx m n ->
  wf_lmatrix (add_multiple_partial m n mx r1 r2 k bound) m n.
Proof.
  move => mx m n r1 r2 k b Hwf. apply mk_lmatrix_wf. apply (lmatrix_m_pos Hwf). apply (lmatrix_n_pos Hwf).
Qed.

Lemma add_multiple_spec: forall m n (mx: lmatrix) r1 r2 k i j,
  wf_lmatrix mx m n ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  get (add_multiple m n mx r1 r2 k) i j =
    if (Z.eq_dec i r2) then (get mx r2 j) + k * (get mx r1 j)
    else get mx i j.
Proof.
  move => m n mx r1 r2 k i j Hwf Hi Hj. by apply mk_bound_mx_full.
Qed.

Lemma add_multiple_row_equiv: forall {m n} (mx: lmatrix) (r1 r2: Z) (k: F) (Hr1 : 0 <= r1 < m) (Hr2: 0 <= r2 < m),
  wf_lmatrix mx m n ->
  lmatrix_to_mx m n (add_multiple m n mx r1 r2 k) = add_mul (lmatrix_to_mx m n mx) k (Z_to_ord Hr1) (Z_to_ord Hr2).
Proof.
  move => m n mx r1 r2 k Hr1 Hr2 Hwf. rewrite /add_mul. apply mk_lmatrix_mx.
  - apply (lmatrix_m_pos Hwf).
  - apply (lmatrix_n_pos Hwf).
  - move => x y Hx Hy. case_ltb y n Hyn; try lia.
    rewrite {Hyn} !mxE /= !Z2Nat.id; try lia. by rewrite eq_ord_int.
Qed. 

End AddRow.

(*The last intermediate function is the analogue of [sub_all_rows]*)
Section SubRows.

Definition sub_all_rows_partial m n (mx: lmatrix) (r: Z) (bound: Z) : lmatrix :=
  fold_left (fun acc x => if Z.eq_dec x r then acc else add_multiple m n acc r x (- 1)) (Ziota 0 bound) mx.

Lemma sub_all_rows_fn_in_conds: forall m n r,
  0 <= r < m ->
  fn_in_conds m n (fun acc x => if Z.eq_dec x r then acc else add_multiple m n acc r x (- 1)).
Proof.
  move => m n r Hr. split; [split |].
  - move => mx' i j r' Hwf' Hi Hj Hir'. case : (Z.eq_dec r' r) => [Hrr' //= | Hneq /=].
    rewrite add_multiple_spec //. by case (Z.eq_dec i r'); try lia.
  - move => mx' i' Hwf'. case : (Z.eq_dec i' r) => [Hir // | Hir /=].
    by apply add_multiple_partial_wf.
  - move => mx' h i j Hwf' Hi Hj Hih. case : (Z.eq_dec i r) => [Hir /= | Hir /=].
    + subst. case (Z.eq_dec h r) =>[ | Hhr /=]; try lia. rewrite add_multiple_spec //.
      by case (Z.eq_dec r h); try lia.
    + case (Z.eq_dec h r) => [//| Hhr /=]. rewrite !add_multiple_spec //.
      case (Z.eq_dec i i) ; try lia. case (Z.eq_dec i h); try lia.
      by case (Z.eq_dec r h); try lia.
      by apply add_multiple_partial_wf.
Qed.

Lemma sub_all_rows_plus_1: forall m n mx r b,
  0 <= b ->
  sub_all_rows_partial m n mx r (b+1) = if Z.eq_dec b r then (sub_all_rows_partial m n mx r b) else 
     add_multiple m n (sub_all_rows_partial m n mx r b) r b (- 1).
Proof.
  move => m n mx r b Hb. by apply foldl_ziota_plus_one.
Qed.

Lemma sub_all_rows_outside: forall m n mx r bound i j,
  wf_lmatrix mx m n ->
  0 <= r < m ->
  0 <= bound <= i ->
  0 <= i < m ->
  0 <= j < n ->
  get (sub_all_rows_partial m n mx r bound) i j = get mx i j.
Proof.
  move => m n mx r b i j Hwf Hr Hb Hi Hj. by rewrite (foldl_ziota_outside (sub_all_rows_fn_in_conds n Hr)).
Qed.

Lemma sub_all_rows_equiv: forall m n (mx: lmatrix) (r: Z) (Hr: 0 <= r < m),
  wf_lmatrix mx m n ->
  lmatrix_to_mx m n (sub_all_rows_partial m n mx r m) = sub_all_rows_noif (lmatrix_to_mx m n mx) (Z_to_ord Hr).
Proof.
  move => m n mx r Hr Hwf. rewrite sub_all_rows_noif_foldl /sub_all_rows_noif_l /Ziota /ord_enum.
  apply foldl_ziota_to_mx; try by [].
  - move => r' Hr' mx' Hwf'. rewrite eq_ord_int. 
    case (Z.eq_dec r' r) => [// | Hrr' /=].
    by apply add_multiple_row_equiv.
  - by apply sub_all_rows_fn_in_conds.
  - apply lmatrix_m_pos in Hwf. lia.
Qed.

Lemma sub_all_rows_partial_wf: forall {m n} mx r bound,
  0 <= r < m ->
  wf_lmatrix mx m n ->
  wf_lmatrix (sub_all_rows_partial m n mx r bound) m n.
Proof.
  move => m n mx r b Hr Hwf. apply mx_foldl_wf =>[|//].
  by apply sub_all_rows_fn_in_conds.
Qed.  

End SubRows.

Section AllSteps.

Definition gauss_all_steps_rows_partial m n (mx: lmatrix) (bound : Z) :=
  fold_left (fun acc r => let A1 := (all_cols_one_partial m n acc r m) in sub_all_rows_partial m n A1 r m) (Ziota 0 bound) mx.

Lemma gauss_all_steps_rows_partial_plus_1: forall m n mx b,
  0 <= b ->
  gauss_all_steps_rows_partial m n mx (b+1) =
  sub_all_rows_partial m n (all_cols_one_partial m n (gauss_all_steps_rows_partial m n mx b) b m) b m.
Proof.
  move => m n mx b Hb. by apply foldl_ziota_plus_one.
Qed.

Lemma gauss_all_steps_rows_equiv: forall m n (mx: lmatrix) (Hmn : m <= n) r,
  wf_lmatrix mx m n ->
  0 <= r <= m ->
  lmatrix_to_mx m n (gauss_all_steps_rows_partial m n mx r) = gauss_all_steps_restrict_beg (lmatrix_to_mx m n mx) (le_Z_N Hmn) (Z.to_nat r).
Proof.
  move => m n mx Hmn r Hwf Hr. rewrite /gauss_all_steps_rows_partial /gauss_all_steps_restrict_beg 
  /gauss_all_steps_restrict_aux /ord_enum. apply foldl_ziota_to_mx'; try by [].
  - move => r' mx' Hr' Hwf'. rewrite insubT. apply /ltP. lia. move => Hrm /=.
    rewrite /gauss_one_step_restrict. rewrite sub_all_rows_equiv. f_equal.
    + rewrite all_cols_one_equiv_partial //=. lia. move => Hrn'.
      rewrite /all_cols_one_noif /ord_enum. f_equal. by apply ord_inj.
      apply lmatrix_m_pos in Hwf. lia.
    + by apply ord_inj.
    + by apply all_cols_one_partial_wf.
  - move => mx' i Hi Hwf'. apply sub_all_rows_partial_wf=>[//|]. by apply all_cols_one_partial_wf.
Qed.

Lemma gauss_all_steps_rows_partial_wf: forall m n (mx: lmatrix) bound,
  0 <= bound <= m ->
  wf_lmatrix mx m n ->
  wf_lmatrix (gauss_all_steps_rows_partial m n mx bound) m n.
Proof.
  move => m n mx b Hb Hwf. apply mx_foldl_wf'.
  - move => mx' i Hi Hwf'. rewrite /=. apply sub_all_rows_partial_wf =>[//|].
    by apply all_cols_one_partial_wf.
  - by [].
  - move => x. rewrite Ziota_In; lia.
Qed.

End AllSteps.

(*Finally, the last function makes all leading coefficients 1*)

Section LCOne.

Definition all_lc_one_rows_partial m n (mx: lmatrix) (bound : Z) :=
  fold_left (fun acc x => scalar_mul_row m n acc x (get mx x x)^-1) (Ziota 0 bound) mx.

Lemma all_lcP_one_fn_in_conds: forall m n mx,
  wf_lmatrix mx m n ->
  fn_in_conds m n (fun acc x => scalar_mul_row m n acc x (get mx x x)^-1).
Proof.
  move => m n mx Hwf. rewrite /fn_in_conds /fn_notin_conds. split; [split|].
  - move => mx' i j r Hwf' Hi Hj Hir. rewrite scalar_mul_row_spec //.
    by case : (Z.eq_dec i r); try lia.
  - move => mx' i Hwf'. apply scalar_mul_row_partial_wf. apply (lmatrix_m_pos Hwf).
    apply (lmatrix_n_pos Hwf).
  - move => mx' h i j Hwf' Hi Hj Hih. rewrite !scalar_mul_row_spec //=.
    case: (Z.eq_dec i i) => [Htriv {Htriv} /= | Hbad]; try lia.
    by case: (Z.eq_dec i h); try lia.
    apply scalar_mul_row_partial_wf. apply (lmatrix_m_pos Hwf). apply (lmatrix_n_pos Hwf).
Qed.

Lemma all_lc_one_plus_one: forall m n mx b,
  0 <= b ->
  all_lc_one_rows_partial m n mx (b+1) = scalar_mul_row m n (all_lc_one_rows_partial m n mx b) b (get mx b b)^-1.
Proof.
  move => m n mx b Hb. by apply foldl_ziota_plus_one.
Qed.

Lemma all_lc_one_outside: forall m n mx bound i j,
  wf_lmatrix mx m n ->
  0 <= bound <= i ->
  0 <= i < m ->
  0 <= j < n ->
  get (all_lc_one_rows_partial m n mx bound) i j = get mx i j.
Proof.
  move => m n mx b i j Hwf Hb Hi Hj. 
  by apply (foldl_ziota_outside (all_lcP_one_fn_in_conds Hwf)).
Qed.

(*There is a slight complication - we only go to m - 1 because the last row's leading coefficient is already 1. This
  optimization is present in the C code*)
Lemma all_lc_one_rows_equiv: forall {m n} (mx: lmatrix) (Hmn: m <= n),
  wf_lmatrix mx m n ->
  lmatrix_to_mx m n (all_lc_one_rows_partial m n mx (m-1)) = mk_identity (lmatrix_to_mx m n mx) (le_Z_N Hmn) (Z.to_nat m-1).
Proof.
  move => m n mx Hmn Hwf. rewrite mk_identity_foldl /all_lc_one_rows_partial /mk_identity_l /Ziota /ord_enum.
  have->: ((Z.to_nat m - 1)%N = (Z.to_nat (m - 1))). have->: (Z.to_nat m - 1)%N = (Z.to_nat m - 1)%coq_nat by []. lia.
  have Hm0: 0 <= m by apply (lmatrix_m_pos Hwf).
  have [Hmeq | Hmpos]: (m = 0%Z \/ 1 <= m) by lia.
  - by subst. 
  - apply foldl_ziota_to_mx; try by []; try lia.
    + move => r Hr mx' Hmx'. rewrite scalar_mul_row_equiv //=. f_equal.
      by rewrite /lmatrix_to_mx mxE /= !Z2Nat.id; try lia.
    + by apply all_lcP_one_fn_in_conds.
Qed.

Lemma all_lc_one_rows_partial_wf: forall {m n} mx bound,
  0 <= bound <= m ->
  wf_lmatrix mx m n ->
  wf_lmatrix (all_lc_one_rows_partial m n mx bound) m n.
Proof.
  move => m n mx b Hb Hwf. apply mx_foldl_wf =>[|//].  by apply all_lcP_one_fn_in_conds.
Qed.

End LCOne.

Section GaussFull.

Definition gauss_restrict_rows m n (mx: lmatrix) :=
  all_lc_one_rows_partial m n (gauss_all_steps_rows_partial m n mx m) (m-1).

Lemma gauss_restrict_rows_equiv: forall {m n} (mx: lmatrix) (Hmn: m <= n),
  wf_lmatrix mx m n ->
  lmatrix_to_mx m n (gauss_restrict_rows m n mx) = gaussian_elim_restrict (lmatrix_to_mx m n mx) (le_Z_N Hmn).
Proof.
  move => m n mx Hmn Hwf.
  have H0m: 0 <= m by apply (lmatrix_m_pos Hwf).
  rewrite /gauss_restrict_rows /gaussian_elim_restrict all_lc_one_rows_equiv.
  rewrite gauss_all_steps_rows_equiv //. rewrite -gauss_all_steps_restrict_both_dirs.
  by rewrite subn1. lia.
  apply gauss_all_steps_rows_partial_wf =>[|//]. lia.
Qed.

Lemma gauss_restrict_rows_wf: forall {m n} (mx: lmatrix),
  wf_lmatrix mx m n ->
  wf_lmatrix (gauss_restrict_rows m n mx) m n.
Proof.
  move => m n mx Hwf. have H0m: 0 <= m by apply (lmatrix_m_pos Hwf).
  have [H0meq | H0mlt]:  (0%Z = m \/ 0 < m) by lia.
  - subst. by rewrite /gauss_restrict_rows /= /gauss_all_steps_rows_partial /= /all_lc_one_rows_partial /=.
  - apply all_lc_one_rows_partial_wf.
    lia. apply gauss_all_steps_rows_partial_wf. lia. by [].
Qed.

End GaussFull.

(*We need a way to specify that a list lmatrix m satisfies [strong_inv] without using dependent types*)
Definition strong_inv_list m n (mx: lmatrix) (r: Z) : Prop :=
  match (range_le_lt_dec 0 r m) with
  | left Hrm =>
      match (Z_le_lt_dec m n) with
      | left H => strong_inv (lmatrix_to_mx m n mx) (le_Z_N H) (Z_to_ord Hrm)
      | right _ => False
      end
  |right _ => False
  end.

Lemma strong_inv_list_unfold: forall m n mx r (Hrm : 0 <= r < m) (Hmn : m <= n),
  strong_inv_list m n mx r ->
  strong_inv (lmatrix_to_mx m n mx) (le_Z_N Hmn) (Z_to_ord Hrm).
Proof.
  move => m n mx r Hrm Hmn. rewrite /strong_inv_list. destruct (range_le_lt_dec 0 r m) => [|//]. (*case doesnt work*)
  destruct (Z_le_lt_dec m n) => [|//]. move => Hstr.
  have <-: (le_Z_N l) = (le_Z_N Hmn) by apply ProofIrrelevance.proof_irrelevance. 
  rewrite strong_inv_dep. apply Hstr. by have: Z.to_nat r == Z.to_nat r by [].
Qed.

(*Even though we already know that the reduced Gaussian elimination is equivalent to the full algorithm
  if [strong_inv 0] is satisfied, that is not enough, since the C code checks and fails if the invariant
  is violated. So we need to use some of the intermediate theories from Gaussian.v - in particular, if we 
  have finished up to row r, then the rth column contains all nonzero entries. Here, we show in several
  steps the analogous result for the list matrices in use in VST*)

Lemma gauss_all_steps_rows_partial_strong_inv: forall m n mx r,
  wf_lmatrix mx m n ->
  0 <= r < m ->
  strong_inv_list m n mx 0 ->
  strong_inv_list m n (gauss_all_steps_rows_partial m n mx r) r.
Proof.
  move => m n mx r Hwf Hrm. rewrite /strong_inv_list.
  case : (range_le_lt_dec 0 0 m) => [H0m | //].
  case : (Z_le_lt_dec m n) => [Hmn | //].
  case : (range_le_lt_dec 0 r m) => [{}Hrm | //]; try lia.
  rewrite gauss_all_steps_rows_equiv => [|//|//].
  rewrite {1}/Z_to_ord => [Hstr].
  have Hrmnat : ((Z.to_nat r) < (Z.to_nat m))%N. apply (introT ltP). lia.
  pose proof (@gauss_all_steps_restrict_beg_strong _ _ _ _ _ _ _ Hrmnat Hstr).
  rewrite strong_inv_dep. apply H. rewrite /Z_to_ord. by have: (Z.to_nat r == Z.to_nat r) by [].
  lia.
Qed.

Lemma gauss_all_steps_rows_partial_gauss_inv: forall m n mx r,
  wf_lmatrix mx m n ->
  0 <= r < m ->
  strong_inv_list m n mx 0 ->
  gauss_invar (lmatrix_to_mx m n (gauss_all_steps_rows_partial m n mx r)) (Z.to_nat r) (Z.to_nat r).
Proof.
  move => m n mx r Hwf Hrm. rewrite /strong_inv_list. case : (range_le_lt_dec 0 0 m) => [H0m |//].
  case : (Z_le_lt_dec m n) => [Hmn Hstr | //].
  rewrite gauss_all_steps_rows_equiv => [|//|//].
  have H0rm: (0 + Z.to_nat r <= Z.to_nat m)%N. rewrite add0n. apply (introT leP). lia.
  pose proof (gauss_all_steps_restrict_aux_inv H0rm (gauss_invar_init _ ) Hstr) as Hinv'.
  rewrite add0n in Hinv'. by []. lia.
Qed.

Lemma gauss_all_steps_rows_partial_zeroes: forall m n mx r (Hr: 0 <= r < m) (Hmn : m <= n),
  wf_lmatrix mx m n ->
  strong_inv_list m n mx 0 ->
  (forall (x: 'I_(Z.to_nat m)), (lmatrix_to_mx m n (gauss_all_steps_rows_partial m n mx r)) x (widen_ord (le_Z_N Hmn)
   (Z_to_ord Hr)) != 0).
Proof.
  move => m n mx r Hr Hmn Hwf Hstr x.
  apply strong_inv_nonzero_cols. by apply gauss_all_steps_rows_partial_gauss_inv.
  pose proof (gauss_all_steps_rows_partial_strong_inv Hwf Hr Hstr) as Htemp.
  by apply strong_inv_list_unfold.
Qed.

Lemma gauss_all_steps_columns_partial_zeroes: forall m n mx r (Hr: 0 <= r < m) (Hmn : m <= n) c ,
  0 <= c <= m ->
  wf_lmatrix mx m n ->
  strong_inv_list m n mx 0 ->
  (forall (x: 'I_(Z.to_nat m)),
  (lmatrix_to_mx m n (all_cols_one_partial m n (gauss_all_steps_rows_partial m n mx r) r c) x (widen_ord (le_Z_N Hmn)
   (Z_to_ord Hr))) != 0).
Proof.
  move => m n mx r Hr Hmn c Hc Hwf Hstr x. rewrite all_cols_one_equiv_partial. lia.
  move => Hrn.
  have Hord: Z_to_ord Hrn = widen_ord (le_Z_N Hmn) (Z_to_ord Hr). apply (elimT eqP). by
  have : Z.to_nat r == Z.to_nat r by []. rewrite Hord.
  have Hz: forall x0 : 'I_(Z.to_nat m),
    lmatrix_to_mx m n (gauss_all_steps_rows_partial m n mx r) x0 (widen_ord (le_Z_N Hmn) (Z_to_ord Hr)) != 0.
  move => x'. by apply gauss_all_steps_rows_partial_zeroes.
  rewrite all_cols_one_noif_gen_zero. apply Hz. 2: apply Hz.
  apply pmap_sub_uniq. apply iota_uniq. by []. apply gauss_all_steps_rows_partial_wf. lia. by [].
Qed.

(*Finally, the result we need for the VST proof*)
Lemma gauss_all_steps_columns_partial_zeroes_list: forall m n mx r c,
  0 <= r < m ->
  0 <= c <= m ->
  m <= n ->
  wf_lmatrix mx m n ->
  strong_inv_list m n mx 0 ->
  (forall x, 0 <= x < m -> get (all_cols_one_partial m n (gauss_all_steps_rows_partial m n mx r) r c) x r <> 0).
Proof.
  move => m n mx r c Hr Hc Hmn Hwf Hstr x Hx.
  pose proof (@gauss_all_steps_columns_partial_zeroes m n mx r Hr Hmn c Hc Hwf Hstr (Z_to_ord Hx)).
  move : H. rewrite /lmatrix_to_mx mxE.
  have ->: (Z.of_nat (Z_to_ord Hx)) = x.  have /eqP Hord: nat_of_ord (Z_to_ord Hx) == Z.to_nat x by []. rewrite Hord. lia.
  have ->: (Z.of_nat (widen_ord (le_Z_N Hmn) (Z_to_ord Hr))) = r. 
    have /eqP Hord: nat_of_ord (widen_ord (le_Z_N Hmn) (Z_to_ord Hr)) == Z.to_nat r by []. rewrite Hord. lia.
  move => Hneq. move => Hget. rewrite Hget in Hneq. by rewrite eq_refl in Hneq.
Qed.

(** ListMatrix definitions for Encoder*) 
Section Encoder.

(*Here, the lmatrix may be partial - ie, not all rows are filled in. So we need to extend with zeroes, 
up to an m x n lmatrix*)
Definition extend_mx m n (l: list (list F)) : lmatrix :=
  mk_lmatrix m n (fun i j => if (Z_lt_le_dec j (Zlength (Znth i l))) then get l i j else 0%R).

Lemma extend_mx_wf: forall m n l,
  0 <= n ->
  0 <= m ->
  wf_lmatrix (extend_mx m n l) m n.
Proof.
  move => m n l Hm Hn. by apply mk_lmatrix_wf.
Qed. 

Lemma extend_mx_spec: forall m n l i j,
  0 <= i < m ->
  0 <= j < n ->
  get (extend_mx m n l) i j = if (Z_lt_le_dec j (Zlength (Znth i l))) then Znth j (Znth i l) else 0%R.
Proof.
  move => m n l i j Hi Hj. by apply mk_lmatrix_get.
Qed.

(* We use the above to define lmatrix multiplication of ListMatrices, since we will be setting the entries
  manually. Using mathcomp summations in VST would be
  very annoying, so we define a specialized summation for our purposes and prove them equivalent*)

Definition dot_prod (mx1: lmatrix) (mx2: lmatrix) i j (bound : Z) : F :=
  foldl (fun acc k => acc + ((get mx1 i k) * (get mx2 k j))) 0 (Ziota 0 bound).

Lemma dot_prod_zero: forall mx1 mx2 i j,
  dot_prod mx1 mx2 i j 0%Z = 0.
Proof. by []. Qed.

Lemma dot_prod_plus_1: forall mx1 mx2 i j bound,
  0 <= bound ->
  dot_prod mx1 mx2 i j (bound+1)%Z = (dot_prod mx1 mx2 i j bound) + (get mx1 i bound * get mx2 bound j).
Proof.
  move => mx1 mx2 i j b Hb. rewrite /dot_prod Ziota_plus_1; try lia. by rewrite foldl_cat.
Qed.

(*Prove that this [dot_prod] expression is equivalent to the lmatrix multiplication sum in ssreflect*)
Lemma dot_prod_sum: forall m n p mx1 mx2 i j b (d: 'I_(Z.to_nat n)) (Hi: 0 <= i < m) (Hj : 0 <= j < p),
  0 <= b <= n ->
  wf_lmatrix mx1 m n ->
  wf_lmatrix mx2 n p ->
  dot_prod mx1 mx2 i j b = 
  \sum_(0 <= i0 < Z.to_nat b) 
    lmatrix_to_mx m n mx1 (Z_to_ord Hi) (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) i0) *
    lmatrix_to_mx n p mx2 (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) i0) (Z_to_ord Hj).
Proof.
  move => m n p mx1 mx2 i j b d Hi Hj Hb Hwf1 Hwf2. rewrite /dot_prod /Ziota. have: (0%nat <= Z.to_nat b)%coq_nat by lia.
  have: (Z.to_nat b <= Z.to_nat n)%coq_nat by lia. rewrite {Hb}.
  (*We will do induction on (Z.to_nat b)*)
  remember (Z.to_nat b) as c. rewrite {b Heqc}. elim: c => [Hub Hlb //= | c' IH Hub Hlb].
  - by rewrite big_mkord big_ord0.
  - have Hc0 : (0 <= c')%N. apply (introT leP). lia.
    rewrite iota_plus_1 map_cat foldl_cat /= big_nat_recr /= =>[|//].
    rewrite IH; try lia.
    rewrite /lmatrix_to_mx !mxE /=. f_equal. 
    have Hc': (0 <= c' < Z.to_nat n)%nat. rewrite Hc0 /=. apply (introT ltP). lia.
    have ->: (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) c') = 
      (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) (Ordinal Hc')) by []. rewrite ordinal_enum //=.
    by rewrite !Z2Nat.id; try lia.
Qed.

(*Therefore, the full product is the same as multiplying matrices*)
Lemma dot_prod_mulmx: forall m n p mx1 mx2 i j (Hi: 0 <= i < m) (Hj : 0 <= j < p),
  wf_lmatrix mx1 m n ->
  wf_lmatrix mx2 n p ->
  dot_prod mx1 mx2 i j n = ((lmatrix_to_mx m n mx1) *m (lmatrix_to_mx n p mx2)) (Z_to_ord Hi) (Z_to_ord Hj).
Proof.
  move => m n p mx1 mx2 i j Hi Hj Hwf1 Hwf2. rewrite !mxE.
  have Hn0: 0 <= n by apply Hwf1.
  have: n = 0%Z \/ 0 < n by lia. move => [{}Hn0 | {} Hn0].
  - subst. rewrite /dot_prod /=. by rewrite big_ord0.
  - (*Now we have an instance of an 'I_n, which we need*)
    have Hnord: 0 <= 0 < n by lia.
    rewrite (big_nth (Z_to_ord Hnord)) /= /index_enum /= ordinal_enum_size /dot_prod.
    apply dot_prod_sum; try by []. lia.
Qed.

Lemma mulmx_dot_equiv: forall m n p mx1 mx2 mx3,
  wf_lmatrix mx1 m n ->
  wf_lmatrix mx2 n p ->
  wf_lmatrix mx3 m p ->
  (forall i j, 0 <= i < m -> 0 <= j < p -> get mx3 i j = dot_prod mx1 mx2 i j n) ->
  lmatrix_to_mx m p mx3 = (lmatrix_to_mx m n mx1) *m (lmatrix_to_mx n p mx2).
Proof.
  move => m n p mx1 mx2 mx3 Hwf1 Hwf2 Hwf3 Hall.
  rewrite -matrixP /eqrel => x y. rewrite mxE.
  have Hxm: 0 <= Z.of_nat x < m. split; try lia. have /ltP Hxm: (x < Z.to_nat m)%N by []. lia.
  have Hyp: 0 <= Z.of_nat y < p. split; try lia. have /ltP Hyp: (y < Z.to_nat p)%N by []. lia.
  rewrite Hall // (dot_prod_mulmx Hxm Hyp Hwf1 Hwf2) /=. f_equal.
  apply ord_inj. by rewrite /= Nat2Z.id.
  apply ord_inj. by rewrite /= Nat2Z.id. 
Qed.

(*Finally, we give a definition with lists so we don't need to directly refer to any
 ssreflect functions in the VST proofs*)

Definition list_lmatrix_multiply m n p mx1 mx2 : lmatrix :=
  mk_lmatrix m p (fun i j => dot_prod mx1 mx2 i j n).

Lemma list_lmatrix_multiply_wf: forall m n p mx1 mx2,
  0 <= m ->
  0 <= p ->
  wf_lmatrix (list_lmatrix_multiply m n p mx1 mx2) m p.
Proof.
  move => m n p mx1 mx2 Hm Hp. by apply mk_lmatrix_wf.
Qed.

Lemma list_lmatrix_multiply_correct: forall m n p mx1 mx2 ,
  wf_lmatrix mx1 m n ->
  wf_lmatrix mx2 n p ->
  lmatrix_to_mx m p (list_lmatrix_multiply m n p mx1 mx2) = (lmatrix_to_mx m n mx1) *m (lmatrix_to_mx n p mx2).
Proof.
  move => m n p mx1 mx2 Hwf1 Hwf2.
  apply mulmx_dot_equiv =>[//|//||].
  apply list_lmatrix_multiply_wf. apply (lmatrix_m_pos Hwf1). apply (lmatrix_n_pos Hwf2).
  move => i j Hi Hj. by rewrite mk_lmatrix_get. 
Qed.

(*This is the submatrix we will need for the encoder - take the first a rows and last b columns of a matrix,
  reversed.*)

Definition submatrix n (mx: lmatrix) a b :=
  mk_lmatrix a b (fun i j => get mx i (n - j - 1)).

Lemma submatrix_wf: forall n mx a b,
  0 <= a ->
  0 <= b ->
  wf_lmatrix (submatrix n mx a b) a b.
Proof.
  move => n mx a b Ha Hb. by apply mk_lmatrix_wf.
Qed.

Lemma submatrix_spec: forall n mx a b i j,
  0 <= i < a ->
  0 <= j < b ->
  get (submatrix n mx a b) i j = get mx i (n - j - 1).
Proof.
  move => n mx a b i j Hi Hj. by rewrite mk_lmatrix_get.
Qed. 

(*A bit of complication because of the ordinals, i -> i and j -> n - j - 1*)
Lemma submatrix_to_mx: forall m n mx a b (Ha: a <= m) (Hb: b <= n),
  wf_lmatrix mx m n ->
  0 <= a ->
  0 <= b ->
  lmatrix_to_mx a b (submatrix n mx a b) = mxsub
    (fun (x: 'I_(Z.to_nat a)) => widen_ord (le_Z_N Ha) x)
    (fun (x: 'I_(Z.to_nat b)) => (rev_ord (widen_ord (le_Z_N Hb) x)))
    (lmatrix_to_mx m n mx).
Proof.
  move => m n mx a b Ha Hb Hwf H0a H0b. apply mk_lmatrix_mx =>[//|//|].
  move => x y Hx Hy. rewrite mxE /=.
  have->: (Z.to_nat n - (Z.to_nat y).+1)%N = (Z.to_nat n - (Z.to_nat y).+1)%coq_nat by []. f_equal; lia.
Qed.

End Encoder.

(** ListMatrix operations for Decoder*)

Section Decoder.

(*The ListMatrix version of [submx_rows_cols] *)
Definition submx_rows_cols_list (mx: lmatrix) m n (rows: list Z) (cols: list Z) : lmatrix :=
  mk_lmatrix m n (fun x y => get mx (Znth x rows) (Znth y cols)) .

Lemma submx_rows_cols_list_wf: forall mx m n rows cols,
  0 <= m ->
  0 <= n ->
  wf_lmatrix (submx_rows_cols_list mx m n rows cols) m n.
Proof.
  move => mx m n rows cols. by apply mk_lmatrix_wf.
Qed.

Lemma submx_rows_cols_list_equiv: forall mx m n m' n' rows cols (Hm: 0 < m) (Hn: 0 < n),
  0 <= m' ->
  0 <= n' ->
  Forall (fun x => 0 <= x < m) rows ->
  Forall (fun x => 0 <= x < n) cols ->
  lmatrix_to_mx m' n' (submx_rows_cols_list mx m' n' rows cols) = 
    submx_rows_cols (Z.to_nat m') (Z.to_nat n') (lmatrix_to_mx m n mx)
       (Z_ord_list rows m) (Z_ord_list cols n) (ord_zero Hm) (ord_zero Hn).
Proof.
  move => mx m n m' n' rows cols Hm Hn Hm' Hn' Hrows Hcols. apply mk_lmatrix_mx =>[//|//| x y Hx Hy].
  rewrite !mxE. f_equal.
  - rewrite (Z_ord_list_Znth Hm) =>[//| |//]. lia.
  - rewrite (Z_ord_list_Znth Hn) => [//||//]. lia.
Qed.

(*Take columns from end instead of beginning - large mx is m x n, submx is m' x n'*)
Definition submx_rows_cols_rev_list (mx: lmatrix) m' n' n rows cols :=
  submx_rows_cols_list mx m' n' rows (map (fun x => (n - x - 1)%Z) cols).

Lemma submx_rows_cols_rev_list_wf: forall mx m' n' n rows cols,
  0 <= m' ->
  0 <= n' ->
  wf_lmatrix (submx_rows_cols_rev_list mx m' n' n rows cols) m' n'.
Proof.
  move => mx m' n' n rows cols.
  apply submx_rows_cols_list_wf.
Qed.

(*m and n are dimensions of the whole matrix, m' and n' are the new dimensions of the submatrix*)
Lemma submx_rows_cols_rev_list_spec: forall mx m n m' n' rows cols (Hm: 0 < m) (Hn: 0 < n),
  0 <= m'->
  0 <= n'->
  Forall (fun x => 0 <= x < m) rows ->
  Forall (fun x => 0 <= x < n) cols ->
  lmatrix_to_mx m' n' (submx_rows_cols_rev_list mx m' n' n rows cols) =
  submx_rows_cols_rev (Z.to_nat m') (Z.to_nat n') (lmatrix_to_mx m n mx)
    (Z_ord_list rows m) (Z_ord_list cols n) (ord_zero Hm) (ord_zero Hn).
Proof.
  move => mx m n m' n' rows cols Hm Hn Hm' Hn' Hrows Hcols.
  rewrite /submx_rows_cols_rev_list /submx_rows_cols_rev.
  apply mk_lmatrix_mx; try lia. move => x y Hx Hy.
  rewrite mxE /=. f_equal.
  - rewrite (Z_ord_list_Znth Hm) =>[//| |//]. lia.
  - rewrite (Z_ord_list_Znth Hn); try lia. 
    + f_equal. f_equal. f_equal. by apply Z_ord_list_rev.
    + move: Hcols. rewrite !Forall_forall => Hcols i. rewrite in_map_iff => [[x' [Hx' Hin]]].
      subst. apply Hcols in Hin. lia.
Qed.


(*Concatenate two matrices*)
Definition row_mx_list (left right: lmatrix) m n1 n2 : lmatrix :=
  mk_lmatrix m (n1 + n2) (fun x y => if Z_lt_ge_dec y n1 then get left x y else get right x (y - n1)).

Lemma row_mx_list_wf: forall left right m n1 n2,
  0 <= m ->
  0 <= n1 ->
  0 <= n2 ->
  wf_lmatrix (row_mx_list left right m n1 n2) m (n1 + n2).
Proof.
  move => l r m n1 n2 Hm Hn1 H2. apply mk_lmatrix_wf; lia.
Qed.

(*Need a cast bc it cannot unify Z.to_nat n + Z.to_nat m with Z.to_nat (n + m)*)
Lemma row_mx_list_spec: forall left right m n1 n2 (Hn1: 0 <= n1) (Hn2: 0 <= n2),
  0 <= m ->
  lmatrix_to_mx m (n1 + n2) (row_mx_list left right m n1 n2) =
    castmx (Logic.eq_refl _, Logic.eq_sym (Z2Nat.inj_add n1 n2 Hn1 Hn2))
    (row_mx (lmatrix_to_mx m n1 left) (lmatrix_to_mx m n2 right)).
Proof.
  move => l r m n1 n2 Hn1 Hn2 Hm. rewrite -matrixP => x y.
  rewrite castmxE !mxE /= mk_lmatrix_get.
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
Definition col_mx_list (top bottom: lmatrix) m1 m2 n : lmatrix :=
  mk_lmatrix (m1 + m2) n (fun x y => if Z_lt_ge_dec x m1 then get top x y else get bottom (x - m1) y).

Lemma col_mx_list_wf: forall top bottom m1 m2 n,
  0 <= m1 ->
  0 <= m2 ->
  0 <= n ->
  wf_lmatrix (col_mx_list top bottom m1 m2 n) (m1 + m2) n.
Proof.
  move => t u m1 m2 n Hm1 Hm2 Hn. apply mk_lmatrix_wf; lia.
Qed.

(*Need a cast bc it cannot unify Z.to_nat n + Z.to_nat m with Z.to_nat (n + m)*)
Lemma col_mx_list_spec: forall top bottom m1 m2 n (Hm1: 0 <= m1) (Hm2: 0 <= m2),
  0 <= n ->
  lmatrix_to_mx (m1 + m2) n (col_mx_list top bottom m1 m2 n) =
    castmx (Logic.eq_sym (Z2Nat.inj_add m1 m2 Hm1 Hm2), Logic.eq_refl)
    (col_mx (lmatrix_to_mx m1 n top) (lmatrix_to_mx m2 n bottom)).
Proof.
  move => t u m1 m2 n Hm1 Hm2 Hn. rewrite -matrixP => x y.
  rewrite castmxE !mxE /= mk_lmatrix_get.
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
Definition id_list (n: Z) := mk_lmatrix n n (fun x y => if Z.eq_dec x y then (GRing.one F) else (GRing.zero F)).

Lemma id_list_wf: forall n,
  0 <= n ->
  wf_lmatrix (id_list n) n n.
Proof.
  move => n Hn. by apply mk_lmatrix_wf.
Qed.

Lemma id_list_spec: forall n,
  0 <= n ->
  lmatrix_to_mx n n (id_list n) = (1%:M)%R.
Proof.
  move => n Hn. rewrite -matrixP => x y.
  rewrite id_A mxE mk_lmatrix_get.
  - case : (Z.eq_dec (Z.of_nat x) (Z.of_nat y)) => [Hxy /= | Hxy /=].
    + have->: x == y. apply /eqP. apply ord_inj. lia. by [].
    + have->:x == y = false. apply /eqP. move => C. rewrite C in Hxy. lia. by [].
  - by apply Z_ord_bound.
  - by apply Z_ord_bound.
Qed.

(*We want to invert a matrix by concatenating it with the identity, then running gaussian elimination. We define
  each part separately to make the VST proof cleaner*)
Definition concat_mx_id (mx: lmatrix) n :=
  row_mx_list mx (id_list n) n n n.

(*Get the right submatrix of an n x (n + n) matrix*)
Definition right_submx n (mx: lmatrix) :=
  mk_lmatrix n n (fun x y => get mx x (n + y)).

Lemma right_submx_wf: forall n mx,
  0 <= n ->
  wf_lmatrix (right_submx n mx) n n.
Proof.
  move => n mx Hn. by apply mk_lmatrix_wf.
Qed.

(*We again need a cast to unify (Z.to_nat (n + n)) and Z.to_nat n + Z.to_nat n*)
Lemma right_submx_spec: forall n mx (Hn: 0 <= n),
  lmatrix_to_mx n n (right_submx n mx) = 
  rsubmx (castmx (Logic.eq_refl _, (Z2Nat.inj_add n n Hn Hn)) (lmatrix_to_mx n (n + n) mx)).
Proof.
  move => n mx Hn. rewrite -matrixP => x y.
  rewrite !mxE castmxE mxE /= mk_lmatrix_get. f_equal; try lia. rewrite Nat2Z.inj_add; lia.
  by apply Z_ord_bound. by apply Z_ord_bound.
Qed.

Definition find_invmx_list (mx: lmatrix) n :=
  right_submx n (gauss_restrict_rows n (n + n) (concat_mx_id mx n)).

(* [find_invmx_list] computes the inverse. This is quite complicated to prove
  because of all the casting, the proofs of which are in Gaussian.v*)
Lemma find_invmx_list_spec: forall mx n,
  strong_inv_list n n mx 0 -> 
  lmatrix_to_mx n n (find_invmx_list mx n) = invmx (lmatrix_to_mx n n mx).
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
      apply (@strong_inv_row_mx _ _ _ (lmatrix_to_mx n n mx) 1%:M (le_Z_N Htriv)
              (cast_leq (erefl (Z.to_nat n), Z2Nat.inj_add n n Hn Hn) (le_Z_N Hnn))).
      by have ->: (Ordinal Hn') = Z_to_ord H0n by apply ord_inj.
  - by apply strong_inv_unitmx in Hstr.
Qed.

(*Lastly, fill in the input matrix with the missing data*)
(*The first matrix is m x n, the second is some m' x n*)
Definition fill_row_list m n (d r: lmatrix) row_d row_r :=
  mk_lmatrix m n (fun i j => if Z.eq_dec i row_d then get r row_r j else get d i j).

Definition fill_rows_list_aux m n (d r: lmatrix) (to_fill: seq Z) (src_idx: list Z) :=
  fold_left (fun acc x => fill_row_list m n acc r (Znth x to_fill) x) src_idx d.

Definition fill_rows_list m n xh (d r: lmatrix) (to_fill: seq Z) :=
  fill_rows_list_aux m n d r to_fill (Ziota 0 xh).

Lemma fill_row_list_wf: forall m n d r row_d row_r,
  0 <= m ->
  0 <= n ->
  wf_lmatrix (fill_row_list m n d r row_d row_r) m n.
Proof.
  move => m n d r row_d row_r. by apply mk_lmatrix_wf.
Qed.

Lemma fill_rows_list_aux_wf: forall m n d r to_fill l,
  wf_lmatrix d m n ->
  wf_lmatrix (fill_rows_list_aux m n d r to_fill l) m n.
Proof.
  move => m n d r to_fill l. apply mx_foldl_wf. move => mx' i Hwf'.
  apply fill_row_list_wf. apply (lmatrix_m_pos Hwf'). apply (lmatrix_n_pos Hwf').
Qed.

Lemma fill_row_list_spec: forall m1 m2 n d r row_d row_r (Hd: 0 <= row_d < m1) (Hr: 0 <= row_r < m2),
  0 <= n ->
  lmatrix_to_mx m1 n (fill_row_list m1 n d r row_d row_r) =
    fill_row (lmatrix_to_mx m1 n d) (lmatrix_to_mx m2 n r) (Z_to_ord Hd) (Z_to_ord Hr).
Proof.
  move => m1 m2 n d r row_d row_r Hd Hr Hn. apply mk_lmatrix_mx; try lia.
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
  lmatrix_to_mx m1 n (fill_rows_list_aux m1 n d r to_fill src_idx) =
    fill_rows_aux (lmatrix_to_mx m1 n d) (lmatrix_to_mx m2 n r)
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

Lemma fill_rows_list_spec: forall m1 m2 n (d r: lmatrix) to_fill (Hd: 0 < m1),
  0 <= n ->
  Forall (fun x => 0 <= x < m1) to_fill ->
  Zlength to_fill = m2 ->
  lmatrix_to_mx m1 n (fill_rows_list m1 n m2 d r to_fill) =
    fill_rows (lmatrix_to_mx m1 n d) (lmatrix_to_mx m2 n r)
       (Z_ord_list to_fill m1) (ord_zero Hd).
Proof.
  move => m1 m2 n d r to_fill Hd Hn Hfill Hlen.
  rewrite (@fill_rows_list_aux_spec m1 m2); try lia; try by [].
  rewrite /fill_rows. f_equal. apply Z_ord_list_iota. list_solve.
  rewrite Forall_forall=> x. rewrite Ziota_In; try lia. list_solve.
Qed.

(* Some general results about casting that we need*)
Lemma Z_to_nat_eq: forall z1 z2,
  z1 = z2 ->
  Z.to_nat z1 = Z.to_nat z2.
Proof.
  move => z1 z2. by move ->.
Qed.

Lemma lmatrix_to_mx_cast: forall m1 m2 n1 n2 mx (Hm: m2 = m1) (Hn: n2 = n1),
  lmatrix_to_mx m1 n1 mx = castmx (Z_to_nat_eq Hm, Z_to_nat_eq Hn) (lmatrix_to_mx m2 n2 mx).
Proof.
  move => m1 m2 n1 n2 mx Hm Hn. rewrite -matrixP => x y.
  rewrite castmxE !mxE. f_equal.
Qed.

(*Restore the packets to their original lengths*)
Definition crop_mx (mx: lmatrix) (lens: list Z) :=
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
  pose proof (@extend_mx_wf (Zlength mx) c mx Hc Hmxlen) as [Hextlen [H0c Hall]].
  have Hcroplen: Zlength (crop_mx (extend_mx (Zlength mx) c mx) lens) = Zlength mx
    by rewrite Zlength_map Zlength_Ziota; try lia.
  apply Znth_eq_ext =>[//| i]. rewrite Hcroplen => Hi.
  rewrite Znth_map /=; [|rewrite Zlength_Ziota; lia]. rewrite !Znth_Ziota //; try lia.
  rewrite Hlens //.
  have Hsublen: Zlength (sublist 0 (Zlength (Znth i mx)) (Znth i (extend_mx (Zlength mx) c mx))) = Zlength (Znth i mx). {
    rewrite Zlength_sublist; try lia. list_solve.
    have Hi': 0 <= i < Zlength (extend_mx (Zlength mx) c mx) by lia.
    move: Hall; rewrite Forall_Znth => /(_ i Hi'). move ->.
    by move: Hcbound; rewrite Forall_Znth => /(_ i Hi). }
  apply Znth_eq_ext =>[//| j]. rewrite Hsublen => Hj. rewrite Znth_sublist; try lia.
  rewrite Z.add_0_r. pose proof extend_mx_spec as Hextget. rewrite /get in Hextget; rewrite Hextget{Hextget} //.
  case : (Z_lt_le_dec j (Zlength (Znth i mx))) => [//= Hj' | /= Hj']. 
  have: j < j by apply (Z.lt_le_trans _ _ _ (proj2 Hj)).  (*lia doesnt work for some reason*)
  lia. move: Hcbound; rewrite Forall_Znth => /(_ i Hi). lia. simpl. lia.
Qed.

(*Because of how the C Code represents matrices, it actually multiplies by effectively reversing the columns
  of the first matrix and the rows of another. We don't need to worry about this in the functional model,
  but we need to prove it equivalent in VST. The equality comes from [rev_cols_row_mul] in gaussian.v*)
(*
Definition rev_cols_list 
*)
End Decoder.

End ListMx.