(* Because the packets arrive in arbitrary order, we need to be very careful when defining the matrix and 
computing the dot prod*)
Require Import VST.floyd.functional_base.

From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import VandermondeByte. (*For B*)
Require Import ZSeq.
Require Import CommonSSR.
Require Import ListMatrix.
Require Import ByteField.

Definition partial_packets_max (pp: seq (seq byte)) : Z :=
  Z.of_nat (list_max (map size pp)).

Lemma partial_packets_max_bound: forall (pp: seq (seq byte)) (bound: Z),
  0 <= bound ->
  Forall (fun p => Zlength p <= bound) pp ->
  partial_packets_max pp <= bound.
Proof.
  move => pp bound Hbound Hall. rewrite /partial_packets_max.
  have->: bound = Z.of_nat (Z.to_nat bound) by rewrite Z2Nat.id.
  rewrite -Nat2Z.inj_le list_max_le. move: Hall.
  rewrite !Forall_forall/= => Hall s. rewrite in_map_iff => [[s' [Hs' Hin']]].
  apply Hall in Hin'. subst. rewrite Nat2Z.inj_le. move: Hin'. rewrite Zlength_correct size_length Z2Nat.id; lia.
Qed.

(*A partial matrix fills up every row in the matrix with information from the packets we have, or zeroes otherwise*)
Definition partial_mx (pp: seq (seq byte)) : lmatrix B :=
  mk_lmatrix (Zlength pp) (partial_packets_max pp) (fun i j => 
  if nilp (Znth i pp) then Byte.zero else
  if Z_gt_le_dec j (Zlength (Znth i pp)) then Byte.zero
  else Znth j (Znth i pp)).

(* Predicate to describe the buffer *)

(*dot prod is just defined on the entries that actually exist - but because we filled in with zeroes, that is
  the same as taking the whole dot prod, then when we update, it just adds a term*)

(*We need a generalized notion of dot product - instead of up to a specific bound, it must include a certain
  list of indices *)
(*TODO: over generic field?*)

Section DotProd.

Local Open Scope ring_scope.

Definition dot_prod_gen_aux (mx1: lmatrix B) (mx2: lmatrix B) i j (indices: seq Z) base : B :=
  foldl (fun acc k => acc + (get mx1 i k) * (get mx2 k j)) base indices.

Definition dot_prod_gen (mx1: lmatrix B) (mx2: lmatrix B) i j (indices: seq Z) : B :=
  dot_prod_gen_aux mx1 mx2 i j indices 0%R.

(*For dot product, need to know that the whole thing is equivalent to regular dot product. This will be much
  easier to do in mathcomp *)
Definition dot_prod_gen_aux_sum: forall m n p mx1 mx2 i j indices base (d: 'I_(Z.to_nat n)) 
  (Hi: 0 <= i < m) (Hj : 0 <= j < p),
  Forall (fun i => 0 <= i < n) indices ->
  wf_lmatrix mx1 m n ->
  wf_lmatrix mx2 n p ->
  dot_prod_gen_aux mx1 mx2 i j indices base = 
  base + \sum_(i0 <- (map Z.to_nat indices)) 
    lmatrix_to_mx m n mx1 (Z_to_ord Hi) (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) i0) *
    lmatrix_to_mx n p mx2 (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) i0) (Z_to_ord Hj).
Proof.
  move => m n p mx1 mx2 i j indices base d Hi Hj Hall Hwf1 Hwf2. rewrite /dot_prod_gen_aux.
  move: base Hall. (*generalize IH*)
  elim : indices => [//= base Hall | h t/= IH base Hall].
  - by rewrite big_nil GRing.addr0.
  - rewrite big_cons IH.
    + rewrite GRing.addrA. f_equal. f_equal. rewrite !mxE/= !Z2Nat.id; try lia.
      have Hh: (0 <= Z.to_nat h < Z.to_nat n)%nat. apply Forall_inv in Hall.
      have->/=: (0 <= Z.to_nat h)%N by (apply /leP; lia). apply /ltP; lia.
      have ->: (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) (Z.to_nat h)) = 
      (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) (Ordinal Hh)) by []. 
        rewrite ordinal_enum //= !Z2Nat.id //; try lia.
      apply Forall_inv in Hall; lia.
    + by apply Forall_inv_tail in Hall.
Qed. 

Lemma dot_prod_gen_sum: forall m n p mx1 mx2 i j indices (d: 'I_(Z.to_nat n)) 
  (Hi: 0 <= i < m) (Hj : 0 <= j < p),
  Forall (fun i => 0 <= i < n) indices ->
  wf_lmatrix mx1 m n ->
  wf_lmatrix mx2 n p ->
  dot_prod_gen mx1 mx2 i j indices = 
  \sum_(i0 <- (map Z.to_nat indices)) 
    lmatrix_to_mx m n mx1 (Z_to_ord Hi) (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) i0) *
    lmatrix_to_mx n p mx2 (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) i0) (Z_to_ord Hj).
Proof.
  move => m n p mx1 mx2 i j indices d Hi Hj Hall Hwf1 Hwf2. 
  by rewrite /dot_prod_gen (@dot_prod_gen_aux_sum m n p _ _ _ _ _ _ d) // GRing.add0r.
Qed.

(*2 parts: If indices has length n and unique elements from 0 to n-1, it is a permutation of (enum n)
  and if this condition holds, this is equivalent to the dot product *)

(*It is quite difficult to prove that if we have a list of elements from m to n-m of length n, then it is a
  permutation of iota m n. It is a bit easier to prove a more general claim: if l and s are unique lists of the
  same length and all elements in l are in s, then l and s are permutations. But to do this we need to define
  a map between elements in the two lists, show that is is bijective, and use the inverse. *)

Definition seq_sub_map {T: choiceType} (l s: seq T) (Hin: forall t, t \in l -> t \in s) : 
  (seq_sub_finType l) -> (seq_sub_finType s).
Proof.
  move => x.
  have y: seq_sub s. case : x => x Hl. have Hs: x \in s by apply (Hin x Hl). apply (SeqSub Hs).
  apply y.
Defined.

Lemma seq_sub_map_inj: forall {T: choiceType} (l s: seq T) (Hin: forall t, t \in l -> t \in s),
  injective (seq_sub_map Hin).
Proof.
  move => T l s Hin. rewrite /injective /seq_sub_map/= => x1 x2.
  case : x1. case: x2. move => x Hx y Hy/=. rewrite /ssr_have.
  move => [Hxy]. subst. by have->: Hx = Hy by apply bool_irrelevance.
Qed.

Lemma perm_conds: forall (l s: seq nat) (n: nat),
  size l = n ->
  size s = n ->
  uniq l ->
  uniq s ->
  (forall i, i \in l -> i \in s) ->
  perm_eq l s.
Proof.
  move => l s n Hszl Hszs Hunl Hsun Hall.
  apply uniq_perm => [//|//|]. move => i.
  have [g Hcan Hcan']: bijective (seq_sub_map Hall). { apply inj_card_bij.
    apply seq_sub_map_inj. by rewrite !card_seq_sub // Hszl Hszs. }
  case Hl: (i \in l).
  - apply Hall in Hl. by rewrite Hl.
  - case Hs: (i \in s) => [|//].
    (*Contradiction - by inverse map, i must be in l*)
    remember (SeqSub Hs) as sf eqn : Hsf.
    remember (g sf) as lf eqn : Hlf.
    move: Hcan'. rewrite /cancel => /(_ sf). rewrite -Hlf Hsf /seq_sub_map /=. move: Hlf. case : lf => [y Hy]/=.
    rewrite /ssr_have => _ [Hiy]. subst. by rewrite Hy in Hl.
Qed.

(*Now we can prove the [iota] result*)
Lemma perm_iota: forall (l: seq nat) (m n: nat),
  (m <= n)%N ->
  size l = (n - m)%N ->
  Forall (fun i => (m <= i < n)%N) l ->
  uniq l ->
  perm_eq l (index_iota m n).
Proof.
  move => l m n Hmn Hsz Hall Huniq. apply (@perm_conds _ _ (n- m)%N) => [//||//||].
  - by apply size_iota.
  - by apply iota_uniq.
  - move => i Hi. move: Hall. rewrite Forall_forall => /(_ i). rewrite -in_mem_In mem_iota subnKC //.
    by move => /(_ Hi).
Qed.

(*And then we can lift that the Z level*)
Lemma enum_perm_conds: forall (l: seq Z) n,
  Zlength l = n ->
  Forall (fun i => 0 <= i < n) l ->
  NoDup l ->
  perm_eq (map Z.to_nat l) (index_iota 0 (Z.to_nat n)).
Proof.
  move => l n. rewrite Zlength_correct -size_length => Hlen Hall Huniq.
  apply uniq_perm.
  - rewrite uniq_NoDup. apply NoDup_map_inj => [ x y Hinx Hiny |//].
    move: Hall; rewrite Forall_forall => Hall. 
    have: 0 <= x < n by apply Hall.
    have: 0 <= y < n by apply Hall. lia.
  - apply iota_uniq.
  - apply perm_mem.
    apply perm_iota.
    + apply /leP. lia.
    + rewrite size_map subn0. lia.
    + move: Hall. rewrite !Forall_forall => Hall x. rewrite in_map_iff => [[y [Hy Hiny]]].
      apply Hall in Hiny. have->/=: (0 <= x)%N by (apply /leP; lia). apply /ltP; lia.
    + rewrite uniq_NoDup. apply NoDup_map_inj => [x y Hinx Hiny|//].
      move: Hall. rewrite !Forall_forall => Hall. apply Hall in Hinx. apply Hall in Hiny. lia.
Qed.

(*Part 2: If the input to dot_prod_gen is a permutation of index_iota, then this equals the full dot product *)
Lemma dot_prod_gen_perm_eq: forall m n p mx1 mx2 i j indices
  (Hi: 0 <= i < m) (Hj : 0 <= j < p),
  Forall (fun i => 0 <= i < n) indices ->
  perm_eq (map Z.to_nat indices) (index_iota 0 (Z.to_nat n)) ->
  wf_lmatrix mx1 m n ->
  wf_lmatrix mx2 n p ->
  dot_prod_gen mx1 mx2 i j indices = 
    ((lmatrix_to_mx m n mx1) *m (lmatrix_to_mx n p mx2)) (Z_to_ord Hi) (Z_to_ord Hj).
Proof.
  move => m n p mx1 mx2 i j indices Hi Hj Hall Hperm Hwf1 Hwf2. rewrite !mxE.
  have Hn0: 0 <= n by apply Hwf1.
  have: n = 0%Z \/ 0 < n by lia. move => [{}Hn0 | {} Hn0].
  - subst. rewrite /dot_prod /=. rewrite big_ord0.
    move: Hperm. rewrite /index_iota /= => /perm_nilP Hnil. apply map_eq_nil in Hnil.
    by rewrite Hnil /dot_prod_gen.
  - (*Now we have an instance of an 'I_n, which we need*)
    have Hnord: 0 <= 0 < n by lia.
    rewrite (big_nth (Z_to_ord Hnord)) /= /index_enum /= ordinal_enum_size /dot_prod.
    rewrite (@dot_prod_gen_sum m n p _ _ _ _ _ (Z_to_ord Hnord)) => [|//|//|//].
    by apply perm_big.
Qed.

(*Putting it all together with useful hypotheses for the client:*)
Lemma dot_prod_gen_eq: forall m n p mx1 mx2 i j indices
  (Hi: 0 <= i < m) (Hj : 0 <= j < p),
  Zlength indices = n ->
  Forall (fun i => 0 <= i < n) indices ->
  NoDup indices ->
  wf_lmatrix mx1 m n ->
  wf_lmatrix mx2 n p ->
  dot_prod_gen mx1 mx2 i j indices = 
    ((lmatrix_to_mx m n mx1) *m (lmatrix_to_mx n p mx2)) (Z_to_ord Hi) (Z_to_ord Hj).
Proof.
  move => m n p mx1 mx2 i j indices Hi Hj Hlen Hall Hnodup Hwf1 Hwf2. rewrite (@dot_prod_gen_perm_eq m n p) //.
  by apply enum_perm_conds.
Qed.

End DotProd.

Require Import ComputableWeights.

Section Predicate.

Definition fec_k : Z := proj1_sig (opaque_constant 6).
Definition fec_k_eq : fec_k = 6%Z := proj2_sig (opaque_constant _).
Hint Rewrite fec_k_eq : rep_lia.
Definition fec_h : Z := proj1_sig (opaque_constant 3).
Definition fec_h_eq : fec_h = 3%Z := proj2_sig (opaque_constant _).
Hint Rewrite fec_h_eq : rep_lia.
(*Predicate *)
(*TODO: need both indices and packets?*)
Definition buffer_filled (buffer: seq (seq (seq byte))) (batchnum : Z) (indices: seq Z) 
  (packets : seq (seq byte)) (bound: Z) : Prop :=
  Zlength packets = fec_k /\
  Zlength indices <= fec_k /\
  NoDup indices /\
  Forall (fun i => 0 <= i < fec_k) indices /\
  0 <= batchnum < Zlength buffer /\
  Forall (fun l => Zlength l <= bound) packets ->
  forall i j, 0 <= i < fec_h -> 0 <= j < bound -> 
    get (Znth batchnum buffer) i j = dot_prod_gen static_weights (partial_mx packets) i j indices.


(*TODO: update lemmas as needed*)
End Predicate.