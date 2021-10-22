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

(*Definition fec_k : Z := proj1_sig (opaque_constant 6).
Definition fec_k_eq : fec_k = 6%Z := proj2_sig (opaque_constant _).
Hint Rewrite fec_k_eq : rep_lia.*)

Definition packet := seq byte.

Definition partial_packets (m: Z) := {packs: seq packet | Zlength packs = m}.

Definition partial_packets_default {m: Z} (Hm: 0 <= m) : partial_packets m :=
  exist _ (zseq m nil) (zseq_Zlength nil Hm).

(*Update the idx'th packet to p *)
Definition partial_packets_update {m: Z} (pp: partial_packets m) (p: packet) (idx: Z) : partial_packets m :=
  exist _ (upd_Znth idx (proj1_sig pp) p) (etrans (Zlength_upd_Znth _ idx (proj1_sig pp) p) (proj2_sig pp)).

Definition partial_packets_max {m: Z} (pp: partial_packets m) : Z :=
  Z.of_nat (list_max (map size (proj1_sig pp))).

Lemma partial_packets_max_bound: forall {m: Z} (pp: partial_packets m) (bound: Z),
  0 <= bound ->
  Forall (fun p => Zlength p <= bound) (proj1_sig pp) ->
  partial_packets_max pp <= bound.
Proof.
  move => m pp bound Hbound Hall. rewrite /partial_packets_max.
  have->: bound = Z.of_nat (Z.to_nat bound) by rewrite Z2Nat.id.
  rewrite -Nat2Z.inj_le list_max_le. move: Hall.
  case : pp => [l Hlen]/=. rewrite !Forall_forall/= => Hall s. rewrite in_map_iff => [[s' [Hs' Hin']]].
  apply Hall in Hin'. subst. rewrite Nat2Z.inj_le. move: Hin'. rewrite Zlength_correct size_length Z2Nat.id; lia.
Qed.

(*A partial matrix fills up every row in the matrix with information from the packets we have, or zeroes otherwise*)
Definition partial_mx {m} (pp: partial_packets m) : lmatrix B :=
  mk_lmatrix m (partial_packets_max pp) (fun i j => 
  if nilp (Znth i (proj1_sig pp)) then Byte.zero else
  if Z_gt_le_dec j (Zlength (Znth i (proj1_sig pp))) then Byte.zero
  else  Znth j (Znth i (proj1_sig pp))).

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

(*Next step: show that when indices is a permutation of (enum n), we get dot prod (shouldn't be too hard
  depending on bigop stuff)*)