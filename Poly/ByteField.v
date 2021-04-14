Require Import VST.floyd.functional_base.
(*Require Import compcert.lib.Integers.
Require Import Coq.ZArith.BinInt.*)
From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import ListPoly.
Require Import CommonSSR.
Require Import mathcomp.algebra.poly.

(*TODO: move to CommonSSR*)
Lemma nth_nth: forall {A: Type} (d: A) (l: seq A) (n: nat),
  nth d l n = List.nth n l d.
Proof.
  move => A d l. elim : l => [//= n | //= h t IH n].
  - by case : n.
  - case: n. by []. move => n. by rewrite /= IH.
Qed.

Section Ziota.
(*Version of [iota] for nonnegative integers*)
Definition Ziota (x len : Z) :=
  map (fun y => Z.of_nat y) (iota (Z.to_nat x) (Z.to_nat len)).

Lemma Zlength_iota: forall a b,
  Zlength (iota a b) = Z.of_nat b.
Proof.
  move => a b. by rewrite Zlength_correct -size_length size_iota.
Qed.

Lemma Zlength_Ziota: forall x len,
  (0<=x) ->
  (0<= len) ->
  Zlength (Ziota x len) = len.
Proof.
  move => x len Hx Hlen. rewrite /Ziota Zlength_map Zlength_iota. by lia.
Qed.

Lemma Znth_Ziota: forall x len i,
  0 <= x ->
  0 <= len ->
  0 <= i < len ->
  Znth i (Ziota x len) = x + i.
Proof.
  move => x len i Hx Hlen Hi.  rewrite /Ziota Znth_map. rewrite -nth_Znth. rewrite -nth_nth nth_iota.
  - have->: (Z.to_nat x + Z.to_nat i)%N = (Z.to_nat x + Z.to_nat i)%coq_nat by []. lia.
  - apply /ltP. lia.
  - rewrite Zlength_iota; lia.
  - rewrite Zlength_iota; lia.
Qed.

Lemma Zseq_In: forall x len z,
  (0 <= x) ->
  (0 <= len) ->
  In z (Ziota x len) <-> (x <= z < x + len).
Proof.
  move => x len z Hx Hlen. rewrite /Ziota in_map_iff. split => [[i [Hiz Hin]] | Hb].
  move : Hin; rewrite -in_mem_In mem_iota. move => /andP[Hxi Hixlen].
  have {} Hxi: (Z.to_nat x <= i)%coq_nat by apply (elimT leP).
  have {} Hixlen: (i < Z.to_nat x + Z.to_nat len)%coq_nat by apply (elimT ltP). subst.
  split. lia. rewrite Z2Nat.inj_lt; try lia. by rewrite Nat2Z.id Z2Nat.inj_add; try lia.
  exists (Z.to_nat z). split. rewrite Z2Nat.id; lia. rewrite -in_mem_In mem_iota.
  apply (introT andP). split. by apply (introT leP); lia. apply (introT ltP).
  move : Hb => [Hxz Hzxlen]. move: Hzxlen. rewrite Z2Nat.inj_lt; try lia. by rewrite Z2Nat.inj_add; try lia.
Qed.

Lemma Ziota_NoDup: forall x len,
  NoDup (Ziota x len).
Proof.
  move => x len. rewrite /Ziota. apply FinFun.Injective_map_NoDup.
  - rewrite /FinFun.Injective => x' y' Hxy. lia.
  - rewrite -uniq_NoDup. apply iota_uniq.
Qed.

Lemma Ziota_plus_1: forall (x len : Z),
  0 <= x ->
  0 <= len ->
  Ziota x (len + 1) = Ziota x len ++ [:: (x +len)%Z].
Proof.
  move => x len Hx Hlen. rewrite /Ziota.
  have ->: (Z.to_nat (len + 1) = Z.to_nat len + 1%nat)%nat by rewrite Z2Nat.inj_add; try lia.
  rewrite iotaD map_cat /=.
  f_equal. f_equal.
  have ->: ((Z.to_nat x + Z.to_nat len)%nat = Z.to_nat (x + len)%Z) by rewrite Z2Nat.inj_add; try lia.
  lia.
Qed.

End Ziota.

(*Converting between polynomials and integers*)

Section ZPoly.

(*List of bits to/from integer. Note that the list is backwards compared to the usual binary representation*)
Definition bits_to_Z (s: seq bool) : Z :=
  foldr (fun x acc => if x then 2 * acc + 1 else 2 * acc) 0%Z s.

Lemma bits_to_Z_cons: forall h t,
  bits_to_Z (h :: t) = if h then 2 * (bits_to_Z t) + 1 else 2 * (bits_to_Z t).
Proof.
  move => h t. by [].
Qed. 

(*Could do more efficiently with rev, but we don't need to run this*)
Definition Z_to_bits (z: Z) : seq bool :=
  map (Z.testbit z) (Ziota 0 (Z.log2 z + 1)).
 (* foldr (fun i acc => acc ++ [:: Z.testbit z i]) nil (Ziota 0 (Z.log2 z)).*)

(*TODO: move*)
Lemma Znth_nil: forall {A: Type} {d: Inhabitant A} (i: Z),
  @Znth A d i [::] = d.
Proof.
  move => A d i. rewrite /Znth. case : (zlt i 0) => [//= Hi0 | //= Hi0].
  by case : (Z.to_nat i).
Qed.

Lemma bits_to_Z_spec: forall s i,
  Z.testbit (bits_to_Z s) i = Znth i s.
Proof.
  move => s. elim : s => [//= i | h t IH i].
  - by rewrite Z.bits_0 Znth_nil.
  - rewrite bits_to_Z_cons.
    have [Hi | [Hi | Hi]]: (i < 0 \/ i = 0 \/ 0 < i) by lia.
    + rewrite Z.testbit_neg_r; try lia. by rewrite Znth_underflow.
    + subst. case : h.
      * by rewrite Z.testbit_odd_0.
      * by rewrite Z.testbit_even_0.
    + have His: i = Z.succ(i-1) by lia. rewrite {1}His Znth_pos_cons; try lia. case : h.
      * rewrite Z.testbit_odd_succ; try lia. apply IH. 
      * rewrite Z.testbit_even_succ; try lia. apply IH.
Qed.

Lemma Z_to_bits_spec: forall z i,
  0 <= z ->
  Z.testbit z i = Znth i (Z_to_bits z).
Proof.
  move => z i Hz. have [Hi | [Hi | Hi]] : (i < 0 \/ 0 <= i <= Z.log2 z \/ i > Z.log2 z) by lia.
  - rewrite Z.testbit_neg_r; try lia. by rewrite Znth_underflow.
  - rewrite /Z_to_bits Znth_map. by rewrite Znth_Ziota //; lia.
    rewrite Zlength_Ziota; lia.
  - rewrite Znth_overflow. rewrite Z.bits_above_log2 //. lia. rewrite Zlength_map Zlength_Ziota; try lia.
    pose proof (Z.log2_nonneg z). lia.
Qed.

Lemma bits_to_Z_size: forall s,
  0 <= (bits_to_Z s) <= 2 ^ (Z.of_nat (size s)) - 1.
Proof.
  move => s. elim : s => [//= | h t [Hlo Hhi]].
  rewrite bits_to_Z_cons. simpl size. (*can i do this in ssreflect?*)
  have Hlarge: 2 * bits_to_Z t + 1 <= 2 ^ Z.of_nat (size t).+1 - 1. { 
    have->:Z.of_nat (size t).+1 = Z.succ (Z.of_nat (size t)) by lia.
    rewrite Z.pow_succ_r; nia. }
  have Hsmall: 0 <= 2 * bits_to_Z t by lia. by case : h; lia.
Qed.

Lemma Z_to_bits_size: forall z,
  size (Z_to_bits z) = (Z.to_nat (Z.log2 z)).+1.
Proof.
  move => z. pose proof (Z.log2_nonneg z).
  rewrite size_map size_length -ZtoNat_Zlength -Z2Nat.inj_succ //.
  f_equal. by rewrite Zlength_Ziota; lia.
Qed.

(*Now we can convert between Z and polynomials*)

Definition GF2 := BoolField.bool_fieldType.

Local Open Scope ring_scope.

Definition poly_to_Z (p: {poly GF2}) : Z :=
  bits_to_Z p.

Definition Z_to_poly (z: Z) : {poly GF2} :=
  @seq_to_lpoly GF2 (Z_to_bits z).

Lemma poly_to_Z_size: forall p,
  0 <= poly_to_Z p <= 2 ^ Z.of_nat (size p) -1.
Proof.
  move => p. rewrite /poly_to_Z. apply bits_to_Z_size.
Qed.

Lemma Z_to_poly_size: forall z,
  size (Z_to_poly z) = (Z.to_nat (Z.log2 z)).+1.
Proof.
  move => z. rewrite /Z_to_poly. 
  (*TODO: prove that last 1 (Z_to_bits z) != 0*)
Search size apply Z_to_bits_size.

(*Now we can convert from bytes to qpolys and vice versa*)
Lemma byte_to_qpoly_bound: forall (b: byte),
  

Definition byte_to_qpoly (b: byte) : 
