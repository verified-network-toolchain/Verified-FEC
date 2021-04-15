(*Definitions and Lemmas about lists indexed by Z, rather than n*)
Require Import VST.floyd.functional_base.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import CommonSSR.

(*Version of [iota] for nonnegative integers*)

Section Ziota.

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

Lemma Ziota_In: forall x len z,
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

(*Z version of [mkseq]*)
Section MkSeqZ.

Definition mkseqZ {A: Type} (f: Z -> A) (bound: Z) :=
  mkseq (fun x => f (Z.of_nat x)) (Z.to_nat bound).

Lemma mkseqZ_Zlength: forall {A} (f: Z -> A) b,
  0 <= b ->
  Zlength (mkseqZ f b) = b.
Proof.
  move => A f b Hb. rewrite /mkseqZ Zlength_correct -size_length size_mkseq. lia.
Qed.

Lemma mkseqZ_Znth: forall {A} `{Inhabitant A} (f: Z -> A) b i,
  0 <= i < b ->
  Znth i (mkseqZ f b) = f i.
Proof.
  move => A Hinhab f b i Hi. rewrite -nth_Znth.
  - rewrite -nth_nth nth_mkseq. f_equal. lia. apply /ltP. lia.
  - rewrite mkseqZ_Zlength; lia.
Qed.

Lemma mkseqZ_plus_1: forall {A} (f: Z -> A) z,
  0 <= z ->
  mkseqZ f (z + 1) = mkseqZ f z ++ [:: f z].
Proof.
  move => A f z Hz. rewrite /mkseqZ /mkseq. have->: (z + 1) = Z.succ z by lia. 
  by rewrite Z2Nat.inj_succ // iota_plus_1 map_cat /= add0n Z2Nat.id.
Qed.

End MkSeqZ.