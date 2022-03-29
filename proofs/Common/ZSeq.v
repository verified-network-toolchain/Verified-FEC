(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

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

(* Similar to above, but with lists indexed by bytes*)
Section MkSeqByte.

Definition mkseqByte {A: Type} (f: byte -> A) (bound: Z) :=
  mkseqZ (fun z => f (Byte.repr z)) bound.

Lemma mkseqByte_Zlength: forall {A} (f: byte -> A) b,
  0 <= b ->
  Zlength (mkseqByte f b) = b.
Proof.
  move => A f b Hb. by apply mkseqZ_Zlength.
Qed.

Lemma mkseqByte_Znth_Z: forall {A} `{Inhabitant A} (f: byte -> A) b i,
  0 <= i < b ->
  Znth i (mkseqByte f b) = f (Byte.repr i).
Proof.
  move => A Hinhab f b i Hi. by rewrite mkseqZ_Znth.
Qed.

Lemma mkseqByte_Znth_byte: forall {A} `{Inhabitant A} (f: byte -> A) b (i: byte),
  0 <= Byte.unsigned i < b ->
  Znth (Byte.unsigned i) (mkseqByte f b) = f i.
Proof.
  move => A Hinhab f b i Hi. by rewrite mkseqZ_Znth //Byte.repr_unsigned.
Qed.

End MkSeqByte.

(*Z version of nseq*)
Section ZSeq.

Definition zseq {A: Type} (z: Z) (x: A) :=
  nseq (Z.to_nat z) x.

Lemma zseq_Zlength: forall {A: Type} z (x: A),
  0 <= z ->
  Zlength (zseq z x) = z.
Proof.
  move => A z x Hz. rewrite /mkseqZ Zlength_correct -size_length size_nseq. lia.
Qed.

Lemma zseq_Znth: forall {A: Type} `{Inhabitant A} z (x: A) i,
  0 <= z ->
  0 <= i < z ->
  Znth i (zseq z x) = x.
Proof.
  move => A Hinhab z x i Hz Hi. rewrite -nth_Znth. rewrite -nth_nth nth_nseq.
  case Hiz: (Z.to_nat i < Z.to_nat z)%N => [//|]. apply (elimF ltP) in Hiz. lia. by rewrite zseq_Zlength.
Qed.

Lemma zseq_map: forall {A B : Type} z (x: A) (f: A -> B),
  map f (zseq z x) = zseq z (f x).
Proof.
  move => A B z x f. by rewrite map_nseq.
Qed.

Lemma zseq_hd: forall {A: Type} (z: Z) (x: A),
  1 <= z ->
  zseq z x = x :: zseq (z - 1) x.
Proof.
  move => A z x Hz. rewrite /zseq. have->:(Z.to_nat z) = (1 + (Z.to_nat (z - 1)))%N.
    have->:(1 + (Z.to_nat (z - 1)))%N = (1 + (Z.to_nat (z - 1)))%coq_nat by []. lia.
  by rewrite nseqD.
Qed.

(*TODO: when this was written, Zrepeat did not exist. We don't really need zseq now, should be
  replaced.*)
Lemma zseq_Zrepeat: forall {A: Type} (x: A) (z: Z),
  0 <= z ->
  Zrepeat x z = zseq z x.
Proof.
  move => A x z Hz. have Hinhab: Inhabitant A by apply x. apply Znth_eq_ext.
  - by rewrite Zlength_Zrepeat // zseq_Zlength.
  - move => i. rewrite Zlength_Zrepeat // => Hi.
    by rewrite Znth_Zrepeat // zseq_Znth.
Qed.

Lemma zseq_app: forall {A: Type} (z1 z2: Z) (x: A),
  0 <= z1 ->
  0 <= z2 ->
  zseq (z1 + z2) x = zseq z1 x ++ zseq z2 x.
Proof.
  move => A z1 z2 x Hz1 Hz2. rewrite /zseq -nseqD. f_equal.
  rewrite Z2Nat.inj_add //; lia.
Qed. 

(*also move this*)
Lemma flatten_nseq: forall {A: Type} n1 n2 (x: A),
  flatten (nseq n1 (nseq n2 x)) = nseq (n1 * n2) x.
Proof.
  move => A n1 n2 x. elim : n1 => [// | n1 /= IH].
  by rewrite IH -nseqD.
Qed. 

Lemma zseq_concat: forall {A: Type} z1 z2 (x: A),
  0 <= z1 ->
  0 <= z2 ->
  concat (zseq z1 (zseq z2 x)) = zseq (z1 * z2) x.
Proof.
  move => A z1 z2 x Hz1 Hz2. rewrite concat_flatten /zseq flatten_nseq. f_equal.
  by rewrite Z2Nat.inj_mul.
Qed.

Lemma Ziota_leq: forall i j,
  0 <= i <= j ->
  Ziota 0 j = Ziota 0 i ++ Ziota i (j - i).
Proof.
  move => i j Hij. rewrite /Ziota -map_cat. f_equal.
  have->: (Z.to_nat j) = ((Z.to_nat i) + (Z.to_nat (j-i)))%coq_nat by lia.
  have->:(Z.to_nat i + Z.to_nat (j - i))%coq_nat = (Z.to_nat i + Z.to_nat (j - i))%N by [].
  by rewrite iotaD.
Qed. 

End ZSeq.

(*TODO: where to put this?*)
Definition Z_eq_mixin := EqMixin Z.eqb_spec.
Canonical Z_eqtype := EqType Z Z_eq_mixin. (*dont want canonical*)

Section Zindex.

Definition Zindex {A: eqType} (x: A) (l: seq A) := Z.of_nat (index x l).

Lemma Zindex_Znth: forall {A: eqType} `{Inhabitant A} (i: Z) (l: list A),
  NoDup l ->
  0 <= i < Zlength l ->
  Zindex (Znth i l) l = i.
Proof.
  move => A Hinhab i l Hi Hnodup. rewrite /Zindex - nth_Znth // -nth_nth index_uniq; try lia.
  rewrite size_length -ZtoNat_Zlength. apply /ltP. lia.
  by apply uniq_NoDup.
Qed.

Lemma Zindex_In: forall {A: eqType} (x: A) (l: list A),
  (Zindex x l) < Zlength l <-> In x l.
Proof.
  move => A x l. 
  by rewrite /Zindex Zlength_correct -size_length -Nat2Z.inj_lt (rwP ltP) index_mem in_mem_In.
Qed.

Lemma Zindex_notin: forall {A: eqType} (x: A) (l: list A),
  (Zindex x l) = Zlength l <-> ~(In x l).
Proof.
  move => A x l. 
  by rewrite /Zindex Zlength_correct -size_length Nat2Z.inj_iff (rwP eqP) index_notin -(@in_mem_In A) (rwP negP).
Qed.

Lemma Znth_Zindex: forall {A: eqType} `{Inhabitant A} (x: A) (l: list A),
  In x l ->
  Znth (Zindex x l) l = x.
Proof.
  move => A Hinhab x l Hin. rewrite /Zindex -nth_Znth; last first.
  split; try lia. by apply Zindex_In. rewrite Nat2Z.id -nth_nth. apply nth_index.
  by apply in_mem_In.
Qed.

Lemma Zindex_nonneg: forall {A: eqType} (x: A) (l: seq A),
  0 <= Zindex x l.
Proof.
  move => A x l. rewrite /Zindex. lia.
Qed.

End Zindex.