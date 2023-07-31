(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

Require Import VST.floyd.functional_base.

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(*Facts about Z, bytes, and bounds that are needed in various places. Some of the proofs use ssreflect because
  they were originally in the ByteField code*)

(** Facts about Z*)

Lemma Z_lxor_nonneg': forall a b,
  0 <= a ->
  0 <= b ->
  0 <= Z.lxor a b.
Proof.
  move => a b Ha Hb. by rewrite Z.lxor_nonneg.
Qed.

Lemma Z_shiftl_nonneg': forall a n,
  0 <= a ->
  0 <= Z.shiftl a n.
Proof.
  move => a n Ha. by rewrite Z.shiftl_nonneg.
Qed.

Lemma Int_repr_zero: forall z,
  0 <= z <= Int.max_unsigned ->
  Int.repr z = Int.zero <-> z = 0.
Proof.
  move => z Hz. split => [| Hzero].
  - rewrite /Int.zero => Hzero. apply repr_inj_unsigned in Hzero; rep_lia. 
  - by subst.
Qed.

(** Facts about byte*)

Lemma byte_unsigned_inj: forall (b1 b2: byte),
  Byte.unsigned b1 = Byte.unsigned b2 ->
  b1 = b2.
Proof.
  move => b1 b2 Hb12. apply Vubyte_injective. by rewrite /Vubyte Hb12.
Qed.

Lemma byte_log2_range: forall (b: byte), 
  0 <= Z.log2 (Byte.unsigned b) <= 7%Z.
Proof.
  move => [z Hz /=]. move: Hz; have ->: Byte.modulus = 256%Z by []; move => [Hlo Hhi]. split.
  apply Z.log2_nonneg. have {}Hhi: z <= 255 by lia.
  apply Z.log2_le_mono in Hhi. by move: Hhi; have->: Z.log2 255 = 7 by [].
Qed. 

Lemma Byte_unsigned_nonneg: forall b,
  0 <= Byte.unsigned b.
Proof.
  move => b. pose proof (Byte.unsigned_range_2 b); lia.
Qed.

(*Fold tactics don't work great*)
Lemma byte_testbit_fold: forall b i,
  Z.testbit (Byte.unsigned b) i = Byte.testbit b i.
Proof.
  by [].
Qed.

Lemma byte_unsigned_zero: forall b,
  Byte.unsigned b = 0%Z -> b = Byte.zero.
Proof.
  move => b. have->:0%Z = Byte.unsigned (Byte.zero) by [] => Hzero.
  by apply byte_unsigned_inj in Hzero.
Qed.

Lemma zbits_small: forall i,
  0 <= i < Byte.modulus ->
  Zbits.Zzero_ext 8 i = i.
Proof.
  move => i Hi. rewrite Zbits.Zzero_ext_mod; try rep_lia. have->: two_p 8 = 256 by [].
  rewrite Zmod_small; rep_lia.
Qed.

Lemma byte_shiftl1: forall b: byte,
  Int.signed (Int.shl (Int.repr (Byte.unsigned b)) (Int.repr 1)) =
  Z.shiftl (Byte.unsigned b) 1.
Proof.
  move => b. rewrite /Int.shl; rewrite !Int.unsigned_repr; try rep_lia.
  apply Int.signed_repr. rewrite Z.shiftl_mul_pow2; rep_lia.
Qed.

Lemma byte_shiftl1': forall b: byte,
  Int.unsigned (Int.shl (Int.repr (Byte.unsigned b)) (Int.repr 1)) =
  Z.shiftl (Byte.unsigned b) 1.
Proof.
  move => b. rewrite /Int.shl (Int.unsigned_repr 1); try rep_lia.
  rewrite (Int.unsigned_repr (Byte.unsigned b)); try rep_lia.
  apply Int.unsigned_repr. rewrite Z.shiftl_mul_pow2; rep_lia.
Qed.

(** Constants *)
Definition fec_n : Z := proj1_sig (opaque_constant 256).
Definition fec_n_eq : fec_n = 256%Z := proj2_sig (opaque_constant _).

Definition modulus : Z := proj1_sig (opaque_constant 285).
Definition modulus_eq : modulus = 285%Z := proj2_sig (opaque_constant _).

Definition fec_max_h : Z := proj1_sig (opaque_constant 128).
Definition fec_max_h_eq : fec_max_h = 128%Z := proj2_sig (opaque_constant _).

Definition fec_max_cols : Z := proj1_sig (opaque_constant 16000).
Definition fec_max_cols_eq: fec_max_cols = 16000%Z := proj2_sig(opaque_constant _).

#[export] Hint Rewrite fec_n_eq : rep_lia.
#[export] Hint Rewrite fec_max_h_eq : rep_lia.
#[export] Hint Rewrite modulus_eq : rep_lia.
#[export] Hint Rewrite fec_max_cols_eq : rep_lia.

(*The next 3 lemmas are trying to prove that, if we take 2 integers whose logs are equal and we add them, 
  the log of the resulting integer is smaller. We need this for the field table correctness and VST proofs*)

(*If z2 has its last true testbit at after z2, then its log is larger*)
Lemma testbit_lt: forall m z1 z2,
  0 <= m ->
  2 <= z2 ->
  (forall n, m <= n -> Z.testbit z1 n = false) ->
  Z.testbit z2 m = true ->
  Z.log2 z1 < Z.log2 z2.
Proof.
  move => m z1 z2 Hm Hz2 Hafter Htestm.
  have [Hz1 | Hz1]: (z1 <= 0 \/ 0 < z1) by lia.
  - rewrite Z.log2_nonpos //. apply Z.log2_le_mono in Hz2. move: Hz2; rewrite /=; lia.
  - have Hmlog: m <= Z.log2 z2. have [Hmlog // | Hmlog]: (m <= Z.log2 z2 \/ Z.log2 z2 < m) by lia.
      apply Z.bits_above_log2 in Hmlog; try lia. by rewrite Hmlog in Htestm.
    have [Hz12 // | Hz12]: (Z.log2 z1 < Z.log2 z2 \/ Z.log2 z2 <= Z.log2 z1) by lia.
    have: Z.testbit z1 (Z.log2 z1) = false. apply Hafter; lia. by rewrite Z.bit_log2.
Qed.

(*This is actually not too bad to prove*)
Lemma Z_lxor_smaller: forall z1 z2,
  2 <= z1 ->
  Z.log2 z1 = Z.log2 z2 ->
  Z.log2 (Z.lxor z1 z2) < Z.log2 z1.
Proof.
  move => z1 z2 Hz1 Hlog. have Hz2: 2 <= z2. { have Hz2: 1 <= Z.log2 z2.
    rewrite -Hlog. by apply Z.log2_le_mono in Hz1. have [Hz21 | Hz21]: (z2 <= 1 \/ 2 <= z2) by lia.
    move: Hz21. rewrite -Z.log2_null. lia. by []. }
  apply (@testbit_lt (Z.log2 z1)) => [|//||].
  - apply Z.log2_nonneg.
  - move => n Hn. rewrite Z.lxor_spec. have [Hzn | Hzn]: (Z.log2 z1 = n \/ Z.log2 z1 < n) by lia.
    + subst. by rewrite {2}Hlog !Z.bit_log2; try lia.
    + by rewrite !Z.bits_above_log2; try lia.
  - apply Z.bit_log2; lia.
Qed.


(*Now, we can prove the result we want*)
Lemma xor_modulus_bound: forall (b: byte),
  2 * Byte.unsigned b >= Byte.modulus ->
  0 <= Z.lxor (2 * Byte.unsigned b) modulus < Byte.modulus.
Proof.
  move => b Hlarge. split.
  - rewrite Z.lxor_nonneg. rep_lia.
  - pose proof (byte_log2_range b) as [Hpos Hb].
    have H2b: (Z.log2 (2 * (Byte.unsigned b)) = 1 + Z.log2 (Byte.unsigned b))%Z
      by rewrite Z.log2_double; rep_lia.
    have: (Z.log2 256 <= Z.log2 (2 * Byte.unsigned b))%Z. apply Z.log2_le_mono. rep_lia.
    have->: Z.log2 256 = 8 by [] => H2b'.
    have Hlog: Z.log2 (2 * Byte.unsigned b) = 8 by lia.
    have Hmod: Z.log2 285 = 8 by [].
    have Hxor: (Z.log2 (Z.lxor (2 * Byte.unsigned b) modulus) < 8)%Z. rewrite -Hlog. apply Z_lxor_smaller; rep_lia.
    by apply Z.log2_lt_cancel.
Qed.

(*We also need some more about xor*)

Lemma byte_xor_size: forall b1 b2,
  0 <= Z.lxor (Byte.unsigned b1) (Byte.unsigned b2) <= Byte.max_unsigned.
Proof.
  intros b1 b2. split.
  - apply Z.lxor_nonneg; rep_lia.
  - pose proof (@Byte_unsigned_nonneg b1) as Hb1.
    pose proof (@Byte_unsigned_nonneg b2) as Hb2.
    pose proof (Z.log2_lxor (Byte.unsigned b1) (Byte.unsigned b2) Hb1 Hb2) as Hlog.
    assert (Hxorlog: Z.log2 (Z.lxor (Byte.unsigned b1) (Byte.unsigned b2)) <= 7). {
      apply (Z.le_trans _ _ _ Hlog). apply Z.max_lub; apply byte_log2_range. }
    assert (Hxorlt: Z.log2 (Z.lxor (Byte.unsigned b1) (Byte.unsigned b2)) < 8) by lia.
    replace 8 with (Z.log2 Byte.modulus) in Hxorlt by reflexivity. 
    apply Z.log2_lt_cancel in Hxorlt. rep_lia.
Qed.

Lemma byte_xor_fold: forall b1 b2,
  (Z.lxor (Byte.unsigned b1) (Byte.unsigned b2)) = Byte.unsigned (Byte.xor b1 b2).
Proof.
  intros b1 b2. unfold Byte.xor. rewrite Byte.unsigned_repr; [ reflexivity | apply byte_xor_size].
Qed.

(*EqType for bytes*)

Lemma reflect_proj_sumbool: forall (P: Prop) (H: {P} + {~P}),
  reflect P H.
Proof.
  move => P H. case : H => [Hy | Hn].
  by apply ReflectT. by apply ReflectF.
Qed.

Definition byte_eqMixin := EqMixin 
  (fun i1 i2 => reflect_proj_sumbool (Byte.eq_dec i1 i2)).
Canonical byte_eqType := EqType byte byte_eqMixin.


