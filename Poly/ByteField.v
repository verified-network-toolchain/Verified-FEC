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
Require Import PolyField.
Require Import BoolField.

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
  if Z.eq_dec z 0 then nil else
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
  move => z i Hz. rewrite /Z_to_bits.
  case : (Z.eq_dec z 0) => [Hz0 /= | Hz0/= ].
  - subst. by rewrite /= Z.bits_0 Znth_nil.
  - have [Hi | [Hi | Hi]] : (i < 0 \/ 0 <= i <= Z.log2 z \/ i > Z.log2 z) by lia.
    + rewrite Z.testbit_neg_r; try lia. by rewrite Znth_underflow.
    + rewrite Znth_map. by rewrite Znth_Ziota //; lia.
      rewrite Zlength_Ziota; lia.
    + rewrite Znth_overflow. rewrite Z.bits_above_log2 //. lia.  rewrite Zlength_map Zlength_Ziota; try lia.
      pose proof (Z.log2_nonneg z). lia.
Qed.

Definition GF2 := bool_finFieldType.

(*TODO: move*)
Lemma last_iota: forall n m k,
  (0 < n)%N ->
  last k (iota m n) = (m+n).-1.
Proof.
  move => n. elim : n => [/= m k | /=n IH m k Hn].
  - by rewrite ltnn.
  - apply ltnSE in Hn. move: Hn; rewrite leq_eqVlt => /orP[/eqP Hn0 | Hnpos].
    + by rewrite -Hn0 /= addn1 -pred_Sn.
    + by rewrite IH // addSnnS.
Qed.

Lemma Z_to_bits_last: forall z,
  0 <= z ->
  last (GRing.one bool_fieldType) (Z_to_bits z) != 0%R.
Proof.
  move => z Hz.  rewrite /Z_to_bits. case : (Z.eq_dec z 0) => [Hz0 //= | Hz0 /=].
  have ->: GRing.one BoolField.bool_fieldType = Z.testbit z (Z.log2 z).
  rewrite Z.bit_log2 //. lia. rewrite last_map.
  have->: (last (Z.log2 z) (Ziota 0 (Z.log2 z + 1))) = Z.log2 z.
    rewrite /Ziota.
    have Hlog: (Z.log2 z) = Z.of_nat (Z.to_nat (Z.log2 z)). rewrite Z2Nat.id //. apply Z.log2_nonneg.
    rewrite {1}Hlog last_map last_iota //=.
    rewrite add0n. lia. apply /ltP. lia. rewrite Z.bit_log2 //. lia.
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

Lemma bits_to_Z_zero: forall s x,
  last x s != 0%R ->
  bits_to_Z s = 0%Z ->
  s= [::].
Proof.
  move => s. elim : s => [//= | h t IH Hlast].
  rewrite bits_to_Z_cons. move: Hlast; simpl last. case : h => [Hlast Hz | x Hlast Ht] .
  - pose proof (bits_to_Z_size t). lia.
  - apply Zmult_integral in Ht. case : Ht => [//| Ht].
    apply (IH false) in Ht =>[|//]. by subst.
Qed.

Lemma bits_to_Z_size_last: forall s x,
  s != [::] ->
  last x s != 0%R ->
  Z.succ (Z.log2 (bits_to_Z s)) = Z.of_nat (size s).
Proof.
  move => s. elim : s => [//= | h t IH x Hs{Hs}].
  rewrite bits_to_Z_cons. simpl size.
  have [Ht | Ht]: (bits_to_Z t = 0%Z \/ 0 < bits_to_Z t) by (pose proof (bits_to_Z_size t); lia).
  - simpl last => Hlast. apply (bits_to_Z_zero Hlast) in Ht. subst. move: Hlast; simpl last.
    by case : h.
  - have Hnil: t != [::]. case Htnil: (t == [::]) => [|//].
    have: bits_to_Z t = 0%Z. apply (elimT eqP) in Htnil. by subst. lia.
    simpl last; case : h => [Hlast | Hlast].
    + by rewrite Z.log2_succ_double // (IH true) // Nat2Z.inj_succ.
    + by rewrite Z.log2_double // (IH false) // Nat2Z.inj_succ.
Qed. 

Lemma Z_to_bits_size: forall z,
  size (Z_to_bits z) = if Z.eq_dec z 0 then 0%N else (Z.to_nat (Z.log2 z)).+1.
Proof.
  move => z. pose proof (Z.log2_nonneg z). rewrite /Z_to_bits.
  case : (Z.eq_dec z 0) => [//= | Hz0 /=].
  rewrite size_map size_length -ZtoNat_Zlength -Z2Nat.inj_succ //.
  f_equal. by rewrite Zlength_Ziota; lia.
Qed.

(*Finally, we show that these are inverses*)
Lemma bits_Z_cancel: forall z, 0 <= z -> bits_to_Z (Z_to_bits z) = z.
Proof.
  move => z Hz. apply Z.bits_inj' => n Hn. by rewrite bits_to_Z_spec -Z_to_bits_spec.
Qed.

Lemma Z_bits_cancel: forall l, last (GRing.one bool_fieldType) l != 0%R -> Z_to_bits (bits_to_Z l) = l.
Proof.
  move => l Hl. apply Znth_eq_ext.
  - rewrite !Zlength_correct -!size_length Z_to_bits_size.
    case Hnil: l => [//= | h t].
    rewrite -Hnil. case : (Z.eq_dec (bits_to_Z l) 0) => [Hl0 /= | Hl0].
    + apply (bits_to_Z_zero Hl) in Hl0. by subst.
    + rewrite Nat2Z.inj_succ Z2Nat.id. have Hnil': l != [::] by rewrite Hnil.
      by rewrite (bits_to_Z_size_last Hnil' Hl). apply Z.log2_nonneg.
  - move => i Hi. rewrite -Z_to_bits_spec. by rewrite bits_to_Z_spec.
    by (pose proof (bits_to_Z_size l)); lia.
Qed.

(*Now we can convert between Z and polynomials*)

Local Open Scope ring_scope.

Definition poly_to_Z (p: {poly BoolField.bool_fieldType}) : Z :=
  bits_to_Z p.

Definition Z_to_poly (z: Z) (Hz: 0 <= z) : {poly BoolField.bool_fieldType} :=
  Polynomial (Z_to_bits_last Hz).

Lemma poly_to_Z_size: forall p,
  0 <= poly_to_Z p <= 2 ^ Z.of_nat (size p) -1.
Proof.
  move => p. rewrite /poly_to_Z. apply bits_to_Z_size.
Qed.

Lemma Z_to_poly_size: forall z (Hz: 0 <= z),
  size (Z_to_poly Hz) = if Z.eq_dec z 0 then 0%N else (Z.to_nat (Z.log2 z)).+1.
Proof.
  move => z Hz. apply Z_to_bits_size.
Qed.

(*Work directly with field of polys over p256*)
Lemma p256_irred: polydiv.Pdiv.Field.irreducible_poly (Poly p256).
Proof.
  pose proof p256_primitive as [Hirred HRest]. by rewrite polyseqK.
Qed.

(*We give a new definition to avoid clashing with the previous canonical structures*)
Definition qpoly_p256 : Type := qpoly (Poly p256).

Definition qpoly_p256_finMixin := @qpoly_finMixin GF2 (Poly p256) p256_irred.
Canonical qpoly_p256_finType : finType := FinType qpoly_p256 qpoly_p256_finMixin. 

Definition qpoly_p256_fieldMixin := @qpoly_fieldmixin GF2 (Poly p256) p256_irred.
Canonical qpoly_p256_fieldType : fieldType := FieldType qpoly_p256 qpoly_p256_fieldMixin.

Lemma size_p256: size (Poly p256) = 9%N.
Proof.
  by rewrite size_Poly_lpoly.
Qed.

(*Now we can convert between bytes and qpolys*)
Definition qpoly_to_Z (q: @qpoly GF2 (Poly p256)) : Z :=
  poly_to_Z q.

Lemma qpoly_to_Z_bound: forall q,
  -1 < qpoly_to_Z q < Byte.modulus.
Proof.
  move => [p Hp].
  rewrite /qpoly_to_Z /=. pose proof (poly_to_Z_size p) as [Hlo Hhi].
  move: Hp; rewrite size_p256 => /ltP Hp.
  have {}Hp : (size p <= 8)%coq_nat by lia.
  have->: Byte.modulus = 256 by []. split; try lia.
  have: 2 ^ Z.of_nat (size p) - 1 <= 2 ^ 8 - 1. rewrite -Z.sub_le_mono_r.
    apply Z.pow_le_mono_r; lia.
  have->: (2 ^ 8 - 1)%Z = 255 by []. move => Hhi'. 
  have: poly_to_Z p <= 255 by apply (Z.le_trans _ _ _ Hhi Hhi'). lia.
Qed.

Definition qpoly_to_byte (q: qpoly_p256) : byte :=
  Byte.mkint _ (qpoly_to_Z_bound q).

(*This will be useful in a few places*)
Lemma Byte_unsigned_nonneg: forall b,
  0 <= Byte.unsigned b.
Proof.
  move => b. pose proof (Byte.unsigned_range_2 b); lia.
Qed.

Definition byte_to_poly (b: byte) :  {poly BoolField.bool_fieldType} :=
  Z_to_poly (@Byte_unsigned_nonneg b).

(*TODO: move*)
Lemma byte_log2_range: forall (b: byte), 
  0 <= Z.log2 (Byte.unsigned b) <= 7%Z.
Proof.
  move => [z Hz /=]. move: Hz; have ->: Byte.modulus = 256%Z by []; move => [Hlo Hhi]. split.
  apply Z.log2_nonneg. have {}Hhi: z <= 255 by lia.
  apply Z.log2_le_mono in Hhi. by move: Hhi; have->: Z.log2 255 = 7 by [].
Qed. 

Lemma byte_to_poly_range: forall b,
  (size (byte_to_poly b) < size (Poly p256))%N.
Proof.
  move => b. rewrite /byte_to_poly Z_to_poly_size size_p256. case : (Z.eq_dec (Byte.unsigned b) 0) => [//= | /= Hb].
  rewrite -addn1 -(addn1 8) leq_add2r. apply /ltP.
  pose proof (byte_log2_range b). lia.
Qed.

Definition byte_to_qpoly (b: byte) : qpoly_p256 :=
  @Qpoly GF2 (Poly p256) _ (byte_to_poly_range b).

(*TODO: move*)
Lemma byte_unsigned_inj: forall (b1 b2: byte),
  Byte.unsigned b1 = Byte.unsigned b2 ->
  b1 = b2.
Proof.
  move => b1 b2 Hb12. apply Vubyte_injective. by rewrite /Vubyte Hb12.
Qed.

(*Now, we have to show that these maps form a bijection, and then we can define the ring and field operations*)
Lemma byte_qpoly_cancel: cancel byte_to_qpoly qpoly_to_byte.
Proof.
  move => b. apply byte_unsigned_inj. rewrite /qpoly_to_byte /byte_to_qpoly /= /qpoly_to_Z /= /byte_to_poly /=
  /poly_to_Z /Z_to_poly /=. apply bits_Z_cancel. rep_lia.
Qed.

Lemma qpoly_byte_cancel: cancel qpoly_to_byte byte_to_qpoly.
Proof.
  move => s. apply val_inj. rewrite /= /byte_to_poly /qpoly_to_byte /=.
  apply val_inj. rewrite /= /qpoly_to_Z /poly_to_Z. apply Z_bits_cancel.
  by case : s => [[p Hp] Hsz /=].
Qed.

(*Now we need to define some structures*)
Definition beq (b1 b2: byte) : bool := (Byte.eq_dec b1 b2).

Lemma beq_axiom: Equality.axiom beq.
Proof.
  move => x y. rewrite /beq. case: (Byte.eq_dec x y) => [Hxy /= | Hxy /=].
  - by apply ReflectT.
  - by apply ReflectF.
Qed.

Definition byte_eqMixin := EqMixin beq_axiom.
Canonical byte_eqType := EqType byte byte_eqMixin.

(*We can get choice and finite types from the above bijection*)
Definition byte_choiceMixin := CanChoiceMixin byte_qpoly_cancel.
Canonical byte_choiceType := ChoiceType byte byte_choiceMixin.
Definition byte_countMixin := CanCountMixin byte_qpoly_cancel.
Canonical byte_countType := CountType byte byte_countMixin.
Definition byte_finMixin := CanFinMixin byte_qpoly_cancel. 
Canonical byte_finType := FinType byte byte_finMixin.

(*Zmodtype*)

(*TODO: how to get it to infer the fieldType - it is already Canonical*)

(*TODO: move probably. We need this because ssreflect stuff uses nth*)
Lemma Z_to_bits_nth: forall z i, (0 <= z)%Z ->
  (Z_to_bits z)`_i = Z.testbit z (Z.of_nat i).
Proof.
  move => z i Hz. rewrite Z_to_bits_spec // /Znth. case : (zlt (Z.of_nat i) 0); try lia ; move => Htriv.
  by rewrite Nat2Z.id nth_nth.
Qed.

Lemma addb_xorb: forall (b1 b2: bool),
  addb b1 b2 = xorb b1 b2.
Proof.
  move => b1 b2. by (case : b1; case : b2).
Qed.

(*Fold tactics don't work great*)
Lemma byte_testbit_fold: forall b i,
  Z.testbit (Byte.unsigned b) i = Byte.testbit b i.
Proof.
  by [].
Qed.

(*Addition is xor, which is not too hard to prove*)
Lemma xor_qpoly: forall (b1 b2: byte),
  byte_to_qpoly (Byte.xor b1 b2) = @GRing.add qpoly_p256_fieldType (byte_to_qpoly b1) (byte_to_qpoly b2).
Proof.
  move => b1 b2. apply val_inj. rewrite -polyP => i /=. rewrite coef_add_poly Z_to_bits_nth.
  rewrite byte_testbit_fold.
  have [Hi | Hi]: (0 <= Z.of_nat i < Byte.zwordsize)%Z \/ ((Z.of_nat i) >= Byte.zwordsize)%Z by lia.
  - rewrite Byte.bits_xor // /byte_to_poly /= !Z_to_bits_nth.
    by rewrite /Byte.testbit -addb_xorb. all: apply Byte_unsigned_nonneg.
  - rewrite Byte.bits_above // /byte_to_poly /= !Z_to_bits_nth.
    rewrite !byte_testbit_fold !Byte.bits_above //. all: apply Byte_unsigned_nonneg.
  - apply Byte_unsigned_nonneg.
Qed.

Lemma byte_zero_qpoly: byte_to_qpoly Byte.zero = (q0 (p256_irred)).
Proof.
  rewrite /byte_to_qpoly /q0. apply val_inj. rewrite /= /byte_to_poly /= /Z_to_poly /=.
  apply val_inj. by rewrite /= polyseq0 /Byte.zero Byte.unsigned_repr.
Qed.

Lemma byte_one_qpoly: byte_to_qpoly Byte.one = (q1 (p256_irred)).
Proof.
  rewrite /byte_to_qpoly /q1. apply val_inj. rewrite /= /byte_to_poly /= /Z_to_poly /=.
  apply val_inj. by rewrite /= polyseq1 /Byte.one Byte.unsigned_repr.
Qed.

(*opp is easy*)
Lemma opp_qpoly: forall (b1: byte),
  byte_to_qpoly b1 = @GRing.opp qpoly_p256_fieldType (byte_to_qpoly b1).
Proof.
  move => b1. apply val_inj. rewrite /= /byte_to_poly /= /Z_to_poly /=.
  rewrite -polyP => i. by rewrite /= coef_opp_poly /=.
Qed.

(*We define multiplication and division in terms of qpolys directly*)
Definition mul_byte (b1 b2: byte) : byte :=
  qpoly_to_byte (@GRing.mul qpoly_p256_fieldType (byte_to_qpoly b1) (byte_to_qpoly b2)).

Definition inv_byte (b: byte) : byte :=
  qpoly_to_byte (@GRing.inv qpoly_p256_fieldType (byte_to_qpoly b)).

(*This proves (implictly) that these rings are isomorphic. Since we need the canonical instances, we prove
  all the conditions manually, but they all follow from the above isomorphism*)



