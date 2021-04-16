Require Import VST.floyd.functional_base.
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
Require Import ZSeq.

(*A few generic results*)

Lemma Znth_nil: forall {A: Type} {d: Inhabitant A} (i: Z),
  @Znth A d i [::] = d.
Proof.
  move => A d i. rewrite /Znth. case : (zlt i 0) => [//= Hi0 | //= Hi0].
  by case : (Z.to_nat i).
Qed.

(*A few results about bytes in general*)
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

(*We need this because ssreflect stuff uses nth*)
Lemma Z_to_bits_nth: forall z i, (0 <= z)%Z ->
  ((Z_to_bits z)`_i)%R = Z.testbit z (Z.of_nat i).
Proof.
  move => z i Hz. rewrite Z_to_bits_spec // /Znth. case : (zlt (Z.of_nat i) 0); try lia ; move => Htriv.
  by rewrite Nat2Z.id nth_nth.
Qed.

Definition GF2 := bool_finFieldType.

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

(*Because of dependent type annoying stuff*)
Lemma Z_to_poly_eq: forall z1 z2 (Hz1: 0 <= z1) (Hz2 : 0 <= z2),
  z1 = z2 ->
  Z_to_poly Hz1 = Z_to_poly Hz2.
Proof.
  move => z1 z2 Hz1 Hz2 Hz12. rewrite /Z_to_poly. apply val_inj. rewrite /=. by subst.
Qed. 

End ZPoly.

Section ByteQpolyMap.

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

Lemma byte_to_poly_range: forall b,
  (size (byte_to_poly b) < size (Poly p256))%N.
Proof.
  move => b. rewrite /byte_to_poly Z_to_poly_size size_p256. case : (Z.eq_dec (Byte.unsigned b) 0) => [//= | /= Hb].
  rewrite -addn1 -(addn1 8) leq_add2r. apply /ltP.
  pose proof (byte_log2_range b). lia.
Qed.

Definition byte_to_qpoly (b: byte) : qpoly_p256 :=
  @Qpoly GF2 (Poly p256) _ (byte_to_poly_range b).



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

Lemma byte_qpoly_bij: bijective byte_to_qpoly.
Proof.
  apply (Bijective byte_qpoly_cancel). apply qpoly_byte_cancel.
Qed.

Lemma byte_to_qpoly_inj: injective byte_to_qpoly.
Proof.
  apply bij_inj. apply byte_qpoly_bij.
Qed.

End ByteQpolyMap.

Section ByteAlg.

Local Open Scope ring_scope.

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

Lemma card_byte: #|byte_finType| = 256%N.
Proof.
  by rewrite (bijective_card byte_qpoly_bij) qpoly_size size_p256 /= card_bool.
Qed. 

(*Zmodtype*)

(*TODO: how to get it to infer the fieldType - it is already Canonical*)

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

Lemma Z_lxor_nonneg': forall a b,
  0 <= a ->
  0 <= b ->
  0 <= Z.lxor a b.
Proof.
  move => a b Ha Hb. by rewrite Z.lxor_nonneg.
Qed.

(*Addition is xor, which is not too hard to prove*)
(*We first prove for general Z, then bytes*)
Lemma xor_poly: forall (z1 z2: Z) (Hz1: 0 <= z1) (Hz2: 0 <= z2) (Hxor: 0 <= Z.lxor z1 z2),
  Z_to_poly Hxor = (Z_to_poly Hz1) + (Z_to_poly Hz2). 
Proof.
  move => z1 z2 Hz1 Hz2 Hxor. rewrite -polyP => i /=.
  by rewrite coef_add_poly /Z_to_poly /= !Z_to_bits_nth // Z.lxor_spec -addb_xorb.
Qed.

Lemma xor_qpoly: forall (b1 b2: byte),
  byte_to_qpoly (Byte.xor b1 b2) = @GRing.add qpoly_p256_fieldType (byte_to_qpoly b1) (byte_to_qpoly b2).
Proof.
  move => b1 b2. apply val_inj. rewrite /=. rewrite /byte_to_poly /Byte.xor.
  rewrite (@Z_to_poly_eq _ (Z.lxor (Byte.unsigned b1) (Byte.unsigned b2))).
  - apply Z_lxor_nonneg'; rep_lia.
  - move => Hxor. by apply xor_poly.
  - rewrite Byte.unsigned_repr //. split. apply Z_lxor_nonneg'; rep_lia.
    pose proof (Z.log2_lxor (Byte.unsigned b1) (Byte.unsigned b2)).
    have: Z.max (Z.log2 (Byte.unsigned b1)) (Z.log2 (Byte.unsigned b2)) <= Z.log2 255. {
      apply Z.max_lub; apply Z.log2_le_mono; rep_lia. } rewrite /= => Hup.
    have: Z.log2 (Z.lxor (Byte.unsigned b1) (Byte.unsigned b2)) < Z.log2 (Byte.modulus). rewrite /=. rep_lia.
    move => Hloglt. apply Z.log2_lt_cancel in Hloglt. rep_lia.
Qed.

Lemma byte_zero_qpoly: byte_to_qpoly Byte.zero = (q0 (p256_irred)).
Proof.
  rewrite /byte_to_qpoly /q0. apply val_inj. rewrite /= /byte_to_poly /= /Z_to_poly /=.
  apply val_inj. by rewrite /= polyseq0 /Byte.zero Byte.unsigned_repr.
Qed.

Lemma byte_zero_qpoly_iff: forall b, (byte_to_qpoly b == (@GRing.zero qpoly_p256_fieldType)) = (b == Byte.zero).
Proof.
  move => b. case Hb: (b == Byte.zero).
  - apply (elimT eqP) in Hb. by rewrite Hb byte_zero_qpoly eq_refl.
  - case Hbq: (byte_to_qpoly b == 0) => [|//]. apply (elimT eqP) in Hbq. move: Hbq.
    have->: (@GRing.zero qpoly_p256_fieldType) = (q0 (p256_irred)) by [].
    rewrite /byte_to_qpoly /q0 => Hq. apply (@congr1 _ _ val (Qpoly (byte_to_poly_range b)) _) in Hq.
    move: Hq; rewrite /= /byte_to_poly /Z_to_poly => Hp.
    apply (@congr1 _ _ val (Polynomial (Z_to_bits_last (Byte_unsigned_nonneg (b:=b))))) in Hp.
    move: Hp; rewrite /= polyseq0 => Hz. apply (congr1 bits_to_Z) in Hz. move: Hz.
    rewrite bits_Z_cancel /=. have->: 0%Z = Byte.unsigned Byte.zero by rewrite Byte.unsigned_zero.
    move => Hun. apply byte_unsigned_inj in Hun. by rewrite Hun in Hb. apply Byte_unsigned_nonneg.
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
Definition byte_mul (b1 b2: byte) : byte :=
  qpoly_to_byte (@GRing.mul qpoly_p256_fieldType (byte_to_qpoly b1) (byte_to_qpoly b2)).

Definition byte_inv (b: byte) : byte :=
  qpoly_to_byte (@GRing.inv qpoly_p256_fieldType (byte_to_qpoly b)).

(*This proves (implictly) that these rings are isomorphic. Since we need the canonical instances, we prove
  all the conditions manually, but they all follow from the above isomorphism*)

Lemma baddA: associative Byte.xor.
Proof.
  move => b1 b2 b3. by rewrite Byte.xor_assoc.
Qed.

Lemma baddC: commutative Byte.xor.
Proof.
  move => b1 b2. apply Byte.xor_commut.
Qed.

Lemma baddFb: left_id Byte.zero Byte.xor.
Proof.
  move => b. apply Byte.xor_zero_l.
Qed.

Lemma baddbb: left_inverse Byte.zero id Byte.xor.
Proof.
  move => b. apply Byte.xor_idem.
Qed.

Definition byte_zmodmixin := ZmodMixin baddA baddC baddFb baddbb.
Canonical byte_zmodtype := ZmodType byte byte_zmodmixin.

Lemma byte_mulA: associative byte_mul.
Proof.
  move => b1 b2 b3. rewrite /byte_mul. f_equal. by rewrite !qpoly_byte_cancel GRing.mulrA.
Qed.

Lemma byte_mulC: commutative byte_mul.
Proof.
  move => b1 b2. rewrite /byte_mul. f_equal. by rewrite GRing.mulrC.
Qed.

Lemma byte_mul1q: left_id Byte.one byte_mul.
Proof.
  move => b. by rewrite /byte_mul byte_one_qpoly GRing.mul1r byte_qpoly_cancel.
Qed.

Lemma byte_mulD: left_distributive byte_mul Byte.xor.
Proof.
  move => b1 b2 b3. rewrite /byte_mul. apply byte_to_qpoly_inj. 
  by rewrite !xor_qpoly !qpoly_byte_cancel GRing.mulrDl.
Qed.

Lemma byte_1not0: Byte.one != Byte.zero.
Proof.
  apply /beq_axiom. apply Byte.one_not_zero.
Qed.

Definition byte_comringmixin := ComRingMixin byte_mulA byte_mulC byte_mul1q byte_mulD byte_1not0.
Canonical byte_ring := RingType byte byte_comringmixin.
Canonical byte_comring := ComRingType byte byte_mulC.

Definition bunit : pred byte :=
  fun x => x != Byte.zero.

Lemma bunit_qunit: forall b,
  bunit b = qunit p256_irred (byte_to_qpoly b).
Proof.
  move => b. by rewrite /bunit /qunit byte_zero_qpoly_iff.
Qed.

Lemma byte_mulVr: {in bunit, left_inverse Byte.one byte_inv byte_mul}.
Proof.
  move => b Hin. rewrite /byte_mul /byte_inv qpoly_byte_cancel GRing.mulVr.
  - apply byte_to_qpoly_inj. by rewrite byte_one_qpoly qpoly_byte_cancel.
  - rewrite GRing.unitfE. have: b != Byte.zero by []. by rewrite byte_zero_qpoly_iff.
Qed.

Lemma byte_mulrV: {in bunit, right_inverse Byte.one byte_inv byte_mul}.
Proof.
  move => b Hin. rewrite byte_mulC. by apply byte_mulVr.
Qed.

Lemma byte_unitP : forall x y : byte, (y * x) = 1 /\ (x * y) = 1 -> bunit x.
Proof.
  move => x y. have->: (x * y) = byte_mul x y by [].
  have->: (y * x) = byte_mul y x by []. rewrite /byte_mul => [[Hun1 Hun2]].
  have Hun: @GRing.mul qpoly_p256_fieldType (byte_to_qpoly y) (byte_to_qpoly x) = (q1 p256_irred) /\
        @GRing.mul qpoly_p256_fieldType (byte_to_qpoly x) (byte_to_qpoly y) = (q1 p256_irred). {
  split.
  - apply (congr1 byte_to_qpoly) in Hun1. move: Hun1; rewrite qpoly_byte_cancel. move ->.
    apply byte_one_qpoly.
  - apply (congr1 byte_to_qpoly) in Hun2. move: Hun2; rewrite qpoly_byte_cancel. move ->.
    apply byte_one_qpoly. }
  apply (qpoly_unitP) in Hun. by rewrite bunit_qunit.
Qed.

Lemma byte_inv0id : {in [predC bunit], byte_inv =1 id}.
Proof.
  move => b Hun. have Hz: ~~ (b != 0) by []. move: Hz; rewrite negbK => /eqP Hz. subst.
  rewrite /byte_inv /= byte_zero_qpoly GRing.invr0. apply byte_to_qpoly_inj.
  rewrite qpoly_byte_cancel. apply /eqP. by rewrite eq_sym byte_zero_qpoly_iff.
Qed.

Definition byte_unitringmixin := UnitRingMixin byte_mulVr byte_mulrV byte_unitP byte_inv0id.
Canonical byte_unitringtype := UnitRingType byte byte_unitringmixin.

Lemma byte_mulf_eq0 : forall x y : byte, (x * y) = 0 -> (x == 0) || (y == 0).
Proof.
  move => x y. have->: (x * y) = byte_mul x y by []. have->:0 = Byte.zero by []. rewrite /byte_mul => Hq.
  apply (congr1 byte_to_qpoly) in Hq. move: Hq; rewrite qpoly_byte_cancel byte_zero_qpoly => Hz.
  apply qpoly_mulf_eq0 in Hz. by rewrite -!byte_zero_qpoly_iff.
Qed.

Canonical byte_comunitring := [comUnitRingType of byte].
Canonical byte_idomaintype := IdomainType byte byte_mulf_eq0.

Lemma byte_mulVf : GRing.Field.axiom byte_inv.
Proof.
  move => b Hnz. by apply byte_mulVr.
Qed. 

Lemma byte_inv0: byte_inv 0%R = 0%R.
Proof. 
  by apply byte_inv0id.
Qed. 

Definition byte_fieldmixin := FieldMixin byte_mulVf byte_inv0.
Canonical byte_fieldType := FieldType byte byte_fieldmixin.
(*Canonical byte_finFieldType := Eval hnf in [finFieldType of byte]. - dont actually need this*)

Lemma F_char_2: 2%N \in [char byte_fieldType]%R.
Proof.
  rewrite /GRing.char //= /in_mem /= GRing.mulr2n /=.
Qed.

End ByteAlg.

Require Import mathcomp.algebra.polydiv.

Section Pow.

Local Open Scope ring_scope.

(*Now we need to define the power and logarithm maps and tables*)
Lemma ord_byte_bound: forall (x: 'I_#|byte_finType|), -1 < Z.of_nat x < Byte.modulus.
Proof.
  move => [n Hn] /=. rewrite card_byte in Hn. move: Hn => /ltP Hn. rep_lia.
Qed.

Definition ord_to_byte (x: 'I_#|byte_finType|) := Byte.mkint _ (ord_byte_bound x).

Lemma byte_ord_bound: forall (b: byte), (Z.to_nat (Byte.unsigned b) < #|byte_finType|)%N.
Proof.
  move => b. rewrite card_byte. pose proof (Byte.unsigned_range b) as Hrange. apply /ltP. rep_lia.
Qed.

Definition byte_to_ord (b: byte) : 'I_#|byte_finType| := Ordinal (byte_ord_bound b).

(*TODO: maybe will need cancel for these, not sure*)

(*Now, we can define the power and inverse power (log) maps*)

Lemma p256_geq_2: (2 < size (Poly p256))%N.
Proof.
  by rewrite size_p256.
Qed.

Lemma byte_qpoly_size: #|byte_finType| = (#|finalg.FinRing.Field.eqType bool_finFieldType| ^ (size (Poly p256)).-1)%N.
Proof.
  by rewrite card_bool size_p256 card_byte.
Qed.

(*TODO; move to commonssr*)
Lemma eq_leqn: forall m n,
  m = n ->
  (m <= n)%N.
Proof.
  move => m n ->. by rewrite leqnn.
Qed. 

Definition eq_ord m n (Hmn: m = n) (x: 'I_m) : 'I_n  := widen_ord (eq_leqn Hmn) x.

Definition byte_pow_map (b: byte) : byte :=
  qpoly_to_byte (qpow_map_full p256_irred p256_geq_2 (eq_ord byte_qpoly_size (byte_to_ord b))).

Definition byte_log_map (b: byte) : byte :=
  ord_to_byte (eq_ord (esym byte_qpoly_size) (find_qpow p256_irred p256_geq_2 (byte_to_qpoly b))).

Definition byte_pows : seq byte :=
  mkseqByte byte_pow_map Byte.modulus.

Definition byte_logs : seq byte :=
  mkseqByte byte_log_map Byte.modulus.

Definition byte_invs: seq byte :=
  mkseqByte byte_inv Byte.modulus.

(*Lemmas about these maps*)
Lemma byte_pow_map_zero: byte_pow_map Byte.zero = Byte.one.
Proof.
  rewrite /byte_pow_map /byte_to_ord /qpow_map_full /=.
  have->:Z.to_nat (Byte.unsigned Byte.zero) = 0%N by []. rewrite GRing.expr0.
  apply byte_to_qpoly_inj. by rewrite byte_one_qpoly qpoly_byte_cancel.
Qed.

(*We will model the functions that populate the lookup tables here, so the VST proof does not need to
  directly reason about any field properties*)

Definition p256_val : Z := 285.

Lemma p256_val_nonneg: 0 <= p256_val.
Proof.
  rewrite /p256_val. lia.
Qed.

Lemma p256_val_poly: Z_to_poly (p256_val_nonneg) = Poly p256.
Proof.
  apply val_inj. by rewrite polyseqK.
Qed. 

(*Multiply a byte by x, directly*)
Definition byte_mulX (b: byte) :=
  let temp := Z.shiftl (Byte.unsigned b) 1 in
  if (Z_lt_ge_dec temp Byte.modulus) then Byte.repr temp else
  Byte.repr (Z.lxor temp p256_val).

Lemma Z_shiftl_nonneg': forall a n,
  0 <= a ->
  0 <= Z.shiftl a n.
Proof.
  move => a n Ha. by rewrite Z.shiftl_nonneg.
Qed.

(*Left shifting an integer multiplies the corresponding poly by X*)
Lemma Z_shiftl_poly: forall z (Hz: 0 <= z) (Hshift: 0 <= Z.shiftl z 1),
  Z_to_poly Hshift = 'X * (Z_to_poly Hz).
Proof.
  move => z Hz Hshift. rewrite -polyP => i. rewrite coefXM /Z_to_poly /polyseq !Z_to_bits_nth //.
  rewrite Z.shiftl_spec; try lia.  case Hi: (i == 0%N).
  - apply (elimT eqP) in Hi. by subst.
  - apply (elimF eqP) in Hi. f_equal. rewrite Nat2Z.inj_pred; lia.
Qed.

Opaque Z.shiftl.
Opaque p256.


(*TODO: move*)
Lemma Z_to_poly_zero: forall z (Hz: 0 <= z),
  (Z_to_poly Hz = 0) <-> z = 0%Z.
Proof.
  move => z Hz. split.
  - rewrite /Z_to_poly => Hpoly. apply (congr1 polyseq) in Hpoly. move: Hpoly; rewrite /= polyseq0 => Hbits.
    apply Z.bits_inj_0. move => n. by rewrite Z_to_bits_spec // Hbits Znth_nil.
  - move => Hz0. subst. rewrite /Z_to_poly. apply val_inj. rewrite /=. by rewrite /Z_to_bits polyseq0.
Qed.

Lemma byte_mulX_correct: forall b,
  byte_to_qpoly (byte_mulX b) = @GRing.mul qpoly_p256_fieldType (qx p256_geq_2) (byte_to_qpoly b).
Proof.
  move => b. rewrite /byte_mulX. case : (Z_lt_ge_dec (Z.shiftl (Byte.unsigned b) 1) Byte.modulus) => [Hsmall |Hbig];
  rewrite /proj_sumbool.
  - rewrite /byte_to_qpoly /=. apply qpoly_eq'.
    have->:(@GRing.mul qpoly_p256_fieldType (qx p256_geq_2) (Qpoly (byte_to_poly_range b))) =
      qmul p256_irred (qx p256_geq_2) (Qpoly (byte_to_poly_range b)) by [].
    rewrite /qmul /= /byte_to_poly /= (@Z_to_poly_eq _ (Z.shiftl (Byte.unsigned b) 1)).
    + apply Z_shiftl_nonneg'. rep_lia.
    + move => Hb1. rewrite Z_shiftl_poly. apply Byte_unsigned_nonneg. move => Hb0.
      rewrite modp_small. f_equal. by apply Z_to_poly_eq.
      have [{}Hb0 | {}Hb0]: Byte.unsigned b <> 0%Z \/ Byte.unsigned b = 0%Z by lia.
      * rewrite size_mul.
        -- rewrite size_polyX /= Z_to_poly_size; try rep_lia.
          case : (Z.eq_dec (Byte.unsigned b) 0) => [// | {}Hb0 /=]; try lia.
          have {}Hsmall: Z.shiftl (Byte.unsigned b) 1 <= 255 by rep_lia.
          have Hlog: Z.log2 (Z.shiftl (Byte.unsigned b) 1) = (Z.log2 (Byte.unsigned b) + 1)%Z. {
            rewrite Z.log2_shiftl; rep_lia. } apply /ltP.
          apply Z.log2_le_mono in Hsmall. move: Hsmall; rewrite Hlog /= size_p256. lia.
        -- by rewrite polyX_eq0.
        -- apply /eqP. by rewrite Z_to_poly_zero.
      * have->: Z_to_poly (Byte_unsigned_nonneg (b:=b)) = 0%R by rewrite Z_to_poly_zero.
        by rewrite GRing.mulr0 size_poly0 size_p256.
    + rewrite Byte.unsigned_repr //. split; try rep_lia. apply Z_shiftl_nonneg'. rep_lia.
  - apply val_inj. rewrite /= /byte_to_poly /= (@Z_to_poly_eq _  (Z.lxor (Z.shiftl (Byte.unsigned b) 1) p256_val)).
    + rewrite Z.lxor_nonneg. split. rewrite /p256_val. lia. move => Hb. apply Z_shiftl_nonneg'; rep_lia.
    + move => Hxor. have->:Z_to_poly Hxor = (('X * Z_to_poly (Byte_unsigned_nonneg (b:=b)) + (Poly p256))). {
      rewrite xor_poly. apply Z_shiftl_nonneg'; rep_lia. rewrite /p256_val; rep_lia.
      move => Hshl Hp256. rewrite Z_shiftl_poly. rep_lia. move => Hb0.
      f_equal. f_equal. by apply Z_to_poly_eq. rewrite /=. rewrite -p256_val_poly. by apply Z_to_poly_eq. }
      (*Now we just have the polynomial goal (the interesting part)*)
      rewrite -(@modp_small _ ('X * Z_to_poly (Byte_unsigned_nonneg (b:=b)) + Poly p256) (Poly p256)).
      * by rewrite modpD modpp GRing.addr0.
      *

(*TODO: need to prove, if size p = size q (bc we are in bool field), size (p + q) < size p*)
(*better yet, do in terms of log (poly_to_Z) and use result from Verif_field*)
Search poly_to_Z.


 Check size_Mmonic.


 Search size (?x + ?Y)%R. rewrite size_add.
 rewrite add_size. Search (size (?x + ?y)%R).

 Search (?x %% ?x). Search ((?x + ?y) %% ?p).


    + by [].
      (*Now, we just have the polynomial goal*)
      by [].
      



      Search Z.lxor poly.


 lia. rep_lia.


 rep_lia.
    


 rewrite /byte_to_qpoly.


 


rep_lia.
    +

 Search size 0%R.

Z_to_poly_zero


Search Z_to_bits. rewrite /Z_to_poly /=.
        apply /ltP. lia.
 lia.


 rewrite Hlog in Hsmall. 
        Search Z.log2 "mono".


        rewrite Hlog in Hsmall.
        move: Hsmall. Check Z.log2_shiftl.

Z_to_poly_size


    Search 
    

 rewrite /=.


 . 
  have->: (Byte_unsigned_nonneg (b:=Byte.repr (Z.shiftl (Byte.unsigned b) 1))) =
    (@Z_shiftl_nonneg' _ 1 (Byte_unsigned_nonneg (b:= b))).
  Search

(Byte_unsigned_nonneg (b:=Byte.repr (Z.shiftl (Byte.unsigned b) 1)))




  rewrite /=.


 rewrite /=. apply val_inj. Search val. Search qp. rewrite /=.


 simpl. apply val_inj. rewrite /qx. rewrite /=.



 rewrite /qp. /byte_to_poly.

(*TODO: prove that byte_to_qpoly (byte_mulX b) = qx * (byte_to_qpoly b)*)

(*Populate the byte_pows and byte_logs up to index i*)
(*Need generic version for induction*)
Definition populate_pows_logs_aux (l: seq Z) (base : (seq byte) * (seq byte)) : (seq byte) * (seq byte) :=
  fold_left (fun (acc: seq byte * seq byte) z => 
    let (pows, logs) := acc in
    if Z.eq_dec z 0 then (upd_Znth z pows Byte.one, logs) else
    let newVal := (byte_mulX (Znth (z -1) pows)) in
    let newPows := upd_Znth z pows newVal in
    let newLogs := upd_Znth (Byte.unsigned (Znth z newPows)) logs (Byte.repr z) in
    (newPows, newLogs)) l base.

Definition populate_pows_logs_iota_aux (i: Z) base : (seq byte) * (seq byte) :=
  populate_pows_logs_aux (Ziota 0 i) base.

Lemma populate_pows_logs_iota_aux_plus_1: forall i base,
  0 <= i ->
  populate_pows_logs_iota_aux (i + 1) base =
  if Z.eq_dec i 0 then (upd_Znth i (populate_pows_logs_iota_aux i base).1 Byte.one, 
    (populate_pows_logs_iota_aux i base).2) else
  (upd_Znth i (populate_pows_logs_iota_aux i base).1 
    (byte_mulX (Znth (i-1) (populate_pows_logs_iota_aux i base).1)),
   upd_Znth (Byte.unsigned (Znth i (populate_pows_logs_iota_aux (i +1) base).1))
      (populate_pows_logs_iota_aux i base).2 (Byte.repr i)).
Proof.
  move => i base Hi. rewrite /populate_pows_logs_iota_aux Ziota_plus_1; try lia.
  have->:(Ziota 0 i ++ [:: (0 + i)%Z]) = (Ziota 0 i ++ [:: (0 + i)%Z])%list by []. rewrite /=.
  case Hbefore : (populate_pows_logs_aux (Ziota 0 i) base)
  => [pows logs]. move: Hbefore.
  rewrite /populate_pows_logs_aux /= fold_left_app /= => Hbefore. rewrite Hbefore.  
  by case : (Z.eq_dec i 0).
Qed.

Definition populate_pows_logs (i: Z) : (seq byte) * (seq byte) :=
  populate_pows_logs_iota_aux i (zseq Byte.modulus Byte.zero, zseq Byte.modulus Byte.zero).

Lemma populate_pows_logs_0: populate_pows_logs 0 = 
  (zseq Byte.modulus Byte.zero, zseq Byte.modulus Byte.zero).
Proof.
  by rewrite /populate_pows_logs /Ziota /=.
Qed.

Lemma populate_pows_logs_aux_length1: forall l b,
  Zlength (populate_pows_logs_aux l b).1 = Zlength b.1.
Proof.
  move => l. elim : l => [//= | h t /= IH b].
  rewrite IH. case : b => [pows logs] /=.
  by case (Z.eq_dec h 0) => [Hh0 /= | Hh0 /=]; rewrite Zlength_upd_Znth.
Qed.

Lemma populate_pows_logs_length1: forall i,
   Zlength (fst (populate_pows_logs i)) = Byte.modulus.
Proof.
  move => i. rewrite /populate_pows_logs populate_pows_logs_aux_length1 /=.
  apply zseq_Zlength. rep_lia.
Qed.

Lemma populate_pows_logs_plus_1: forall (i: Z),
  0 <= i ->
  populate_pows_logs (i+1) =
  if Z.eq_dec i 0 then (upd_Znth i (populate_pows_logs i).1 Byte.one, (populate_pows_logs i).2) else
  (upd_Znth i (populate_pows_logs i).1 (byte_mulX (Znth (i-1) (populate_pows_logs i).1)),
   upd_Znth (Byte.unsigned (Znth i (populate_pows_logs (i+1)).1))
      (populate_pows_logs i).2 (Byte.repr i)).
Proof.
  move => i Hi. rewrite {1}/populate_pows_logs. by rewrite populate_pows_logs_iota_aux_plus_1.
Qed.

(*Now, we need to prove that this is actually correct*)

(*The "loop invariant"*)
Definition populate_pows_logs_invar (l: seq byte * seq byte) (i: Z) :=
  (forall z, 0 <= z < i -> Znth z l.1 = byte_pow_map (Byte.repr z)) /\
  (forall (b: byte), Byte.unsigned (byte_log_map b) < i -> Znth (Byte.unsigned b) l.2 = byte_log_map b).

Lemma populate_pows_logs_correct_ind: forall (i: Z) base,
  0 <= i <= Byte.modulus ->
  Zlength base.1 = Byte.modulus ->
  populate_pows_logs_invar (populate_pows_logs_iota_aux i base) i.
Proof.
  move => i base Hi. have Hinat: i = Z.of_nat (Z.to_nat i) by lia. move: Hinat Hi ->. move : base.
  elim : (Z.to_nat i) => [//= base Hi | n IH base].
  - rewrite /populate_pows_logs_invar. split.
    + move => z. lia.
    + move => b. rep_lia.
  - have->: Z.of_nat n.+1 = (Z.of_nat n + 1) %Z by lia. move => Hn1 Hlen.
    move: IH; rewrite /populate_pows_logs_invar => IH. split.
    + move => z Hz. rewrite populate_pows_logs_iota_aux_plus_1; try lia.
      case : (Z.eq_dec (Z.of_nat n) 0) => [Hn0 /= | Hn0 /=].
      * have->: z = 0%Z by lia. rewrite Hn0. rewrite /populate_pows_logs_iota_aux /=.
        rewrite upd_Znth_same. have->:Byte.repr 0 = Byte.zero by []. by rewrite byte_pow_map_zero. lia.
      * have [Hbef | Hcurr]: (0 <= z < Z.of_nat n)%Z \/ (z = Z.of_nat n)%Z by lia.
        -- rewrite upd_Znth_diff; try lia. apply IH. rep_lia. lia. by []. 
           rewrite populate_pows_logs_aux_length1. lia. 
           rewrite populate_pows_logs_aux_length1. lia. 
        -- rewrite Hcurr upd_Znth_same; last first. rewrite populate_pows_logs_aux_length1. lia. 
           have Hprev: (Znth (z - 1) (populate_pows_logs_iota_aux (Z.of_nat n) base).1) = byte_pow_map (Byte.repr (z-1)).
           apply IH; lia. rewrite Hcurr in Hprev. rewrite Hprev.


byte_mulX (byte_pow_map (Byte.repr (Z.of_nat n - 1))) = byte_pow_map (Byte.repr (Z.of_nat n))
          




 rewrite Hprev. lia. lia. rewrite Hpref.
           rewrite IH. 


 have [Hn0 | Hn0]: n = 0%N \/ n <> 0%N by lia.
           { subst. rewrite /=.  

 Search (?x + 0)%Z.


 move ->.

 rewrite / 

move => lo len base Hlo Hlen Hlolen. rewrite /populate_pows_logs_invar /populate_pows_logs_aux.


  populate_pows_logs_invar lo lo base ->
  populate_pows_logs_invar 
  
  
  

End Pow.


