(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

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
Require Import ByteFacts.

(*A few generic results*)

Lemma Znth_nil: forall {A: Type} {d: Inhabitant A} (i: Z),
  @Znth A d i [::] = d.
Proof.
  move => A d i. rewrite /Znth. case : (Z_lt_dec i 0) => [//= Hi0 | //= Hi0].
  by case : (Z.to_nat i).
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
  move => z i Hz. rewrite Z_to_bits_spec // /Znth. case : (Z_lt_dec (Z.of_nat i) 0); try lia ; move => Htriv.
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

Lemma Z_to_poly_zero: forall z (Hz: 0 <= z),
  (Z_to_poly Hz = 0) <-> z = 0%Z.
Proof.
  move => z Hz. split.
  - rewrite /Z_to_poly => Hpoly. apply (congr1 polyseq) in Hpoly. move: Hpoly; rewrite /= polyseq0 => Hbits.
    apply Z.bits_inj_0. move => n. by rewrite Z_to_bits_spec // Hbits Znth_nil.
  - move => Hz0. subst. rewrite /Z_to_poly. apply val_inj. rewrite /=. by rewrite /Z_to_bits polyseq0.
Qed.

End ZPoly.

(*TODO: different file?*)
Require Import mathcomp.algebra.finalg.
Require Import mathcomp.algebra.polydiv.

(*We need a different version of discrete log, where log(1) = |F|^(deg p) -1 and not 1*)
Section DlogAlt.

Local Open Scope ring_scope.

Variable F : finFieldType.
Variable p : {poly F}.
Variable p_irred: irreducible_poly p.
Variable p_prim: primitive_poly p.
Variable p_notx: (2 < size p)%N.

Lemma field_size_lt: ((#|F| ^ (@size F p).-1).-1 < #|F| ^ (@size F p).-1)%N.
Proof.
  rewrite ltn_predL expn_gt0. apply /orP. left.
  have gt_01: (0 < 1)%N by [].
  apply (ltn_trans gt_01). by apply finfield.finRing_gt1.
Qed.

Notation QF := (qpoly_fieldType p_irred).

Definition dlog_alt (q: QF) : 'I_(#|F| ^ (@size F p).-1) :=
  if q == 1 then (Ordinal field_size_lt) else (widen_ord (ltnW field_size_lt) (dlog p_irred p_notx q)).

Lemma dlog_alt_nonzero (q: QF):
  q != 0 ->
  nat_of_ord (dlog_alt q) != 0%N.
Proof.
move=> q_neq0. rewrite /dlog_alt.
case q_neq1: (q == 1) =>/=.
- rewrite -lt0n. by apply field_gt0.
- case log_zero: (nat_of_ord (dlog p_irred p_notx q) != 0%N) => //.
  apply negbFE in log_zero. move: log_zero => /eqP log_zero.
  have log_exp := (exp_dlog p_prim p_notx q_neq0).
  move: log_exp. rewrite log_zero GRing.expr0 => q_eq1.
  move: q_neq1. by rewrite -q_eq1 eq_refl.
Qed.

Lemma dlog_alt_correct (q: QF) : 
  q != 0 ->
  (qx p_notx) ^+ (dlog_alt q) = q.
Proof.
move=> q_neq0. rewrite /dlog_alt.
case: (q == 1) /eqP => /= q1; last by apply exp_dlog.
rewrite q1. by apply qx_field_sz1.
Qed.

Lemma dlog_alt_zero: nat_of_ord (dlog_alt 0) = 0%N.
Proof.
rewrite /dlog_alt.
have->:0 == 1 = false. move => R. apply /eqP => eq_10.
have: (@GRing.one R) != 0 by apply (GRing.oner_neq0). by rewrite eq_10 eq_refl.
by apply dlog0.
Qed.

Lemma dlog_alt_eq0 (q: QF):
  (nat_of_ord (dlog_alt q) == 0%N) = (q == 0%R).
Proof.
case q_eq0: (q == 0).
  by move: q_eq0 => /eqP ->; rewrite dlog_alt_zero eq_refl.
apply negbT in q_eq0.
case: (nat_of_ord (dlog_alt q) == 0%N) /eqP => // log_zero.
apply dlog_alt_correct in q_eq0.
move: q_eq0. rewrite log_zero GRing.expr0 => q_eq1.
move: log_zero. rewrite -q_eq1/dlog_alt eq_refl/= => field0.
have: (0 < 0)%N. rewrite -{2}field0. by apply field_gt0.
by rewrite ltnn.
Qed.

Lemma dlog_map_zero (q: qpolyNZ p_irred):
  nat_of_ord (dlog_map p_notx q) = 0%N ->
  qq q = (@GRing.one QF).
Proof.
move=> log_eq.
have: dlog_map p_notx q = Ordinal (field_gt0 p_irred p_notx) by apply val_inj.
have unit1: qunit p_irred (@GRing.one QF).
  by rewrite /qunit; apply GRing.oner_neq0.
have<-: dlog_map p_notx (Qnz unit1) = Ordinal (field_gt0 p_irred p_notx).
  have->:(Qnz unit1) = qpow_map p_irred p_notx (Ordinal (field_gt0 p_irred p_notx)).
    rewrite /qpow_map/=. apply val_inj=>/=. by rewrite GRing.expr0.
  by rewrite qpow_map_can.
move: log_eq => _ log_eq. apply (@dlog_map_inj _ _ p_irred p_prim p_notx) in log_eq.
by rewrite log_eq.
Qed.

Lemma dlog_alt_inj: injective dlog_alt.
Proof.
move=> q1 q2. rewrite /dlog_alt. 
case: (q1 == 1) /eqP => q1_eq1; case: (q2 == 1) /eqP => q2_eq1 //.
- by rewrite q1_eq1 q2_eq1.
- move => eq_ord. apply (f_equal val) in eq_ord. move: eq_ord => /=eq_dlog.
  have: (nat_of_ord (dlog p_irred p_notx q2) <  (#|F| ^ (size p).-1).-1)%N by [].
  by rewrite -eq_dlog ltnn.
- move => eq_ord. apply (f_equal val) in eq_ord. move: eq_ord => /=eq_dlog.
  have: (nat_of_ord (dlog p_irred p_notx q1) <  (#|F| ^ (size p).-1).-1)%N by [].
  by rewrite eq_dlog ltnn.
- move => [].
  (*need to break abstraction here*)
  rewrite /dlog. move: erefl erefl.
  case: {2 3} (qunit p_irred q2); case: {2 3} (qunit p_irred q1).
  + move=> q2_unit q1_unit log_eq.
    have: Qnz q1_unit = Qnz q2_unit by apply (@dlog_map_inj _ _ p_irred p_prim p_notx), ord_inj, log_eq.
    by move => [].
  + move=> q2_unit q1_nunit/=. have /eqP->: q1 == 0 by apply negbFE.
    move=> log0. symmetry in log0. by apply dlog_map_zero in log0.
  + move=>q2_nunit q1_unit/=. have /eqP->:q2 == 0 by apply negbFE.
    move=> log0. by apply dlog_map_zero in log0.
  + move=>q2_nunit q1_nunit _. have /eqP->: q1 == 0 by apply negbFE.
    by have /eqP->:q2 == 0 by apply negbFE.
Qed.

(*We also define the corresponding power map*)
Definition qpow_map_alt (i: 'I_(#|F|^((size p).-1))) : QF := 
  if (nat_of_ord i == 0%N) then (@GRing.zero QF) else (qx p_notx) ^+ i.

Definition qpow_map_full (i: 'I_(#|F|^((size p).-1))): QF := (qx p_notx) ^+ i.

Lemma qpow_map_full_equiv i:
  nat_of_ord i != 0%N ->
  qpow_map_full i = qpow_map_alt i.
Proof.
rewrite /qpow_map_alt /qpow_map_full. by case : (nat_of_ord i == 0%N).
Qed.

Lemma dlog_map_val (q1 q2: qpolyNZ p_irred):
  val q1 = val q2 ->
  dlog_map p_notx q1 = dlog_map p_notx q2.
Proof.
move=>val_eq. by rewrite /dlog_map; rewrite !val_eq.
Qed.

Lemma qpow_map_full_inv i:
  nat_of_ord i != 0%N ->
  dlog_alt (qpow_map_full i) = i.
Proof.
move=>i_neq0. rewrite qpow_map_full_equiv//.
rewrite /qpow_map_alt /dlog_alt.
rewrite (negbTE i_neq0).
case: (i == Ordinal field_size_lt) /eqP => i_big.
  by rewrite i_big/= qx_field_sz1 // eq_refl.
(*Now we have an ordinal in the correct range*)
have i_small: (nat_of_ord i < (#|F| ^ (size p).-1).-1)%N.
  rewrite ltn_neqAle. apply /andP; split.
    apply /eqP => i_eq. apply i_big. by apply ord_inj.
  rewrite leq_predR // -qpoly_size. apply /card_gt0P.
  by exists (qx p_notx).
case x_ieq1: (qx p_notx ^+ i == 1); last first.
  apply ord_inj=>/=.
  rewrite /dlog. move: erefl.
  case: {2 3} (qunit p_irred (qx p_notx ^+ i)); last
    by have->: qunit p_irred (@GRing.exp QF (qx p_notx) i) by apply qpow_unit.
  move=> pow_unit.
  have->:Qnz pow_unit = (@qpow_map _ _ p_irred p_notx (Ordinal i_small)) by apply val_inj.
  by rewrite qpow_map_can.
have pow_unit: qunit p_irred (@GRing.exp QF (qx p_notx) i) by apply qpow_unit.
have log_i: dlog_map p_notx (Qnz pow_unit) = (Ordinal i_small).
  have->:Qnz pow_unit = (@qpow_map _ _ p_irred p_notx (Ordinal i_small)) by apply val_inj.
  by rewrite qpow_map_can.
have unit1: qunit p_irred (@GRing.one QF) by rewrite /qunit GRing.oner_neq0.
have val_eq: val (Qnz pow_unit) = val (Qnz unit1)
  by rewrite /=; apply /eqP.
have log_0: dlog_map p_notx (Qnz pow_unit) = (Ordinal (field_gt0 p_irred p_notx)).
  rewrite (dlog_map_val val_eq)/=.
  have pows_eq: qpow_map p_irred p_notx (dlog_map p_notx (Qnz unit1)) = 
    qpow_map p_irred p_notx (Ordinal (field_gt0 p_irred p_notx)).
    rewrite dlog_map_can //. apply val_inj=>/=. by rewrite GRing.expr0.
  by apply (bij_inj (qpow_map_bij p_irred p_prim p_notx)) in pows_eq.
move: log_i. rewrite log_0 => i_eq0.
apply (f_equal (@nat_of_ord _)) in i_eq0; move: i_eq0=>/= i_eq0.
move: i_neq0. by rewrite -i_eq0 eq_refl.
Qed.

Lemma qpow_map_full_neq0 i:
  qpow_map_full i != 0.
Proof.
rewrite /qpow_map_full. rewrite GRing.expf_neq0 //. apply qx_neq0.
Qed.

End DlogAlt.

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

Lemma qpoly_to_Z_0: forall q,
  qpoly_to_Z q = 0 <-> q = (GRing.zero qpoly_p256_fieldType).
Proof.
  move => [[p Hlast] Hsz]. rewrite /qpoly_to_Z /poly_to_Z. split.
  - move => /= Hb. apply val_inj. apply val_inj. rewrite /=. rewrite polyseq0. 
    by apply (bits_to_Z_zero Hlast).
  - move ->. by rewrite polyseq0.
Qed.

Definition qpoly_to_byte (q: qpoly_p256) : byte :=
  Byte.mkint _ (qpoly_to_Z_bound q).

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

Section Pow.

Local Open Scope ring_scope.

(*Now we need to define the power and logarithm maps and tables*)
Lemma ord_byte_bound: forall (x: 'I_#|byte_finType|), -1 < Z.of_nat x < Byte.modulus.
Proof.
  move => [n Hn] /=. rewrite card_byte in Hn. move: Hn => /ltP Hn. rep_lia.
Qed.

Definition ord_to_byte (x: 'I_#|byte_finType|) := Byte.mkint _ (ord_byte_bound x).

Lemma ord_to_byte_zero: forall x,
  nat_of_ord x = 0%N ->
  ord_to_byte x = Byte.zero.
Proof.
  move => x Hx. apply byte_unsigned_inj. by rewrite /= Hx Byte.unsigned_zero.
Qed.

Lemma byte_ord_bound: forall (b: byte), (Z.to_nat (Byte.unsigned b) < #|byte_finType|)%N.
Proof.
  move => b. rewrite card_byte. pose proof (Byte.unsigned_range b) as Hrange. apply /ltP. rep_lia.
Qed.

Definition byte_to_ord (b: byte) : 'I_#|byte_finType| := Ordinal (byte_ord_bound b).

(*Now, we can define the power and inverse power (log) maps*)

Lemma p256_geq_2: (2 < size (Poly p256))%N.
Proof.
  by rewrite size_p256.
Qed.

Lemma byte_qpoly_size: #|byte_finType| = (#|finalg.FinRing.Field.eqType bool_finFieldType| ^ (size (Poly p256)).-1)%N.
Proof.
  by rewrite card_bool size_p256 card_byte.
Qed.

(*We don't want to use Byte.modulus directly because it will simplify*)

Definition byte_pow_map (b: byte) : byte :=
  qpoly_to_byte (qpow_map_full p256_irred p256_geq_2 (eq_ord byte_qpoly_size (byte_to_ord b))).

Definition byte_log_map (b: byte) : byte :=
  ord_to_byte (eq_ord (esym byte_qpoly_size) (dlog_alt p256_geq_2 (byte_to_qpoly b))).

Definition byte_pows : seq byte :=
  mkseqByte byte_pow_map fec_n.

Definition byte_logs : seq byte :=
  mkseqByte byte_log_map fec_n.

Definition byte_invs: seq byte :=
  mkseqByte byte_inv fec_n.

(*So we don't need to unfold the definitions ever*)
Lemma byte_pows_Zlength: Zlength byte_pows = Byte.modulus.
Proof.
  by rewrite /byte_pows mkseqByte_Zlength; rep_lia.
Qed.

Lemma byte_pows_Znth: forall i,
  0 <= i < Byte.modulus ->
  Znth i byte_pows = byte_pow_map (Byte.repr i).
Proof.
  move => i Hi. by apply mkseqByte_Znth_Z; rep_lia.
Qed.

Lemma byte_logs_Zlength: Zlength byte_logs = Byte.modulus.
Proof.
  by rewrite /byte_logs mkseqByte_Zlength; rep_lia.
Qed.

Lemma byte_logs_Znth: forall i,
  0 <= i < Byte.modulus ->
  Znth i byte_logs = byte_log_map (Byte.repr i).
Proof.
  move => i Hi. by apply mkseqByte_Znth_Z; rep_lia.
Qed.

Lemma byte_invs_Zlength: Zlength byte_invs = Byte.modulus.
Proof.
  by rewrite /byte_invs mkseqByte_Zlength; rep_lia.
Qed.

Lemma byte_invs_Znth: forall i,
  0 <= i < Byte.modulus ->
  Znth i byte_invs = byte_inv (Byte.repr i).
Proof.
  move => i Hi. by apply mkseqByte_Znth_Z; rep_lia.
Qed.

(* Clear definitions of each map for paper *)

(* The power map *)

(*The element "x"*)
Definition bx := qpoly_to_byte (qx p256_geq_2).

Lemma byte_exp_unfold: forall (q: qpoly_p256) n,
  qpoly_to_byte (@GRing.exp qpoly_p256_fieldType q n) = (qpoly_to_byte q) ^+ n.
Proof.
  move => q n. elim : n => [//= | n' /= IH].
  - rewrite !GRing.expr0. apply byte_to_qpoly_inj. by rewrite byte_one_qpoly qpoly_byte_cancel.
  - rewrite !GRing.exprS -IH. apply byte_to_qpoly_inj. rewrite qpoly_byte_cancel.
    have->: (@GRing.mul byte_fieldType (qpoly_to_byte q) (qpoly_to_byte (@GRing.exp qpoly_p256_fieldType q n'))) = 
      byte_mul (qpoly_to_byte q) (qpoly_to_byte (@GRing.exp qpoly_p256_fieldType q n')) by [].
    by rewrite /byte_mul !qpoly_byte_cancel.
Qed.

(* Describes clearly what byte_pows is*)
Lemma byte_pows_elts: forall i,
  0 <= i < Byte.modulus ->
  Znth i byte_pows = bx ^+ (Z.to_nat i).
Proof.
  move => i Hi. rewrite byte_pows_Znth // /byte_pow_map /bx /qpow_map_full/= Byte.unsigned_repr.
  2: rep_lia. apply byte_exp_unfold.
Qed.

(*Describes clearly what byte_logs is*)
Lemma byte_logs_elts: forall i,
  0 < i < Byte.modulus ->
  bx ^+ Z.to_nat (Byte.unsigned (Znth i byte_logs)) = Byte.repr i.
Proof.
  move => i Hi. rewrite byte_logs_Znth // /byte_log_map; try lia. rewrite /bx/= Nat2Z.id -byte_exp_unfold dlog_alt_correct.
  - apply byte_qpoly_cancel.
  - rewrite polyseqK. apply p256_primitive.
  - apply negbT. rewrite byte_zero_qpoly_iff. apply /eqP. move => Hiz. apply (congr1 Byte.unsigned) in Hiz.
    move: Hiz. rewrite Byte.unsigned_zero Byte.unsigned_repr; rep_lia.
Qed.

Lemma byte_invs_elts: forall i,
  0 <= i < Byte.modulus ->
  Znth i byte_invs = (Byte.repr i)^-1.
Proof.
  move => i Hi. by rewrite byte_invs_Znth.
Qed.

(*Lemmas about these maps*)
Lemma byte_pow_map_zero: byte_pow_map Byte.zero = Byte.one.
Proof.
  rewrite /byte_pow_map /byte_to_ord /qpow_map_full /=.
  have->:Z.to_nat (Byte.unsigned Byte.zero) = 0%N by []. rewrite GRing.expr0.
  apply byte_to_qpoly_inj. by rewrite byte_one_qpoly qpoly_byte_cancel.
Qed.

(*We will model the functions that populate the lookup tables here, so the VST proof does not need to
  directly reason about any field properties*)

Lemma modulus_nonneg: 0 <= modulus.
Proof.
  rep_lia.
Qed.

Lemma modulus_val_poly: Z_to_poly modulus_nonneg = Poly p256.
Proof.
  apply val_inj. by rewrite polyseqK /= modulus_eq.
Qed. 

(*Multiply a byte by x, directly*)
Definition byte_mulX (b: byte) :=
  let temp := Z.shiftl (Byte.unsigned b) 1 in
  if (Z_lt_ge_dec temp Byte.modulus) then Byte.repr temp else
  Byte.repr (Z.lxor temp modulus).

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

(*We need the crucial step from above (which is also used in the VST proof - when we xor
  the current value with 285, the result fits in a byte*)
Lemma byte_mulX_correct: forall b,
  byte_to_qpoly (byte_mulX b) = @GRing.mul qpoly_p256_fieldType (qx p256_geq_2) (byte_to_qpoly b).
Proof.
  move => b. rewrite /byte_mulX. case : (Z_lt_ge_dec (Z.shiftl (Byte.unsigned b) 1) Byte.modulus) => [Hsmall |Hbig];
  rewrite /proj_sumbool.
  - rewrite /byte_to_qpoly /=. apply qpoly_inj.
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
  - apply val_inj.
    have [Hlo Hhi]: 0 <= Z.lxor (Z.shiftl (Byte.unsigned b) 1) modulus <= Byte.max_unsigned. {
      move: Hbig. rewrite Zbits.Zshiftl_mul_two_p; try lia. have->: two_p 1 = 2%Z by [].
      rewrite Z.mul_comm => Hbig. pose proof (xor_modulus_bound Hbig). rep_lia. }
    have Hbyte: Byte.unsigned (Byte.repr (Z.lxor (Z.shiftl (Byte.unsigned b) 1) modulus)) =
      Z.lxor (Z.shiftl (Byte.unsigned b) 1) modulus by rewrite Byte.unsigned_repr.
    have Hlopoly: Z_to_poly Hlo = (('X * Z_to_poly (Byte_unsigned_nonneg (b:=b)) + (Poly p256))). {
      rewrite xor_poly. apply Z_shiftl_nonneg'; rep_lia. rep_lia.
      move => Hshl Hp256. rewrite Z_shiftl_poly. rep_lia. move => Hb0.
      f_equal. f_equal. by apply Z_to_poly_eq. rewrite -modulus_val_poly. by apply Z_to_poly_eq. }
    rewrite /= /byte_to_poly /= (@Z_to_poly_eq _  (Z.lxor (Z.shiftl (Byte.unsigned b) 1) modulus)).
    + rewrite Hlopoly -(@modp_small _ ('X * Z_to_poly (Byte_unsigned_nonneg (b:=b)) + Poly p256) (Poly p256)).
      * by rewrite modpD modpp GRing.addr0.
      * rewrite -Hlopoly Z_to_poly_size size_p256.
        case : (Z.eq_dec (Z.lxor (Z.shiftl (Byte.unsigned b) 1) modulus) 0) => [// | /= Hx0].
        apply /ltP. apply Z.log2_le_mono in Hhi. rewrite /= in Hhi. rep_lia.
    + by rewrite Byte.unsigned_repr.
Qed.

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

Lemma populate_pows_logs_aux_length2: forall l b,
  Zlength (populate_pows_logs_aux l b).2 = Zlength b.2.
Proof.
  move => l. elim : l => [//= | h t /= IH b].
  rewrite IH. case : b => [pows logs] /=.
  by case (Z.eq_dec h 0) => [Hh0 //= | Hh0 /=]; rewrite Zlength_upd_Znth.
Qed.

Lemma populate_pows_logs_length2: forall i,
   Zlength (snd (populate_pows_logs i)) = Byte.modulus.
Proof.
  move => i. rewrite /populate_pows_logs populate_pows_logs_aux_length2 /=.
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

(*Why do we need these? Why doesn't lia work directly?*)
Lemma nat_leq_1: forall n,
  Z.of_nat n < 1 ->
  n = 0%N.
Proof.
  move => n Hn. lia.
Qed.

Lemma z_leq_n_1: forall z n,
  z < n + 1 ->
  z < n \/ z = n.
Proof.
  lia.
Qed.

Lemma p256_primitive': primitive_poly (Poly p256).
Proof.
  rewrite polyseqK. apply p256_primitive.
Qed.

(*Now, we need to prove that this is actually correct*)

(*The "loop invariant". The first part is not hard, since we fill up each power in order.
  But we fill in the logs in an unknown order, so we need to make a claim about all powers
  whose log is below the current loop value, then later prove that we fill the list in correctly
  because each individual element is filled in correctly*)
Definition populate_pows_logs_invar (l: seq byte * seq byte) (i: Z) :=
  (forall z, 0 <= z < i -> Znth z l.1 = byte_pow_map (Byte.repr z)) /\ Znth 0 l.2 = Byte.zero /\
  (forall (b: byte), Byte.unsigned (byte_log_map b) < i -> Znth (Byte.unsigned b) l.2 = byte_log_map b).

Lemma populate_pows_logs_correct_ind: forall (i: Z) base,
  0 <= i <= Byte.modulus ->
  Zlength base.1 = Byte.modulus ->
  Zlength base.2 = Byte.modulus ->
  Znth 0 base.2 = Byte.zero ->
  populate_pows_logs_invar (populate_pows_logs_iota_aux i base) i.
Proof.
  move => i base Hi. have Hinat: i = Z.of_nat (Z.to_nat i) by lia. move: Hinat Hi ->. move : base.
  elim : (Z.to_nat i) => [//= base Hi | n IH base].
  - rewrite /populate_pows_logs_invar. repeat split.
    + move => z. lia.
    + by rewrite /populate_pows_logs_iota_aux. 
    + move => b. rep_lia.
  - have->: Z.of_nat n.+1 = (Z.of_nat n + 1) %Z by lia. move => Hn1 Hlen1 Hlen2 Hbase2.
    move: IH; rewrite /populate_pows_logs_invar => IH.
    (*We need the first one in the second one*)
    have Hinv1: (forall z : Z,
      0 <= z < Z.of_nat n + 1 ->
      Znth z (populate_pows_logs_iota_aux (Z.of_nat n + 1) base).1 = byte_pow_map (Byte.repr z)). {
      move => z Hz. rewrite populate_pows_logs_iota_aux_plus_1; try lia.
      case : (Z.eq_dec (Z.of_nat n) 0) => [Hn0 /= | Hn0 /=].
      * have->: z = 0%Z by lia. rewrite Hn0. rewrite /populate_pows_logs_iota_aux /=.
        rewrite upd_Znth_same. have->:Byte.repr 0 = Byte.zero by []. by rewrite byte_pow_map_zero. lia.
      * have [Hbef | Hcurr]: (0 <= z < Z.of_nat n)%Z \/ (z = Z.of_nat n)%Z by lia.
        -- rewrite upd_Znth_diff; try lia. apply IH; try rep_lia. by [].  
           rewrite populate_pows_logs_aux_length1. lia. 
           rewrite populate_pows_logs_aux_length1. lia. 
        -- rewrite Hcurr upd_Znth_same; last first. rewrite populate_pows_logs_aux_length1. lia. 
           have Hprev: (Znth (z - 1) (populate_pows_logs_iota_aux (Z.of_nat n) base).1) = byte_pow_map (Byte.repr (z-1)).
           apply IH; try lia. by []. rewrite Hcurr in Hprev. rewrite Hprev. apply byte_to_qpoly_inj.
           rewrite byte_mulX_correct. rewrite /byte_pow_map !qpoly_byte_cancel /qpow_map_full.
           rewrite -{1}(GRing.expr1 (qx p256_geq_2)) -GRing.exprD. f_equal. rewrite /=.
           rewrite !Byte.unsigned_repr; try rep_lia. 
           have->:(1 + Z.to_nat (Z.of_nat n - 1))%N = (1 + Z.to_nat (Z.of_nat n - 1))%coq_nat by []. lia. }
    split => [//| ].  rewrite populate_pows_logs_iota_aux_plus_1; try lia.
    case : (Z.eq_dec (Z.of_nat n) 0) => [Hn0 /= | Hn0 /=].
    * rewrite Hn0 /populate_pows_logs_iota_aux /= /byte_log_map. split => [//|b Hb]. 
      move: Hb => Hpow. apply nat_leq_1 in Hpow.
      rewrite ord_to_byte_zero //.
      apply (introT eqP) in Hpow. move: Hpow. rewrite dlog_alt_eq0; last first. apply p256_primitive'.
      rewrite byte_zero_qpoly_iff => /eqP Hb0. 
      by rewrite Hb0 Byte.unsigned_zero.
    * split. 
      { rewrite upd_Znth_diff //. apply IH; try rep_lia. by [].
        rewrite populate_pows_logs_aux_length2; lia.
        rewrite populate_pows_logs_aux_length2; rep_lia.
        rewrite Hinv1; try lia. rewrite /byte_pow_map /= => Hzero. apply esym in Hzero; move: Hzero.
        rewrite qpoly_to_Z_0 => Hpow.
        have: (GRing.zero qpoly_p256_fieldType) != 0. rewrite -{1}Hpow. apply qpow_map_full_neq0. by rewrite eq_refl.
      }
      { move => b Hb. rewrite Hinv1; try lia. apply z_leq_n_1 in Hb. case : Hb => [Hbef | Hcurr].
        { rewrite upd_Znth_diff. apply IH; try by []. rep_lia.
          rewrite populate_pows_logs_aux_length2; rep_lia.
          rewrite populate_pows_logs_aux_length2; rep_lia.
          move: Hbef. rewrite -Nat2Z.inj_lt /byte_pow_map => Hpow Hbpow. 
          apply byte_unsigned_inj in Hbpow. apply (congr1 byte_to_qpoly) in Hbpow. 
          apply (congr1 (@dlog_alt _ _ p256_irred p256_geq_2)) in Hbpow.  move: Hbpow.
          rewrite qpoly_byte_cancel qpow_map_full_inv //.
          { move => Hbpow. rewrite Hbpow in Hpow. move: Hpow.
            rewrite /= Byte.unsigned_repr; rep_lia. }
          { by apply p256_primitive'. }
          { rewrite /=. apply /eqP. rewrite Byte.unsigned_repr; rep_lia. }
        }
        { have Hbpow: (byte_pow_map (Byte.repr (Z.of_nat n))) = b. {
            apply Nat2Z.inj in Hcurr. rewrite /byte_pow_map. apply byte_to_qpoly_inj.
            rewrite qpoly_byte_cancel. apply (@dlog_alt_inj _ _ (p256_irred) (p256_primitive') p256_geq_2).
            rewrite qpow_map_full_inv //=. apply ord_inj. rewrite Hcurr /=. by rewrite Byte.unsigned_repr; rep_lia.
            apply p256_primitive'. apply /eqP. by rewrite Byte.unsigned_repr; rep_lia. }
          rewrite Hbpow upd_Znth_same; last first.
          rewrite populate_pows_logs_aux_length2; rep_lia. move: Hbpow.
          rewrite /byte_log_map /byte_pow_map. move <-. rewrite qpoly_byte_cancel qpow_map_full_inv /=.
          { apply byte_unsigned_inj. rewrite /=. rep_lia. }
          { apply p256_primitive'. }
          { apply /eqP. by rewrite Byte.unsigned_repr; rep_lia. }
      }
    }
Qed.

(*Now, we can prove the full correctness*)
Lemma populate_pows_logs_correct:
  populate_pows_logs Byte.modulus = (byte_pows, byte_logs).
Proof.
  rewrite /populate_pows_logs. remember (zseq Byte.modulus Byte.zero, zseq Byte.modulus Byte.zero) as base.
  have Hmod: 0 <= Byte.modulus <= Byte.modulus by rep_lia.
  have Hb1: Zlength base.1 = Byte.modulus by rewrite Heqbase /= zseq_Zlength //.
  have Hb2: Zlength base.2 = Byte.modulus by rewrite Heqbase /= zseq_Zlength //.
  have Hb0: Znth 0 base.2 = Byte.zero. rewrite Heqbase /= zseq_Znth //.
  pose proof (populate_pows_logs_correct_ind Hmod Hb1 Hb2 Hb0) as Hinvar. move: Hinvar.
  case Hpop : (populate_pows_logs_iota_aux Byte.modulus base) => [pows logs].
  have Hsz1: Zlength pows = Byte.modulus. { 
    have->: pows = (populate_pows_logs_iota_aux Byte.modulus base).1 by rewrite Hpop.
    by rewrite populate_pows_logs_aux_length1. }
  have Hsz2: Zlength logs = Byte.modulus. {
    have->: logs = (populate_pows_logs_iota_aux Byte.modulus base).2 by rewrite Hpop.
    by rewrite populate_pows_logs_aux_length2. }
  rewrite /populate_pows_logs_invar //= => [[Hfst [Hzero Hsnd]]].
  have->: pows = byte_pows. { apply Znth_eq_ext.
  - rewrite /byte_pows mkseqByte_Zlength //. rep_lia. rep_lia.
  - move => i. rewrite Hsz1 => Hi. rewrite Hfst // /byte_pows mkseqByte_Znth_Z. by []. rep_lia. }
  have->: logs = byte_logs. { apply Znth_eq_ext.
  - rewrite /byte_pows mkseqByte_Zlength; rep_lia.
  - move => i. rewrite Hsz2 => Hi. 
    have Hibyte: i = Byte.unsigned (Byte.repr i) by rewrite Byte.unsigned_repr; rep_lia.
    rewrite {1}Hibyte. rewrite Hsnd.
    * rewrite /byte_logs mkseqByte_Znth_Z. by []. rep_lia.
    * have->: Byte.modulus = Z.of_nat (256%N) by []. apply inj_lt.
      apply /ltP. case : (dlog_alt p256_geq_2 (byte_to_qpoly (Byte.repr i))) => [m Hm].
      rewrite /=. move: Hm. by rewrite card_bool size_p256.
  }
  by [].
Qed.

(*Similarly, we will have a functional version of the VST code for generating the inverse table*)

Definition populate_invs_aux i base :=
  fold_left (fun acc z => 
    let inv := byte_pow_map (Byte.repr (fec_n - 1 - Byte.unsigned (byte_log_map (Byte.repr z)))) in
    upd_Znth (Byte.unsigned inv) acc (Byte.repr z)) (Ziota 0 i) base.

Definition populate_invs i :=
  populate_invs_aux i (zseq Byte.modulus Byte.zero).

Lemma populate_invs_0: populate_invs 0 = zseq Byte.modulus Byte.zero.
Proof.
  by rewrite /populate_invs.
Qed.

Lemma populate_invs_aux_plus_1: forall i base,
  0 <= i ->
  populate_invs_aux (i+1) base =
  upd_Znth (Byte.unsigned (byte_pow_map (Byte.repr (fec_n - 1 - Byte.unsigned (byte_log_map (Byte.repr i))))))
    (populate_invs_aux i base) (Byte.repr i).
Proof.
  move => i base Hi. rewrite /populate_invs_aux Ziota_plus_1; try lia.
  have->: (Ziota 0 i ++ [:: (0 + i)%Z]) = (Ziota 0 i ++ [:: (0 + i)%Z])%list by []. by rewrite fold_left_app.
Qed.

Lemma populate_invs_plus_1: forall i,
    0 <= i ->
  populate_invs (i+1) =
  upd_Znth (Byte.unsigned (byte_pow_map (Byte.repr (fec_n - 1 - Byte.unsigned (byte_log_map (Byte.repr i))))))
    (populate_invs i) (Byte.repr i).
Proof.
  move => i Hi. by apply populate_invs_aux_plus_1.
Qed.


Lemma populate_invs_aux_length: forall i base,
  Zlength (populate_invs_aux i base) = Zlength base.
Proof.
  move => i. rewrite /populate_invs_aux. elim : (Ziota 0 i) => [base //= | h t /= IH base].
  by rewrite IH Zlength_upd_Znth.
Qed.

Lemma populate_invs_length: forall i,
  Zlength (populate_invs i) = Byte.modulus.
Proof.
  move => i. by rewrite populate_invs_aux_length zseq_Zlength.
Qed.

(*Part of definition of primitive poly*)
Lemma prim_fieldsize: qx p256_geq_2 ^+ 255 = (GRing.one qpoly_p256_fieldType).
Proof.
rewrite-(qx_field_sz1 p256_irred p256_primitive' p256_geq_2). f_equal.
by rewrite size_p256 card_bool.
Qed.
  
(*Inverse calculation is correct (the key part of the inverse proof)*)
Lemma inv_calc: forall b,
    b <> Byte.zero ->
   byte_pow_map (Byte.repr (fec_n - 1 - Byte.unsigned (byte_log_map b))) = byte_inv b.
Proof.
  move => b Hb. rewrite /byte_pow_map /byte_log_map /byte_inv /= /qpow_map_full /=.
  have /ltP Hbound: (nat_of_ord (dlog_alt p256_geq_2 (byte_to_qpoly b)) < 256)%N. {
    case : (dlog_alt p256_geq_2 (byte_to_qpoly b)) => [m Hm /=].
    move : Hm. by rewrite card_bool size_p256. } 
  rewrite Byte.unsigned_repr; last first.
  - remember (nat_of_ord (dlog_alt p256_geq_2 (byte_to_qpoly b))) as x. rewrite -Heqx. rep_lia.
  - f_equal. symmetry. apply (@GRing.mulr1_eq qpoly_p256_fieldType). remember (byte_to_qpoly b) as q.
    have Hq0: q != (GRing.zero qpoly_p256_fieldType). rewrite Heqq byte_zero_qpoly_iff.
    by apply /eqP. apply (dlog_alt_correct p256_primitive' p256_geq_2) in Hq0.
    rewrite -{1}Hq0 -GRing.exprD.
    have->: (dlog_alt p256_geq_2 q +
      Z.to_nat (fec_n - 1 - Z.of_nat (dlog_alt p256_geq_2 q)))%N = 255%N.
    { rewrite Z2Nat.inj_sub; try rep_lia. rewrite Nat2Z.id /=.
      remember (nat_of_ord (dlog_alt p256_geq_2 q)) as x. rewrite -Heqx. 
      have->: (x + (Z.to_nat (fec_n - 1) - x)%coq_nat)%N = (x + (Z.to_nat (fec_n - 1) - x)%coq_nat)%coq_nat by [].
      rep_lia. }
    { apply prim_fieldsize. }
Qed.

Lemma inv_calc_zero: 
  byte_pow_map (Byte.repr (fec_n - 1 - Byte.unsigned (byte_log_map Byte.zero))) = Byte.one.
Proof.
  rewrite /byte_log_map /= byte_zero_qpoly /=. 
  have->:nat_of_ord (@dlog_alt _ _ p256_irred p256_geq_2 (q0 p256_irred)) = 0%N. apply /eqP.
    by rewrite dlog_alt_zero.
  rewrite /= Z.sub_0_r /byte_pow_map. apply byte_to_qpoly_inj. 
  rewrite qpoly_byte_cancel byte_one_qpoly /qpow_map_full /=.
  rewrite Byte.unsigned_repr; try rep_lia. have->:Z.to_nat (fec_n - 1) = 255%N by rep_lia.
  apply prim_fieldsize.
Qed.

Lemma inv_calc_nonzero: forall b,
  byte_pow_map (Byte.repr (fec_n - 1 - Byte.unsigned (byte_log_map b))) <> Byte.zero.
Proof.
  move => b. case : (Byte.eq_dec b Byte.zero) => [Hb0 | Hb0].
  - by rewrite Hb0 inv_calc_zero.
  - rewrite inv_calc //. apply /eqP. apply GRing.invr_neq0. by apply /eqP.
Qed. 

(*The proof of correctness for [populate_invs] is similar to the log part of the above, but a bit simpler*)
Lemma populate_invs_aux_invar : forall i base,
  0 <= i <= Byte.modulus ->
  Zlength base = Byte.modulus ->
  Znth 0 base = Byte.zero ->
  (Znth 0 (populate_invs_aux i base) = Byte.zero /\ forall (b: byte), Byte.unsigned (byte_inv b) < i ->
    Znth (Byte.unsigned b) (populate_invs_aux i base) = byte_inv b).
Proof.
  move => i base Hi. have Hinat: i = Z.of_nat (Z.to_nat i) by lia. move: Hinat Hi ->. move : base.
  elim : (Z.to_nat i) => [//= base Hi Hlen Hb0 | n IH base].
  - rewrite /populate_invs_aux /=. split =>[//|b].
    have->: (@GRing.inv (qpoly_fieldType p256_irred)) (byte_to_qpoly b) = @qinv _ _ p256_irred (byte_to_qpoly b) by [].
    pose proof (@qpoly_to_Z_bound) (qinv p256_irred (byte_to_qpoly b)). lia.
  - have->: Z.of_nat n.+1 = (Z.of_nat n + 1) %Z by lia. move => Hn1 Hlen Hb0.
    rewrite populate_invs_aux_plus_1; try lia.
    (*Need first one separately*)
    have Hfst: Znth 0  (upd_Znth
     (Byte.unsigned
        (byte_pow_map (Byte.repr (fec_n - 1 - Byte.unsigned (byte_log_map (Byte.repr (Z.of_nat n)))))))
     (populate_invs_aux (Z.of_nat n) base) (Byte.repr (Z.of_nat n))) = Byte.zero. {
      rewrite upd_Znth_diff //. apply IH. lia. by []. by []. rewrite populate_invs_aux_length. lia.
      rewrite populate_invs_aux_length; rep_lia. move => Hzero. apply esym in Hzero. 
      apply byte_unsigned_zero in Hzero. apply (inv_calc_nonzero Hzero). }
    split => [//| b Hb]. 
    case : (Byte.eq_dec b Byte.zero) => [Hby0 | Hby0].
    + by rewrite Hby0 Byte.unsigned_zero Hfst byte_inv0.
    + rewrite {Hfst}. apply z_leq_n_1 in Hb. case : Hb => [Hbn | Hbn].
      * rewrite upd_Znth_diff. apply IH; try by []. lia. 
        rewrite populate_invs_aux_length; rep_lia.
        rewrite populate_invs_aux_length; rep_lia.
        move => Hbninv. apply byte_unsigned_inj in Hbninv.
        move: Hbninv. rewrite inv_calc => Hinv. apply (congr1 GRing.inv) in Hinv.
        move: Hinv Hbn. rewrite GRing.invrK. have->: b^-1 = byte_inv b by []. move ->.
        rewrite Byte.unsigned_repr; try rep_lia. apply (congr1 Byte.unsigned) in Hinv.
        move: Hinv. rewrite Byte.unsigned_zero Byte.unsigned_repr; rep_lia.
      * rewrite inv_calc.
        { have->: Byte.unsigned b = (Byte.unsigned (byte_inv (Byte.repr (Z.of_nat n)))). {
           f_equal. rewrite -Hbn Byte.repr_unsigned.
           have->: byte_inv (byte_inv b) = b^-1^-1 by []. by rewrite GRing.invrK. }
          rewrite upd_Znth_same. by rewrite -Hbn Byte.repr_unsigned.
          rewrite populate_invs_aux_length; rep_lia.
        }
        { move => Hzero. apply (congr1 Byte.unsigned) in Hzero. move: Hzero.
          rewrite Byte.unsigned_repr; try rep_lia. rewrite Byte.unsigned_zero => Hn.
          rewrite Hn in Hbn. apply byte_unsigned_zero in Hbn. 
          have: byte_inv b <> Byte.zero. apply /eqP. apply GRing.invr_neq0. by apply /eqP. by [].
        }
Qed.

(*Full correctness*)
Lemma populate_invs_correct:
  populate_invs Byte.modulus = byte_invs.
Proof.
  rewrite /populate_invs. remember (zseq Byte.modulus Byte.zero) as base.
  have Hmod: 0 <= Byte.modulus <= Byte.modulus by rep_lia.
  have Hb1: Zlength base = Byte.modulus by rewrite Heqbase /= zseq_Zlength //.
  have Hb0: Znth 0 base = Byte.zero by rewrite Heqbase /= zseq_Znth.
  pose proof (populate_invs_aux_invar Hmod Hb1 Hb0) as [Hfst Hinvs].
  apply Znth_eq_ext.
  - rewrite populate_invs_aux_length byte_invs_Zlength. rep_lia.
  - move => i. rewrite populate_invs_aux_length Hb1 => Hi.
    have Hib: i = Byte.unsigned (Byte.repr i) by rewrite Byte.unsigned_repr; rep_lia.
    rewrite {1}Hib Hinvs; try rep_lia. by rewrite byte_invs_Znth.
Qed.

End Pow.

(*The theorems for the proof of multiplication in VST (using the pow and log tables)*)

Section Mult.

Local Open Scope ring_scope.

Lemma ord_byte_simpl: forall (x: 'I_#|byte_finType|),
  Byte.unsigned (ord_to_byte x) = Z.of_nat (nat_of_ord x).
Proof.
  move => x. by [].
Qed.

Lemma nat_eq_ord: forall n m (Hmn: m = n) (x: 'I_m),
  nat_of_ord (eq_ord Hmn x) = nat_of_ord x.
Proof.
  move => m n Hmn x. by [].
Qed.

(*A key result, needed in a few places: if a and b are equal mod 255, then x ^+ a = x^+ b*)
Lemma powX_eq_mod: forall a b,
  modn a 255%N = modn b 255%N ->
  (@GRing.exp qpoly_p256_fieldType (qx p256_geq_2) a) = (qx p256_geq_2) ^+ b.
Proof.
have->:255%N=(#|bool_finFieldType| ^ (size (Poly p256)).-1).-1 by rewrite size_p256 card_bool.
apply qpoly_exp_modn.
apply p256_primitive'.
Qed.

(*Therefore, we can add the field size without changing anything*)
Lemma powX_add_255: forall a,
  (@GRing.exp qpoly_p256_fieldType (qx p256_geq_2) a) =
  (qx p256_geq_2) ^+ (a + 255).
Proof.
  move => a. apply powX_eq_mod. by rewrite addnC modnDl.
Qed. 

(*The large case of multiplication*)
Lemma mult_large: forall b1 b2,
  fec_n - 1 < Byte.unsigned (byte_log_map b1) + Byte.unsigned (byte_log_map b2) ->
  byte_pow_map (Byte.repr (Byte.unsigned (byte_log_map b1) + Byte.unsigned (byte_log_map b2) - (fec_n - 1))) =
    byte_mul b1 b2.
Proof.
  move => b1 b2. rewrite /byte_log_map /byte_pow_map /byte_mul /qpow_map_full !ord_byte_simpl !nat_eq_ord.
  move => Hbig. f_equal.
  (*so we don't have to do it twice*)
  have Hnz: forall (x y : byte), fec_n - 1 <
       Z.of_nat (dlog_alt p256_geq_2 (byte_to_qpoly x)) +
       Z.of_nat (dlog_alt p256_geq_2 (byte_to_qpoly y)) ->
       x != 0. { move => x y Hbig'.
    case Hx: (x == 0) => [|//]. rewrite -byte_zero_qpoly_iff in Hx.
    apply (elimT eqP) in Hx. move: Hbig'.
    rewrite Hx. have->:nat_of_ord (dlog_alt p256_geq_2 (GRing.zero qpoly_p256_fieldType)) = 0%N.
      apply /eqP. by rewrite dlog_alt_zero. rewrite Nat2Z.inj_0 Z.add_0_l.
    case : (dlog_alt p256_geq_2 (byte_to_qpoly y)) => [m Hm].
    move: Hm. rewrite size_p256 card_bool /=. have->: (2^ 8)%N = 256%N by []. move => /ltP Hm. rep_lia. }
  have Hb1: b1 != 0. apply (Hnz b1 b2 Hbig).
  have Hb2: b2 != 0. rewrite Z.add_comm in Hbig. apply (Hnz b2 b1 Hbig). rewrite {Hnz}.
  rewrite -byte_zero_qpoly_iff in Hb1. rewrite -byte_zero_qpoly_iff in Hb2.
  apply (dlog_alt_correct p256_primitive' p256_geq_2) in Hb1.
  apply (dlog_alt_correct p256_primitive' p256_geq_2) in Hb2.
  rewrite powX_add_255 -{2}Hb1 -{2}Hb2 -GRing.exprD. f_equal. cbn.
  move: Hbig.  remember (nat_of_ord (dlog_alt p256_geq_2 (byte_to_qpoly b1))) as a. rewrite -Heqa.
  remember (nat_of_ord (dlog_alt p256_geq_2 (byte_to_qpoly b2))) as b. rewrite -Heqb => Hbig.
  rewrite Byte.unsigned_repr.
  - have->:(Z.to_nat (Z.of_nat a + Z.of_nat b - (fec_n - 1)) + 255)%Nrec =
           (Z.to_nat (Z.of_nat a + Z.of_nat b - (fec_n - 1)) + 255)%coq_nat by [].
    have->: (a + b)%Nrec = (a + b)%coq_nat by []. rep_lia.
  - move: Heqa Heqb Hbig. case : (dlog_alt p256_geq_2 (byte_to_qpoly b1)) => [a'].
    case : (dlog_alt p256_geq_2 (byte_to_qpoly b2)) => [b'].
    rewrite size_p256 card_bool /=. have->:( 2 ^ 8)%N = 256%N by []. 
    move => /ltP Ha' /ltP Hb' -> ->. rep_lia.
Qed.

(*The small and easier case*)
Lemma mult_small: forall b1 b2,
  b1 <> Byte.zero ->
  b2 <> Byte.zero ->
  fec_n - 1 >= Byte.unsigned (byte_log_map b1) + Byte.unsigned (byte_log_map b2) ->
  byte_pow_map (Byte.repr (Byte.unsigned (byte_log_map b1) + Byte.unsigned (byte_log_map b2))) =
    byte_mul b1 b2.
Proof.
  move => b1 b2 /eqP Hb1 /eqP Hb2 Hsmall.
  rewrite -byte_zero_qpoly_iff in Hb1. rewrite -byte_zero_qpoly_iff in Hb2.
  apply (dlog_alt_correct p256_primitive' p256_geq_2) in Hb1.
  apply (dlog_alt_correct p256_primitive' p256_geq_2) in Hb2.
  move: Hsmall.
  rewrite /byte_log_map /byte_pow_map /byte_mul /qpow_map_full !ord_byte_simpl !nat_eq_ord => Hsmall.
  rewrite -{2}Hb1 -{2}Hb2 -GRing.exprD. f_equal. f_equal. cbn. move: Hsmall.
  case : (dlog_alt p256_geq_2 (byte_to_qpoly b1)) => [a].
  case : (dlog_alt p256_geq_2 (byte_to_qpoly b2)) => [b]. rewrite card_bool size_p256 /=.
  have ->: (2 ^ 8)%N = 256%N by []. move => /ltP Ha /ltP Hb Hab.
  rewrite Byte.unsigned_repr ; try rep_lia.
  have->:(a + b)%Nrec = (a + b)%coq_nat by []. rep_lia.
Qed.

End Mult.
  