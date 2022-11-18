(*Comparing Sequence Numbers for an arbitrary wordsize*)
Require Import VST.floyd.functional_base.

(*We want sequence number comparison that works for both Int and Int64.
  If we parameterize by the WORDSIZE directly, we end up with two
  non-identical copies of Int/Int64 that we have to convert between.
  Instead, we define a Module Type consisting only of the int
  operations that we need for the sequence number comparison.
  Then we instantiate this for both Int and Int64 (it could be
    instantiated with any other size ints if needed).*)

(*Problems if we have ssreflect in scope here*)
Module Type IntType.

Parameter wordsize: nat.
Definition modulus : Z := two_power_nat wordsize.
Definition half_modulus : Z := modulus / 2.
Definition max_unsigned : Z := modulus - 1.
Definition max_signed : Z := half_modulus - 1.
Definition min_signed : Z := - half_modulus.

Parameter int: Type.

Parameter unsigned: int -> Z.
Parameter signed: int -> Z.

Parameter repr: Z -> int.
Definition eq (x y: int) : bool :=
  if zeq (unsigned x) (unsigned y) then true else false.
Definition sub (x y: int) : int :=
  repr (unsigned x - unsigned y).

Axiom half_modulus_modulus: modulus = 2 * half_modulus.
Axiom half_modulus_pos: half_modulus > 0.
Axiom unsigned_repr_eq:
  forall x, unsigned (repr x) = Z.modulo x modulus.
Axiom signed_repr_eq:
  forall x, signed (repr x) = if zlt (Z.modulo x modulus) half_modulus 
  then Z.modulo x modulus else Z.modulo x modulus - modulus.

Axiom eq_sym:
forall x y, eq x y = eq y x.

Axiom unsigned_range:
  forall i, 0 <= unsigned i < modulus.
Axiom signed_range:
  forall i, min_signed <= signed i <= max_signed.

End IntType.

(*Instantiate for Int*)
Module I32 <: IntType.

Definition wordsize := Int.wordsize.
Definition modulus := Int.modulus.
Definition half_modulus := Int.half_modulus.
Definition max_unsigned := Int.max_unsigned.
Definition max_signed := Int.max_signed.
Definition min_signed := Int.min_signed.
Definition int := int.
Definition unsigned := Int.unsigned.
Definition signed := Int.signed.
Definition repr := Int.repr.
Definition eq := Int.eq.
Definition sub := Int.sub.
Definition half_modulus_modulus := Int.half_modulus_modulus.
Definition half_modulus_pos := Int.half_modulus_pos.
Definition unsigned_repr_eq := Int.unsigned_repr_eq.
Definition signed_repr_eq := Int.signed_repr_eq.
Definition eq_sym := Int.eq_sym.
Definition unsigned_range := Int.unsigned_range.
Definition signed_range := Int.signed_range.

End I32.

(*Instantiate for Int64*)
Module I64 <: IntType.

Definition wordsize := Int64.wordsize.
Definition modulus := Int64.modulus.
Definition half_modulus := Int64.half_modulus.
Definition max_unsigned := Int64.max_unsigned.
Definition max_signed := Int64.max_signed.
Definition min_signed := Int64.min_signed.
Definition int := Int64.int.
Definition unsigned := Int64.unsigned.
Definition signed := Int64.signed.
Definition repr := Int64.repr.
Definition eq := Int64.eq.
Definition sub := Int64.sub.
Definition half_modulus_modulus := Int64.half_modulus_modulus.
Definition half_modulus_pos := Int64.half_modulus_pos.
Definition unsigned_repr_eq := Int64.unsigned_repr_eq.
Definition signed_repr_eq := Int64.signed_repr_eq.
Definition eq_sym := Int64.eq_sym.
Definition unsigned_range := Int64.unsigned_range.
Definition signed_range := Int64.signed_range.

End I64.

From Coq Require Import ssreflect.


Definition z_abs_diff (z1 z2: Z) : Z :=
  Z.abs (z1 - z2).

Lemma z_abs_diff_max: forall z1 z2,
  z_abs_diff z1 z2 =
  Z.max (z1 - z2) (z2 - z1).
Proof.
  move=> z1 z2. rewrite /z_abs_diff. lia.
Qed.

Lemma z_abs_diff_sym: forall z1 z2,
  z_abs_diff z1 z2 = z_abs_diff z2 z1.
Proof.
  move=> z1 z2. rewrite /z_abs_diff. lia.
Qed.

Module SeqCmp (I: IntType).

(*Integer comparison is more difficult - we don't want
  just Int.ltu - since 0 should be considered larger than
  2^32-1. The following function is based on "Serial number
  arithmetic" in RFC 1982 and the wikipedia article*)
  (*We use this for comparing times*)

(*Module I := Make WS.*)

Ltac rep_lia_setup2 ::=
pose_lemmas I.unsigned I.unsigned_range;
pose_lemmas I.signed I.signed_range;
unfold I.max_unsigned in *;
pose proof I.half_modulus_pos;
pose proof I.half_modulus_modulus.

Ltac rep_nia :=
  rep_lia_setup; rep_lia_setup2; nia.


(*From netinet/tcp_seq.h*)
(*This function determines if a sequence number is less than another.
If |i1 -i2| = I.half_modulus, then this returns true even 
though the comparison value should be undefined.*)
Definition seq_lt (i1 i2: I.int) : bool :=
  Z_lt_ge_dec (I.signed (I.sub i1 i2)) 0.


(*Proof that this works*)
(*RFC spec for when i1 is considered smaller than i2
  (i1 and i2 are s1 and s2 in the spec, a1 and a2 are i1 and i2 in
  the spec)*)
Definition serial_lt (i1 i2: I.int) : Prop :=
  let a1 := I.unsigned i1 in
  let a2 := I.unsigned i2 in
  (a1 < a2 /\ a2 - a1 < I.half_modulus) \/
  (a1 > a2 /\ a1 - a2 > I.half_modulus).

(*Part 1: Prove that [seq_lt] is true exactly when
  [serial_lt] holds or the two values are I.half_modulus apart*)


Definition int_diff (i1 i2: I.int) :=
  z_abs_diff (I.unsigned i1) (I.unsigned i2).

Lemma int_diff_le (i1 i2 : I.int):
  I.unsigned i1 <= I.unsigned i2 ->
  int_diff i1 i2 = I.unsigned i2 - (I.unsigned i1).
Proof.
  move=> Hle. rewrite /int_diff z_abs_diff_max. 
  rewrite Z.max_r; try lia.
Qed.

Lemma int_diff_ge (i1 i2: I.int):
  I.unsigned i1 >= I.unsigned i2 ->
  int_diff i1 i2 = I.unsigned i1 - (I.unsigned i2).
Proof.
  move=> Hge. rewrite /int_diff z_abs_diff_max.
  rewrite Z.max_l; try lia.
Qed.

Lemma I_signed_repr_eq_sign_neg: forall x,
  0 <= x <= I.max_unsigned ->
  I.signed (I.repr x) < 0 <-> x >= I.half_modulus.
Proof.
  move=> x Hx.  rewrite I.signed_repr_eq. 
  have ->: x mod I.modulus = x by rewrite Zmod_small; rep_lia.
  case: (zlt x I.half_modulus); rep_lia.
Qed.

Lemma seq_lt_correct (i1 i2: I.int):
  reflect 
  (int_diff i1 i2 = I.half_modulus \/ serial_lt i1 i2)
  (seq_lt i1 i2) .
Proof.
  rewrite /serial_lt/seq_lt/=.
  case:  (Z_lt_ge_dec (I.signed (I.sub i1 i2)) 0) => [Hlt | Hge]/=.
  - apply ReflectT. move: Hlt.
    rewrite /I.sub.
    case : (Z_lt_ge_dec (I.unsigned i2) (I.unsigned i1) ) => Hi12/=.
    + rewrite I_signed_repr_eq_sign_neg; try rep_lia.
      rewrite int_diff_ge; lia.
    + rewrite I.signed_repr_eq.
      case: (Z.eq_dec (I.unsigned i1) (I.unsigned i2)) => Heq.
      * rewrite Heq Z.sub_diag /= Zmod_0_l. case:zlt; rep_lia. 
      * rewrite -(Z_mod_plus_full _ 1) !Zmod_small; try rep_lia.
        case: zlt => Hhalf; try rep_lia. move => _.
        rewrite int_diff_le; rep_lia.
  - apply ReflectF => C. move: Hge.
    rewrite /Int.sub.
    case : (Z_lt_ge_dec (I.unsigned i2) (I.unsigned i1) ) => Hi12/=.
    + rewrite I.signed_repr_eq Zmod_small; try rep_lia.
      case: zlt => [Hlt | Hge]; try rep_lia.
      (*Contradiction from C*)
      rewrite int_diff_ge in C; rep_lia.
    + rewrite int_diff_le in C; try rep_lia. 
      case: (Z.eq_dec (I.unsigned i1) (I.unsigned i2)) => Heq; 
      first by rep_lia.
      rewrite I.signed_repr_eq  -(Z_mod_plus_full _ 1) !Zmod_small; 
      try rep_lia.
      case: zlt => Hhalf; rep_lia.
Qed.

(*Part 2: If we have two Z values which are less than I.half_modulus
  apart, then the sequence comparison function is equivalent to the
  Z lt function. This is the wraparound property that we want.*)

(*First, some intermediate lemmas*)

Lemma div_le (n m: Z):
  0 < m ->
  0 <= n ->
  n / m <= n.
Proof.
  move=> Hm Hn.
  have:=(Zdiv_interval_2 0 n n m). lia.
Qed.

(*The big intermediate lemma: two ints separated by n
  cannot have their difference mode (2 * n) be n*)
Lemma abs_diff_mod (z1 z2 n: Z):
  0 < n ->
  z_abs_diff z1 z2 < n ->
  z_abs_diff (z1 mod (2 * n)) (z2 mod (2 * n)) <> n.
Proof.
  move=> Hn.
  wlog: z1 z2 /z1 <= z2; last first.
  - move=> Hle.
    rewrite !z_abs_diff_max (Z.max_r _ (z2 - z1)); try lia.
    set (m := 2 * n).
    move => Hlt C.
    case: (Z.max_spec_le (z1 mod m - z2 mod m) 
      (z2 mod m - z1 mod m)) => 
      [[Hmodle Hmax] | [Hmodle Hmax]].
    + rewrite Hmax in C.
      have: z2 mod m - z1 mod m = (z2 - z1) mod m. {
        rewrite Zminus_mod (Zmod_small (z2 mod m - z1 mod m)); try lia.
      }
      rewrite C Zmod_small; try lia. 
    + rewrite Hmax in C. (*TODO: repetitive*)
      have: z1 mod m - z2 mod m = (z1 - z2) mod m. {
        rewrite Zminus_mod (Zmod_small (z1 mod m - z2 mod m)); try lia. 
      }
      rewrite C.
      have Hlower: z1 - z2 > - n by lia.
      case: (Z.eq_dec z1 z2) => Heq.
      * (*minor case: when equal, show n = 0*)
        rewrite Heq Z.sub_diag /= Zmod_0_l. lia.
      * rewrite -(Z_mod_plus_full _ 1) Zmod_small; lia.
  - move=> Hwlog Habs.
    have [H1 | H2]: (z1 <= z2 \/ z2 <= z1) by lia.
    + by apply Hwlog.
    + rewrite z_abs_diff_sym. apply Hwlog=>//.
      by rewrite z_abs_diff_sym.
Qed.

Lemma Zplus_gt: forall a b c d,
  a > b ->
  c > d ->
  a + c > b + d.
Proof.
  lia.
Qed.

(*The theorem we want:*)
(*Lots of tedious cases, and we need to do extra work
  because rep_lia doesn't know the constants*)
Lemma seq_lt_lt (z1 z2: Z):
  z_abs_diff z1 z2 < I.half_modulus ->
  seq_lt (I.repr z1) (I.repr z2) = Z.ltb z1 z2.
Proof.
  rewrite /z_abs_diff => Habs.
  case: (seq_lt (I.repr z1) (I.repr z2)) /seq_lt_correct.
  - move => [Heq | Hlt].
    + move: Heq. rewrite /int_diff !I.unsigned_repr_eq.
      move=> Hdiff.
      exfalso. apply (@abs_diff_mod z1 z2 I.half_modulus); try rep_lia.
      by rewrite /z_abs_diff.
      have->//: 2 * I.half_modulus = I.modulus by rep_lia.
    + (*Now do lt case*)
      move: Hlt. rewrite /serial_lt !I.unsigned_repr_eq.
      case: (z1 <? z2) /Z.ltb_spec => // Hleq.
      rewrite Z.abs_eq in Habs; try lia.
      have Hz1eq:=(Z_div_mod_eq_full z1 I.modulus).
      have Hz2eq:=(Z_div_mod_eq_full z2 I.modulus).
      have Hdiv:=Hleq.
      apply (Z.div_le_mono _ _ I.modulus) in Hdiv;try rep_lia.
      apply Z.le_lteq in Hdiv. rep_nia.
  - move => Hnot. case: (z1 <? z2) /Z.ltb_spec =>// Hlt.
    move: Habs.
    have->: Z.abs (z1 - z2) = z2 - z1 by lia. move=> Habs.
    exfalso. apply: Hnot.
    right. (*left case cannot happen by [abs_diff_mod]*)
    rewrite /serial_lt !I.unsigned_repr_eq.
    have Hz1eq:=(Z_div_mod_eq_full z1 I.modulus).
    have Hz2eq:=(Z_div_mod_eq_full z2 I.modulus).
    have Hdiv: z1 <= z2 by lia.
    apply (Z.div_le_mono _ _ I.modulus) in Hdiv; try rep_lia.
    have Hsub:(
      z1 mod I.modulus <= z2 mod I.modulus ->
      z2 mod I.modulus - z1 mod I.modulus =
        (z2 - z1) mod I.modulus). {
      move=> H.
      rewrite Zminus_mod (Zmod_small (_ - _)); try rep_lia. 
      split;
      have:=(Z.mod_pos_bound z1 I.modulus);
      have:=(Z.mod_pos_bound z2 I.modulus); rep_lia.
    }
    case: (Z.lt_total (z1 mod I.modulus) (z2 mod I.modulus)) => 
    [Hgt21 | [Heq21 | Hgt12]]; try rep_nia.
    + have Hmod0: (z2 - z1) mod I.modulus = 0 by lia.
      have:=(Z_div_mod_eq_full (z2 - z1) I.modulus).
      rewrite Hmod0 Z.add_0_r.
      have: (0 <= ((z2 - z1) / I.modulus)) by
        apply Z.div_pos; rep_lia.
      rewrite Z.le_lteq => [[Hgt0 | Heq0]]; try rep_lia.
      rep_nia.
      (*Again, need to know that multiply with something >= 1, 
      get that thing*)
    + right. split=>//; try rep_lia.
      have->:z1 mod I.modulus - z2 mod I.modulus =
        (z1 - z2) + I.modulus * ((z2 / I.modulus) - (z1 / I.modulus)) by lia.
      have: z1 - z2 + I.modulus * (z2 / I.modulus - z1 / I.modulus) >
      - I.half_modulus + I.modulus; try rep_lia.
      move: Hdiv.
      rewrite Z.le_lteq => [[Hgt0 | Heq0]]; rep_nia.
Qed.

(*Equality*)
Definition seq_eq (i1 i2: I.int) : bool := I.eq i1 i2.

Lemma seq_eq_sym (i1 i2: I.int):
  seq_eq i1 i2 = seq_eq i2 i1.
Proof.
  by rewrite /seq_eq I.eq_sym.
Qed. 

(*Here, we need a weaker condition*)
Lemma seq_eq_eq (z1 z2: Z):
  z_abs_diff z1 z2 < I.modulus ->
  seq_eq (I.repr z1) (I.repr z2) = Z.eqb z1 z2.
Proof.
  wlog: z1 z2 / (z2 <= z1); last first.
  - rewrite /z_abs_diff => Hlt Habs.
    rewrite /seq_eq /I.eq !I.unsigned_repr_eq.
    case: zeq => [Heq | Hneq].
    + case: (z1 =? z2) /Z.eqb_spec=>// C.
      (*Idea: if mod is same, need to be equal or separated by >=modulus*)
      have Hzero: (z1 - z2) mod I.modulus = 0 by
        rewrite Zminus_mod Heq Z.sub_diag Zmod_0_l.
      apply Z_div_exact_full_2 in Hzero; try rep_lia.
      have Hge0: 0 <= ((z1 - z2) / I.modulus) by
        apply Z.div_pos; rep_lia.
      apply Zle_lt_or_eq in Hge0. 
      by rep_nia.
    + (*easy case*)
      by case: (z1 =? z2) /Z.eqb_spec=>// Heq; subst.
  - move=> Hgen Habs.
    case: (Z.le_ge_cases z1 z2) => Hle.
    + rewrite seq_eq_sym Z.eqb_sym.
      apply Hgen=>//. by rewrite z_abs_diff_sym.
    + by apply Hgen.
Qed.

(*Another lemma about int equality we need*)
Lemma int_eq_sub (i1 i2: I.int) :
  I.eq i1 i2 = Z.eqb (I.signed (I.sub i1 i2)) 0.
Proof.
  rewrite /I.eq /I.sub.
  case: (_ =? _) /Z.eqb_spec=>/=; last first.
    case: zeq; try rep_lia.
    move->. rewrite Z.sub_diag/= I.signed_repr_eq !Zmod_0_l.
    case: zlt; rep_lia.
  case: zeq=>// Hneq. rewrite I.signed_repr_eq.
  case: (Z.le_ge_cases (I.unsigned i1) (I.unsigned i2)) => Hle; last first.
  - rewrite !Zmod_small; try rep_lia.
    case: zlt; rep_lia.
  - case: zlt.
    + move=> Hltmod Hzero.
      apply Z_div_exact_full_2 in Hzero; try rep_lia.
      have Hle0: 
        (((I.unsigned i1 - I.unsigned i2) / I.modulus) <= 0) by rep_nia.
      apply Zle_lt_or_eq in Hle0. 
      by rep_nia.
    + have:=(Z.mod_pos_bound (I.unsigned i1 - I.unsigned i2) I.modulus).
      rep_lia.
Qed. 
      
(*Sequence Leq*)
Definition seq_leq (i1 i2: I.int) : bool :=
  Z_le_gt_dec (I.signed (I.sub i1 i2)) 0.

Lemma seq_leq_equiv (i1 i2: I.int):
  seq_leq i1 i2 = seq_lt i1 i2 || seq_eq i1 i2.
Proof.
  rewrite /seq_leq/seq_lt/seq_eq.
  case: Z_le_gt_dec => [Hle0 | Hgt0];
  case: Z_lt_ge_dec=>/=; try lia.
  - move=> Hge0. rewrite int_eq_sub. lia.
  - move=> _. move: Hgt0.
    rewrite /I.eq /I.sub. case: zeq=>//==>->.
    rewrite Z.sub_diag/= I.signed_repr_eq !Zmod_0_l.
    case: zlt; rep_lia.
Qed.

(*And therefore the final lemma is an easy corollary*)
Lemma seq_leq_leq (z1 z2: Z):
  z_abs_diff z1 z2 < I.half_modulus ->
  seq_leq (I.repr z1) (I.repr z2) = Z.leb z1 z2.
Proof.
  move=> Habs. rewrite seq_leq_equiv seq_lt_lt // seq_eq_eq; rep_lia.
Qed.

End SeqCmp.

