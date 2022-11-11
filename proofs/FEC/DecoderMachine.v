(*A decoder that does arithmetic on machine-length integers, not nats*)
(*TODO: also provide a version with some efficiency/speedups closer
  to C code (or maybe wait until VST see)*)
(*Here, we prove that under certain generous conditions of the
  input packet stream, this is equivalent to the idealized decoder.*)
Require Import VST.floyd.functional_base.
Require Import AbstractEncoderDecoder.
Require Import ZSeq.
Require Import Block.
Require Import DecoderTimeouts.
Require Import DecoderGeneric.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.
Section Machine.

Definition create_block_with_fec_packet_m (p: fpacket) (time : int) : 
  block :=
  let k := fd_k p in
  let h := fd_h p in
  let allPackets := upd_Znth 
    (Int.unsigned (Int.repr (Z.of_nat (fd_blockIndex p)))) 
    (zseq (k + h) None) (Some p) in
  mk_blk (fd_blockId p) (sublist 0 k allPackets) 
    (sublist k (k+h) allPackets) k h false (Int.unsigned time).

Definition create_block_with_packet_black_m (p: fpacket) (time: int) : block * list packet :=
  let new_block := create_block_with_fec_packet_m p time in
  let packets  := (if (fd_isParity p) then nil else 
    [:: p_packet p ]) ++
    (if Int.eq (Int.repr (fd_k p)) Int.one then 
      (decode_block new_block) else nil) in
  let marked_block := if Int.eq (Int.repr (fd_k p)) Int.one then 
    new_block <| black_complete := true |> else new_block in
  (marked_block, packets).

(*2. add packet to block*)
Definition add_fec_packet_to_block_m (p: fpacket) (b: block) : block :=
  let new_packets := upd_Znth 
    (Int.unsigned (Int.repr (Z.of_nat (fd_blockIndex p)) ))
    (data_packets b ++ parity_packets b) (Some p) in
  b <| data_packets := sublist 0 (blk_k b) new_packets |> 
      <| parity_packets := sublist (blk_k b) (blk_k b + blk_h b) new_packets |>.

Definition add_packet_to_block_black_m (p: fpacket) (b: block) : block * list packet :=
  (*NOTE: we still must add the packet even if the block is complete
    to keep the time correctly updated. But we don't need to output anything*)
  let new_block := add_fec_packet_to_block_m p b in
  if black_complete b then (new_block, if (fd_isParity p) then nil else 
    [:: p_packet p]) else 
    (*NOTE: theirs does not release data packet here - we can do either, the
      block has been recovered so this would just be a duplicate. But
      not returning anything does violate their stated spec*)
    let packets := (if (fd_isParity p) then nil else [:: p_packet p]) ++
      (if recoverable new_block then (decode_block new_block) else nil) in
    let marked_block := if recoverable new_block then 
      new_block <| black_complete := true |> else new_block in
    (marked_block, packets).

Variable threshold : int.

(*Once again, will have more efficient version like C code, 
  for now just prove equivalence*)
(*TODO: is it nontrivial to prove equivalence? Probably not
  because we can easily prove everything is within required bounds*)
(*TODO: use from before?*)
Definition block_notin_packet block packet : bool :=
    ~~ (packet_in_block packet block).

(*NOTE: We are changing the code to use 64 bit integers and thus
  Int64 comparison operations. Then, we can assume that all
  packets have unique sequence numbers (at current network speeds,
  it would take around 600,000 years before we run into problems).
  Otherwise, we need to deal with wraparound, which is highly 
  nontrivial, because we would need to reason both about
  reorder/duplication as well as loss, in a different way from 
  the stronger conditions for ensuring packet recovery.
  TOOD: write this somewhere
  *)

(*The check to update the time*)
Fixpoint upd_time_m (time: int) (curr: fpacket) (blocks: list block) :
  int := 
  match blocks with
  | nil => Int.add time Int.one
  | bl :: tl =>
    let currSeq := Int64.repr (Z.of_nat (fd_blockId curr)) in
    let blkid := Int64.repr (Z.of_nat (blk_id bl)) in
    if Int64.eq currSeq blkid then
      if (block_notin_packet bl curr) 
      then Int.add time Int.one 
      else time
    else if Int64.ltu currSeq blkid then Int.add time Int.one
    else upd_time_m time curr tl
  end.

  (*Here, we use *)


(*Integer comparison is more difficult - we don't want
  just Int.ltu - since 0 should be considered larger than
  2^32-1. The following function is based on "Serial number
  arithmetic" in RFC 1982 and the wikipedia article*)
  (*We use this for comparing times*)
(**
Definition seq_comp (i1 i2: int) : Z :=
  if Int.eq i1 i2 then 0%Z else
  if Int.ltu b a then Int.signed (Int.sub i1 i2)
  else 



  Definition compare (a b: Z) : Z :=
  if Z.eq_dec a b then 0%Z else 
  if Z_gt_le_dec a b then Z.modulo (a - b) Int.modulus (*TODO: see*) else
  Int.max_unsigned - (b - a - 1).
*)
(*From netinet/tcp_seq.h*)
(*This function determines if a sequence number is less than another.
If |i1 -i2| = 2^31, then this returns true even though the value is
undefined.*)
Definition int_seq_lt (i1 i2: int) : bool :=
  Z_lt_ge_dec (Int.signed (Int.sub i1 i2)) 0.

(*Proof that this works*)
(*RFC spec for when i1 is considered smaller than i2
  (i1 and i2 are s1 and s2 in the spec, a1 and a2 are i1 and i2 in
  the spec)*)
Definition serial_lt (i1 i2: int) : Prop :=
  let a1 := Int.unsigned i1 in
  let a2 := Int.unsigned i2 in
  (a1 < a2 /\ a2 - a1 < Int.half_modulus) \/
  (a1 > a2 /\ a1 - a2 > Int.half_modulus).

  (*From verified-packet-reorder*)
  (*OK, both are equivalent - so I can do either*)
  (*TODO: copy proof/modify as needed, prove properties
    THEN, we will prove something like: because of the reordering
    bound, every time we compare two packet sequence numbers,
    we can determine unambiguously if the difference is
    bigger or smaller than 2^31 and therefore prove that the comparison
    of nats is equivalent to one on ints
    (we will also need a similar but easier for result for equality)

    To do this, we need some kind of invariant - likely just that
    blockId of each block is seqNum of some packet, then use
    [u_seqNum_reorder_bound] - hmm do we need to relate to time at all?
    dont think so
    ah but we do - because this wouldnt work if we kept everything
    need to know that at most threshold unique packets between
    (weaker than with timeouts where we could unique packets exactly)
    so u_seqNum could only have increased by threshold at most
    (could be much less if we consider duplicates as newly seen)
    so this means that difference between u_seqNums can be at most
    threshold, so 
    hmmm think about this more
    
    it must
    be the case that one of the [serial_lt] cases applies and hence
    the [int_seq_lt] function is equivalent to *)
  Lemma test i1 i2:
    Int.signed (Int.sub i1 i2) =
    Int.signed (Int.repr ((Int.unsigned i1 - Int.unsigned i2) mod Int.modulus)).
  Proof.
    rewrite /Int.sub !Int.signed_repr_eq.
    by rewrite !Zmod_mod.
  Qed.

  (*2 options:
  Int.signed (Int.sub i1 i2) OR
  Int.signed (Int.repr ((Int.unsigned i1 - Int.unsigned i2) mod Int.modulus))*)
  
Lemma Int_signed_repr_eq_sign: forall x,
  0 <= x <= Int.max_unsigned ->
  Int.signed (Int.repr x) > 0 <-> 0 < x < Int.half_modulus.
Proof.
  move=> x Hx. rewrite Int.signed_repr_eq. 
  have->: x mod Int.modulus = x by rewrite Zmod_small; rep_lia.
  case: zlt; rep_lia.
Qed.

Lemma Int_signed_repr_eq_sign_neg: forall x,
  0 <= x <= Int.max_unsigned ->
  Int.signed (Int.repr x) < 0 <-> x >= Int.half_modulus.
Proof.
  move=> x Hx.  rewrite Int.signed_repr_eq. 
  have ->: x mod Int.modulus = x by rewrite Zmod_small; rep_lia.
  case: (zlt x Int.half_modulus); rep_lia.
Qed.

Definition z_abs_diff (z1 z2: Z) : Z :=
  Z.abs (z1 - z2).

Lemma z_abs_diff_max: forall z1 z2,
  z_abs_diff z1 z2 =
  Z.max (z1 - z2) (z2 - z1).
Proof.
  move=> z1 z2. rewrite /z_abs_diff. lia.
Qed.

Definition int_diff (i1 i2: int) :=
  z_abs_diff (Int.unsigned i1) (Int.unsigned i2).

Lemma int_diff_le (i1 i2 : int):
  Int.unsigned i1 <= Int.unsigned i2 ->
  int_diff i1 i2 = Int.unsigned i2 - (Int.unsigned i1).
Proof.
  move=> Hle. rewrite /int_diff /Int.sub z_abs_diff_max. 
  rewrite Z.max_r; try lia.
Qed.

Lemma int_diff_ge (i1 i2: int):
  Int.unsigned i1 >= Int.unsigned i2 ->
  int_diff i1 i2 = Int.unsigned i1 - (Int.unsigned i2).
Proof.
  move=> Hge. rewrite /int_diff /Int.sub z_abs_diff_max.
  rewrite Z.max_l; try lia.
Qed.

Lemma int_seq_lt_correct (i1 i2: int):
  reflect 
  (int_diff i1 i2 = Int.half_modulus \/ serial_lt i1 i2)
  (int_seq_lt i1 i2) .
Proof.
  rewrite /serial_lt/int_seq_lt/=.
  case:  (Z_lt_ge_dec (Int.signed (Int.sub i1 i2)) 0) => [Hlt | Hge]/=.
  - apply ReflectT. move: Hlt.
    rewrite /Int.sub.
    case : (Z_lt_ge_dec (Int.unsigned i2) (Int.unsigned i1) ) => Hi12/=.
    + rewrite Int_signed_repr_eq_sign_neg; try rep_lia.
      rewrite int_diff_ge; lia.
    + rewrite Int.signed_repr_eq.
      case: (Z.eq_dec (Int.unsigned i1) (Int.unsigned i2)) => Heq.
      * rewrite Heq Z.sub_diag /= Zmod_0_l. lia.
      * rewrite -(Z_mod_plus_full _ 1) !Zmod_small; try rep_lia.
        case: zlt => Hhalf; try rep_lia. move => _.
        rewrite int_diff_le; rep_lia.
  - apply ReflectF => C. move: Hge.
    rewrite /Int.sub.
    case : (Z_lt_ge_dec (Int.unsigned i2) (Int.unsigned i1) ) => Hi12/=.
    + rewrite Int.signed_repr_eq Zmod_small; try rep_lia.
      case: zlt => [Hlt | Hge]; try rep_lia.
      (*Contradiction from C*)
      rewrite int_diff_ge in C; rep_lia.
    + rewrite int_diff_le in C; try rep_lia. 
      case: (Z.eq_dec (Int.unsigned i1) (Int.unsigned i2)) => Heq; 
      first by rep_lia.
      rewrite Int.signed_repr_eq  -(Z_mod_plus_full _ 1) !Zmod_small; 
      try rep_lia.
      case: zlt => Hhalf; rep_lia.
Qed.

(*Is this lemma true?*)
(*This cannot be true as written - z2 could be much much larger*)
Lemma div_le (n m: Z):
  0 < m ->
  0 <= n ->
  n / m <= n.
Proof.
  move=> Hm Hn.
  have:=(Zdiv_interval_2 0 n n m). lia.
Qed.

Lemma z_abs_diff_sym: forall z1 z2,
  z_abs_diff z1 z2 = z_abs_diff z2 z1.
Proof.
  move=> z1 z2. rewrite /z_abs_diff. lia.
Qed.

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

(*TODO: start here*)

(*Now we will want to prove: if the unsigned value between
  any two Z is < Int.half_modulus, then this equals the integer lt function*)
Lemma int_seq_lt_lt (z1 z2: Z):
  z_abs_diff z1 z2 < Int.half_modulus ->
  int_seq_lt (Int.repr z1) (Int.repr z2) = Z.ltb z1 z2.
Proof.
  rewrite /z_abs_diff => Habs.
  case: (int_seq_lt (Int.repr z1) (Int.repr z2)) /int_seq_lt_correct.
  - move => [Heq | Hlt].
    + move: Heq. rewrite /int_diff !Int.unsigned_repr_eq.
      move=> Hdiff.
      (*Hmm, how do we do this?*)
      exfalso. apply (@abs_diff_mod z1 z2 Int.half_modulus); try rep_lia.
      by rewrite /z_abs_diff.
      have->//: 2 * Int.half_modulus = Int.modulus by [].
    + (*Now do lt case*)

(*We need an integer comparison function that works for any
  2 ints *)

Definition int_leu (i1 i2: int) : bool :=
  Int.ltu i1 i2 || Int.eq i1 i2.

(*Timeouts if threshold exceeded*)
(*Hmm, what happens if time wraps around? - maybe for this 
we should do sequence number comparison because times will 
always be within threshold?*)
Definition not_timed_out_m: int -> block -> bool := fun currTime =>
  (fun b => int_leu currTime (Int.add (Int.repr(black_time b)) threshold)).


Fixpoint update_dec_state_m (blocks: list block) (curr: fpacket)
  (time: int) : list block * list packet:=
match blocks with
| nil => let t := create_block_with_packet_black_m curr time in 
    ([:: t.1], t.2)
| bl :: tl =>
  let currSeq := Int.repr (Z.of_nat (fd_blockId curr)) in
  let blkid := Int.repr (Z.of_nat (blk_id bl)) in
  if Int.eq currSeq blkid then
    let t := add_packet_to_block_black_m curr bl in
    (t.1 :: tl, t.2)
    else if Int.ltu currSeq blkid then
    let t := create_block_with_packet_black_m curr time in 
      (t.1 :: blocks, t.2)
  else 
    let t := update_dec_state_m tl curr time
    in (bl :: t.1, t.2)
end.

Definition decoder_one_step_m (blocks: list block) curr (time : int) :
list block * list packet * int :=
(*First, we process timeouts; this covers the case when the packet
  which makes the block timeout is the kth packet; we should not
  recover this block (it makes our invariants much harder).*)
let tm := upd_time_m time curr blocks in
let blks := filter (not_timed_out_m tm) blocks in
let t := update_dec_state_m blks curr tm in
(t, tm).

Definition decoder_multiple_steps_m
(prev_packs packs: list fpacket)
(state: list block) (sent: list packet) (time: int) :
list block * list packet * int * list fpacket :=
foldl (fun (acc: list block * list packet * int * list fpacket) 
  (p: fpacket) =>
  let t := decoder_one_step_m acc.1.1.1 p acc.1.2 in
  (t.1.1, acc.1.1.2 ++ t.1.2, t.2, acc.2 ++ [:: p])) 
(state, sent, time, prev_packs) packs.

Definition decoder_all_steps_m (received: list fpacket) :
(list block * list packet * int) :=
(decoder_multiple_steps_m nil received nil nil Int.zero).1.

(*Now we have to prove equivalence. This means we have to show that
  every*)