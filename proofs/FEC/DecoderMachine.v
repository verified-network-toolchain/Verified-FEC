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

(*The check to update the time*)
Fixpoint upd_time_m (time: int) (curr: fpacket) (blocks: list block) :
  int := 
  match blocks with
  | nil => Int.add time Int.one
  | bl :: tl =>
    let currSeq := Int.repr (Z.of_nat (fd_blockId curr)) in
    let blkid := Int.repr (Z.of_nat (blk_id bl)) in
    if Int.eq currSeq blkid then
      if (block_notin_packet bl curr) 
      then Int.add time Int.one 
      else time
    else if Int.ltu currSeq blkid then Int.add time Int.one
    else upd_time_m time curr tl
  end.
Print Int.sub.
(*Integer comparison is more difficult - we don't want
  just Int.ltu - since 0 should be considered larger than
  2^32-1. The following function is based on "Serial number
  arithmetic" in RFC 1982 and the wikipedia article*)
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
Check Int.signed_repr_eq.
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
  
Lemma Int_signed_repr_eq_sign_neg: forall x,
  0 <= x <= Int.max_unsigned ->
  Int.signed (Int.repr x) < 0 <-> x >= Int.half_modulus.
Proof.
  move=> x Hx.  rewrite Int.signed_repr_eq. 
  have ->: x mod Int.modulus = x by rewrite Zmod_small; rep_lia.
  case: (zlt x Int.half_modulus); rep_lia.
Qed.

Lemma int_seq_lt_correct (i1 i2: int):
  reflect (serial_lt i1 i2) (int_seq_lt i1 i2).
Proof.
  rewrite /serial_lt/int_seq_lt/=.
  case:  (Z_lt_ge_dec (Int.signed (Int.sub i1 i2)) 0) => [Hlt | Hge]/=.
  - apply ReflectT. move: Hlt.
    rewrite /Int.sub Int.signed_repr_eq.
    Check Int_signed_repr_eq_sign.

(*We need an integer comparison function that works for any
  2 ints *)

Definition int_leu (i1 i2: int) : bool :=
  Int.ltu i1 i2 || Int.eq i1 i2.

(*Timeouts if threshold exceeded*)
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