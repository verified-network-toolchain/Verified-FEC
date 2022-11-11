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
Require Import SeqCmp.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.

Module S64:=SeqCmp Wordsize_64.
Module S32:=SeqCmp Wordsize_32.

(*Coq module weirdness: it does not recognize
  S32.I.int and Int.int as equal, though they are.
  We can give a trivial conversion function*)
Definition sint (i: int) : S32.I.int :=
  S32.I.mkint (Int.intval i) (Int.intrange i).

Definition sint64 (i: int64) : S64.I.int :=
  S64.I.mkint (Int64.intval i) (Int64.intrange i).

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
    else if S64.seq_lt (sint64 currSeq) (sint64 blkid) 
      then Int.add time Int.one
    else upd_time_m time curr tl
  end.

(*TODO: may need to add to SeqCmp.v - SEE*)
Definition seq_leq (i1 i2: int) : bool :=
  Int.eq i1 i2 || S32.seq_lt (sint i1) (sint i2).

(*Timeouts if threshold exceeded*)
(*Hmm, what happens if time wraps around? - maybe for this 
we should do sequence number comparison because times will 
always be within threshold?*)
Definition not_timed_out_m: int -> block -> bool := fun currTime =>
  (fun b => seq_leq currTime (Int.add (Int.repr(black_time b)) threshold)).

Fixpoint update_dec_state_m (blocks: list block) (curr: fpacket)
  (time: int) : list block * list packet:=
match blocks with
| nil => let t := create_block_with_packet_black_m curr time in 
    ([:: t.1], t.2)
| bl :: tl =>
  let currSeq := Int64.repr (Z.of_nat (fd_blockId curr)) in
  let blkid := Int64.repr (Z.of_nat (blk_id bl)) in
  if Int64.eq currSeq blkid then
    let t := add_packet_to_block_black_m curr bl in
    (t.1 :: tl, t.2)
    else if S64.seq_lt (sint64 currSeq) (sint64 blkid) then
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