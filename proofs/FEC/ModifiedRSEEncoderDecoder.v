Require Import AbstractEncoderDecoder.
Require Import RSEEncoderDecoder.
Require Import VST.floyd.functional_base.
Require Import ByteFacts.
Require Import Block.
Require Import Reorder.

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section UpdateDecoder.

Variable threshold : Z.

(*First, we give the updated version of the decoder*)
(*Do timeouts separately, and time out ALL expired blocks*)
Definition process_timeouts (blocks: list block) (time : Z) : list block :=
    filter (fun b => ~~ (Z.ltb (black_time b + threshold) time)) blocks. 
    
(*We will separate out the check for duplicates and the updating for the
analysis (and to prevent us from needing to change everything
from before), though in the code, they are done together. Maybe we will
prove another version that combines it to make the VST proof simpler.*)
(*True if packet not present*)
Definition check_block_for_dup block packet : bool :=
    isNone (Znth (Int.unsigned (fd_blockIndex packet))
        (data_packets block ++ parity_packets block)).

(*Our version will be simpler for analysis, so we will simply find
  the correct block, check if the packet is there, and add it if not.
  We will later give a version that is close to the C code to make
  the VST proofs easier*)
Fixpoint update_dec_state' (blocks: list block) (curr: fec_packet_act)
    (time: Z) : list block * list packet * Z :=
  match blocks with
  | nil => let t := create_block_with_packet_black curr time in 
      ([:: t.1], t.2, time + 1)
  | bl :: tl =>
    let currSeq := fd_blockId curr in
    if Int.eq currSeq (blk_id bl) then
      let b := check_block_for_dup bl curr in
      let t := add_packet_to_block_black curr bl in
      (upd_Znth (Zlength blocks - 1) blocks t.1, t.2, 
        if b then time + 1 else time)
    else if Int.lt (blk_id bl) currSeq then 
      let t := create_block_with_packet_black curr time in 
        (blocks ++ [:: t.1], t.2, time + 1)
    else update_dec_state' tl curr time
  end.

Definition decoder_one_step (blocks: list block) curr time :
  list block * list packet * Z :=
  let t := update_dec_state' blocks curr time in
  let blks := process_timeouts t.1.1 t.2 in
  (blks, t.1.2, t.2). 

(*Might make it easier for induction*)
(*We include the previously-received packets as well to make the
proofs easier - we can formulate invariants easier.*)
Definition decoder_multiple_steps (prev_packs packs: list fec_packet_act)
  (state: list block) (sent: list packet) (time: Z) :
  list block * list packet * Z * list fec_packet_act :=
  foldl (fun (acc: list block * list packet * Z * list fec_packet_act) 
    (p: fec_packet_act) =>
    let t := decoder_one_step acc.1.1.1 p acc.1.2 in
    (t.1.1, acc.1.1.2 ++ t.1.2, t.2, acc.2 ++ [:: p])) 
  (state, sent, time, prev_packs) packs.

Definition decoder_all_steps (received: list fec_packet_act) :
  (list block * list packet) :=
  (decoder_multiple_steps nil received nil nil 0).1.1.

(*Now we want to prove some invariants*)

(*The condition on the received list: suppose two packets are in 
  the same block. Then the sequence numbers of their first occurrence
  in the received list are separated by at most k + h + 2d for some d *)

Variable k: nat.
Variable h : nat.
(*The displacement bound*)
Variable d: nat.

Definition bounded_reorder_list (rec: list fec_packet_act):=
  forall (p1 p2: fec_packet_act),
  p1 \in rec ->
  p2 \in rec ->
  fd_blockId p1 = fd_blockId p2 ->
  (nat_abs_diff (u_seqNum rec p1) (u_seqNum rec p2) <= (k + h) + 2 * d)%N.
  
(*Then, we need the bound on duplication*)
Variable dup : nat.

(*The big one: the time always equals the number of unique packets
  seen so far*)

Lemma time_counts_packets_one: forall (prev_packs : list fec_packet_act)
  (curr: fec_packet_act)
  (state: list block) (time: Z),
  (*From bound on reordering*)
  bounded_reorder_list (prev_packs ++ [:: curr]) ->
  (*Bound on duplicates*)
  duplicates_bounded (prev_packs ++ [:: curr]) fec_packet_act_inhab dup ->
  (*TODO: need conditions on how blocks relate to prev_packs*)
  (*Then, the time is always the number of unique packets seen so far*)
  time = Z.of_nat (size (undup_fst prev_packs)) ->
  (decoder_one_step state curr time).2 = 
    Z.of_nat (size (undup_fst (prev_packs ++ [:: curr]))).
Proof.
  (*TODO:*)

(*hmm lets think about this: need to know about the whole list*)
(*what about: ALSO take as input the previous packets*)
(*then in the whole one, we give nil*)

  (*need to know that the block contain all packets seen in that*)


Definition decoder_all_steps' (received: list fec_packet_act): 
  (list block * list packet * Z) :=
  foldl (fun (acc: list block * list packet * Z) (x: fec_packet_act))


  foldl (fun (acc: list block * list packet * Z) (x: fec_packet_act * Z) =>
    let t := update_dec_state' acc.1 x.1 x.2 in
    (t.1, acc.2 ++ t.2)) (nil, nil) (received, 0) (combine received times).


Definition update_dec_state' (blocks: list block) (curr: fec_packet_act) (time: Z) :
    (list block * list packet * Z) :=
    match blocks with
    | nil => let t := create_block_with_packet_black curr time in 
        ([:: t.1], t.2, time + 1)
    | bl :: tl => 
    let currBlock := Znth (Zlength blocks - 1) blocks in
    let currSeq := fd_blockId curr in
    if Int.eq currSeq (blk_id currBlock) then
      let b := check_block_for_dup currBlock curr in
      let t := add_packet_to_block_black curr currBlock in
      (upd_Znth (Zlength blocks - 1) blocks t.1, t.2, 
      if b then time + 1 else time)
    else if Int.lt (blk_id currBlock) currSeq then 
      let t := create_block_with_packet_black curr time in 
        (blocks ++ [:: t.1], t.2, time + 1)
    else
      (*here we have to deal with timeouts*)
      update_past_blocks (sublist 0 (Zlength blocks - 1) blocks) curr time
  end.

(**)


Fixpoint update_past_blocks (blocks: list block) (curr: fec_packet_act) (time: Z) :
  (list block * list packet) :=
  match blocks with
  | bl :: tl =>
    if (Z.ltb (black_time bl) time) && int_le (fd_blockId curr) (blk_id bl) then
      (tl, if fd_isParity curr then nil else [p_packet curr])
    else if Int.lt (fd_blockId curr) (blk_id bl) then
      let t := create_block_with_packet_black curr time in
      (t.1 :: blocks, t.2)
    else if Int.eq (fd_blockId curr) (blk_id bl) then
      let t := add_packet_to_block_black curr bl in
      (t.1 :: tl, t.2)
    else
      let t := update_past_blocks tl curr time in
      (bl :: t.1, t.2)
  | [::] => (*not sure we can reach here - should prove*)
      (nil,  if fd_isParity curr then nil else [p_packet curr])
  end. 

(*We cannot build the blocks in 1 go since we must take into account timeouts. Instead, we build it up
  incrementally*)
Definition update_dec_state (blocks: list block) (curr: fec_packet_act) (time : Z) : 
  (list block * list packet) :=
  match blocks with
  | nil => let t := create_block_with_packet_black curr time in ([t.1], t.2)
  | bl :: tl => 
    let currBlock := Znth (Zlength blocks - 1) blocks in
    let currSeq := fd_blockId curr in
    if Int.eq currSeq (blk_id currBlock) then
      let t := add_packet_to_block_black curr currBlock in
      (upd_Znth (Zlength blocks - 1) blocks t.1, t.2)
    else if Int.lt (blk_id currBlock) currSeq then 
      let t := create_block_with_packet_black curr time in (blocks ++ [t.1], t.2)
    else
      (*here we have to deal with timeouts*)
      update_past_blocks (sublist 0 (Zlength blocks - 1) blocks) curr time
  end.

(*Versions without changing params or timeouts*)

Section Simple.

Variable k : Z.
Variable h : Z.
Variable Hkbound: 0 < k <= fec_n - 1 - fec_max_h.
Variable Hhbound: 0 < h <= fec_max_h.

Definition rse_encode_gen_nochange (blocks: seq block) (currBlock: option block) (curr: packet) :=
  match currBlock with
  | Some b => 
      let t := encode_exist curr b in (t.1.1 ++ blocks, t.1.2, t.2)
  | None => 
      let t := encode_new curr k h in (t.1.1 ++ blocks, t.1.2, t.2)
  end.

Definition rse_encode_concat_nochange (orig: seq packet) : list block * option block * list (list fec_packet_act) :=
  foldl (fun acc x =>
    let t := rse_encode_gen_nochange acc.1.1 acc.1.2 x in
    (t.1.1, t.1.2, acc.2 ++ [:: t.2])) (nil, None, nil) orig.
(*can easily get rse_encode_all_nochange from this if we need it*)

End Simple.
*)