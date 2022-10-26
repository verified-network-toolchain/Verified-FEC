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

From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.

(*Here we provide the encoder and (updated) decoder functional models,
  in several different forms. Later, we prove results that differ
  based on the assumptions used*)

Section UpdateDecoder.


(*Now we prove that all blocks are well-formed*)

(*Plan should be - combine files, make this decoder, fix proofs there,
  get results for generic decoder and generic packet streams,
  then do this one - otherwise, too much duplicated effort*)

Definition packet_in_block (p: fec_packet_act) (b: block) :=
  (Some p) \in (data_packets b ++ parity_packets b).

(*all packets in blocks in received list*)
Lemma decoder_one_step_recvd: forall blocks curr time prev,
  (forall p b, b \in blocks -> packet_in_block p b ->
    p \in prev) ->
  (forall p b, b \in (decoder_one_step_gen blocks curr time).1.1 ->
    packet_in_block p b ->
    p \in (prev ++ [:: curr])).
Proof.
  move => blocks curr time prev Hrec p b.
  rewrite /decoder_one_step_gen mem_filter => /andP[_ ].
  move: Hrec.
  elim: blocks => [//= _ | bhd btl /= Hrec IH].
  - case: (proj_sumbool (Z.eq_dec (fd_k curr) 1)); 
    rewrite in_cons orbF => /eqP Hb; rewrite Hb.
    + rewrite /create_block_with_fec_packet/packet_in_block/=. Search create_block_with_fec_packet.
  rewrite /update_dec_state_gen.

(*TODO: prove stuff about wf blocks*)

End GenDecode.

      
      
      
      rewrite /add_packet_to_block_black/=. Search black_time.
      
      by []. f_equal. 
      by rewrite !catA.
    
    
    apply Hcreate in Hblks. case

  rewrite /decoder_one_step/=.
  (*Not sure on order I have to do these things: first, let's tr*)



Definition decoder_one_step (blocks: list block) curr time :
  list block * list packet * Z :=
  let t := update_dec_state' blocks curr time in
  let blks := process_timeouts t.1.1 t.2 in
  (blks, t.1.2, t.2). 




  ((*All packets that arrived within time interval are in blocks*)
  (*See how to do this one*)
    forall p l1 l2, prev = l1 ++ [:: p] ++ l2 ->
      (forall p, fd_blockId p )
    )
    
    In p (data_packets b ++ parity_packets b) /\
    (*TODO: do we need *)

    
  

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