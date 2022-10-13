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

(*First, we give a generalized version of the decoder, which enables
  us to prove theorems about versions with different (or no) timeout
  mechanism*)
Section GenDecode.

(*We can update the time, in general, by looking at the current time,
  the list of blocks, and the current packet*)
Variable upd_time: Z -> fec_packet_act -> list block -> Z.
Variable not_timeout : block -> bool.

Fixpoint update_dec_state_gen (blocks: list block) (curr: fec_packet_act)
    (time: Z) : list block * list packet:=
  match blocks with
  | nil => let t := create_block_with_packet_black curr time in 
      ([:: t.1], t.2)
  | bl :: tl =>
    let currSeq := fd_blockId curr in
    if Int.eq currSeq (blk_id bl) then
      let t := add_packet_to_block_black curr bl in
      (t.1 :: tl, t.2)
    else if Int.lt currSeq (blk_id bl) then 
      let t := create_block_with_packet_black curr time in 
        (t.1 :: blocks, t.2)
    else update_dec_state_gen tl curr time
  end.

Definition decoder_one_step_gen (blocks: list block) curr time :
  list block * list packet * Z :=
  let t := update_dec_state_gen blocks curr time in
  let tm := upd_time time curr blocks in
  let blks := filter not_timeout t.1 in
  (blks, t.2, tm).

Definition decoder_multiple_steps_gen 
  (prev_packs packs: list fec_packet_act)
  (state: list block) (sent: list packet) (time: Z) :
  list block * list packet * Z * list fec_packet_act :=
  foldl (fun (acc: list block * list packet * Z * list fec_packet_act) 
    (p: fec_packet_act) =>
    let t := decoder_one_step_gen acc.1.1.1 p acc.1.2 in
    (t.1.1, acc.1.1.2 ++ t.1.2, t.2, acc.2 ++ [:: p])) 
  (state, sent, time, prev_packs) packs.

Definition decoder_all_steps_gen (received: list fec_packet_act) :
  (list block * list packet) :=
  (decoder_multiple_steps_gen nil received nil nil 0).1.1.

(*We can prove some general lemmas about any such decoder*)

(*First, prove something about the prev_packets*)
Lemma prev_packets_multiple: forall prev packs state sent time,
  (decoder_multiple_steps_gen prev packs state sent time).2 =
  prev ++ packs.
Proof.
  move=> prev packs. move: prev.
  rewrite /decoder_multiple_steps_gen; elim: packs => 
    [//= prev state sent time | h t /= IH prev packs state time/=].
  by rewrite cats0.
  by rewrite IH -catA.
Qed.

(*A framework for showing facts about the decoder, expressed by invariants*)
Lemma prove_decoder_invariant_multiple 
  (P: list fec_packet_act -> list block -> Z -> Prop) 
  prev_packs state packs sent time:
  (forall blks curr tm prv, P prv blks tm ->
  P (prv ++ [:: curr]) ((decoder_one_step_gen blks curr tm).1.1)
    (decoder_one_step_gen blks curr tm).2) ->
  P prev_packs state time ->
  P ((decoder_multiple_steps_gen prev_packs packs state sent time).2)
    ((decoder_multiple_steps_gen prev_packs packs state sent time).1.1.1)
    ((decoder_multiple_steps_gen prev_packs packs state sent time).1.2).
Proof.
  move=> Hind.
  move: prev_packs state sent time.
  elim: packs => [//= | p1 ptl /= IH prev state sent time Hbase].
  move: IH; rewrite /decoder_multiple_steps_gen/= => IH.
  apply IH.
  apply Hind.
  apply Hbase.
Qed.

Lemma int_lt_trans: forall x y z,
  Int.lt x y ->
  Int.lt y z ->
  Int.lt x z.
Proof.
  move=> x y z. rewrite /Int.lt.
  case Hxy: (zlt (Int.signed x) (Int.signed y)) => // _.
  case Hyz: (zlt (Int.signed y) (Int.signed z)) => // _.
  case Hxz: (zlt (Int.signed x) (Int.signed z)) => //. lia.
Qed.

Lemma int_lt_irrefl: forall x,
  Int.lt x x = false.
Proof.
  move=> x. rewrite /Int.lt.
  case: (zlt (Int.signed x) (Int.signed x)) => //; lia.
Qed.

(*TODO: move*)
Lemma add_packet_to_block_black_id: forall p b,
  blk_id (add_packet_to_block_black p b).1 =
  blk_id b.
Proof.
  move=> p b. rewrite /add_packet_to_block_black.
  case Hcomp: (black_complete b) => //=.
  by case Hrec: (recoverable (add_fec_packet_to_block p b)).
Qed.

(*sortedness*)

Definition blk_order: rel block :=
  (fun x y => Int.lt (blk_id x) (blk_id y)).
(*Should make block IDs nats, do everything in terms of nats*)
Lemma decoder_one_step_sorted: forall blocks curr time,
  sorted blk_order blocks ->
  sorted blk_order
    (decoder_one_step_gen blocks curr time).1.1.
Proof.
  move=> blocks curr time.
  rewrite /blk_order /decoder_one_step_gen/= => Hsort.
  apply sorted_filter.
    move => b1 b2 b3. apply int_lt_trans.
  move: Hsort. elim: blocks => [// | bhd btl /= IH Hpath].
  case Heq: (Int.eq (fd_blockId curr) (blk_id bhd)).
  - rewrite /= {IH}. move: Hpath. case: btl => //= bhd' btl /andP[Hlt Hpath].
    rewrite Hpath andbT. by rewrite add_packet_to_block_black_id.
  - case Hlt: (Int.lt (fd_blockId curr) (blk_id bhd) ).
    + by case Hk1: (proj_sumbool (Z.eq_dec (fd_k curr) 1));
      rewrite /= Hlt Hpath.
    + apply IH. move: Hpath. rewrite {IH}.
      by case: btl => //= hd tl /andP[_ H].
Qed.

(*From this, we get uniqueness for free*)

Lemma decoder_one_step_uniq: forall blocks curr time,
  sorted blk_order blocks ->
  uniq (decoder_one_step_gen blocks curr time).1.1.
Proof.
  move=> blocks curr time Hsort.
  apply sorted_uniq_in with(leT:=blk_order).
  - move => b1 b2 b3 _ _ _. apply int_lt_trans.
  - move=> b1 _. apply int_lt_irrefl.
  - by apply decoder_one_step_sorted.
Qed.

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

(*Now we specialize the decoder for our timeout function*)
Section DecodeTimeouts.

Variable threshold : Z.

(*We will separate out the check for duplicates and the updating for the
analysis (and to prevent us from needing to change everything
from before), though in the code, they are done together. Maybe we will
prove another version that combines it to make the VST proof simpler.*)
(*True if packet not present*)
(*Very inefficient/different from real impl, we will prove that this
is equivalent to a version like the C code, but this is easier for analysis
because we don't need to reason about wf blocks*)
Definition block_notin_packet block packet : bool :=
    (Some packet) \notin (data_packets block ++ parity_packets block).

(*The check to update the time*)
Fixpoint upd_time (time: Z) (curr: fec_packet_act) (blocks: list block) :
  Z := 
  match blocks with
  | nil => time + 1
  | bl :: tl =>
    let currSeq := fd_blockId curr in
    if Int.eq currSeq (blk_id bl) then
      if (block_notin_packet bl curr) then time + 1 else time
    else if Int.lt currSeq (blk_id bl) then time + 1
    else upd_time time curr tl
  end.

(*Timeouts if threshold exceeded*)
Definition is_timed_out: block -> bool :=
  (fun b => ~~ (Z.ltb (black_time b + threshold) (black_time b))).

Definition decoder_one_step :=
  decoder_one_step_gen upd_time is_timed_out.
Definition decoder_multiple_steps:=
  decoder_multiple_steps_gen upd_time is_timed_out.
Definition decoder_all_steps:=
  decoder_all_steps_gen upd_time is_timed_out.

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

(*We need several sets of invariants to prove what we want
  (that under the reordering assumptions, the decoder is equivalent
  to a version with no timeouts)*)

(*TODO: want to change blocks to match this closer
  ie: use nats, not Z or int to packet seqNum and blk_id
  But I need to make sure this is OK - are we able to prove
  that the C code implements the rep version? - need rep
  version of functional model and prove equivalence. For now, just
  keep going*)

(*First, some intermediate, easy results about decoder invariants*)
(*TODO: generalize decoder to prove for *)
Lemma decoder_timeout_blocks_uniq: forall blocks prev time,
  uniq blocks ->
  (decoder_one_step blocks p time).1.1


Lemma decoder_timeout_blocks_sorted:

Lemma decoder_timeout_packets_recvd:



Definition decoder_timeout_invar (blocks: list block) 
  (prev: list fec_packet_act) (time: Z) : Prop :=
  (*The real invariant we want to show (the others, some of
    which are independently useful, are mainly there to enable
    us to prove this one): the time is calculated correctly
    as the number of unique packets to arrive*)
  (time = Z.of_nat (size (undup_fst prev))) /\
  (*For every block, there is a packet that represents the time
    at which the block was created*)
  (forall b, b \in blocks ->
    exists p l1 l2, prev = l1 ++ [:: p] ++ l2 /\
      p \notin l1 /\
      Z.of_nat (size (undup_fst l1)) = (black_time b) (*/\
      Znth (Int.unsigned (fd_blockIndex p)) 
        (data_packets b ++ parity_packets b) = Some p*)) /\
  (*All packets in the block were seen*)
  (forall b p, b \in blocks -> Some p \in (data_packets b ++ parity_packets b) ->
    p \in prev) /\
  (*If a packet arrived but is NOT in a block, there is a packet
    with the same blockIndex that has timed out*)
  (forall (p: fec_packet_act), p \in prev -> 
    ~exists b, (Some p) \in (data_packets b ++ parity_packets b) ->
    exists (p' : fec_packet_act) l1 l2, fd_blockId p' = fd_blockId p /\ 
      prev = l1 ++ [:: p'] ++ l2 /\
      p' \notin l1 /\
      Z.of_nat (size (undup_fst prev)) - 
      Z.of_nat (size (undup_fst l1)) > threshold
  ) /\
  (*The blocks are unique*)
  uniq blocks /\
  (*All packets are in the correct block*)
  (forall (p: fec_packet_act) b, 
  (Some p) \in (data_packets b ++ parity_packets b) ->
  fd_blockId p = blk_id b).

(*The condition we need on the list*)
Definition reorder_dup_cond (l: list fec_packet_act) :=
  bounded_reorder_list l /\
  duplicates_bounded l fec_packet_act_inhab dup /\
  threshold >= Z.of_nat (k + h + 2 * d + dup).

(*Lemmas: (TODO: move)*)
Lemma in_process_timeouts: forall blks time b,
  b \in (process_timeouts blks time) ->
  b \in blks.
Proof.
  move =>blks time b.
  by rewrite /process_timeouts mem_filter => /andP[_ H].
Qed.

Lemma in_update_dec_state: forall blks p time b,
  b \in (update_dec_state' blks p time).1.1 ->
  b \in blks \/
  (exists b', b' \in blks /\ b = (add_packet_to_block_black p b').1) \/
  b = (create_block_with_packet_black p time).1.
Proof.
  move => blks p time b. elim: blks => [// | bhd btl /= IH].
  - rewrite /update_dec_state'/= in_cons orbF => /eqP Hb.
    right. by right.
  - case Heq: (Int.eq (fd_blockId p) (blk_id bhd)) => /=.
    + rewrite in_cons => /orP[/eqP Hb | Hinb].
      * right. left. exists bhd. by rewrite in_cons eq_refl.
      * left. by rewrite in_cons Hinb orbT.
    + case Hlt: (Int.lt (blk_id bhd) (fd_blockId p)).
      * rewrite in_cons mem_cat => /orP[/eqP Hbhd | /orP[Hbtl | Hbnew]].
        -- left. by rewrite in_cons Hbhd eq_refl.
        -- left. by rewrite in_cons Hbtl orbT.
        -- right. right. by move: Hbnew; rewrite in_cons orbF => /eqP.
      * move => Hb.
        move: IH => /(_ Hb) => [[Hbtl | [[b' [Hb' Hbb']] | Hbnew]]].
        -- left. by rewrite in_cons Hbtl orbT.
        -- right. left. exists b'. by rewrite in_cons Hb' orbT.
        -- right. by right.
Qed.

Print wf_packet_stream.

Lemma add_packet_to_block_black_time: forall p b,
  black_time (add_packet_to_block_black p b).1 =
  black_time b.
Proof.
  move=>p b. rewrite /add_packet_to_block_black.
  case Hcomp: (black_complete b) => //=.
  by case Hrec: (recoverable (add_fec_packet_to_block p b)).
Qed.

(*TODO: can we improve the handling of blocks and indices?
  This is so painful - think about this (maybe not, already did a lot)
  maybe we have results about this*)
  (*
Lemma add_packet_to_block_black_Znth: forall (p p': fec_packet_act) b,
  (fd_blockIndex p' == fd_blockIndex p) = (p == p') ->
  Znth (Int.unsigned (fd_blockIndex p'))
  (data_packets b ++ parity_packets b) = Some p' ->
  Znth (Int.unsigned (fd_blockIndex p'))
    ((data_packets (add_packet_to_block_black p b).1) ++
    (parity_packets (add_packet_to_block_black p b).1)) =
  if fd_blockIndex p' == fd_blockIndex p then Some p else Some p'.
Proof.
  move => p p' b Heq Hnth. rewrite /add_packet_to_block_black/=.
  case Hcomp: (black_complete b) => //=.
  - rewrite Hnth Heq. by case: (p == p') /eqP => [->| //].
  - case Hrec: (recoverable (add_fec_packet_to_block p b)) => /=.
    +*)


(*We prove that this invariant is preserved. This is the key
  structural lemma to characterize the timeout behavior*)
Lemma decoder_timeout_invar_preserved_one: forall blocks prev time p,
  wf_packet_stream (prev ++ [:: p]) ->
  reorder_dup_cond (prev ++ [:: p]) ->
  decoder_timeout_invar blocks prev time ->
  decoder_timeout_invar (decoder_one_step blocks p time).1.1
    (prev ++ [:: p]) (decoder_one_step blocks p time).2.
Proof.
  move=>blocks prev time p Hwf. 
  rewrite /reorder_dup_cond/bounded_reorder_list/duplicates_bounded =>
  [[Hreord [Hdups Hthresh]]].
  rewrite /decoder_timeout_invar => 
    [[Hcreate [Htime [Hprevin Hprevnotin]]]].
  (*For now, do each part individually - see*)
  repeat split.
  - move => b. rewrite /decoder_one_step/= => Hb.
    apply in_process_timeouts in Hb.
    apply in_update_dec_state in Hb.
    case: Hb => [Hblks | [[b' [Hb' Hbb']] | Hbnew]].
    + (*easy case: from IH*) move: Hcreate => /(_ _ Hblks) => 
      [[p' [l1 [l2 [Hprev [Hnotin [Hsz Hnth]]]]]]].
      exists p'. exists l1. exists (l2 ++ [:: p]). repeat split => //.
      rewrite Hprev. by rewrite /= -!catA.
    + (*add case: mostly straightforward because 1st packet not changing,
      just need to show we don't overwrite the packet*)
      move: Hcreate => /(_ _ Hb') => 
      [[p' [l1 [l2 [Hprev [Hnotin [Hsz Hnth]]]]]]].
      exists p'. exists l1. exists (l2 ++ [:: p]).
      repeat split => //.
      * by rewrite Hprev /= -!catA.
      * subst. by rewrite add_packet_to_block_black_time.
      * subst => /=.
      
      
      
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