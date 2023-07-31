(*A Consumer that does arithmetic on machine-length integers, not nats*)
(*Future: should provide a version with some efficiency/speedups closer
  to C code*)
(*Here, we prove that under certain generous conditions of the
  input packet stream, this is equivalent to the idealized decoder.*)
Require Export DecoderTimeouts.
Require Export SeqCmp.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Module S64:=SeqCmp I64.
Module S32:=SeqCmp I32.

Section Machine.


Definition create_block_with_fec_packet_m (p: fpacket) (time : Z) : 
  block :=
  let k := fd_k p in
  let h := fd_h p in
  let allPackets := upd_Znth 
    (Int.unsigned (Int.repr (Z.of_nat (fd_blockIndex p)))) 
    (zseq (k + h) None) (Some p) in
  mk_blk (fd_blockId p) (sublist 0 k allPackets) 
    (sublist k (k+h) allPackets) k h false time.

Lemma create_m_eq (p: fpacket) (time: Z) :
  (Z.of_nat (fd_blockIndex p) <= Int.max_unsigned) ->
  create_block_with_fec_packet_m p time =
  create_block_with_fec_packet p time.
Proof.
  move=> Hidx. 
  rewrite /create_block_with_fec_packet_m/create_block_with_fec_packet.
  by rewrite Int.unsigned_repr; try rep_lia.
Qed.

Definition create_block_with_packet_black_m (p: fpacket) (time: Z) : block * list packet :=
  let new_block := create_block_with_fec_packet_m p time in
  let packets  := (if (fd_isParity p) then nil else 
    [:: p_packet p ]) ++
    (if Int.eq (Int.repr (fd_k p)) Int.one then 
      (decode_block new_block) else nil) in
  let marked_block := if Int.eq (Int.repr (fd_k p)) Int.one then 
    new_block <| black_complete := true |> else new_block in
  (marked_block, packets).

Lemma create_black_m_eq (p: fpacket) (time: Z) : 
  (Z.of_nat (fd_blockIndex p) <= Int.max_unsigned) ->
  (0 <= fd_k p <= Int.max_unsigned) ->
  create_block_with_packet_black_m p time =
  create_block_with_packet_black p time.
Proof.
  move=> Hidx Hk.
  rewrite /create_block_with_packet_black_m
    /create_block_with_packet_black.
  rewrite /Int.eq Int.unsigned_repr=>[|//].
  rewrite Int.unsigned_one /zeq.
  by case: Z.eq_dec=> [Heq/=| Hneq/=];
  rewrite create_m_eq.
Qed.

(*2. add packet to block*)
Definition add_fec_packet_to_block_m (p: fpacket) (b: block) : block :=
  let new_packets := upd_Znth 
    (Int.unsigned (Int.repr (Z.of_nat (fd_blockIndex p)) ))
    (data_packets b ++ parity_packets b) (Some p) in
  b <| data_packets := sublist 0 (blk_k b) new_packets |> 
      <| parity_packets := sublist (blk_k b) (blk_k b + blk_h b) new_packets |>.

Lemma add_m_eq (p: fpacket) (b: block) :
  (Z.of_nat (fd_blockIndex p) <= Int.max_unsigned) ->
  add_fec_packet_to_block_m p b =
  add_fec_packet_to_block p b.
Proof.
  move=> Hidx. rewrite /add_fec_packet_to_block_m/add_fec_packet_to_block.
  by rewrite !Int.unsigned_repr //; rep_lia.
Qed.

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

Lemma add_black_m_eq (p: fpacket) (b: block) :
  (Z.of_nat (fd_blockIndex p) <= Int.max_unsigned) ->
  add_packet_to_block_black_m p b =
  add_packet_to_block_black p b.
Proof.
  move=> Hidx.
  rewrite /add_packet_to_block_black_m/add_packet_to_block_black.
  by rewrite !add_m_eq.
Qed.

Lemma add_black_m_id (curr: fpacket) (b: block) :
  blk_id (add_packet_to_block_black_m curr b).1 =
  blk_id b.
Proof.
  rewrite /add_packet_to_block_black_m.
  case: (black_complete b)=>//=.
  by case: (recoverable (add_fec_packet_to_block_m curr b)).
Qed.

Variable threshold : int.

(*still store Z, just do comparisons on Int.repr time*)
(*The check to update the time*)
Fixpoint upd_time_m (time: Z) (curr: fpacket) (blocks: list block) :
  Z := 
  match blocks with
  | nil => time + 1
  | bl :: tl =>
    let currSeq := Int64.repr (Z.of_nat (fd_blockId curr)) in
    let blkid := Int64.repr (Z.of_nat (blk_id bl)) in
    if S64.seq_eq currSeq blkid then
      if (block_notin_packet bl curr) 
      then time + 1
      else time
    else if S64.seq_lt currSeq blkid
      then time + 1
    else upd_time_m time curr tl
  end.

(*Timeouts if threshold exceeded - we again need sequence number
  comparison because times may wrap around*)
Definition not_timed_out_m: Z -> block -> bool := fun currTime =>
  (fun b => S32.seq_leq (Int.repr currTime)
    (Int.add (Int.repr(black_time b)) threshold)).

Fixpoint update_dec_state_m (blocks: list block) (curr: fpacket)
  (time: Z) : list block * list packet:=
match blocks with
| nil => let t := create_block_with_packet_black curr time in 
    ([:: t.1], t.2)
| bl :: tl =>
  let currSeq := Int64.repr (Z.of_nat (fd_blockId curr)) in
  let blkid := Int64.repr (Z.of_nat (blk_id bl)) in
  if S64.seq_eq currSeq blkid then
    let t := add_packet_to_block_black_m curr bl in
    (t.1 :: tl, t.2)
    else if S64.seq_lt currSeq blkid then
    let t := create_block_with_packet_black curr time in 
      (t.1 :: blocks, t.2)
  else 
    let t := update_dec_state_m tl curr time
    in (bl :: t.1, t.2)
end.

Definition decoder_one_step_m (blocks: list block) curr (time : Z) :
list block * list packet * Z :=
(*First, we process timeouts; this covers the case when the packet
  which makes the block timeout is the kth packet; we should not
  recover this block (it makes our invariants much harder).*)
let tm := upd_time_m time curr blocks in
let t := update_dec_state_m blocks curr tm in
let blks := filter (not_timed_out_m tm) t.1 in
(blks, t.2, tm).


Definition decoder_multiple_steps_m
(prev_packs packs: list fpacket)
(state: list block) (sent: list packet) (time: Z) :
list block * list packet * Z * list fpacket :=
foldl (fun (acc: list block * list packet * Z * list fpacket) 
  (p: fpacket) =>
  let t := decoder_one_step_m acc.1.1.1 p acc.1.2 in
  (t.1.1, acc.1.1.2 ++ t.1.2, t.2, acc.2 ++ [:: p])) 
(state, sent, time, prev_packs) packs.

Definition decoder_all_steps_m (received: list fpacket) :
(list block * list packet * Z) :=
(decoder_multiple_steps_m nil received nil nil 0).1.

Lemma decoder_multiple_steps_m_rewrite: forall prev packs blks sent time,
  decoder_multiple_steps_m prev packs blks sent time =
  (foldl (fun (acc: seq block * seq packet * Z * seq fpacket) (p: fpacket) =>
    let t := decoder_one_step_m acc.1.1.1 p acc.1.2 in
    (t.1.1, acc.1.1.2 ++ t.1.2, t.2, acc.2 ++ [:: p]))
    (blks, sent, time, prev) packs).
Proof.
  by [].
Qed.

(*Now we have to prove equivalence. This means we have to show that
  every comparison between unsigned ints occurs between those
  representing a nat within 2^31 of each other, and likewise for
  longs.*)

(*To do this, we use an assumption that all packet sequence
  numbers are between 0 and 2^63-1, and they are unique. This is
  not at all a restrictive assumption - if we could send
  10^9 packets per second (already at least 2-3 orders of
  magnitude above current speeds), it would take us nearly
  300 years to run out of sequence numbers. This also assumes
  we send no parity packets and have no other traffic on the
  network.*)
Section Equiv.

Local Open Scope nat_scope.

(*We also assume that the threshold is less than 2^30. This is also
  safe: if each block was 100 bytes (it can be much larger depending on
  packet sizes), a larger threshold would require storing at least
  100 GB *)

Variable thresh_bound: 
  (Int.unsigned threshold < Int.half_modulus / 2)%Z.

(*Our invariant:*)
Definition dec_machine_invar (blks: seq block)
  (time: Z) : Prop :=
  (*All black times are no more than [threshold] behind the
    current time*)
  (forall (b: block), b \in blks ->
    (0 <= time - (black_time b) <= Int.unsigned threshold)%Z) /\
  (*All block ids are smaller than 2^61-1*)
  (forall (b: block), b \in blks -> 
    Z.of_nat (blk_id b) < Int64.half_modulus)%Z.

(*First, show this invariant implies equality*)

(*Helpful here*)
Lemma znat_eq (n1 n2 : nat) :
  Z.eqb (Z.of_nat n1) (Z.of_nat n2) = (n1 == n2).
Proof.
  case: (Z.of_nat n1 =? Z.of_nat n2)%Z /Z.eqb_spec => [Heq | Hneq];
  symmetry; apply /eqP; lia.
Qed. 

Lemma znat_lt (n1 n2: nat):
  Z.ltb (Z.of_nat n1) (Z.of_nat n2) = (n1 < n2).
Proof.
  case: ((Z.of_nat n1 <? Z.of_nat n2)%Z) /Z.ltb_spec => [Hlt | Hge];
  symmetry; apply /ltP; lia.
Qed.

(*Dont need anymore, but would will need in VST proofs*)
Lemma int_add_one (z: Z):
  Int.add (Int.repr z) Int.one = Int.repr (z + 1).
Proof.
  apply Endian.int_unsigned_inj.
  by rewrite /Int.add/Int.one !Int.unsigned_repr_eq -Zplus_mod.
Qed.

Lemma not_timed_out_m_add (time: Z) (curr: fpacket) (b: block) :
  not_timed_out_m time (add_packet_to_block_black curr b).1 =
  not_timed_out_m time b.
Proof.
  by rewrite /not_timed_out_m add_black_time.
Qed.

Lemma not_timed_out_add (thresh: Z) (time: Z) (curr: fpacket) (b: block):
  not_timed_out thresh time (add_packet_to_block_black curr b).1 =
  not_timed_out thresh time b.
Proof.
  by rewrite /not_timed_out add_black_time.
Qed.

Opaque create_block_with_packet_black.

Lemma in_prop_tl: forall {A: eqType} (h: A) (s: seq A) (P: A -> Prop),
  (forall x, x \in (h :: s) -> P x) ->
  (forall x, x \in s -> P x).
Proof.
  move => A s h p Hall x Hxin. apply Hall. by rewrite in_cons Hxin orbT.
Qed.

(*Equality for one step, assuming invariant*)
Lemma decoder_one_step_m_eq (blks: seq block) (time: Z) 
  (curr: fpacket) :
  (Z.of_nat (fd_blockId curr) < Int64.half_modulus)%Z ->
  (Z.of_nat (fd_blockIndex curr) <= Int.max_unsigned)%Z ->
  (0 <= fd_k curr < Int.modulus)%Z ->
  dec_machine_invar blks time ->
  decoder_one_step_m blks curr time =
  decoder_one_step (Int.unsigned threshold) blks curr time.
Proof.
  move=> Hcurr Hidx Hkbound [Hthresh Hallid].
  rewrite /decoder_one_step_m/decoder_one_step/decoder_one_step_gen/=.
  have Htime: upd_time_m time curr blks = 
    upd_time time curr blks. {
    rewrite {Hthresh}. move: Hallid. elim: blks => [_ //=|b btl IH Hallid /=].
      have Hbound: (z_abs_diff 
      (Z.of_nat (fd_blockId curr)) (Z.of_nat (blk_id b)) <
        Int64.half_modulus)%Z. {
        (*Easy: both are smaller than half_modulus*)
        rewrite /z_abs_diff.
        move: Hallid => /(_ _ (mem_head _ _)). rep_lia.
      }
      rewrite S64.seq_eq_eq. 
      + rewrite znat_eq.
        case: (fd_blockId curr == blk_id b) /eqP => Hbcurr.
        * by case: (block_notin_packet b curr).
        * rewrite S64.seq_lt_lt // znat_lt.
          case: (fd_blockId curr < blk_id b) =>//. 
          apply IH => b' Hinb'. apply Hallid. 
          by rewrite in_cons Hinb' orbT.
      + have: (Int64.half_modulus < I64.modulus)%Z by []. lia.
  }
  f_equal=>//.
  rewrite Htime.
  have Hblkstime: forall b, b \in blks ->
    not_timed_out_m (upd_time time curr blks) b =
    not_timed_out (Int.unsigned threshold) (upd_time time curr blks) b.
  {
    move=> b Hinb.
    rewrite /not_timed_out_m/not_timed_out.
    rewrite -S32.seq_leq_leq.
    - f_equal.
      rewrite /Int.add.
      apply Endian.int_unsigned_inj.
      rewrite !Int.unsigned_repr_eq.
      by rewrite Zplus_mod_idemp_l.
    - (*Here, use fact that upd_time increases by at most 1
        and that before, all were within threshold. So here,
        should be ok*)
        have:=(upd_time_bound time curr blks).
        rewrite /z_abs_diff.
        move: Hthresh => /(_ b Hinb).
        have->: I32.half_modulus = Int.half_modulus by [].
        move: thresh_bound=>/=. rep_lia.
    }
    move: Hblkstime.
    move: (upd_time time curr blks) => tm.
    rewrite {Htime}.
    move: Hthresh Hallid.
    have Hadd: Int.add (Int.repr tm) threshold =
    I32.repr (tm + Int.unsigned threshold). {
      rewrite /Int.add.
      apply Endian.int_unsigned_inj.
      rewrite !Int.unsigned_repr_eq.
      by rewrite Zplus_mod_idemp_l.
    }
    have Htm: (z_abs_diff tm (tm + Int.unsigned threshold) < I32.half_modulus)%Z. {
      rewrite /z_abs_diff.
      have->:(Z.abs (tm - (tm + Int.unsigned threshold)) =
        Int.unsigned threshold) by rep_lia.
      have: (Int.half_modulus / 2 < I32.half_modulus)%Z by [].
      lia.
    }
    elim: blks=>[_ _ _ //| b btl IH Hthresh Hallid /= Hbtime].
    - f_equal. rewrite /not_timed_out/not_timed_out_m /update_dec_state_m.
      by rewrite /= create_black_time Hadd S32.seq_leq_leq //. 
    - have Hbound: (z_abs_diff 
      (Z.of_nat (fd_blockId curr)) (Z.of_nat (blk_id b)) <
        Int64.half_modulus)%Z. {
        (*Easy: both are smaller than half_modulus*)
        rewrite /z_abs_diff.
        move: Hallid => /(_ _ (mem_head _ _)). rep_lia.
      }
      rewrite S64.seq_eq_eq; last first.
        have: (Int64.half_modulus < I64.modulus)%Z by []. lia.
      rewrite znat_eq.
      have Htl: [seq x <- btl | not_timed_out_m tm x] =
      [seq x <- btl | not_timed_out (Int.unsigned threshold) tm x] by
        apply eq_in_filter => b' Hinb'; apply Hbtime;
        rewrite in_cons Hinb' orbT.
      case: (fd_blockId curr == blk_id b) /eqP => [Heq|Hneq].
      + rewrite add_black_m_eq //. simpl filter. 
        by rewrite not_timed_out_m_add not_timed_out_add 
          -(Hbtime b (mem_head _ _)) Htl.
      + rewrite S64.seq_lt_lt // znat_lt.
        case: (fd_blockId curr < blk_id b) =>//=.
        * by rewrite {1}/not_timed_out_m 
          {1}/not_timed_out !create_black_time Hadd
          S32.seq_leq_leq // (Hbtime b (mem_head _ _)) Htl.
        * move: IH => /(_ (in_prop_tl Hthresh) (in_prop_tl Hallid) 
          (in_prop_tl Hbtime)) [] ->->.
          by rewrite (Hbtime _ (mem_head _ _)).
Qed.

(*Now, we have to prove preservation of the invariant.
  Here, we prove for the non-machine version, then use
  the previous lemma to show the invariant for the machine one*)
Lemma decoder_m_invar_one_step (blks: seq block) (time: Z) 
  (curr: fpacket) :
  (Z.of_nat (fd_blockId curr) < Int64.half_modulus)%Z ->
  dec_machine_invar blks time ->
  dec_machine_invar (decoder_one_step (Int.unsigned threshold) 
    blks curr time).1.1
    (decoder_one_step (Int.unsigned threshold) blks curr time).2.
Proof.
  rewrite /dec_machine_invar => Hid [Hthresh Hallid].
  rewrite /decoder_one_step/=.
  split.
  - move=> b.
    rewrite mem_filter /not_timed_out =>/andP[/Z.leb_spec0 Htime].
    move=> Hinb.
    split; try lia.
    move: Hinb Hthresh.
    clear.
    elim: blks => [//=| bhd btl IH /=].
    + rewrite in_cons orbF => /eqP ->.
      rewrite create_black_time. lia.
    + move=> Hinb Hthresh; move: Hinb.
      have Hhd:=(Hthresh bhd (mem_head _ _)).
      have Htl:=(in_prop_tl Hthresh).
      case: (fd_blockId curr == blk_id bhd).
      * rewrite in_cons => /orP[/eqP -> | Hinb].
        -- rewrite add_black_time. 
          by case: (block_notin_packet bhd curr); lia.
        -- by case: (block_notin_packet bhd curr);
          move: Htl => /(_ _ Hinb); lia.
      * case: (fd_blockId curr < blk_id bhd).
        -- rewrite in_cons => /orP[/eqP -> | Hinb].
          ++ rewrite create_black_time. lia.
          ++ move: Hthresh => /(_ _ Hinb); lia.
        -- rewrite in_cons => /orP[/eqP -> | Hinb].
          ++ have:=(upd_time_bound time curr btl).
            lia.
          ++ by apply IH in Hinb.
  - (*This invariant is a bit easier*)
    move=> b. rewrite mem_filter => /andP[_]. move: b.
    move: Hallid. clear -Hid. elim: blks => [//= _ b | bhd btl IH /= Hallid b].
    + rewrite in_cons orbF=> /eqP ->.
      by rewrite create_black_id.
    + have Hhd:=(Hallid _ (mem_head _ _)).
      have Htl:=(in_prop_tl Hallid).
      case: (fd_blockId curr == blk_id bhd).
      * rewrite in_cons => /orP[/eqP -> | Hinb].
        -- by rewrite add_black_id.
        -- by apply Htl.
      * case: (fd_blockId curr < blk_id bhd).
        -- rewrite in_cons => /orP[/eqP -> | Hinb].
          ++ by rewrite create_black_id.
          ++ by apply Hallid. 
        -- rewrite in_cons => /orP[/eqP -> // | Hinb].
          by apply IH.
Qed.

(*Put both lemmas together*)
Lemma decoder_multiple_steps_m_eq (blks: seq block) (time: Z)
  (prev_pkts pkts: seq fpacket) (sent: seq packet) :
  (forall (p: fpacket), p \in prev_pkts ++ pkts -> 
    (Z.of_nat (fd_blockId p) < Int64.half_modulus)%Z /\
    (Z.of_nat (fd_blockIndex p) <= Int.max_unsigned)%Z /\
    (0 <= fd_k p < Int.modulus)%Z) ->
  dec_machine_invar blks time ->
  decoder_multiple_steps_m prev_pkts pkts blks sent time =
  decoder_multiple_steps (Int.unsigned threshold) 
    prev_pkts pkts blks sent time.
Proof.
  rewrite decoder_multiple_steps_rewrite
  decoder_multiple_steps_m_rewrite.
  move: blks time prev_pkts sent.
  elim: pkts => 
    [//|curr pkts IH blks time prev sent Hbounds Hinvar].
  Opaque decoder_one_step decoder_one_step_m.
  rewrite /= IH.
  - by rewrite decoder_one_step_m_eq //; apply Hbounds;
    rewrite mem_cat mem_head orbT.
  - rewrite -catA. by apply Hbounds.
  - rewrite decoder_one_step_m_eq //; try (by apply Hbounds;
    rewrite mem_cat mem_head orbT).
    apply decoder_m_invar_one_step=> //.
    apply Hbounds. by rewrite mem_cat mem_head orbT.
Qed.

(*And therefore, if all indicies, ids, and k values are 
  bounded appropriately, then the machine-length version is
  equal to the infinte precision decoder.*)
Corollary decoder_all_steps_m_eq (pkts: seq fpacket) :
  (forall (p: fpacket), p \in pkts -> 
  (Z.of_nat (fd_blockId p) < Int64.half_modulus)%Z /\
  (Z.of_nat (fd_blockIndex p) <= Int.max_unsigned)%Z /\
  (0 <= fd_k p < Int.modulus)%Z) ->
  decoder_all_steps_m pkts =
  decoder_all_steps (Int.unsigned threshold) pkts.
Proof.
  move=> Hbounds.
  by rewrite /decoder_all_steps_m decoder_multiple_steps_m_eq.
Qed.

End Equiv.

Section AllDat.

(*One unequivocal spec we can give of the machine-length decoder:
  all data packets are outputted*)
Lemma all_data_outputted_one_m (blks: seq block) (time: Z) 
  (curr: fpacket):
  fd_isParity curr = false ->
  p_packet curr \in (decoder_one_step_m blks curr time).1.2.
Proof.
  move=> Hdat.
  rewrite /decoder_one_step_m/=.
  move: (upd_time_m time curr blks)=> tm'.
  elim blks => [//= | b bs /= IH].
  - by rewrite Hdat mem_cat mem_head.
  - case: (S64.seq_eq (Int64.repr (Z.of_nat (fd_blockId curr)))
      (Int64.repr (Z.of_nat (blk_id b))))=>/=.
    + rewrite /add_packet_to_block_black_m Hdat/=.
      case: (black_complete b) =>/=; by rewrite mem_head.
    + case: (S64.seq_lt (Int64.repr (Z.of_nat (fd_blockId curr)))
      (Int64.repr (Z.of_nat (blk_id b))))=>//=.
      by rewrite Hdat mem_head.
Qed.

Lemma all_data_outputted_multiple_m (blks: seq block) (time: Z)
  (prev_pkts pkts: seq fpacket) (sent: seq packet):
  (forall (p: fpacket), p \in prev_pkts ->
    fd_isParity p = false ->
    p_packet p \in sent) ->
  forall (p: fpacket), p \in  (prev_pkts ++ pkts) ->
    fd_isParity p = false ->
    p_packet p \in 
      (decoder_multiple_steps_m prev_pkts pkts blks sent time).1.1.2.
Proof.
  rewrite decoder_multiple_steps_m_rewrite.
  move: blks time prev_pkts sent.
  elim: pkts => [//= _ _ prev sent Hin p| 
    curr ptl IH blks time prev sent Hinprev p].
  - rewrite cats0. by apply Hin.
  - move=> Hinp Hpar. 
    Opaque decoder_one_step_m.
    rewrite /=. apply IH =>//; last by rewrite -catA.
    move=> p'. rewrite mem_cat in_cons orbF => /orP[Hinp' Hpar' | 
      /eqP -> /= Hpar'].
    + by rewrite mem_cat Hinprev.
    + by rewrite mem_cat all_data_outputted_one_m // orbT.
Qed.

Corollary all_data_outputted_m (pkts: seq fpacket) :
  forall (p: fpacket), p \in pkts ->
  fd_isParity p = false ->
  p_packet p \in 
    (decoder_all_steps_m pkts).1.2.
Proof.
  move=> p Hinp Hpar.
  by apply all_data_outputted_multiple_m.
Qed.

End AllDat.

End Machine.