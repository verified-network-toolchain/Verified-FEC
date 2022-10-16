Require Import AbstractEncoderDecoder.
Require Import DecoderGeneric.
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
    isNone (Znth (Z.of_nat (fd_blockIndex packet)) 
      (data_packets block ++ parity_packets block)).

(*The check to update the time*)
Fixpoint upd_time (time: Z) (curr: fpacket) (blocks: list block) :
  Z := 
  match blocks with
  | nil => time + 1
  | bl :: tl =>
    let currSeq := fd_blockId curr in
    if currSeq ==  (blk_id bl) then
      if (block_notin_packet bl curr) then time + 1 else time
    else if (currSeq < (blk_id bl))%N then time + 1
    else upd_time time curr tl
  end.

(*Timeouts if threshold exceeded*)
Definition not_timed_out: Z -> block -> bool := fun currTime =>
  (fun b => (Z.ltb (black_time b + threshold) currTime)).

Definition decoder_one_step :=
  decoder_one_step_gen upd_time not_timed_out.
Definition decoder_multiple_steps:=
  decoder_multiple_steps_gen upd_time not_timed_out.
Definition decoder_all_steps:=
  decoder_all_steps_gen upd_time not_timed_out.

(*Now we want to prove some invariants*)

(*The condition on the received list: suppose two packets are in 
  the same block. Then the sequence numbers of their first occurrence
  in the received list are separated by at most k + h + 2d for some d *)

Variable k: nat.
Variable h : nat.
(*The displacement bound*)
Variable d: nat.

(*We proved in Reorder.v that this condition is implied by
  bounded reordering. We will combine this in the
  eventual proof (TODO: put info)*)
Definition bounded_reorder_list (rec: list fpacket):=
  forall (p1 p2: fpacket),
  p1 \in rec ->
  p2 \in rec ->
  fd_blockId p1 = fd_blockId p2 ->
  (nat_abs_diff (u_seqNum rec p1) (u_seqNum rec p2) <= (k + h) + 2 * d)%N.
  
(*Then, we need the bound on duplication*)
Variable dup : nat.

(*We need several sets of invariants to prove what we want
  (that under the reordering assumptions, the decoder is equivalent
  to a version with no timeouts)*)

Definition decoder_timeout_invar (blocks: list block) 
  (prev: list fpacket) (time: Z) : Prop :=
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
      Z.of_nat (size (undup_fst l1)).+1 = (black_time b) (*/\
      Znth (Int.unsigned (fd_blockIndex p)) 
        (data_packets b ++ parity_packets b) = Some p*)) /\
  (*If a packet arrived but is NOT in a block, there is a packet
    with the same blockIndex that has timed out*)
  (forall (p: fpacket), p \in prev -> 
    (~exists b, (b \in blocks) && packet_in_block p b ) ->
    exists (p' : fpacket) l1 l2, fd_blockId p' = fd_blockId p /\ 
      prev = l1 ++ [:: p'] ++ l2 /\
      p' \notin l1 /\
      Z.of_nat (size (undup_fst prev)) - 
      Z.of_nat (size (undup_fst l1)) > threshold
  ) /\
  (*The blocks are sorted*)
  sorted (fun x y => ((blk_id x) < (blk_id y))%N) blocks /\
  (*All packets in the block were seen*)
  (forall b p, b \in blocks -> packet_in_block p b ->
    p \in prev).
  (*uniq blocks /\*)
  (*All packets are in the correct block*)
  (*
  (forall (p: fec_packet_act) b, 
  (Some p) \in (data_packets b ++ parity_packets b) ->
  fd_blockId p = blk_id b).*)

(*The condition we need on the list*)
Definition reorder_dup_cond (l: list fpacket) :=
  bounded_reorder_list l /\
  duplicates_bounded l fpacket_inhab dup /\
  threshold >= Z.of_nat (k + h + 2 * d + dup).

(*TODO: use existsP?*)
Lemma existsbP: forall {A: eqType} {s: seq A} {P: A -> bool},
  reflect (exists x, (x \in s) && P x) (existsb P s).
Proof.
  move=> A s P. elim: s => [//= | hd tl /= IH].
  - by apply ReflectF => [[]].
  - case Hhd: (P hd).
    + apply ReflectT. exists hd. by rewrite mem_head Hhd.
    + move: IH. case Htl: (existsb P tl) => IH.
      * apply ReflectT. apply elimT in IH =>//.
        case: IH => [x /andP[Hintl Hp]].
        exists x. by rewrite in_cons Hintl orbT.
      * apply ReflectF. apply elimF in IH=>//.
        move => [x]. 
        rewrite in_cons => /andP[/orP[/eqP Hx | Hintl] Hpx]; subst.
        by rewrite Hpx in Hhd. apply IH. exists x.
        by rewrite Hintl Hpx.
Qed.

(*TODO: move*)
(*This is why we define [undup_fst] rather than [undup], which
  keeps the last ocurrence of each element*)
Lemma undup_fst_rcons: forall {A: eqType} (s: seq A) (x: A),
  undup_fst (s ++ [:: x]) = if x \in s then undup_fst s 
    else undup_fst s ++ [:: x].
Proof.
  move=> A s x. rewrite /undup_fst rev_cat/=.
  case Hin: (x \in rev s); rewrite mem_rev in Hin; rewrite Hin =>//.
  by rewrite rev_cons -cats1.
Qed. 

(*Lemma characterizing [upd_time] - relies on invariants about blocks*)
Lemma upd_time_spec: forall time p blocks,
  sorted (fun x y => (blk_id x < blk_id y)%N) blocks ->
  (forall b (p: fpacket), b \in blocks -> packet_in_block p b ->
    fd_blockId p = blk_id b) ->
  (forall b (p: fpacket), b \in blocks -> 
    packet_in_block p b <->
    isSome (Znth (Z.of_nat (fd_blockIndex p)) 
      (data_packets b ++ parity_packets b))) ->
  upd_time time p blocks =
    if (existsb (fun b => packet_in_block p b) blocks) then time else
      time + 1.
Proof.
  move=>time p blocks. elim: blocks => [//= | bhd btl /= IH Hsort Hids Hnth].
  case: (fd_blockId p == blk_id bhd) /eqP => Heq.
  - rewrite /block_notin_packet.
    case Hin: (packet_in_block p bhd).
    + move: Hnth => /(_ bhd p (mem_head _ _)). rewrite Hin => [[Hnth _]].
      by rewrite /isNone Hnth.
    + rewrite /isNone.
      case Hnth': (Znth (Z.of_nat (fd_blockIndex p)) (data_packets bhd ++ parity_packets bhd)) => [p'//= |//=].
      * move: Hnth => /(_ bhd p (mem_head _ _)). rewrite Hin Hnth' =>
        [[_ Hf]]. by have: false by apply Hf.
      * case: (existsb (fun b => packet_in_block p b) btl) /existsbP =>
        [[b] /andP[Hinb Hinbx] |//].
        (*Now we know it cannot be in tail because all have 
              larger sequence number*)
        have: (blk_id bhd < blk_id b)%N. {
          move: Hsort. rewrite path_sortedE; 
            last by move => b1 b2 b3; apply ltn_trans.
          by move=>/andP[/allP Hlt _]; move: Hlt => /(_ _ Hinb).
        }
        have<-//: fd_blockId p = blk_id b by 
          apply Hids =>//; rewrite in_cons Hinb orbT.
        by rewrite Heq ltnn.
  - (*First, we know cannot be in this packet*)
    case Hibphd: (packet_in_block p bhd) =>/=; first by
      exfalso; apply Heq; apply Hids=>//; rewrite mem_head.
    case Hlt: (fd_blockId p < blk_id bhd)%N.
    + (*similarly, contradiction from sorting*)
      case: (existsb [eta packet_in_block p] btl) /existsbP =>
      [[b] /andP[Hinb Hinbx] |//]; subst.
      move: Hsort. rewrite path_sortedE; 
        last by move => b1 b2 b3; apply ltn_trans.
        move=>/andP[/allP Halllt _].
      have Heq': (fd_blockId p = blk_id b) by 
          apply Hids=>//; rewrite in_cons Hinb orbT.
      move: Halllt => /(_ _ Hinb).
      by rewrite -Heq' ltnNge leq_eqVlt Hlt orbT.
    + apply IH.
      * move: Hsort. rewrite path_sortedE; last by
          move=> b1 b2 b3; apply ltn_trans.
        by move=>/andP[_].
      * move=> b p' Hin. apply Hids. by rewrite in_cons Hin orbT.
      * move=> b p' Hin. apply Hnth. by rewrite in_cons Hin orbT.
Qed. 

(*TODO: move*)
(*Lemma add_packet_to_block_black_time: forall p b,
  black_time (add_packet_to_block_black p b).1 =
  black_time b.
Proof.
  move=>p b. rewrite /add_packet_to_block_black.
  case Hcomp: (black_complete b) => //=.
  by case Hrec: (recoverable (add_fec_packet_to_block p b)).
Qed.*)

Lemma create_block_time: forall p time,
  black_time (create_block_with_packet_black p time).1 = time.
Proof.
  move=> p time /=.
  by case: (Z.eq_dec (fd_k p) 1).
Qed.


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
    [[Htime [Hcreate [Hprevnotin [Hsort Hinprev]]]]].
  (*For now, do each part individually - see*)
  repeat split.
  - (*We start with the most important invariant - time*)
    rewrite /decoder_one_step/= undup_fst_rcons.
    rewrite upd_time_spec =>//.
    (*TODO:derive others from wf_packet_list*)
    + case: (existsb [eta packet_in_block p] blocks) /existsbP => 
      [[b /andP[Hinb Hinpb]] | Hnotin].
      * (*If the packet is in some block, then it is was in prev*)
        by have->:p \in prev by apply (Hinprev _ _ Hinb Hinpb).
      * (*Now we need to show that this packet could not have been
        previously seen. This is the hard part.*)
        (*We use our other invariant to argue that there was
          a packet in this block that arrived so long ago that
          the block already timed out. Therefore, this contradicts
          the fact that any two packets in a block will be separated
          by less than the threshold*)
        case Hpinprev: (p \in prev); last
          by rewrite size_cat/= Nat2Z.inj_add/= Htime.
        move: Hprevnotin => /(_ p Hpinprev Hnotin) 
          [p' [l1 [l2 [Hidpp'[Hprev [Hnotinp' Htimeout]]]]]].
        have Hcon: ((size (undup_fst prev) - size (undup_fst l1))%N <= 
          (k + h + 2 * d) + dup)%N. {
            rewrite Hprev.
            eapply (@packets_reorder_dup_bound _ (prev ++ [:: p]) fpacket_inhab
              (fun (x: fpacket) =>  (x \in prev ++ [:: p]) 
                && (fd_blockId x == fd_blockId p)) _ _) with(p2:=p)(l3:=nil) =>//.
            - move=> p1 p2 /andP[Hinp1 /eqP Hidp1] /andP[Hinp2 /eqP Hidp2].
              apply Hreord=>//. by rewrite Hidp1 Hidp2.
            - by rewrite cats0 Hprev -catA.
            - by rewrite Hidpp' Hprev !mem_cat in_cons !eq_refl !orbT.
            - by rewrite mem_cat in_cons !eq_refl !orbT.
          }
        (*Now we get an easy contradiction of inequalities*)
        rewrite -Nat2Z.inj_sub in Htimeout.
        have /ltP: (size (undup_fst prev) - size (undup_fst l1) > k + h + 2 * d + dup)%coq_nat. {
          apply Nat2Z.inj_gt. eapply Zgt_le_trans. apply Htimeout. lia.
        }
        by rewrite ltnNge Hcon.
        rewrite Hprev.
        rewrite /=. apply /leP. apply size_undup_fst_le_app.
    + (*TODO: from wf_packet list*) admit.
    + (*same*) admit.
  - (*TODO: there will be some duplication here: find out how to deal with it*)
    (*This one shouldnt be too hard: just show that when we create a new block,
      the existing packet satisfies the condition*)
    move=> b Hinb.
    apply in_decoder_one_step in Hinb.
    case: Hinb => [Hinb | [[Hb Hall] | H]].
    + (*easy case: follows from IH*)
      move: Hcreate => /(_ b Hinb) [p' [l1 [l2 [Hprev [Hpnotin Hl1time]]]]].
      exists p'. exists l1. exists (l2 ++ [:: p]). repeat split =>//.
      rewrite Hprev. by rewrite !catA.
    + (*Create new packet - the hard case. We need to prove p was not
        in l1 (prev). The difficult case is that there could have been
        a block with p that timed out. We prove a similar contradiction
        as before (TODO: factor out).*)
      case Hinp: (p \in prev); last first.
        (*easy case*) exists p. exists prev. exists nil.
        split. by rewrite cats0. split. by rewrite Hinp.
        rewrite Hb create_block_time Nat2Z.inj_succ -Htime.
        rewrite upd_time_spec=>//.
        case: (existsb [eta packet_in_block p] blocks) /existsbP=>//
          [[b' /andP[Hinb' Hpb']]].
        by rewrite (Hinprev _ _ Hinb' Hpb') in Hinp.
        admit. admit. (*Same as before: TODO*)
      (*The interesting case: in p is in prev, consider 2 cases*)
      case: (existsb [eta packet_in_block p] blocks) /existsbP.
      (*Need 2 more invariants: 
      1. all packets in a block have the same blockId as the block
      2. need to know: all packets in blks are not timed out (can show
        each of these separately i think)*)
      * move => [b' /andP[Hinb' Hpb']].
        have Hpid: fd_blockId p = blk_id b'. admit. (*TODO*)
        have Hbid: blk_id b' = blk_id b. {
          rewrite Hb/=. by case: (Z.eq_dec (fd_k p) 1).
        }
        move: Hall => /(_ _ Hinb') => [[ | //]].
        rewrite /not_timed_out.
        (*Here we again need to get a contradiction because
        packets have arrived too far apart (is >= enough?)
        We should get the previous into a generic lemma*)
        admit.
      * (*OK, now I am confused and need to think a bit more*)
      
      
      (*Here, we can use the IH*)
        move => Hnoblock. move: Hprevnotin => /( _ _ Hinp Hnoblock)
        [p' [l1 [l2 [Hids [Hprev [Hpnotin Hnoto]]]]]].
        (*Here, want to get contradiction by showing that distance
          between p and p' exceeds threshold and is thus impossible*)
        (*proved something very similar before*)
        admit.