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
    ~~ (packet_in_block packet block).
    (*
    isNone (Znth (Z.of_nat (fd_blockIndex packet)) 
      (data_packets block ++ parity_packets block)).*)

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
  (fun b => (Z.leb currTime (black_time b + threshold))).

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

(*The first 2 invariants are the main ones we want, the others are mainly
  there to enable us to prove them (TODO: is this true)*)
Definition decoder_timeout_invar (blocks: list block) 
  (prev: list fpacket) (time: Z) : Prop :=
  (*The time is calculated correctly
    as the number of unique packets to arrive*)
  (time = Z.of_nat (size (undup_fst prev))) /\
  (*For every block, there is a packet that represents the time
    at which the block was created*)
  (forall b, b \in blocks ->
    exists (p: fpacket) l1 l2, 
      fd_blockId p = blk_id b /\
      prev = l1 ++ [:: p] ++ l2 /\
      p \notin l1 /\
      Z.of_nat (size (undup_fst l1)).+1 = (black_time b)) /\
  (*If a packet arrived but is NOT in a block, there is a packet
    with the same blockIndex that has timed out*)
  (forall (p: fpacket), p \in prev -> 
    (~exists b, (b \in blocks) && packet_in_block p b ) ->
    exists (p' : fpacket) l1 l2, fd_blockId p' = fd_blockId p /\ 
      prev = l1 ++ [:: p'] ++ l2 /\
      p' \notin l1 /\
      Z.of_nat (size (undup_fst prev)) - 
      Z.of_nat (size (undup_fst l1)).+1 > threshold
  ) /\
  (*We also have two invariants that we need to prove the above,
    but that we can/have proved separately*)
  (*The blocks are sorted*)
  sorted (fun x y => ((blk_id x) < (blk_id y))%N) blocks /\
  (*All blocks are subblocks of [get_blocks] of the received stream*)
  (forall b, b \in blocks -> exists b', b' \in (get_blocks prev) /\
    subblock b b').

(*The condition we need on the list*)
Definition reorder_dup_cond (l: list fpacket) :=
  bounded_reorder_list l /\
  duplicates_bounded l fpacket_inhab dup /\
  threshold >= Z.of_nat (k + h + 2 * d + dup).

(*Lemma characterizing [upd_time] - relies on invariants about blocks*)
Lemma upd_time_spec: forall time p blocks,
  sorted (fun x y => (blk_id x < blk_id y)%N) blocks ->
  (forall b (p: fpacket), b \in blocks -> packet_in_block p b ->
    fd_blockId p = blk_id b) ->
  upd_time time p blocks =
    if (existsb (fun b => packet_in_block p b) blocks) then time else
      time + 1.
Proof.
  move=>time p blocks. elim: blocks => [//= | bhd btl /= IH Hsort Hids (*Hnth*)].
  case: (fd_blockId p == blk_id bhd) /eqP => Heq.
  - rewrite /block_notin_packet.
    case Hin: (packet_in_block p bhd)=>//=.
    case: (existsb (fun b => packet_in_block p b) btl) /existsbP =>
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
Qed. 

(*TODO move these*)
Lemma create_black_time: forall p time,
  black_time (create_block_with_packet_black p time).1 = time.
Proof.
  move=> p time /=.
  by case: (Z.eq_dec (fd_k p) 1).
Qed.

Lemma create_black_id: forall p time,
  blk_id (create_block_with_packet_black p time).1 = fd_blockId p.
Proof.
  move=> p time/=.
  by case: (Z.eq_dec (fd_k p) 1).
Qed.

Lemma add_black_time: forall p b,
  black_time (add_packet_to_block_black p b).1 = black_time b.
Proof.
  move=> p b. rewrite /add_packet_to_block_black.
  case: (black_complete b)=>//.
  by case: (recoverable (add_fec_packet_to_block p b)).
Qed.

Lemma add_black_id: forall p b,
  blk_id (add_packet_to_block_black p b).1 = blk_id b.
Proof.
  move=>p b. rewrite /add_packet_to_block_black.
  case:(black_complete b)=>//.
  by case: (recoverable (add_fec_packet_to_block p b)).
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
    [[Htime [Hcreate [Hprevnotin [Hsort Hsubblock]]]]].
  (*There are a number of results we will need many times*)
  (*First: prev stream is wf*)
  have Hwfcons: wf_packet_stream (p :: prev) by
      apply (wf_perm Hwf); rewrite cats1 perm_rcons perm_refl.
  have Hwf': wf_packet_stream prev by
    apply (wf_packet_stream_tl Hwfcons). 
  (*All packets in blocks agree with ID values*)
  have Hallid: forall (b' : block) (p0 : fpacket),
    b' \in blocks -> packet_in_block p0 b' -> fd_blockId p0 = blk_id b'. {
    move=> b p' Hinb Hinp'.
    move: Hsubblock=> /(_ b Hinb) [b' [Hinb' Hsubb]].
    have Hinb2:= (subblock_in Hsubb Hinp').
    rewrite (proj1 Hsubb).
    by apply (get_blocks_ids Hwf').
  }
  (*All packets in a block are in prev*)
  have Hinprev: forall (b: block) (p: fpacket),
    b \in blocks -> packet_in_block p b -> p \in prev. {
      move=> b p' Hinb Hinpb'.
      move: Hsubblock => /(_ b Hinb) [b1 [Hinb1 Hsub]].
      apply (get_blocks_in_orig Hwf' Hinb1).
      apply (subblock_in Hsub Hinpb').
  }
  (*A key result that we use in several places and which underlies
    the entire invariant: we cannot have a packet in the same block
    as the current packet that arrived too much earlier*)
  have Hclose: forall (p1 (*p2*): fpacket) l1 l2,
    prev (*++ [:: p]*) = l1 ++ [:: p1] ++ l2 (*++ [:: p2]*) ->
    p1 \notin l1 ->
    fd_blockId p1 = fd_blockId p ->
    ~(Z.of_nat (size (undup_fst (l1 ++ [:: p1] ++ l2 ++ [:: p]))) -
    Z.of_nat (size (undup_fst (l1 ++ [:: p1]))) > threshold). {
      move=> p1 l1 l2 Hprev Hnotin1 Hids.
      have Hcon: ((size (undup_fst (l1 ++ [:: p1] ++ l2 ++ [:: p])) - 
        size (undup_fst (l1 ++ [:: p1])))%N <= 
        (k + h + 2 * d) + dup)%N. {
          eapply (@packets_reorder_dup_bound' _ (prev ++ [:: p]) fpacket_inhab
            (fun (x: fpacket) =>  (x \in prev ++ [:: p]) 
              && (fd_blockId x == fd_blockId p)) _ _) with(p2:=p)(l3:=nil) =>//.
          - move=> pa pb /andP[Hinpa /eqP Hidpa] /andP[Hinpb /eqP Hidpb].
            apply Hreord=>//. by rewrite Hidpa Hidpb.
          - by rewrite cats0 Hprev -catA.
          - by rewrite Hids Hprev !mem_cat in_cons !eq_refl !orbT.
          - by rewrite mem_cat in_cons !eq_refl !orbT.
        }
      (*Now we get an easy contradiction of inequalities*)
      move=>Htimeout.
      rewrite -Nat2Z.inj_sub in Htimeout.
      - have /ltP: (size (undup_fst (l1 ++ [:: p1] ++ l2 ++ [:: p])) - 
          size (undup_fst (l1 ++ [:: p1])) > k + h + 2 * d + dup)%coq_nat. {
          apply Nat2Z.inj_gt. eapply Zgt_le_trans. apply Htimeout. lia.
        }
        by rewrite ltnNge Hcon.
      - rewrite catA. apply /leP. apply size_undup_fst_le_app. 
    }
  (*We do the 1st invariant separately, since it's useful
    in the rest*)
  have Hupdtime: (upd_time time p blocks = Z.of_nat (size (undup_fst (prev ++ [:: p])))). {
    rewrite undup_fst_rcons upd_time_spec =>//.
    + case: (existsb [eta packet_in_block p] blocks) /existsbP => 
      [[b /andP[Hinb Hinpb]] | Hnotin].
      * (*If the packet is in some block, then it is was in prev*)
        by have->:p \in prev by apply (Hinprev _ _ Hinb Hinpb).
      * (*Otherwise, we need to argue that this packet could
        not have been seen. We use the 3rd invariant to argue that there
        was some block that arrived so long ago that its
        block timed out. Thus, this contradicts the fact that any
        two packets in a block are separated by less than
        the threshold.*)
        case Hpinprev: (p \in prev); last
          by rewrite size_cat/= Nat2Z.inj_add/= Htime.
        move: Hprevnotin => /(_ p Hpinprev Hnotin) 
          [p' [l1 [l2 [Hidpp'[Hprev [Hnotinp' Htimeout]]]]]].
        exfalso. apply (Hclose p' (*p*) l1 l2 (*nil*))=>//. 
        have->: l1 ++ [:: p'] ++ l2 ++ [:: p] = prev ++ [:: p] by
          rewrite !catA -(catA l1) Hprev.
        by rewrite !undup_fst_rcons Hpinprev (negbTE Hnotinp') 
          size_cat/= addn1.
  }
  repeat split.
  - (*We already did the first one*)
    by rewrite /decoder_one_step/=. 
  - (*For the second invariant, we need to show that every new block
    satisfies the condition. The difficult part is to show that
    the current packet has not been seen before.*)
    move=> b Hinb.
    apply in_decoder_one_step in Hinb.
    case: Hinb => [Hinb | [[Hb Hall] | H]].
    + (*easy case: follows from IH*)
      move: Hcreate => /(_ b Hinb) [p' [l1 [l2 [Hidp' [Hprev [Hpnotin Hl1time]]]]]].
      exists p'. exists l1. exists (l2 ++ [:: p]). repeat split =>//.
      rewrite Hprev. by rewrite !catA.
    + (*Once again, if there was a block with p that timed out,
      we have a similar contradiction.*)
      case Hinp: (p \in prev); last first.
      * (*easy case*) exists p. exists prev. exists nil.
        split_all.
        -- by rewrite Hb create_black_id. 
        -- by rewrite cats0.
        -- by rewrite Hinp.
        -- rewrite Hb create_black_time Nat2Z.inj_succ -Htime.
          rewrite upd_time_spec=>//.
          case: (existsb [eta packet_in_block p] blocks) /existsbP=>//
            [[b' /andP[Hinb' Hpb']]].
          by rewrite (Hinprev _ _ Hinb' Hpb') in Hinp.
      * (*The interesting case: in p is in prev, consider 2 cases*)
        case: (existsb [eta packet_in_block p] blocks) /existsbP.
        -- (*If p was in a block, that block must have timed out,
          so we have a previous packet in p's block that is too far apar*)
         move => [b' /andP[Hinb' Hpb']].
          have Hpid: fd_blockId p = blk_id b' by apply Hallid.
          have Hbid: blk_id b' = blk_id b. {
            rewrite Hb/=. by case: (Z.eq_dec (fd_k p) 1).
          }
          move: Hall => /(_ _ Hinb') => [[ | //]].
          rewrite /not_timed_out Hupdtime.
          (*Get the previous packet that gives us a contradiction*)
          move: Hcreate => /( _ b' Hinb') 
            [p' [l1 [l2 [Hidp' [Hprev [Hnotinp' Htimeb']]]]]].
          rewrite Z.leb_antisym => Hto. apply negbFE in Hto.
          move: Hto => /Z.ltb_spec0. rewrite Hprev -Htimeb' => Hcon.
          exfalso. apply (Hclose p' (*p*) l1 l2 (*nil*))=>//.
          by rewrite Hpid Hidp'.
          rewrite undup_fst_rcons (negbTE Hnotinp') size_cat/=addn1.
          rewrite -!catA in Hcon. simpl in *; lia.
        -- (*Otherwise, we use the 3rd invariant, since p's previous block
          must already have timed out *)
          move => Hnotex.
          move: Hprevnotin => /(_ p Hinp Hnotex) 
            [p' [l1 [l2 [Hideq [Hprev [Hnotinp' Htimeout]]]]]].
          exfalso. apply (Hclose p' l1 l2)=>//.
          have->:(l1 ++ [:: p'] ++ l2 ++ [:: p]) = prev ++ [:: p]
            by rewrite !catA -(catA l1) Hprev.
          by rewrite !undup_fst_rcons (negbTE Hnotinp') Hinp size_cat/= 
            addn1.
    + (*last case: use the IH, easy*)
      case: H => [b' [Hinb' Hb]].
      move: Hcreate => /(_ b' Hinb') 
        [p' [l1 [l2 [Hideq [Hprev [Hnotinp' Htimeout]]]]]].
      exists p'. exists l1. exists (l2 ++ [:: p]).
      split_all=>//.
      * by rewrite Hb add_black_id.
      * by rewrite Hprev -catA.
      * by rewrite Hb add_black_time.  
    + by [].
  - (*To prove the 3rd invariant, we have 2 cases:
      1. If p' is the current packet, then immediate 
        contradiction, since there is always a block with p in it
      2. If p' is in prev, then we again have 2 cases:
        A. If there is no block with p' in prevs, then we can
          use the IH
        B. Otherwise, assume there is a block with p' in prevs.
          Then it must have timed out in the current iteration
           so we can use the start packet of this
          (from the 2nd invariant) as the packet we need to 
          prove the invariant *)
    move=> p'. case: (p' == p) /eqP => [Hpp' _ | Hpp']. 
    + move => Hnotex.
      exfalso. apply Hnotex. subst. apply (packet_in_one_step _ _ _ Hwf).
      * by rewrite mem_cat mem_head orbT.
      * move=> b1 p1 Hinp1 Hinb1 Hids.
        move: Hsubblock => /( _ _ Hinb1) [b2 [Hinb2 Hsub]].
        (*Not quite enough, need a block from [get_blocks (prev ++ [:: p])]*)
        have Hsubstream: (forall (x: fpacket), x \in prev -> 
          x \in prev ++ [:: p]) by move=> x; rewrite mem_cat=>->.
        have [b3 [Hinb3 Hsub2]]:=(get_blocks_sublist Hwf Hsubstream Hinb2).
        have Hsub3 :=(subblock_trans Hsub Hsub2).
        have Hideq: blk_id b1 = blk_id b3 by apply Hsub3.
        rewrite Hideq in Hids. rewrite {Hideq}.
        have[-> ->]:blk_k b1 = blk_k b3 /\ blk_h b1 = blk_h b3 by apply Hsub3.
        apply (get_blocks_kh Hwf)=>//. by rewrite mem_cat mem_head orbT.
      * move=> b' Hinb'. move: Hsubblock=>/(_ b' Hinb') 
          [b'' [Hinb'' [Hids [Hdat [Hpars [Hk Hh]]]]]].
        rewrite Hk Hh (proj1 Hdat) (proj1 Hpars).
        by apply (get_blocks_Zlength Hwf').
    + rewrite mem_cat in_cons orbF => /orP[Hinp' | /eqP //].
      move=> Hnotex.
      (*Case 1: there is no block with p' in prevs*)
      case: (existsb [eta packet_in_block p'] blocks) /existsbP; last first.
      * (*easy: use IH*)
        move=> Hnotex'. move: Hprevnotin => /(_ p' Hinp' Hnotex')
          [p'' [l1 [l2 [Hid [Hprev [Hnotin Htimeout]]]] ]].
        exists p''. exists l1. exists (l2 ++ [:: p]). split_all=>//.
        by rewrite Hprev !catA. 
        have: Z.of_nat (size (undup_fst (prev ++ [:: p]))) >=
          Z.of_nat (size (undup_fst (prev))); last by lia.
        apply inj_ge. apply /leP. apply size_undup_fst_le_app.
      * (*Now, we know that this block must have timed out because
        p and p' cannot have the same blockIndex and blockId
        (from wf); hence we can use [notin_decoder_one_step]*) 
        move=> [b /andP[Hinb Hinpb]].
        have Hidpp': (fd_blockId p <> fd_blockId p' \/ 
          fd_blockIndex p <> fd_blockIndex p'). {
            case: (fd_blockId p == fd_blockId p') /eqP=>[Heq |]; last by
              move=> C; left.
            case: (fd_blockIndex p == fd_blockIndex p') /eqP => [Heq2 |];
              last by move=> C; right.
            exfalso. apply Hpp'. apply Hwf=>//; rewrite mem_cat.
            by rewrite Hinp'. by rewrite mem_head orbT.
          }
        (*Now we apply [notin_decoder_one_step] to know that the block
          must have timed out*)
        have: not_timed_out (upd_time time p blocks) b = false. {
          apply (notin_decoder_one_step Hidpp')=>//.
          (*These all follow from the subblock relation and 
            [wf_packet_stream], proved in Block.v*)
          - move=> b' Hinb'. move: Hsubblock=>/(_ b' Hinb') 
            [b'' [Hinb'' [Hids [Hdat [Hpars [Hk Hh]]]]]].
            rewrite Hk Hh (proj1 Hdat) (proj1 Hpars).
            by apply (get_blocks_Zlength Hwf').
          - move => b' p'' Hinb' Hinp''.
            move: Hsubblock =>/(_ b' Hinb')
            [b'' [Hinb'' Hsub]].
            by apply (get_blocks_sub_Znth Hwf' Hinb'' Hsub).
        }
        rewrite /not_timed_out.
        (*Now we need to get info about times*)
        move: Hcreate => /(_ b Hinb) 
          [p1 [l1 [l2 [Hidp1 [Hprev [Hnotin Hbtime]]]]]].
        rewrite Hupdtime -Hbtime Z.leb_antisym => Hlt.
        apply negbFE in Hlt; move: Hlt => /Z.ltb_spec0 Htimeout.
        exists p1. exists l1. exists (l2 ++ [:: p]). 
        split_all=>//.
        -- rewrite Hidp1. symmetry. by apply Hallid.
        -- by rewrite Hprev !catA.
        -- lia.
  - by apply decoder_one_step_sorted.
  - move=> b Hinb.
    (*need permutation*)
    have [b' [Hinb' Hsub]]: exists (b': block), 
      b' \in get_blocks (p :: prev) /\ subblock b b' :=
      (decoder_one_step_gen_subblocks Hwfcons Hsubblock Hinb).
    have Hperm: perm_eq (get_blocks (p :: prev)) 
      (get_blocks (prev ++ [:: p])). {
        apply get_blocks_perm=>//. 
        by rewrite cats1 -perm_rcons perm_refl.
      }
    exists b'.
    by rewrite -(perm_mem Hperm).
Qed.

End DecodeTimeouts.