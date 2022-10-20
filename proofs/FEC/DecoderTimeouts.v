Require Import AbstractEncoderDecoder.
Require Import DecoderGeneric.
Require Import DecoderNoTimeouts.
Require Import VST.floyd.functional_base.
Require Import CommonSSR.
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


Lemma decoder_all_steps_rewrite: forall l,
  decoder_all_steps l =
  (foldl (fun (acc: seq block * seq packet * Z * seq fpacket) (p: fpacket) =>
    let t := decoder_one_step acc.1.1.1 p acc.1.2 in
    (t.1.1, acc.1.1.2 ++ t.1.2, t.2, acc.2 ++ [:: p]))
    (nil, nil, 0, nil) l).1.
Proof.
  by [].
Qed.
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

(*TODO: move*)
Lemma u_seqNum_cat_in: forall {A: eqType} (l1 l2: seq A) (x: A),
  x \in l1 ->
  u_seqNum (l1 ++ l2) x = u_seqNum l1 x.
Proof.
  move=> A l1 l2 x Hinx. 
  rewrite /u_seqNum/undup_fst rev_cat undup_cat rev_cat index_cat.
  have->//: x \in rev (undup (rev l1)).
  by rewrite mem_rev mem_undup mem_rev.
Qed.

Lemma bounded_reorder_list_cat_fst: forall l1 l2,
  bounded_reorder_list (l1 ++ l2) ->
  bounded_reorder_list l1.
Proof.
  move=> l1 l2. rewrite /bounded_reorder_list => Hreord p1 p2 
  Hinp1 Hinp2 Hid.
  move: Hreord => /(_ p1 p2).
  rewrite !mem_cat Hinp1 Hinp2 /= => /(_ isT isT Hid).
  by rewrite !u_seqNum_cat_in.
Qed.

(*TODO: move*)
Lemma duplicates_bounded_cat_fst {A: eqType}: 
  forall (l1 l2 : list A) d m,
  duplicates_bounded (l1 ++ l2) d m ->
  duplicates_bounded l1 d m.
Proof.
  rewrite /duplicates_bounded.
  move=> l1 l2 def m Hdup i j Hij.
  rewrite -size_length => Hj Hnth.
  apply Hdup=>//.
  - rewrite -size_length size_cat. apply (ltn_leq_trans Hj).
    by rewrite leq_addr.
  - rewrite !nth_cat Hj.
    have->//: (i < size l1)%N. by apply (leq_ltn_trans Hij).
Qed.


(*Then, we need the bound on duplication*)
Variable dup : nat.

(*The condition we need on the list*)
Definition reorder_dup_cond (l: list fpacket) :=
  bounded_reorder_list l /\
  duplicates_bounded l fpacket_inhab dup /\
  threshold >= Z.of_nat (k + h + 2 * d + dup).

Lemma reorder_dup_cond_cat_fst: forall l1 l2,
  reorder_dup_cond (l1 ++ l2) ->
  reorder_dup_cond l1.
Proof.
  move=> l1 l2 [Hreord [Hdup Hthresh]].
  repeat split=>//.
  - by apply (bounded_reorder_list_cat_fst Hreord).
  - by apply (duplicates_bounded_cat_fst Hdup).
Qed. 


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

(*A key lemma that we need for our invariant: a packet with the
  same blockId as the current block could not have appeared too
  far in the past*)
Lemma same_block_close: forall prev (p p1: fpacket) l1 l2,
  reorder_dup_cond (prev ++ [:: p]) ->
  prev = l1 ++ [:: p1] ++ l2 ->
  p1 \notin l1 ->
  fd_blockId p1 = fd_blockId p ->
  ~(Z.of_nat (size (undup_fst (l1 ++ [:: p1] ++ l2 ++ [:: p]))) -
    Z.of_nat (size (undup_fst (l1 ++ [:: p1]))) > threshold).
Proof.
  move=> prev p p1 l1 l2.
  rewrite /reorder_dup_cond/bounded_reorder_list/duplicates_bounded =>
  [[Hreord [Hdups Hthresh]]] Hprev Hnotin1 Hids.
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
Qed. 

(*TODO: could move to BLocks maybe*)
Lemma decoder_invar_allid: forall (blocks : seq block) prev,
  wf_packet_stream prev ->
  (forall b, b \in blocks -> exists b', b' \in (get_blocks prev) /\
  subblock b b') ->
  forall (b' : block) (p0 : fpacket),
  b' \in blocks -> packet_in_block p0 b' -> fd_blockId p0 = blk_id b'.
Proof.
  move=> blocks prev Hwf Hsubblock b p' Hinb Hinp'.
  move: Hsubblock=> /(_ b Hinb) [b' [Hinb' Hsubb]].
  have Hinb2:= (subblock_in Hsubb Hinp').
  rewrite (proj1 Hsubb).
  by apply (get_blocks_ids Hwf).
Qed.
(*same*)
Lemma decoder_invar_inprev: forall (blocks: seq block) prev,
  wf_packet_stream prev ->
  (forall b, b \in blocks -> exists b', b' \in (get_blocks prev) /\
  subblock b b') ->
  forall (b: block) (p: fpacket),
    b \in blocks -> packet_in_block p b -> p \in prev.
Proof.
  move=> blocks prev Hwf Hsubblock b p' Hinb Hinpb'.
  move: Hsubblock => /(_ b Hinb) [b1 [Hinb1 Hsub]].
  apply (get_blocks_in_orig Hwf Hinb1).
  apply (subblock_in Hsub Hinpb').
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
  have Hallid:= (decoder_invar_allid Hwf' Hsubblock).
  (*All packets in a block are in prev*)
  have Hinprev:= (decoder_invar_inprev Hwf' Hsubblock). 
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
        exfalso. apply (@same_block_close prev p p' (*p*) l1 l2 (*nil*))=>//. 
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
          exfalso. apply (@same_block_close prev p p' (*p*) l1 l2 (*nil*))=>//.
          by rewrite Hpid Hidp'.
          rewrite undup_fst_rcons (negbTE Hnotinp') size_cat/=addn1.
          rewrite -!catA in Hcon. simpl in *; lia.
        -- (*Otherwise, we use the 3rd invariant, since p's previous block
          must already have timed out *)
          move => Hnotex.
          move: Hprevnotin => /(_ p Hinp Hnotex) 
            [p' [l1 [l2 [Hideq [Hprev [Hnotinp' Htimeout]]]]]].
          exfalso. apply (@same_block_close prev p p' l1 l2)=>//.
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

(*Opaque decoder_one_step.*)

(*Therefore, the invariant holds of [decoder_all_steps]*)
Lemma decoder_timeout_invar_all: forall packets,
  wf_packet_stream packets ->
  reorder_dup_cond packets ->
  decoder_timeout_invar (decoder_all_steps packets).1.1
    packets (decoder_all_steps packets).2.
Proof.
  move=> packs Hwf Hreord.
  rewrite /decoder_all_steps/decoder_all_steps_gen.
  have Hpacks: packs = (decoder_multiple_steps_gen upd_time not_timed_out nil packs nil nil 0).2
    by rewrite prev_packets_multiple.
  rewrite {2}Hpacks.
  apply (@prove_decoder_invariant_multiple upd_time not_timed_out
    (fun packs block time => decoder_timeout_invar block packs time)
    (fun l => wf_packet_stream l /\ reorder_dup_cond l))=>//.
  - move=> blks curr tm prv Hinvar [Hwf' Hdup'].
    by apply decoder_timeout_invar_preserved_one.
  - move => l1 l2 [Hwfl1 Hdupl1].
    split. apply (wf_substream Hwfl1). move=> x Hin.
    by rewrite mem_cat Hin.
    by apply (reorder_dup_cond_cat_fst Hdupl1).
Qed.

(*Now we want to prove that this decoder is equivalent to one
  without timeouts (in terms of output). 
  The key idea is that all blocks that contain packets
  that might arrive later are kept*)

(*let' see if this condition works first*)

(*Maybe this condition: if there is a block in blks2 not in
  blks1, then there is some packet in previous that was sent
  before timeout threshold AND every block in blks1 is in blks2
  is this sufficient: search for block, if not same, contradiction
  to prove preserved: assume true,
  (informal) hard case: adding p or timing out block
  when we add p to blks2, need to know that block is equal as block in blks1
  (and know sorted, which we do)
  if it is not, then have previous outside threshol - contradiction
  so we have this when we add p to blks2 
  if no block in blks2 but have one in blks1, contradict second part
  OK, so adding p is good
  what about if we timeout a block
  then, use decoder_invar and show that this is true
  (in fact, maybe follows directly from)
  *)

(*Our invariant is the following*)
Definition to_nto_invar (blks1 blks2 : list block) 
  (prev : list fpacket) :=
  (forall (b: block), b \in blks1 -> b \in blks2) /\
  (forall (b: block), b \in blks2 -> b \notin blks1 ->
    exists (p: fpacket) l1 l2, fd_blockId p = blk_id b /\
      prev = l1 ++ [:: p] ++ l2 /\
      p \notin l1 /\
      Z.of_nat (size (undup_fst prev)) -
      Z.of_nat (size (undup_fst l1)).+1 > threshold) /\
  (*All received packets are in blks2*)
  (forall (p: fpacket), p \in prev -> exists (b: block),
    (b \in blks2) && packet_in_block p b) /\
  (*All blocks are subblocks of [get_blocks] of the received stream*)
  (forall b, b \in blks2 -> exists b', b' \in (get_blocks prev) /\
    subblock b b').
(*This is very very similar to the decoder invariant - does it
  follow? Should we change? see*)

  (*The plan: 2 proofs (assuming nice packet stream)
    1. If we have blks1 and blks2 satsifying this
      and if blks1 satisfies invar, then result of
      one step on decoder no to and decoder timeouts is
      the same (just packets)
    2. If we have blks1 and blks2 satsifying this
      and if blks1 satisfies invar, then
      result of each still satisfies this invariant
    maybe combine these proofs
    then lift to multiple and/or all steps*)
(*Search find.*)
(*Let's think about this: maybe we should rewrite [upd_dec_state_gen]
  as something like: 
  if (has blks (fun b => blockId b = fd_blockId p)) then
  let b := nth (find (fun b => ...)) blks in
  insert (add_packet_to_block p b) (remove b blks) else
  insert (new_packet_with_block p time) blks

  then we can reason about \in more directly without induction
  
  let n := find (blockId =fd_blockId p) blks in
    if
    *)

(*Idea: lemma: if block with id = fd_blockId p is
  equal, then update_dec_state .2 is equal*)
(*Lemma *)

Lemma len1: forall (n: nat),
  (n <= 1)%N = (n == 0)%N || (n == 1)%N.
Proof.
  move=> n. case: n=>//= n'.
  by rewrite ltn1.
Qed.
 (*If there is only at most 1 element satisfying a predicate in a list,
  then any two elements in the last satisfying the predicate must be
  equal*)
Lemma nth_uniq_eq: forall {A: eqType} (s: seq A) (p: pred A) (x y: A),
  (count p s <= 1)%N ->
  p x ->
  p y ->
  x \in s ->
  y \in s ->
  x = y.
Proof.
  (*TODO: in ListPoly, move size1P to CommonSSR*)
  move=> A s p x y. rewrite -size_filter len1 => /orP[/eqP Hnil | 
    /ListPoly.size1P [z Hs]] Hpx Hpy Hinx Hiny.
  - apply size0nil in Hnil.
    have: x \in [seq x <- s | p x] by rewrite mem_filter Hpx.
    by rewrite Hnil.
  - have: x \in [seq x <- s | p x] by rewrite mem_filter Hpx.
    have: y \in [seq x <- s | p x] by rewrite mem_filter Hpy.
    rewrite !Hs !in_cons !orbF => /eqP Hyz /eqP Hxz.
    by rewrite Hyz Hxz.
Qed.

Lemma find_uniq_eq: forall {A: eqType} (s1 s2: seq A) (p: pred A) (d: A),
  (count p s1 <= 1)%N ->
  (count p s2 <= 1)%N ->
  has p s1 ->
  has p s2 ->
  (forall x, x \in s1 -> x \in s2) ->
  nth d s1 (find p s1) = nth d s2 (find p s2).
Proof.
  move=> A s1 s2 p def Hc1 Hc2 Hhas1 Hhas2 Hsub.
  case: (findP p s1). by rewrite Hhas1.
  move=> i1 Hi1 Hnth1 Hbef1.
  case: (findP p s2). by rewrite Hhas2.
  move=> i2 Hi2 Hnth2 Hbef2.
  have Hin1: nth def s1 i1 \in s1 by apply mem_nth.
  have Hin2: nth def s1 i1 \in s2 by apply Hsub.
  have Hin2': nth def s2 i2 \in s2 by apply mem_nth.
  by apply (nth_uniq_eq Hc2).
Qed.

(*Finally, prove that sorted by blk_order implies count <= 1*)
Lemma blk_count: forall (blks: list block) (n: nat),
  sorted blk_order blks ->
  (count (fun b => blk_id b == n) blks <= 1)%N.
Proof.
  move=> blks n.
  elim: blks => [// | bhd btl /= IH].
  rewrite path_sortedE; last by apply blk_order_trans.
  move=> /andP[/allP Hall Hsort].
  case: (blk_id bhd == n) /eqP => Hhd/=; last by apply IH.
  have->//:count (fun b : block => blk_id b == n) btl = 0%N.
  apply /eqP. apply negbFE. rewrite -lt0n -has_count.
  apply negbTE. apply /hasP => [[b Hinb] /eqP Hidb].
  have: (blk_id bhd < blk_id b)%N by apply Hall.
  by rewrite Hidb Hhd ltnn.
Qed.

Lemma blk_order_irrefl: irreflexive blk_order.
Proof.
  move=> b. by rewrite /blk_order ltnn.
Qed.

Lemma blk_order_sort_uniq: forall blks,
  sorted blk_order blks ->
  uniq blks.
Proof.
  move=> blks. apply sorted_uniq.
  apply blk_order_trans.
  apply blk_order_irrefl.
Qed.

Lemma orb_notfirst: forall (b1 b2: bool),
  b1 || b2 = b1 || (~~ b1 && b2).
Proof.
  move=> b1 b2. by case: b1.
Qed. 


(*maybe do as 1 step*)
Lemma decoder_timeout_notimeout_one: 
  forall blks1 blks2 prev p time,
  to_nto_invar blks1 blks2 prev ->
  wf_packet_stream (prev ++ [:: p]) ->
  reorder_dup_cond (prev ++ [:: p]) ->
  decoder_timeout_invar blks1 prev time ->
  sorted blk_order blks2 ->
  (*The outputs are equal*)
  (decoder_one_step blks1 p time).1.2 =
  (decoder_one_step_gen upd_time triv_timeout blks2 p time).1.2 /\
  (*The blocks mantain the invariant*)
  to_nto_invar (decoder_one_step blks1 p time).1.1
    (decoder_one_step_gen upd_time triv_timeout blks2 p time).1.1 
    (prev ++ [:: p]) /\
  (*The updated times are equal*)
  (decoder_one_step blks1 p time).2 =
  (decoder_one_step_gen upd_time triv_timeout blks2 p time).2.
Proof.
  move=> blks1 blks2 prev p time Hinvar Hwf Hcond Hdecinv Hsort2.
  have Hwfcons: wf_packet_stream (p :: prev) by
    apply (wf_perm Hwf); rewrite cats1 perm_rcons perm_refl.
  have Hwf': wf_packet_stream prev by
    apply (wf_packet_stream_tl Hwfcons).
  (*Some results that are useful, since there are several impossible
    cases from timeouts we use multiple times*)
  (*1. The block in blks2 with p's id is in blks1*)
  have Hbpin21: forall b,
    b \in blks2 -> blk_id b = fd_blockId p ->
    b \in blks1. {
    move=> b Hinb Hid. 
    case Hinb1: (b \in blks1)=>//.
    have Hbnot: b \notin blks1 by rewrite Hinb1.
    case: Hinvar => [Hb12 [Hnotb12 Hsubs]].
    move: Hnotb12 => /(_ b Hinb Hbnot) 
      [p' [l1 [l2 [Hidp' [Hprev [Hnotin Htimeout]]]]]].
    exfalso. apply (@same_block_close prev p p' l1 l2)=>//; first
      by rewrite Hidp' Hid.
    have->: (l1 ++ [:: p'] ++ l2 ++ [:: p]) = prev ++ [:: p]
      by rewrite Hprev !catA.
    rewrite !undup_fst_rcons (negbTE Hnotin).
    case Hinp: (p \in prev); rewrite !size_cat !addn1; lia.
  }
  (*2: The block in blks2 containing p (if one exists), is in blks1*)
  have Hbpin21': forall b,
    b \in blks2 ->
    packet_in_block p b ->
    b \in blks1. {
    move=> b Hinb Hinp.
    apply Hbpin21 =>//. symmetry. by apply (decoder_invar_allid Hwf' 
      (proj2 (proj2 (proj2 Hinvar)))).   
    }
  (*Sorted lemmas*)
  have Hsort1': sorted blk_order 
    [seq x <- blks1 | not_timed_out (upd_time time p blks1) x] by
    (apply sorted_filter; [apply blk_order_trans | apply Hdecinv]).
  have Hsort2': sorted blk_order 
    [seq x <- blks2 | triv_timeout (upd_time time p blks2) x] by
    (apply sorted_filter=>//; apply blk_order_trans).
  (*Can we provethis?*)
  have Hupdtime: upd_time time p blks1 = 
    if p \in prev then time else time + 1. {
      rewrite upd_time_spec.
      - case: (existsb [eta packet_in_block p] blks1) /existsbP => 
        [[b /andP[Hinb1 Hidb1]] | Hnotex1].
        + have->//=: p \in prev. eapply (decoder_invar_inprev Hwf').
          apply Hdecinv. apply Hinb1. by [].
        + (*We can prove this*)
          case Hin: (p \in prev)=>//.
          move: Hinvar => [_ [_ [/(_ p Hin) [b' /andP[Hinb' Hinp]] _]]].
          exfalso. apply Hnotex1. exists b'. rewrite Hinp andbT.
          by apply Hbpin21'.
      - apply Hdecinv.
      - apply (decoder_invar_allid Hwf'). apply Hdecinv.
  }
  (*We need the time invariant for the output result*)
  have Htimes: upd_time time p blks1 = upd_time time p blks2. {
    rewrite Hupdtime upd_time_spec.
    - case: (existsb [eta packet_in_block p] blks2) /existsbP => 
      [[b /andP[Hinb2 Hidb2]] | Hnotex1].
      + have->//: p \in prev. 
        eapply (decoder_invar_inprev Hwf') with(b:=b)=>//.
        2: apply Hinb2. apply Hinvar.
      + case Hin: (p \in prev)=>//.
        move: Hinvar => [_ [_ [/(_ p Hin) [b' /andP[Hinb' Hinp] _]]]].
        exfalso. apply Hnotex1. exists b'. by rewrite Hinb'.
    - apply Hsort2.
    - apply (decoder_invar_allid Hwf'). apply Hinvar.
  } 
  rewrite /=.
  rewrite -and_assoc. split=>//.
  (*Handle the 2 easier ones first*)
  rewrite /to_nto_invar -!and_assoc. split; last first.
    (*easy and same as above: maybe separate lemma*)
    move=> b Hinb.
    (*need permutation*)
    have [b' [Hinb' Hsub]]: exists (b': block), 
      b' \in get_blocks (p :: prev) /\ subblock b b' :=
      (decoder_one_step_gen_subblocks Hwfcons 
        (proj2 (proj2 (proj2 Hinvar))) Hinb).
    have Hperm: perm_eq (get_blocks (p :: prev)) 
      (get_blocks (prev ++ [:: p])). {
        apply get_blocks_perm=>//. 
        by rewrite cats1 -perm_rcons perm_refl.
      }
    exists b'.
    by rewrite -(perm_mem Hperm).
  split; last first. {
    (*TODO: maybe dont do this first, not as easy as I thought
      do we need this for sure?*)
    move=> p'.
    rewrite mem_cat => /orP[Hprev | ]; last first.
    - rewrite in_cons orbF => /eqP Hp; subst.
      apply (packet_in_one_step _ _ _ Hwf).
      + by rewrite mem_cat in_cons eq_refl orbT.
      + (*NOTE: copied this - bad*) 
      move=> b1 p1 Hinp1 Hinb1 Hids.
      case: Hinvar => [_ [_ [_ /( _ _ Hinb1) [b2 [Hinb2 Hsub]]]]].
      (*Not quite enough, need a block from [get_blocks (prev ++ [:: p])]*)
      have Hsubstream: (forall (x: fpacket), x \in prev -> 
        x \in prev ++ [:: p]) by move=> x; rewrite mem_cat=>->.
      have [b3 [Hinb3 Hsub2]]:=(get_blocks_sublist Hwf Hsubstream Hinb2).
      have Hsub3 :=(subblock_trans Hsub Hsub2).
      have Hideq: blk_id b1 = blk_id b3 by apply Hsub3.
      rewrite Hideq in Hids. rewrite {Hideq}.
      have[-> ->]:blk_k b1 = blk_k b3 /\ blk_h b1 = blk_h b3 by apply Hsub3.
      apply (get_blocks_kh Hwf)=>//. by rewrite mem_cat mem_head orbT.
      + (*also copied BAD - need proof that subblock implies
          these as separate lemma*)
        move=> b' Hinb'.
        case: Hinvar => [_ [_ [_ /( _ _ Hinb') 
          [b'' [Hinb'' [Hids [Hdat [Hpars [Hk Hh]]]]]]]]].
        rewrite Hk Hh (proj1 Hdat) (proj1 Hpars).
        by apply (get_blocks_Zlength Hwf').
    - rewrite update_dec_state_gen_eq //.
      rewrite /=/triv_timeout/=.
      rewrite filter_predT.
      case Hhas: (has (fun b0 : block => blk_id b0 == fd_blockId p) blks2).
      + have:=Hhas => /hasP [b Hinb /eqP Hidb].
        case: (fd_blockId p' == fd_blockId p) /eqP => Hids/=.
        * exists (add_packet_to_block_black p
        (nth block_inhab blks2
           (find (fun b1 : block => blk_id b1 == fd_blockId p) blks2))).1.
          rewrite mem_insert eq_refl/=. 
          (*ugh: continue with this: we know there is some block
            that contains p' by IH, it is the same as nth find
            because of uniquenss. Only way p' could not
            be in is if blockIndex equals, but then p' is p, so good*)
          admit.
        * (*From IH, know it cannot equal add_black bc id different
            and will be in rem before not same ID*)
          admit.
      + rewrite /=. (*since false, use IH, cannot be
        in same as p or else there would be a block in blks2
        with id, contradict HHas*)
        admit.
  }        
        
  rewrite !and_assoc !update_dec_state_gen_eq //.
  (*See if there is a block with p's ID inside blks2*)
  case Hhas2: (has (fun b : block => blk_id b == fd_blockId p)
    [seq x <- blks2 | triv_timeout (upd_time time p blks2) x]).
  - have:=Hhas2 => /hasP [b]. 
    rewrite mem_filter => /andP[_ Hinb2] /eqP Hidb. 
    (*We know that this block is also in blks1*)
    have Hinb1: b \in blks1 by apply Hbpin21.
    (*See if it has timed out or not*)
    case Hto: (not_timed_out (upd_time time p blks1) b).
    + (*If it timed out, "has" is true*)
      have Hhas1: has (fun b0 : block => blk_id b0 == fd_blockId p)
      [seq x <- blks1 | not_timed_out (upd_time time p blks1) x]. {
        apply /hasP. exists b. by rewrite mem_filter Hto. 
        by rewrite Hidb.
      }
      rewrite Hhas1.
      (*This result is needed in multiple places:*)
      have Hntheq: 
      nth block_inhab [seq x <- blks1 | not_timed_out (upd_time time p blks1) x]
      (find (fun b0 : block => blk_id b0 == fd_blockId p)
         [seq x <- blks1 | not_timed_out (upd_time time p blks1) x]) =
      nth block_inhab [seq x <- blks2 | triv_timeout (upd_time time p blks2) x]
      (find (fun b0 : block => blk_id b0 == fd_blockId p)
         [seq x <- blks2 | triv_timeout (upd_time time p blks2) x]). {
        apply find_uniq_eq=>//; last by
        move=> x; rewrite !mem_filter/= =>/andP[_ Hinx];
        apply Hinvar.
        all: apply blk_count; apply sorted_filter=>//; try apply
          blk_order_trans.
        apply Hdecinv.
      }
      (*Now we prove each result in turn*)
      split_all=>//.
      * by rewrite/= Hntheq.
      * move =>/= b'.
        rewrite !mem_insert Hntheq => /orP[/eqP Hb | Hinrest]; first
        by rewrite Hb eq_refl.
        apply /orP. right. move: Hinrest. 
        rewrite !mem_rem_uniq.
        -- rewrite /in_mem/= => /andP[Hbnot].
          rewrite Hbnot !mem_filter/= => /andP[_ Hinb']. by apply Hinvar.
        -- apply (blk_order_sort_uniq Hsort2').
        -- apply (blk_order_sort_uniq Hsort1'). 
      * move=> b'.
        rewrite !mem_insert !Hntheq => 
          /orP[/eqP Hb | Hinrest2]; first by
          rewrite Hb eq_refl.
        rewrite negb_orb => /andP[Hneq Hnotinrest].
        move: Hnotinrest Hinrest2. rewrite !mem_rem_uniq;
          [|apply (blk_order_sort_uniq Hsort2')|
            apply (blk_order_sort_uniq Hsort1')].
        setoid_rewrite <- addn1. (*to stop simpl*)
        rewrite /in_mem/=. rewrite negb_and => Htemp /andP[Hneq' Hinb2'].
        move: Hinb2'. rewrite mem_filter/==> Hinb2'.
        move: Htemp. rewrite Hneq'/= mem_filter.
        rewrite negb_and => /orP[Htimeout | Hnotin]; last first.
        -- (*from IH*)
          move: Hinvar => [_ [/( _ _ Hinb2' Hnotin) 
            [p' [l1 [l2 [Hids [Hprev [Hnotinp' Hthresh]]]]]] _]].
          exists p'. exists l1. exists (l2 ++ [:: p]).
          split_all=>//. by rewrite Hprev -!catA. rewrite addn1.
          rewrite undup_fst_rcons.
          case Hin: (p \in prev); first by apply Hthresh.
          move: Hthresh.
          rewrite size_cat addn1 !Nat2Z.inj_succ. simpl in *; lia.
        -- (*Now we have the timeout case: TODO: separate lemma*)
          (*TODO: *)
          move: Htimeout. rewrite /not_timed_out Z.leb_antisym => Htimeout.
          rewrite negbK in Htimeout.
          move: Htimeout => /Z.ltb_spec0 Htimeout.
          (*OK, we still need to know that blocks in blks2
            have a packet which has the time of arrival*)
            (*TODO: start with this tomorrow*)
          

          Print decoder_timeout_invar.
          (*Idea: put new invariant that all blocks in blks
            are not timed out- can show preserved very easily
            then: we know that b' was not timed out,
            so it must be the case that p was a new packet not
            in an existing block and the time *)



          eapply Zgt_trans. 2: apply Hthresh.
          move: Ht
          have: 
          Search (?x - ?y <= ?z + ?w)%Z.
          
          lia.
          move: Hthresh.
        
          
          rewrite /=. lia.

        have Hinb1': b' \in blks1.
        
        Hinb1.

        Search (negb ())
        
      
      rewrite /=.
        
        apply Hin. by [].

  
  - (*This*)
  split_all=>//.
  - rewrite /= !update_dec_state_gen_eq //=. 
    (*See if there is a block with p inside blks1*)
    (*TODO: case before split?*)
    case : (existsb (fun b => blk_id b == fd_blockId p) blks1) /existsbP 
      =>// [[b /andP[Hinb /eqP Hbid]] | Hnotex].
    + (*This block is definitely in blks2*)
      have Hinb2: b \in blks2 by apply Hinvar.
      have Hhas2: (has (fun b0 : block => blk_id b0 == fd_blockId p)
        [seq x <- blks2 | triv_timeout (upd_time time p blks2) x]).
        apply /hasP. exists b. by rewrite mem_filter/=. by rewrite Hbid.
      rewrite Hhas2.
      (*Now we see if this block (or any block) is in blks1 after timeouts*)
      case Hto: (not_timed_out (upd_time time p blks1) b).
      * (*If it was, then we have the "has" predicate*)
        have Hhas1: (has (fun b0 : block => blk_id b0 == fd_blockId p)
        [seq x <- blks1 | not_timed_out (upd_time time p blks1) x]).
          apply /hasP. exists b. by rewrite mem_filter Hto.
          by rewrite Hbid.
        rewrite Hhas1/=.
        (*Now, we can show that the two blocks are equal
        TODO: make separate lemma or maybe change case and split*)
        f_equal. f_equal.
        apply find_uniq_eq=>//; last by
          move=> x; rewrite !mem_filter/= =>/andP[_ Hinx];
          apply Hinvar.
        all: apply blk_count; apply sorted_filter=>//; try apply
          blk_order_trans.
        apply Hdecinv.
      * (*If not, then we have a timed out block, so we can
        use the [decoder_timeout_invar] to get a packet that
        arrived too long ago*)
        exfalso. move: Hto. rewrite upd_time_spec; 
          [| apply Hdecinv| apply (decoder_invar_allid Hwf'); apply Hdecinv].
        rewrite /not_timed_out Z.leb_antisym => Hto. 
        apply negbFE in Hto.
        move: Hto => /Z.ltb_spec0 Hto.
        case: Hdecinv => [Htime [Hstart [Htimed [Hsort Hsubs]]]].
        move: Hto.
        rewrite Htime. move: Hstart => /( _ b Hinb) 
          [p' [l1 [l2 [Hidp' [Hprev [Hnotin Hblackt]]]]]].
        rewrite -Hblackt => Hto.
        apply (@same_block_close prev p p' l1 l2) =>//.
          by rewrite Hidp' Hbid.
        have->:(l1 ++ [:: p'] ++ l2 ++ [:: p]) = prev ++ [:: p]
          by rewrite Hprev !catA.
        rewrite !undup_fst_rcons (negbTE Hnotin) size_cat addn1.
        move: Hto.
        case : (existsb [eta packet_in_block p] blks1) /existsbP => 
          [[b' /andP[Hinb' Hidb']] | ].
        {
          have->//: p \in prev; try lia. by apply (decoder_invar_inprev Hwf' Hsubs Hinb'). 
        }
        move => Hnotex.
        case Hinp: (p \in prev); last by rewrite size_cat addn1; lia.
        (*In this case, we use the 3rd decoder invariant to get
          our contradiction - TODO reduce duplication*)
        exfalso. clear -Htimed Hinp Hnotex Hcond.
        move: Htimed => /(_ _ Hinp Hnotex) 
          [p' [l1 [l2 [Hids [Hprev [Hnotin Htimeout]]]]]].
        apply (@same_block_close prev p p' l1 l2)=>//.
        have->:(l1 ++ [:: p'] ++ l2 ++ [:: p]) = prev ++ [:: p]
          by rewrite Hprev !catA.
        by rewrite !undup_fst_rcons (negbTE Hnotin) Hinp size_cat addn1.
    + (*Now there is nothing inside blks1. *)
      have Hhas1: has (fun b : block => blk_id b == fd_blockId p)
      [seq x <- blks1 | not_timed_out (upd_time time p blks1) x] = false. {
        apply negbTE. apply /hasP. move=> [x Hx Hxid]. apply Hnotex.
        exists x. move: Hx. rewrite mem_filter => /andP[_ Hinx].
        by rewrite Hinx Hxid.
      }
      rewrite Hhas1.
      (*Now we determine if there is a block with this idx in
        blks2.*)
      case: (existsb (fun b => blk_id b == fd_blockId p) blks2) /existsbP 
      =>// [[b /andP[Hinb /eqP Hbid]] | Hnotex2]; last first.
      * (*If not, then easy to show that these are equal*)
        have Hhas2: ( has (fun b : block => blk_id b == fd_blockId p)
        [seq x <- blks2 | triv_timeout (upd_time time p blks2) x] = false). {
          apply negbTE. apply /hasP. move=> [x Hx Hxid]. apply Hnotex2.
          exists x. move: Hx. rewrite mem_filter => /andP[_ Hinx].
          by rewrite Hinx Hxid.
        }
        rewrite Hhas2/=.
        (*Need to know time invariant here*)
        by rewrite Htimes.
      * (*If there is, then we get a contradiction since a packet
          appeared too long ago*)
        exfalso. apply Hnotex. exists b. rewrite Hbid eq_refl andbT.
        by apply Hbpin21.
  - (*Now we prove that the invariant is preserved*)  
    rewrite /to_nto_invar; split_all; last first.
    + 
    + move=> b.
      rewrite !update_dec_state_gen_eq //.
      (*Once again, we proceed by cases (TODO: should we do
        cases like this? i think so - should refactor)*)
      case Hhas2: 



          NOTE: Here is by blockID
          
          so idea:
          1. for any block in blks1, blk_id b == fd_blockId p =
            (p \in prev ==> packet_in_block p b)

          2. have block with p's id in blks2 ->
              no block with p's id in blks1 ->
              contradiction

          3. have block with p's id in blks2 <-> block with p's id in blks1

          4. therefore, have block that p is in blks2 ->

          
          *)



        lia.


        have Hcon: black_time b + threshold < time + 1 -> False; last first.
           apply Hcon. move: Hto. case: (existsb [eta packet_in_block p] blks1); lia.
        case: Hdecinv => [Htime [Hstart [Htimed [Hsort Hsubs]]]].
        rewrite Htime. move: Hstart => /( _ b Hinb) 
          [p' [l1 [l2 [Hidp' [Hprev [Hnotin Hblackt]]]]]].
        rewrite -Hblackt => Hto'.
        apply (@same_block_close prev p p' l1 l2) =>//.
        by rewrite -Hbid Hidp'.
        have->:(l1 ++ [:: p'] ++ l2 ++ [:: p]) = prev ++ [:: p]
          by rewrite Hprev !catA.
        rewrite !undup_fst_rcons (negbTE Hnotin).
        (*lia is being annoying*)
        have to'': Z.of_nat (size (undup_fst prev)) - 
        Z.of_nat (size (undup_fst l1)) > threshold by lia.
        case Hpin: (p \in prev); rewrite !size_cat/=.
        {
          rewrite Nat2Z.inj_add. lia.
          Search (Z.of_nat (?x + ?y)%coq_nat).
          eapply Zgt_trans. 2: apply to''.  lia.
          Search Z.gt "trans".
          eapply Z.gt_trans.
        }
        lia.
        existsb [eta packet_in_block p] blks1

        
        
          2: apply Hdecinv.
        
      + (*If not, then see if we have such a block in blks2*)
        case Hhas2: (has (fun b : block => blk_id b == fd_blockId p)
        [seq x <- blks2 | triv_timeout (upd_time time p blks2) x]).
        * (*Here, we use the invariant to get a contradiction*)
          move: Hhas2 => /hasP [b]; rewrite mem_filter => /andP[_ Hinb] /eqP Hbid.
          (*packets too far apart - TODO: put previous lemma and 
          generalize (or maybe just that one)*)
          exfalso.
          have Hnotin1: b \notin blks1. 
          case: Hinvar => [_ /(_ b Hinb)].
          apply (@same_block_close )

    --  


    (*case : (existsb (fun b => blk_id b == fd_blockId p) blks1) /existsbP 
    =>// [[b /andP[Hinb /eqP Hbid]] | Hnotex].*)
    + (*In this case, there is one inside blks2. Thus, these blocks
      must be the same (TODO: make this a separate
      lemma and use it later - we prove MORE than just about packet
      output, prove that blocks are the same)*) 
      have Hinb2: b \in blks2 by apply Hinvar.
      rewrite !update_dec_state_gen_eq.
      * case Hhas1: (has (fun b0 : block => blk_id b0 == fd_blockId p)
        [seq x <- blks1 | not_timed_out (upd_time time p blks1) x]). 
      -- have:= Hhas1 => /hasP [b'] Hinb' /eqP Hidb'. 
        move: Hinb'. rewrite mem_filter => /andP[Htob' Hinb']/=.
        have Hhas2: has (fun b0 : block => blk_id b0 == fd_blockId p)
        [seq x <- blks2 | triv_timeout (upd_time time p blks2) x]. {
          apply /hasP. exists b'. rewrite mem_filter/=.
          by apply Hinvar. by rewrite Hidb'.
        }
        rewrite Hhas2/=. f_equal. f_equal.
        apply find_uniq_eq=>//; last by
          move=> x; rewrite !mem_filter/= =>/andP[_ Hinx];
          apply Hinvar.
        all: apply blk_count; apply sorted_filter=>//; try apply
          blk_order_trans.
        apply Hdecinv.
      --  
          
        
        
        try (apply blk_count; apply sorted_filter=>//).

        case: (findP (fun b0 : block => blk_id b0 == fd_blockId p)
        [seq x <- blks1 | not_timed_out (upd_time time p blks1) x]).
        by rewrite Hhas1. move => i1 Hi1 Hnth1 Hbefore1/=.
        case: (findP (fun b0 : block => blk_id b0 == fd_blockId p)
        [seq x <- blks2 | triv_timeout (upd_time time p blks2) x]).
        by rewrite Hhas2. move=> i2 Hi2 Hnth2 Hbefore2/=.
        (*Need to know that these two blocks are equal - TODO separate
          lemma for some of this?*)
        f_equal. f_equal. 

        rewrite /=.
        
      
      
      rewrite


      (*TODO: lemma above*) admit.
    + (*maybe - lemma saying if none, then equal to insert (maybe)*)
      (*Then we see if such a block is in blks2*)
      case : (existsb (fun b => blk_id b == fd_blockId p) blks2) /existsbP 
      =>// [[b /andP[Hinb /eqP Hbid]] | Hnotex2].
      * move: Hinvar => [_ /(_ b Hinb)].
        have->: b \notin blks1. case Hinb1: (b \in blks1) =>//.
        exfalso. apply Hnotex. exists b. by rewrite Hinb1 Hbid eq_refl.
        move=>/(_ isT) [p' [l1 [l2 [Hidp' [Hprev [Hnotin Htimeout]]]]]].
        (*Here, we get a contradiction because packets too far apart*)
        (*TODO: put previous result in separate lemma*)
        admit.
      * (*Here, we need a lemma that says about the insertion to
        prove that they are equal: all we really need for this part is:
        if no block, then packets outputted are those from (create_block_black))*)
        admit.
  - rewrite /to_nto_invar. split.
    + (*Yeah, we will need some sort of lemma like above, let's try to
      prove it*)

  
  
  rewrite /=.
  
  move: blks1 Hinvar.
  rewrite /decoder_one_step/=/triv_timeout. 
  elim: blks2 => [//= [//= | bhd1 btl1] | bhd2 btl2 ].
  - move=> _ Hinvar. split_all=>//.
    rewrite /to_nto_invar/=. split=>//.
    move=> b. by rewrite !in_cons orbF =>->.
  - move=> Hinvar. exfalso.
    move: Hinvar. rewrite /to_nto_invar => [[Hcon _]].
    by move: Hcon => /(_ bhd1 (mem_head _ _)).
  - move => Hinvar [//= ]. 
    
    
    
    => Hinv1. by []. 

  decoder_multiple_steps prev packets 


Lemma decoder_timeout_notimeout_multiple: 
  forall blocks prev packets sent time,
  wf_packet_stream (prev ++ packets) ->
  reorder_dup_cond (prev ++ packets) ->
  decoder_timeout_invar blocks prev time ->


  (decoder_multiple_steps prev packets blocks sent time).1.1.2



  wf_packet_stream (prev ++ [:: p]) ->
  reorder_dup_cond (prev ++ [:: p]) ->
  decoder_timeout_invar blocks prev time ->
  decoder_timeout_invar (decoder_one_step blocks p time).1.1
    (prev ++ [:: p]) (decoder_one_step blocks p time).2.

End DecodeTimeouts.