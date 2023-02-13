Require Import VST.floyd.functional_base.
Require Import AbstractEncoderDecoder.
Require Import CommonSSR.
Require Import ZSeq.
Require Import Encoder.
Require Import DecoderGeneric.
Require Import Block.
Require Import CommonFEC.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.

(*We first prove the versions for the infinite-precision versions*)

Section GenericCorrect.

Variable upd_time : Z -> fpacket -> seq block -> Z.
Variable not_timeout: Z -> block -> bool.

(*One of our correctness theorems: all outputted packets are valid.*)
  
(* The first (strongest) version of the theorem*)
Theorem all_decoded_in_Z: forall (orig : list packet) (encoded received: list fpacket)
  (decoded: list packet) (enc_params: list (Z * Z)),
  Zlength orig = Zlength enc_params ->
  (forall k h, (k, h) \in enc_params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  encoded = (encoder_all_steps orig enc_params).2 ->
  (forall p, p \in received -> p \in encoded) ->
  decoded = (decoder_all_steps_gen upd_time not_timeout received).1.2 ->
  forall p, p \in decoded -> exists p', p' \in orig /\ remove_seqNum p = remove_seqNum p'.
Proof.
  move => orig encoded received decoded enc_params Hleno Hencparams Hallvalid Hallenc Hseqnum
    Henc Hloss Hdec p Hind; subst.
  (*Step 1: since p is in the decoder, it must have been in [rse_decode_func] at some point*)
  move: Hind. rewrite decoder_all_steps_concat // in_mem_In in_concat => [[dec]] [Hinp].
  rewrite In_Znth_iff; zlist_simpl => [[i] [Hi]]. zlist_simpl. move => Hdec. subst. move: Hinp. rewrite -in_mem_In => Hp.
  have Hleno': size orig = size enc_params by rewrite !size_Zlength Hleno.
  have Hwfenc: wf_packet_stream (encoder_all_steps orig enc_params).2 by apply rse_encode_stream_wf.
  have Hwfrec: wf_packet_stream received by apply (wf_substream Hwfenc).
  have Hidx: 0 <= Z.of_nat (fd_blockIndex (Znth i received)) < fd_k (Znth i received) + fd_h (Znth i received). {
    split; try lia; apply Hwfrec. rewrite in_mem_In. by apply Znth_In. }
  have Hcurrh: 0 <= fd_h (Znth i received). { apply Hwfrec. rewrite in_mem_In. by apply Znth_In. }
  have Hsubstream: forall x : fpacket_eqType,
    x \in Znth i received :: sublist 0 i received ->
    x \in (encoder_all_steps orig enc_params).2. {
      move=> x. rewrite in_cons => /orP[/eqP Hx | Hinrec].
      - rewrite Hx. apply Hloss. apply /inP. by apply Znth_In.
      - apply Hloss. by apply (mem_sublist Hinrec).
    }
  (*Step 2: Thus, p either was in received or was produced by running [decode_block].*) 
  apply in_decode_func_in_block in Hp =>//.
  case : Hp => [[Hp Hpar] | [b1 [b2 [Hinb2 [Hsub [Hrec Hpin]]]]]].
  - (*In the first case, this is easy, since all data packets produced by the encoder are in the original stream*)
    exists p. split => //. rewrite -Hp. apply (rse_encode_stream_from_orig Hencparams) => //.
    apply Hloss. rewrite in_mem_In. by apply Znth_In.
  - (*In the second case, we use lots of previous results. Namely, we need to know that b is a subblock of
      some block b' that is well-formed and encoded (it comes directly from the encoder). We need 2 layers, 
      since the subblock in the decoder is a subblock of a block in (get_blocks received), which is a subblock
      of a block from (get_blocks encoded). Once we have this, we can use [in_decode_block_in_data], which
      uses the correctness of the (Reed Solomon) decoder*)
    have [b' [Hsubb' [Hwfb' [Hencb' Hgetb]]]]: exists b', subblock b1 b' /\ block_wf b' /\ block_encoded b' /\
      b' \in (get_blocks (encoder_all_steps orig enc_params).2) . {
      (*Idea: b2 is a subblock of something in received (by sublist), 
        which is a subblock of something in encoded (by sublist), then
        we use transitivity*)
      have [b3 [Hinb3 Hsubb3]]:= 
        (get_blocks_sublist Hwfenc Hsubstream Hinb2).
      exists b3. split_all=>//.
      - by apply (subblock_trans Hsub).
      - by apply (rse_encode_stream_blocks_wf Hencparams Hallvalid).
      - apply (rse_encode_stream_recoverable_encoded Hencparams Hallvalid) => //.
        by apply (subblock_recoverable (subblock_trans Hsub Hsubb3)).
    }
    (*Now we apply [in_decode_block_in_data]*)
    have [p' [Hpin' Hpnum]]:=in_decode_block_in_data Hwfb' Hencb' Hsubb' Hrec Hpin.
    exists (p_packet p'). split => //.
    have Hpar': fd_isParity p' = false. apply Hwfb'=>//. 
    apply (rse_encode_stream_from_orig Hencparams) => //.
    apply (get_blocks_in_orig Hwfenc Hgetb). by apply data_in_block.
  - by apply (wf_substream Hwfenc Hsubstream).
Qed.

End GenericCorrect.

Require Import ByteFacts.
Require Import Reorder.
Require Import DecoderTimeouts.
Require Import DecoderNoTimeouts.

(*Correctness With Timeouts/Reordering*)
Section TimeoutCorrect.

Local Open Scope nat_scope.

Variable k: Z.
Variable h: Z.
Variable k_bound: (0 < k <= fec_n - 1 - fec_max_h)%Z.
Variable h_bound: (0 < h <= fec_max_h)%Z.

Definition loss_cond_i (sent received: list fpacket) (i: nat) : Prop :=
  (*At least k unique packets are received from 
    packets i(k+h) to (i+1)(k+h)*)
    let n := Z.to_nat (k+h) in
    i < size sent %/ n ->
    count (fun x => x \in received) 
      (undup (sublist (Z.of_nat (i * n)) (Z.of_nat ((i+1) * n)) sent))
      >= Z.to_nat k.

(*The condition on loss*)
Definition loss_cond (sent received: list fpacket) : Prop :=
  forall i, loss_cond_i sent received i.

(*If at least k of packets (i(k+h)) to (i+1)(k+h) in
  the encoded stream are recovered, then all packets
  from ik to (i+1)k in the original stream are recovered*)
Theorem block_i_recovered_Z (orig : list packet) 
  (encoded received: list fpacket)
  (decoded: list packet) (enc_params: list (Z * Z))
  (d m: nat) (threshold: Z) (i: nat):
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  Zlength enc_params = Zlength orig ->
  all (fun x => x == (k, h)) enc_params ->
  encoded = (encoder_all_steps orig enc_params).2 ->
  (*No new packets are added*)
  (forall p, p \in received -> p \in encoded) ->
  (*At least k packets in i(k+h) to (i+1) (k+h) received*)
  i < size orig %/ Z.to_nat k ->
  loss_cond_i encoded received i->
  (*Bound on reordering and duplication*)
  duplicates_bounded received fpacket_inhab m ->
  reorder_bounded encoded received d ->
  decoded = (decoder_all_steps threshold received).1.2 ->
  (*Threshold is large enough*)
  (threshold >= k + h + Z.of_nat (2 * d + m))%Z ->
  (*Then any packet from ik to (i+1)k in the original list
    appears in the output*)
  forall p, p \in 
    sublist (Z.of_nat i * k) (Z.of_nat (i+1) * k) orig -> 
    exists p', p' \in decoded /\ remove_seqNum p = remove_seqNum p'.
Proof.
  move => Hallvalid Hallenc Hseqnum Hlenenc Hallkh Henc Hsub Hi Hloss Hdups 
    Hreord Hdec Hthresh p Hinp.
  (*First, we use [encoder_concat_nochange_eq] to reason about
    the encoder with no parameter changes*)
  have Henceq: enc_params = zseq (Zlength orig) (k, h) by
    apply zseq_eq.
  rewrite Henceq in Henc. clear Hlenenc Hallkh Henceq enc_params.
  move: Henc. rewrite encoder_all_steps_concat 
    -encoder_concat_nochange_eq => Henc.
  (*Next, use [encoder_boundaries_i] to get the boundary*)
  have:=(encoder_boundaries_i k_bound h_bound 
    Hallvalid Hallenc Hseqnum Hinp Hi)=>/=.
  rewrite -Henc.
  set (b := nth block_inhab (rev (encoder_concat_nochange k h orig).1.1) i).
  move=> [Hinb [Hencb [Hwfb [Hbk [Huniq [Hall [Hszenc [f [Hpf [Hparf Hinfb]]]]]]]]]].
  (*Now, we use [decoder_timeout_notimeout_all] to show that the
    decoder is equivalent to one without timeouts. We first need
    the preconditions:*)
  have Hwf: wf_packet_stream encoded. {
    (*ugh, dont want to reverse*)
    rewrite Henc encoder_concat_nochange_eq -encoder_all_steps_concat.
    apply rse_encode_stream_wf=>//.
    - move=> k' h'. by rewrite /zseq mem_nseq => /andP[_ /eqP[]->->].
    - by rewrite /zseq size_nseq Zlength_size Nat2Z.id.
  } 
  have Hwf': wf_packet_stream received by
    apply (wf_substream Hwf); apply Hsub.
  have Hreordup: 
    reorder_dup_cond threshold (Z.to_nat k) (Z.to_nat h) d m received. {
    rewrite /reorder_dup_cond. split_all=>//.
    - rewrite /bounded_reorder_list.
      (*Here we use [u_seqNum_reorder_bound] to show that the 
        [reorder_bounded] condition implies that packets do not get too
        far apart *)
      move=> p1 p2 Hinp1 Hinp2 Hideq.
      apply u_seqNum_reorder_bound with(sent:=encoded)=>//.
      + rewrite Henc encoder_concat_nochange_eq -encoder_all_steps_concat.
        apply rse_encode_stream_uniq=>//.
        * move=> k' h'. by rewrite /zseq mem_nseq => /andP[_ /eqP[]->->].
        * by rewrite /zseq size_nseq Zlength_size Nat2Z.id.
      + rewrite Henc.
        by apply same_block_index=>//; rewrite -Henc; apply Hsub.
    - move: Hthresh. rewrite !Nat2Z.inj_add. lia.
  }
  move: Hdec. rewrite (decoder_timeout_notimeout_all Hwf' Hreordup) 
    => Hdec.
  (*Now, we use the loss condition to show that enough packets are seen,
    hence we can apply [all_packets_in_block_recovered] to get
    the results we want*)
  move: Hloss.
  have Hi': let n:= Z.to_nat (k + h) in 
    size encoded %/ n = size orig %/ Z.to_nat k. {
    rewrite Hszenc/= Z2Nat.inj_add; try lia.
    to_ssrnat.
    set n:=(Z.to_nat k + Z.to_nat h).
    rewrite divnDl; last by apply dvdn_mull; rewrite dvdnn.
    have Hn0: 0 < n by subst n; solve_by_lia.
    rewrite mulnK // (@divn_small (_ %% _)); first by rewrite addn0.
    have Hk0: 0 < Z.to_nat k by apply /ltP; lia.
    apply (ltn_leq_trans (ltn_pmod _ Hk0)). subst n.
    by rewrite leq_addr.
  }
  move: Hi'. rewrite /loss_cond_i /= => -> /(_ Hi) Hloss.
  have Hinpdat: packet_in_data f b by 
    apply (wf_in_data Hwfb Hinfb (negbTE Hparf)).
  have Hkh: Z.to_nat (k+h) = Z.to_nat k + Z.to_nat h by
    rewrite Z2Nat.inj_add //; lia.
  rewrite Hkh in Hloss.
  have:=(all_packets_in_block_recovered Hwf Hsub 
    Hwfb Hencb Hinb Hbk Hall Hloss Hinpdat).
  rewrite -Hdec => [[Hinf | Hinf0]].
  - exists p. by rewrite -Hpf.
  - exists (p_packet f <| p_seqNum := 0 |>). split=>//.
    by rewrite /remove_seqNum/= Hpf.
Qed.

(*A corollary: if for all i, the loss condition holds, then any
  packet in the first |O|/k packets (ie: all but the last, in-progress
  batch) is recovered*)
Corollary all_packets_recovered_Z (orig : list packet) 
  (encoded received: list fpacket)
  (decoded: list packet) (enc_params: list (Z * Z))
  (d m: nat) (threshold: Z):
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  Zlength enc_params = Zlength orig ->
  all (fun x => x == (k, h)) enc_params ->
  encoded = (encoder_all_steps orig enc_params).2 ->
  (*No new packets are added*)
  (forall p, p \in received -> p \in encoded) ->
  (*At least k packets in i(k+h) to (i+1) (k+h) received, for all i*)
  (forall i, i < size orig %/ Z.to_nat k -> 
    loss_cond_i encoded received i) ->
  (*Bound on reordering and duplication*)
  duplicates_bounded received fpacket_inhab m ->
  reorder_bounded encoded received d ->
  decoded = (decoder_all_steps threshold received).1.2 ->
  (*Threshold is large enough*)
  (threshold >= k + h + Z.of_nat (2 * d + m))%Z ->
  (*We cannot make guarantees about the last portion of the list*)
  forall p, p \in 
    sublist 0 (Z.of_nat (size orig %/ Z.to_nat k * Z.to_nat k)) orig -> 
    exists p', p' \in decoded /\ remove_seqNum p = remove_seqNum p'.
Proof.
  move=> Hallvalid Hallenc Hseqnum Hlenenc Hallkh Henc Hsub Hloss Hdups 
  Hreord Hdec Hthresh p Hinp.
  (*The only thing we need is to find which batch the packet is in,
    which we get from [find_batch]*)
  have Hszsub: size (sublist 0 (Z.of_nat (size orig %/ Z.to_nat k * Z.to_nat k)) orig) =
    (size orig %/ Z.to_nat k * Z.to_nat k). {
      rewrite size_Zlength Zlength_sublist; try lia.
      rewrite Zlength_size. apply inj_le. to_ssrnat.
      by rewrite leq_trunc_div.
  }
  have Hk0: 0 < Z.to_nat k by apply /ltP; lia.
  apply (@find_batch _  _(Z.to_nat k)) in Hinp=>//; last first.
    rewrite Hszsub. apply dvdn_mull. by rewrite dvdnn.
  case: Hinp => [i [Hisz Hinp]].
  move: Hisz. rewrite Hszsub mulnK // => Hi.
  apply (block_i_recovered_Z Hallvalid Hallenc Hseqnum Hlenenc Hallkh Henc Hsub Hi 
    (Hloss i Hi) Hdups Hreord Hdec Hthresh).
  move: Hinp. rewrite !Z2Nat.id; try lia.
  rewrite sublist_sublist0 //; try lia.
  (*All we need is a bounds proof*)
  have Hk: k = Z.of_nat (Z.to_nat k) by lia.
  rewrite {1 2}Hk.
  split; try lia.
  - to_ssrnat. by rewrite addn1 mulSn leq_addl.
  - rewrite {1}Hk. to_ssrnat. by rewrite leq_pmul2r// addn1.
Qed.

(*A simple corollary: if we send some multiple of k packets,
  then all packets are received*)
Corollary all_packets_recovered_div_Z (orig : list packet) 
  (encoded received: list fpacket)
  (decoded: list packet) (enc_params: list (Z * Z))
  (d m: nat) (threshold: Z):
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  Zlength enc_params = Zlength orig ->
  all (fun x => x == (k, h)) enc_params ->
  encoded = (encoder_all_steps orig enc_params).2 ->
  (*No new packets are added*)
  (forall p, p \in received -> p \in encoded) ->
  (*At least k packets in i(k+h) to (i+1) (k+h) received, for all i*)
  (forall i, i < size orig %/ Z.to_nat k -> 
    loss_cond_i encoded received i) ->
  (*Bound on reordering and duplication*)
  duplicates_bounded received fpacket_inhab m ->
  reorder_bounded encoded received d ->
  decoded = (decoder_all_steps threshold received).1.2 ->
  (*Threshold is large enough*)
  (threshold >= k + h + Z.of_nat (2 * d + m))%Z ->
  (Z.to_nat k) %| size orig ->
  forall p, p \in orig -> 
    exists p', p' \in decoded /\ remove_seqNum p = remove_seqNum p'.
Proof.
  move => Hallvalid Hallenc Hseqnum Hlenenc Hallkh Henc Hsub Hloss Hdups 
  Hreord Hdec Hthresh Hdiv p Hinp.
  apply (all_packets_recovered_Z Hallvalid Hallenc Hseqnum 
    Hlenenc Hallkh Henc Hsub Hloss Hdups Hreord Hdec Hthresh).
  by rewrite divnK // -Zlength_size sublist_same; try lia.
Qed. 

(*One more collary, combining the two previous ones:
  under these conditions, the original and decoded streams
  have the same elements up to sequence numbers*)
Corollary orig_decoded_streams_Z (orig : list packet) 
  (encoded received: list fpacket)
  (decoded: list packet) (enc_params: list (Z * Z))
  (d m: nat) (threshold: Z):
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  Zlength enc_params = Zlength orig ->
  all (fun x => x == (k, h)) enc_params ->
  encoded = (encoder_all_steps orig enc_params).2 ->
  (*No new packets are added*)
  (forall p, p \in received -> p \in encoded) ->
  (*At least k packets in i(k+h) to (i+1) (k+h) received for all i*)
  (forall i, i < size orig %/ Z.to_nat k -> 
    loss_cond_i encoded received i) ->
  (*Bound on reordering and duplication*)
  duplicates_bounded received fpacket_inhab m ->
  reorder_bounded encoded received d ->
  decoded = (decoder_all_steps threshold received).1.2 ->
  (*Threshold is large enough*)
  (threshold >= k + h + Z.of_nat (2 * d + m))%Z ->
  (Z.to_nat k) %| size orig ->
  map remove_seqNum orig =i map remove_seqNum decoded.
Proof.
  move => Hallvalid Hallenc Hseqnum Hlenenc Hallkh Henc Hsub Hloss Hdups 
  Hreord Hdec Hthresh Hdiv.
  move=> p.
  case: (p \in [seq remove_seqNum i | i <- orig]) /mapP =>
    [[p'] Hinp' Hp'| Hnotin].
  - symmetry. apply /mapP.
    apply (all_packets_recovered_div_Z Hallvalid Hallenc Hseqnum 
    Hlenenc Hallkh Henc Hsub Hloss Hdups Hreord Hdec Hthresh)
    in Hinp'=>//.
    case: Hinp' => [p2 [Hinp2 Hremp2]]. exists p2=>//.
    by rewrite Hp'.
  - symmetry. apply /mapP => [[p2]] Hinp2 Hpp2.
    apply Hnotin. 
    (*Need 1 assumption for [all_decoded_in]*) 
    have Hkhb: (forall k' h', (k', h') \in enc_params -> 
      (0 < k' <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h)%Z /\
      (0 < h' <= ByteFacts.fec_max_h)%Z) by
      move=> k' h' Hin; move: Hallkh => /allP /(_ _ Hin) /eqP []->->.
    have[p1 [Hinp1 Hp1]]:=(all_decoded_in_Z (esym Hlenenc) Hkhb Hallvalid Hallenc 
      Hseqnum Henc Hsub Hdec Hinp2).
    exists p1=>//. by rewrite Hpp2.
Qed.

End TimeoutCorrect.

(*Now prove these theorems for the machine-length version of the
  decoder*)
Require Import DecoderMachine.
Section Machine.

(*The weakest spec: all data packets that are received by the
  decoder are returned*)
Section Weak.

(*Doesn't even need anything about encoder*)
Theorem all_data_sent: forall (threshold: int) 
  (received: list fpacket) (p: fpacket),
  p \in received ->
  fd_isParity p = false ->
  p_packet p \in (decoder_all_steps_m threshold received).1.2.
Proof.
  apply all_data_outputted_m.
Qed.

End Weak.

(*Intermediate spec: if the FEC params are within the correct bounds
  and all packet sequence numbers are at most 2^63-1, then the
  decoder only outputs packets that were originally given to the encoder,
  modulo sequence numbers.*)
Section Intermediate.

Theorem all_decoded_in (orig : list packet) 
  (encoded received: list fpacket)
  (decoded: list packet) (enc_params: list (Z * Z))
  (threshold: int) :
  Int.unsigned threshold < Int.half_modulus / 2 ->
  Zlength orig = Zlength enc_params ->
  (forall k h, (k, h) \in enc_params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  (forall (p: packet), p \in orig ->
    Z.of_nat (p_seqNum p) < Int64.half_modulus) ->
  encoded = (encoder_all_steps orig enc_params).2 ->
  (forall p, p \in received -> p \in encoded) ->
  decoded = (decoder_all_steps_m threshold received).1.2 ->
  forall p, p \in decoded -> 
    exists p', p' \in orig /\ remove_seqNum p = remove_seqNum p'.
Proof.
  move=>Hthresh Hlenorig Hparams
    Hallval Hallenc Huniq Hseqs Henc Hsublist Hdec p Hinp.
  apply (@all_decoded_in_Z upd_time (not_timed_out (Int.unsigned threshold))
    orig encoded received decoded enc_params)=>//.
  rewrite Hdec decoder_all_steps_m_eq //.
  move=> p' Hinp'.
  apply (encoder_bounds Hparams Hallval Hallenc Huniq)=>//.
  - move: Hlenorig. rewrite !Zlength_size. lia.
  - rewrite -Henc. by apply Hsublist.
Qed.

End Intermediate.

(*The strongest spec: If the above holds and additionally,
  we do not change the FEC parameters,
  there is not too much reordering or duplication and
  for block i (i < size orig / k), if at most h packets
  from i(k+h) to (i+1) (k+h) in the encoded stream are lost,
  then all packets from ik to (i+1)k from the original stream
  are recovered.
  The corollaries (after) show that if all such blocks satisfy
  the condition, all packets are recovered.*)
Section Strong.

Variable k: Z.
Variable h: Z.
Variable k_bound: (0 < k <= fec_n - 1 - fec_max_h)%Z.
Variable h_bound: (0 < h <= fec_max_h)%Z.

Theorem block_i_recovered (orig : list packet) 
  (encoded received: list fpacket)
  (decoded: list packet) (enc_params: list (Z * Z))
  (d m: nat) (threshold: int) (i: nat):
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  (forall (p: packet), p \in orig ->
  Z.of_nat (p_seqNum p) < Int64.half_modulus) ->
  Zlength enc_params = Zlength orig ->
  all (fun x => x == (k, h)) enc_params ->
  encoded = (encoder_all_steps orig enc_params).2 ->
  (*No new packets are added*)
  (forall p, p \in received -> p \in encoded) ->
  (*At least k packets in i(k+h) to (i+1) (k+h) received*)
  (i < size orig %/ Z.to_nat k)%N ->
  loss_cond_i k h encoded received i->
  (*Bound on reordering and duplication*)
  duplicates_bounded received fpacket_inhab m ->
  reorder_bounded encoded received d ->
  decoded = (decoder_all_steps_m threshold received).1.2 ->
  (*Threshold is large enough but less than 2^30*)
  (k + h + Z.of_nat (2 * d + m) <= Int.unsigned threshold <
    Int.half_modulus / 2)%Z ->
  (*Then any packet from ik to (i+1)k in the original list
    appears in the output*)
  forall p, p \in 
    sublist (Z.of_nat i * k) (Z.of_nat (i+1) * k) orig -> 
    exists p', p' \in decoded /\ remove_seqNum p = remove_seqNum p'.
Proof.
  move=>Hallval Hallenc Huniq Hseqs Hsz Hallkh Henc Hsub Hi Hloss 
    Hdups Hreord Hdec Hthresh p. 
  apply (@block_i_recovered_Z k h k_bound h_bound orig encoded
    received decoded enc_params d m (Int.unsigned threshold))=>//; try lia.
  rewrite Hdec decoder_all_steps_m_eq //; try lia.
  move=> p' Hinp'.
  apply (@encoder_bounds orig enc_params)=>//.
  - move=> k' h' Hin.
    by move: Hallkh => /allP /(_ _ Hin) /eqP [] ->->.
  - move: Hsz. by rewrite !Zlength_size; lia.
  - rewrite -Henc. by apply Hsub.
Qed.

Theorem all_packets_recovered (orig : list packet) 
  (encoded received: list fpacket)
  (decoded: list packet) (enc_params: list (Z * Z))
  (d m: nat) (threshold: int):
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  (forall (p: packet), p \in orig ->
    Z.of_nat (p_seqNum p) < Int64.half_modulus) ->
  Zlength enc_params = Zlength orig ->
  all (fun x => x == (k, h)) enc_params ->
  encoded = (encoder_all_steps orig enc_params).2 ->
  (*No new packets are added*)
  (forall p, p \in received -> p \in encoded) ->
  (*At least k packets in i(k+h) to (i+1) (k+h) received for all i*)
  (forall i, (i < size orig %/ Z.to_nat k)%N ->
    loss_cond_i k h encoded received i) ->
  (*Bound on reordering and duplication*)
  duplicates_bounded received fpacket_inhab m ->
  reorder_bounded encoded received d ->
  decoded = (decoder_all_steps_m threshold received).1.2 ->
  (*Threshold is large enough but less than 2^30*)
  (k + h + Z.of_nat (2 * d + m) <= Int.unsigned threshold <
    Int.half_modulus / 2)%Z ->
  (*We cannot make guarantees about the last portion of the list*)
  forall p, p \in 
    sublist 0 (Z.of_nat (size orig %/ Z.to_nat k * Z.to_nat k)) orig -> 
    exists p', p' \in decoded /\ remove_seqNum p = remove_seqNum p'.
Proof.
  move=>Hallval Hallenc Huniq Hseqs Hsz Hallkh Henc Hsub Hloss 
    Hdups Hreord Hdec Hthresh p. 
  apply (@all_packets_recovered_Z k h k_bound h_bound orig encoded
    received decoded enc_params d m (Int.unsigned threshold))=>//; try lia.
  rewrite Hdec decoder_all_steps_m_eq //; try lia.
  move=> p' Hinp'.
  apply (@encoder_bounds orig enc_params)=>//.
  - move=> k' h' Hin.
    by move: Hallkh => /allP /(_ _ Hin) /eqP [] ->->.
  - move: Hsz. by rewrite !Zlength_size; lia.
  - rewrite -Henc. by apply Hsub.
Qed.

(*If the length of orig is a multiple of k, then the output list
  has the same elements as the original input list*)
Theorem orig_decoded_streams (orig : list packet) 
  (encoded received: list fpacket)
  (decoded: list packet) (enc_params: list (Z * Z))
  (d m: nat) (threshold: int):
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  (forall (p: packet), p \in orig ->
    Z.of_nat (p_seqNum p) < Int64.half_modulus) ->
  Zlength enc_params = Zlength orig ->
  all (fun x => x == (k, h)) enc_params ->
  encoded = (encoder_all_steps orig enc_params).2 ->
 (*No new packets are added*)
 (forall p, p \in received -> p \in encoded) ->
 (*At least k packets in i(k+h) to (i+1) (k+h) received for all i*)
 (forall i, (i < size orig %/ Z.to_nat k)%N ->
   loss_cond_i k h encoded received i) ->
  (*Bound on reordering and duplication*)
  duplicates_bounded received fpacket_inhab m ->
  reorder_bounded encoded received d ->
  decoded = (decoder_all_steps_m threshold received).1.2 ->
  (*Threshold is large enough but less than 2^30*)
  (k + h + Z.of_nat (2 * d + m) <= Int.unsigned threshold <
    Int.half_modulus / 2)%Z ->
  (Z.to_nat k) %| size orig ->
  map remove_seqNum orig =i map remove_seqNum decoded.
Proof.
  move=>Hallval Hallenc Huniq Hseqs Hsz Hallkh Henc Hsub Hloss 
    Hdups Hreord Hdec Hthresh p. 
  apply (@orig_decoded_streams_Z k h k_bound h_bound orig encoded
    received decoded enc_params d m (Int.unsigned threshold))=>//; try lia.
  rewrite Hdec decoder_all_steps_m_eq //; try lia.
  move=> p' Hinp'.
  apply (@encoder_bounds orig enc_params)=>//.
  - move=> k' h' Hin.
    by move: Hallkh => /allP /(_ _ Hin) /eqP [] ->->.
  - move: Hsz. by rewrite !Zlength_size; lia.
  - rewrite -Henc. by apply Hsub.
Qed.

End Strong.

End Machine.