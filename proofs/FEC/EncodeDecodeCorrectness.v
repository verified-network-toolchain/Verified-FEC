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

Section GenericCorrect.

Variable upd_time : Z -> fpacket -> seq block -> Z.
Variable not_timeout: Z -> block -> bool.

(*One of our correctness theorems: all outputted packets are valid.
  TODO: do relational version later*)
  
(* The first (strongest) version of the theorem*)

Theorem all_decoded_in: forall (orig : list packet) (encoded received: list fpacket)
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
  have Hleno': size orig = size enc_params by rewrite !size_length -!ZtoNat_Zlength Hleno.
  have Hwfenc: wf_packet_stream (encoder_all_steps orig enc_params).2 by apply rse_encode_stream_wf.
  have Hwfrec: wf_packet_stream received by apply (wf_substream Hwfenc).
  have Hidx: 0 <= Z.of_nat (fd_blockIndex (Znth i received)) < fd_k (Znth i received) + fd_h (Znth i received). {
    split; try lia; apply Hwfrec. rewrite in_mem_In. by apply Znth_In. }
  have Hcurrh: 0 <= fd_h (Znth i received). { apply Hwfrec. rewrite in_mem_In. by apply Znth_In. }
  (*Step 2: Thus, p either was in received or was produced by running [decode_block].*) 
  apply in_decode_func_in_block in Hp =>//.
  case : Hp => [[b [Hb [Hrec Hp]]] | [Hp Hpar]]; last first.
  - (*In the first case, this is easy, since all data packets produced by the encoder are in the original stream*)
    exists p. split => //. rewrite -Hp. apply (rse_encode_stream_from_orig Hencparams) => //.
    apply Hloss. rewrite in_mem_In. by apply Znth_In.
  - (*In the second case, we use lots of previous results. Namely, we need to know that b is a subblock of
      some block b' that is well-formed and encoded (it comes directly from the encoder). We need 2 layers, 
      since the subblock in the decoder is a subblock of a block in (get_blocks received), which is a subblock
      of a block from (get_blocks encoded). Once we have this, we can use [in_decode_block_in_data], which
      uses the correctness of the (Reed Solomon) decoder*)
    have [b' [Hsubb' [Hwfb' [Hencb' Hgetb]]]]: exists b', subblock b b' /\ block_wf b' /\ block_encoded b' /\
      b' \in (get_blocks (encoder_all_steps orig enc_params).2) . {
      move: Hb. rewrite !cat_app -!sublist_last_1; try lia. move=> Hb.
      have Htb:=Hb.
      apply decoder_all_steps_state_subblocks in Htb.
      (*The blocks from (get_blocks received)*)
      case : Htb => [b2 [Hinb2 Hsub2]].
      have [b1 [Hinb1 Hsub1]]: exists b1, b1 \in (get_blocks (encoder_all_steps orig enc_params).2) /\ subblock b2 b1. {
        apply (@get_blocks_sublist _ (sublist 0 (i + 1) received)) => // x Hinx. apply Hloss.
        move: Hinx. rewrite !in_mem_In => Hsub. by apply sublist_In in Hsub. }
      exists b1. have Hbb1: subblock b b1 by apply (subblock_trans Hsub2). split_all => //.
      - by apply (rse_encode_stream_blocks_wf Hencparams Hallvalid).
      - apply (rse_encode_stream_recoverable_encoded Hencparams Hallvalid) => //.
        by apply (subblock_recoverable Hbb1).
      - apply (wf_substream Hwfrec). move => x. rewrite !in_mem_In => Hin. by apply sublist_In in Hin.
    }
    (*Now we apply [in_decode_block_in_data]*)
    have [p' [Hpin Hpnum]]:=in_decode_block_in_data Hwfb' Hencb' Hsubb' Hrec Hp.
    exists (p_packet p'). split => //.
    have Hpar': fd_isParity p' = false. apply Hwfb'=>//. 
    apply (rse_encode_stream_from_orig Hencparams) => //.
    apply (get_blocks_in_orig Hwfenc Hgetb). by apply data_in_block.
Qed.

End GenericCorrect.

Require Import ByteFacts.

(*Correctness With Timeouts/Reordering*)
Section TimeoutCorrect.

Local Open Scope nat_scope.

Variable k: Z.
Variable h: Z.
Variable k_bound: (0 < k <= fec_n - 1 - fec_max_h)%Z.
Variable h_bound: (0 < h <= fec_max_h)%Z.

(*The condition on loss*)
Definition loss_cond (sent received: list fpacket) : Prop :=
  (*No new packets are added*)
  (forall p, p \in received -> p \in sent) /\
  (*At least k unique packets are received from 
    packets i(k+h) to (i+1)(k+h)*)
  forall (i: nat),
    let n := Z.to_nat (k+h) in
    i < size sent %/ n ->
    count (fun x => x \in received) 
      (undup (sublist (Z.of_nat (i * n)) (Z.of_nat ((i+1) * n)) sent))
      >= Z.to_nat k.

(*Now we prove that this implies condition for decoder
  (with [encoder_boundaries_exist]). TODO: do we need
  condition that block in [get_blocks rec] is recoverable
  or that we have k packets in list (and hence can split) *)

End TimeoutCorrect.



