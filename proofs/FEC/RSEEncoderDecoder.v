(*Implement the abstract encoder/decoder relations from AbstractEncoderDecoder with RSE algorithm *)
Require Import VST.floyd.functional_base.
Require Import AssocList.
Require Import IP.
Require Import AbstractEncoderDecoder.
Require Import CommonSSR.
Require Import ReedSolomonList.
Require Import ZSeq.
Require Import Endian.
Require Import ByteFacts.
(*Require Import ByteField.*) (*For byte equality - TODO: move to ByteFacts*)
Require Import Block.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.



(*The decoder is more complicated because of timeouts. We include a list of values indicating whether a timeout
  has occurred*)

(*The timeout part: we take in the state representing whether each block is timed out or not
  and we update the state as the actuator does*)
(*Note: since the state is abstract, we will assume it is long enough*)
Fixpoint update_past_blocks (blocks: list block) (curr: fpacket) (time: Z) :
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
Definition update_dec_state (blocks: list block) (curr: fpacket) (time : Z) : 
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

(*The decoder simply repeatedly applies the above function, generating output packets and updating the state*)
Definition decoder_all_steps (received: list fpacket) (times: list Z) : (list block * list packet) :=
  foldl (fun (acc: list block * list packet) (x: fpacket * Z) =>
    let t := update_dec_state acc.1 x.1 x.2 in
    (t.1, acc.2 ++ t.2)) (nil, nil) (combine received times).

Definition decoder_block_state (received: list fpacket) (times: list Z) :=
  (decoder_all_steps received times).1.

(*Now we can define the decoder function and predicate*)
Definition rse_decode_func (received: list fpacket) (curr: fpacket) 
  (times: list Z) (time: Z) : list packet :=
  (update_dec_state (decoder_all_steps received times).1 curr time).2.

Definition rse_decoder : (@decoder fec_data) :=
  fun (received: list fpacket) (decoded: list (list packet)) (curr: fpacket) (new: list packet) =>
    exists (times: list Z) (time: Z),
      Zlength times = Zlength received /\
      new = rse_decode_func received curr times time.

End Decoder.

Definition rse_decoder_list := AbstractEncoderDecoder.decoder_list fpacket_inhab rse_decoder.

(*This shows that the rse_decoder_list definition is usable: for any possible states, if we 
  decode using those states, we still get the predicate*)
Lemma rse_decoder_list_add: forall (received : list fpacket) (curr: fpacket)
  (decoded: list (list packet)),
  rse_decoder_list received decoded ->
  forall (t: Z) (times: list Z),
    Zlength times = Zlength received ->
    rse_decoder_list (received ++ [curr]) (decoded ++ [rse_decode_func received curr times t]).
Proof.
  move => received curr decoded. rewrite /rse_decoder_list /AbstractEncoderDecoder.decoder_list
    => [[Hllen Hith]] t times Hstslen.
  split.
  - rewrite !Zlength_app. list_solve.
  - move => i. rewrite Zlength_app Zlength_cons /= => Hi. have Hi' := (z_leq_n_1 (proj2 Hi)). (*why cant lia do this*)
    case Hi' => [Hiprev | Hicurr].
    + rewrite !sublist_app1; try lia. rewrite !Znth_app1; try lia. apply Hith. lia.
    + rewrite Hicurr. rewrite !sublist_app1; try lia. rewrite !sublist_same //.
      rewrite !Znth_app2; try lia. rewrite Hllen !Z.sub_diag !Znth_0_cons.
      rewrite /rse_decoder. exists times. exists t. by [].
Qed.


(*Next steps
  1. prove specific encoder properties we need (4 of them - wf stream, get_blocks perm, all blocks wf, 
  and recoverable -> encoded)
  2. Prove theorem for encoder_all_steps and decoder_all_steps (maybe decode_func)
  3. Prove that encoder is injective in params - in 2 steps (for 1 step and all steps), then extend to
    encoder_list
  4. Prove full theorem (and we will see if 3+4 are needed*) 

(** Final Correctness Theorem*)

Section FinalCorrect.

(* The first (strongest) version of the theorem*)

Theorem all_decoded_in: forall (orig : list packet) (encoded received: list fpacket)
  (decoded: list packet) (enc_params: list (Z * Z)) (dec_times: list Z),
  Zlength orig = Zlength enc_params ->
  Zlength received = Zlength dec_times ->
  (forall k h, In (k, h) enc_params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  encoded = (rse_encode_all orig enc_params).2 ->
  (forall p, p \in received -> p \in encoded) ->
  decoded = (decoder_all_steps received dec_times).2 ->
  forall p, p \in decoded -> exists p', p' \in orig /\ remove_seqNum p = remove_seqNum p'.
Proof.
  move => orig encoded received decoded enc_params dec_params Hleno Hlenr Hencparams Hallvalid Hallenc Hseqnum
   Henc Hloss Hdec p Hind; subst.
  (*Step 1: since p is in the decoder, it must have been in [rse_decode_func] at some point*)
  move: Hind. rewrite decoder_all_steps_concat // in_mem_In in_concat => [[dec]] [Hinp].
  rewrite In_Znth_iff; zlist_simpl => [[i] [Hi]]. zlist_simpl. move => Hdec. subst. move: Hinp. rewrite -in_mem_In => Hp.
  have Hleno': size orig = size enc_params by rewrite !size_length -!ZtoNat_Zlength Hleno.
  have Hwfenc: wf_packet_stream (rse_encode_all orig enc_params).2 by apply rse_encode_stream_wf.
  have Hwfrec: wf_packet_stream received by apply (wf_substream Hwfenc).
  have Hidx: 0 <= Int.unsigned (fd_blockIndex (Znth i received)) < fd_k (Znth i received) + fd_h (Znth i received). {
    apply Hwfrec. rewrite in_mem_In. by apply Znth_In. }
  have Hcurrh: 0 <= fd_h (Znth i received). { apply Hwfrec. rewrite in_mem_In. by apply Znth_In. }
  (*Step 2: Thus, p either was in received or was produced by running [decode_block].*) 
  apply in_decode_func_in_block in Hp => //; last first.
    rewrite !size_length -!ZtoNat_Zlength. list_solve.
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
      b' \in (get_blocks (rse_encode_all orig enc_params).2) . {
      move: Hb. rewrite !cat_app -!sublist_last_1; try lia. rewrite in_mem_In => Hb.
      have Htb: In b (decoder_block_state (sublist 0 (i + 1) received) (sublist 0 (i + 1) dec_params)) by [].
      apply decoder_all_steps_state_subblocks in Htb.
      (*The blocks from (get_blocks received)*)
      case : Htb => [b2 [Hinb2 Hsub2]].
      have [b1 [Hinb1 Hsub1]]: exists b1, In b1 (get_blocks (rse_encode_all orig enc_params).2) /\ subblock b2 b1. {
        apply (@get_blocks_sublist _ (sublist 0 (i + 1) received)) => // x Hinx. apply Hloss.
        move: Hinx. rewrite !in_mem_In => Hsub. by apply sublist_In in Hsub. }
      exists b1. have Hbb1: subblock b b1 by apply (subblock_trans Hsub2). split_all => //.
      - apply (rse_encode_stream_blocks_wf Hencparams Hallvalid) => //. by rewrite in_mem_In.
      - apply (rse_encode_stream_recoverable_encoded Hencparams Hallvalid) => //. by rewrite in_mem_In.
        by apply (subblock_recoverable Hbb1).
      - by rewrite in_mem_In.
      - apply (wf_substream Hwfrec). move => x. rewrite !in_mem_In => Hin. by apply sublist_In in Hin.
      - rewrite !size_length -!ZtoNat_Zlength. list_solve.
    }
    (*Now we apply [in_decode_block_in_data]*)
    have [p' [Hpin Hpnum]]:=in_decode_block_in_data Hwfb' Hencb' Hsubb' Hrec Hp.
    exists (p_packet p'). split => //.
    have Hpar': fd_isParity p' = false. apply Hwfb'. by rewrite -in_mem_In.
    apply (rse_encode_stream_from_orig Hencparams) => //.
    apply (get_blocks_in_orig Hwfenc Hgetb). by rewrite mem_cat Hpin.
Qed.

(*The last step is to prove the [valid_encoder_decoder] version of the theorem. We prove it using the above theorem*)
(*TODO move*)

(*The key difference is that we need to know that we can get the list of encoder params to show that the encoded 
  outputs actually come from repeated (consistent) iterations of the encoder. We do so with
  the following alternate version of the encoder which outputs a list (list packet) rather than just
  the full concatenated list*)


(*TODO: move pmap stuff*)

Lemma pmap_Zlength: forall {A: eqType} (s: seq (option A)) (Hall: all isSome s),
  Zlength (pmap id s) = Zlength s.
Proof.
  move => A s. elim : s => [// | h t /= IH /andP[Hh Hallt]].
  move: Hh. case: h => // x _/=. apply IH in Hallt. list_solve.
Qed.

Lemma pmap_Znth: forall {A: eqType} `{Inhabitant A} (s: seq (option A)) (Hall: all isSome s) i,
  0 <= i < Zlength s ->
  Some (Znth i (pmap id s)) = Znth i s.
Proof.
  move => A Hinhab s Hall i Hi. rewrite -!nth_Znth //. 2: by rewrite pmap_Zlength.
  rewrite -!nth_nth (nth_pmap Inhabitant_option Hinhab) //.
  rewrite size_length -ZtoNat_Zlength. apply /ltP. simpl in *. lia.
Qed.

Lemma pmap_sublist: forall {A: eqType} (s: seq (option A)) (Hall: all isSome s) lo hi,
  0 <= lo <= hi ->
  hi <= Zlength s ->
  sublist lo hi (pmap id s) = pmap id (sublist lo hi s).
Proof.
  move => A s. elim : s => [// _ lo hi Hlohi Hi /= | h t /= IH /andP[Hh Hallt] lo hi Hlohi Hhi/=].
  - have->/=: hi = 0 by list_solve. have->/=: lo = 0 by list_solve. by rewrite sublist_nil.
  - move: Hh Hhi. case: h => //= x _ Hhi.
    have [Hlo | Hlo]: lo = 0 \/ 0 < lo by lia.
    + subst. have[Hhi0 | Hhi0]: hi = 0 \/ 0 < hi by lia.
      * subst. by rewrite !sublist_nil.
      * rewrite !sublist_0_cons; try lia. rewrite /= IH //; try lia. list_solve.
    + rewrite !sublist_S_cons; try lia. apply IH => //. lia. list_solve.
Qed. 

Import AbstractEncoderDecoder.

(*Now the crucial lemma: if "encoded" satisfies [encoder_list], then in fact is is really [rse_encode_concat] for
  some params, which are all valid. This is where we use the fact that there could have only been 1 set of
  parameters to produce a consistent output*)
(*TODO: we could just give the actual list?*)
Lemma encoder_list_concat_equiv: forall orig encoded,
  encoder_list rse_encoder orig encoded ->
  exists (enc_params : list (Z * Z)),
    Zlength enc_params = Zlength orig /\
    encoded = (rse_encode_concat orig enc_params).2 /\
    (forall k h, In (k, h) enc_params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h).
Proof.
  move => orig encoded. rewrite /encoder_list /rse_encoder => [[Hlens Hith]].
  exists (pmap id (map get_encode_params encoded)).
  have Hall: all isSome [seq get_encode_params i | i <- encoded]. {
      apply /allP => x. rewrite in_mem_In In_Znth_iff => [[j]] [Hj].
      rewrite Zlength_map in Hj.
      rewrite Znth_map //. have Hj': 0 <= j < Zlength orig by rewrite Hlens.
      apply Hith in Hj'. case: Hj' => [k' [h' [Hk' [Hh' Hjth]]]]. rewrite Hjth.
      move => Hget. rewrite encode_func_get_params' in Hget. by subst.
    }
  split_all.
  - by rewrite pmap_Zlength // Zlength_map.
  - f_equal. apply Znth_eq_ext.
      by rewrite rse_concat_Zlength // pmap_Zlength // Zlength_map.
    move => i Hi. rewrite -Hlens in Hi. have Hallith:=Hith. move: Hith => /(_ _ Hi) [k [h [Hk [Hh Hith]]]].
    rewrite Hith. rewrite /rse_encode_func'/=.
    rewrite rse_concat_nth //; last first.
      by rewrite pmap_Zlength // Zlength_map.
    have Hi': 0 <= i < Zlength [seq get_encode_params i | i <- encoded]. {
      rewrite Zlength_map. by rewrite -Hlens. }
    have Hith': Znth i (pmap id [seq get_encode_params i | i <- encoded]) = (k, h). {
      have Hpith:=(@pmap_Znth _ (@Inhabitant_pair Z Z Inhabitant_Z Inhabitant_Z) _ Hall _ Hi').
      move: Hpith. rewrite Znth_map; try lia. by rewrite Hith encode_func_get_params'/= => [[Hith']].
      (*what is wrong with lia?*) by rewrite -Hlens. } 
    f_equal.
    + rewrite pmap_sublist //; try lia. rewrite -map_sublist //. (*why doesn't lia work?*) rewrite Zlength_map.
      apply Z.lt_le_incl. rewrite -Hlens. apply (proj2 Hi).
    + by rewrite Hith'.
    + by rewrite Hith'.
  - move => k h. rewrite In_Znth_iff => [[i]]. rewrite pmap_Zlength // => [[Hi Hpith]].
    have Hpith':=(@pmap_Znth _ (@Inhabitant_pair Z Z Inhabitant_Z Inhabitant_Z) _ Hall _ Hi).
    move: Hpith'. have Hiorig: 0 <= i < Zlength orig. { move: Hi. rewrite Zlength_map. by rewrite Hlens. (* lia.*) }
    rewrite Znth_map; try lia. rewrite Hpith. move: Hith => /( _ _ Hiorig) => [[k' [h' [Hk' [Hh' Hith]]]]].
    rewrite Hith encode_func_get_params'/= => [[Hkeq] Hheq]. by subst. (*ugh*) by rewrite -Hlens.
Qed.

Corollary encoder_list_all_equiv: forall orig encoded,
  encoder_list rse_encoder orig encoded ->
  exists (enc_params : list (Z * Z)),
    Zlength enc_params = Zlength orig /\
    concat encoded = (rse_encode_all orig enc_params).2 /\
    (forall k h, In (k, h) enc_params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h).
Proof.
  move => orig encoded Henclist. apply encoder_list_concat_equiv in Henclist.
  case: Henclist => [p [Hlen [Henc Hallkh]]]. exists p. split_all => //.
  by rewrite rse_encode_all_concat Henc.
Qed.

(*TODO: move*)
Lemma rse_decode_func_all: forall rec curr sts st x,
  Zlength rec = Zlength sts ->
  x \in (rse_decode_func rec curr sts st) ->
  x \in (decoder_all_steps (rec ++ [curr]) (sts ++ [st])).2.
Proof.
  move => rec curr sts st x Hlens. rewrite /rse_decode_func /decoder_all_steps coqlib4.combine_app' //.
  rewrite foldl_cat/= mem_cat. move => Hin. apply /orP. by right.
Qed.


(*The final theorem: the encoder-decoder pair is valid*)
Theorem rse_encoder_decoder_valid : valid_encoder_decoder valid_packet encodable fec_data_eq_dec 
  fpacket_inhab rse_encoder rse_decoder.
Proof.
  rewrite /valid_encoder_decoder. move => orig received encoded decoder [l Hl] Hvalid Henc Huniq Henclist/=.
  apply encoder_list_all_equiv in Henclist. case: Henclist => [enc_params [Henclen [Hencall Hparams]]].
  rewrite /decoder_list => [[Hlendec Hdecith]] Hlos x.
  rewrite in_mem_In in_concat => [[l1 [Hinl1 Hindecs]]].
  move: Hindecs. rewrite In_Znth_iff => [[i]]. rewrite -Hlendec => [[Hi Hl1]].
  subst. move: Hdecith => /( _ _ Hi). rewrite /rse_decoder => [[dec_states] [st]] [Hdeclen Hdeci].
  apply (@all_decoded_in orig (concat encoded) (sublist 0 (i+1) received)
    (decoder_all_steps (sublist 0 (i+1) received) (dec_states ++ [st])).2 enc_params (dec_states ++ [st])) => //.
  - rewrite sublist_last_1; try lia. rewrite !Zlength_app !Zlength_cons /=. lia.
  - move => p. rewrite in_mem_In => Hinp.
    rewrite /valid_loss in Hl. apply (Hl _ _ Hlos). rewrite in_mem_In. by apply sublist_In in Hinp.
  - rewrite sublist_last_1; try lia. apply rse_decode_func_all => //. by rewrite -Hdeci in_mem_In.
Qed.

End FinalCorrect.

End Correctness.
