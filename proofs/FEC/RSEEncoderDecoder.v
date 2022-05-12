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
Require Import ByteField. (*For byte equality - TODO: move to ByteFacts*)
Require Import Block.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.

(** Encoder **)

Section Encoder.

Definition populate_packets (id: int) (model : packet) (contents: list (list byte)) : list packet :=
  map (fun l => let newHeader := copy_fix_header (p_header model) l in mk_pkt newHeader l id) contents.

(*Finally, we can define what it means to encode a block with a model*)
Definition encode_block_aux (b: block) (model: packet) : block * seq fec_packet_act :=
  let packetsNoFec := populate_packets (blk_id b) model 
     (encoder_list (blk_h b) (blk_k b) (blk_c b) (packet_mx b))  in
  let packetsWithFec := map_with_idx packetsNoFec (fun p i => 
    mk_fecpkt p (mk_data (blk_k b) (blk_h b) true (blk_id b) (Int.repr ((blk_k b) + i)))) in
  (b <| parity_packets := map Some packetsWithFec |>, packetsWithFec).

(*Encoding a block chooses an appropriate model packet - either the inputted packet
  or the last packet in the block*)
Definition encode_block (b: block) (o: option packet) : block * list fec_packet_act :=
  match (pmap id (data_packets b)), o with
  | nil, None => (b, nil) (*can't happen*)
  | _, Some p => encode_block_aux b p
  | h :: t, _ => encode_block_aux b (f_packet (last h (h :: t)))
  end.

(*From here, we need a few utility functions for block so we can create the encoder predicate*)

Definition get_fec_packet (p: packet) (b: block) : fec_packet_act :=
   mk_fecpkt p (mk_data (blk_k b) (blk_h b) false (blk_id b) (Int.repr (Zindex None (data_packets b)))).

Definition new_fec_packet (p: packet) (k: Z) (h: Z) : fec_packet_act :=
  mk_fecpkt p (mk_data k h false (p_seqNum p) Int.zero).

Definition add_packet_to_block_red (p: packet) (b: block) : block :=
  let idx := Zindex None (data_packets b) in
  b <| data_packets := upd_Znth idx (data_packets b) (Some (get_fec_packet p b)) |>.

Definition create_block_with_packet_red (p: packet) (k: Z) (h: Z) : block :=
  let f := new_fec_packet p k h in
  mk_blk (p_seqNum p) (upd_Znth 0 (zseq k None) (Some f)) (zseq h None) k h false 0.

(** Encoder predicate*)

(*TODO: change name state*)

(*We will write our encoder first as a function (with inputted k and h), then write the predicate, where
  we quantify over k and h*)
(*We include 2 pieces of state: the list of blocks include all previous blocks, and the current block is
  represented separately as a block option*)

(*For the situations when we start a new block*)
Definition encode_new (p: packet) (k' h': Z) : list block * option block * list fec_packet_act :=
    let blk := create_block_with_packet_red p k' h' in
    let t := encode_block blk (Some p) in
    if Z.eq_dec k' 1 then ([t.1], None, new_fec_packet p k' h' :: t.2) else (nil, Some blk, [new_fec_packet p k' h']).

(*For the situation when we add to an existing block*)
Definition encode_exist (p :packet) (b: block) : list block * option block * list fec_packet_act :=
    let newBlock := add_packet_to_block_red p b in
    let t := encode_block newBlock (Some p) in
    if Z.eq_dec (Zlength (filter isSome (data_packets newBlock))) (blk_k newBlock) then
      ([t.1], None, get_fec_packet p b :: t.2) else (nil, Some newBlock, [get_fec_packet p b]).

Definition rse_encode_gen (blocks: list block) (currBlock : option block) (curr: packet)
  (k h: Z) : list block * option block * list fec_packet_act :=
  match currBlock with
  | None => (*last block finished, need to create a new one*)
    let t := encode_new curr k h in
    (t.1.1 ++ blocks, t.1.2, t.2)
  | Some b =>
      if ~~(Z.eq_dec (blk_k b) k) || ~~(Z.eq_dec (blk_h b) h)
      then let t1 := encode_block b None in
           let t2 := encode_new curr k h in
           (t2.1.1 ++ [t1.1] ++ blocks, t2.1.2, t1.2 ++ t2.2)
      else
        let t := encode_exist curr b in
        (t.1.1 ++ blocks, t.1.2, t.2)
  end.

(*TODO: just use all steps version below*)

(*For proofs, a version which concatenates all of the results of rse_encode_gen*)
Definition rse_encode_all (orig: list packet) (params: list (Z * Z)) : list block * option block * list fec_packet_act :=
  foldl (fun (acc: list block * option block * list fec_packet_act) (x : packet * (Z * Z)) =>
   let t := rse_encode_gen acc.1.1 acc.1.2 x.1 x.2.1 x.2.2 in
    (t.1.1, t.1.2, acc.2 ++ t.2)) (nil, None, nil) (combine orig params).

Definition rse_encode_func orig params curr k h :=
  (rse_encode_gen (rse_encode_all orig params).1.1 (rse_encode_all orig params).1.2 curr k h).2.

(*For the final predicate, we need to find the past parameters that were used. We can do so with
  the following:*)

Definition get_encode_params (l: list fec_packet_act) : option (Z * Z) :=
  match filter (fun (x: fec_packet_act) => ~~ (fd_isParity x)) l with
  | [ :: p] => Some (fd_k p, fd_h p)
  | _ => None
  end.

Lemma encode_block_aux_filter: forall b p,
  [seq x <- (encode_block_aux b p).2 | ~~ fd_isParity (p_fec_data' x)] = [::].
Proof.
  move => b p. erewrite eq_in_filter. apply filter_pred0.
  move => x. rewrite in_mem_In /= In_Znth_iff; zlist_simpl. move => [i] [Hi]. zlist_simpl.
  by move <-.
Qed.

Lemma encode_block_filter : forall b o,
  [seq x <- (encode_block b o).2 | ~~ fd_isParity (p_fec_data' x)] = nil.
Proof.
  move => b o. rewrite /encode_block/=.
  case Hmap: (pmap id (data_packets b)) => [// | h t ]; case : o => [p |//]; apply encode_block_aux_filter.
Qed.

Lemma encode_func_get_params: forall l orig params curr k h,
  l = rse_encode_func orig params curr k h ->
  get_encode_params l = Some (k, h).
Proof.
  move => l orig params curr k h. rewrite /rse_encode_func /rse_encode_gen/encode_new/encode_exist/=/get_encode_params.
  case : (rse_encode_all orig params).1.2 => [b | ].
  - case Hneq: (~~ Z.eq_dec (blk_k b) k || ~~ Z.eq_dec (blk_h b) h).
    + case : (Z.eq_dec k 1) => Hk1 //=.
      * move ->. rewrite filter_cat/=.
        by rewrite encode_block_filter /= encode_block_filter.
      * move ->. rewrite filter_cat/=. by rewrite encode_block_filter.
    + apply orb_false_elim in Hneq.
        case : Hneq => [Hkeq Hneq]. apply negbFE in Hkeq. apply negbFE in Hneq. solve_sumbool.
      case: (Z.eq_dec
        (Zlength
           [seq x <- upd_Znth (Zindex None (data_packets b)) (data_packets b)
                       (Some (get_fec_packet curr b))
              | isSome x]) (blk_k b)) => /= Hk ->/=.
      * rewrite encode_block_filter. by subst. 
      * by subst.
  - case: (Z.eq_dec k 1) => Hk/= -> //=.
    by rewrite encode_block_filter.
Qed.

Corollary encode_func_get_params': forall orig params curr k h,
  get_encode_params (rse_encode_func orig params curr k h) = Some (k, h).
Proof.
  move => orig params curr k h. by eapply encode_func_get_params.
Qed. 

(*Then, we have our final function and predicate*)

Definition rse_encode_func' (orig: list packet) (encoded: list (list fec_packet_act)) (curr: packet) (param: Z * Z) :
  list fec_packet_act :=
  let prevStates := pmap id (map get_encode_params encoded) in
  rse_encode_func orig prevStates curr param.1 param.2.

Definition rse_encoder: (@encoder fec_data) :=
  fun orig encoded curr new =>
    exists (k h: Z),
    0 < k <= fec_n - 1 - fec_max_h /\ 0 < h <= fec_max_h /\
    new = rse_encode_func' orig encoded curr (k, h).

End Encoder.

(** The Decoder *)

Section Decoder.

(*First major step: what does it mean to decode a block?*)
(*[decoder_list] takes in a value i, representing the sublist of parities that we will look at
  to find xh parity packets. We will write a function to find that value so the user doesn't need
  to know it. TODO: maybe move to ReedSolomonList.v*)

Definition find_decoder_list_param (b: block) : Z :=
  let numMissing := Zlength (filter isNone (data_packets b)) in
  match (pick (fun (i: ordinal (Z.to_nat (Zlength (parity_packets b) + 1))) => 
    Z.eq_dec (Zlength (filter isSome (sublist 0 (Z.of_nat i) (parity_packets b)))) numMissing)) with
  | None => -1
  | Some i => Z.of_nat i
  end.

(*Lengths of stats, parity_mx*)
Lemma parity_mx_sublist_length: forall (i: nat) (s: seq (option fec_packet_act)),
Zlength [seq x <- sublist 0 (Z.of_nat i) s | isSome x] =
Zlength
  [seq x <- sublist 0 (Z.of_nat i)
              [seq match x with
                   | Some p => Some (p_contents (f_packet p))
                   | None => None
                   end
                 | x <- s]
     | isSome x].
Proof.
  move => i. elim : i => [s //= | i IH s].
  have->: (Z.of_nat i.+1) = Z.of_nat i + 1 by lia.
  have[Hin | Hout]: (Z.of_nat i + 1 <= Zlength s \/ Z.of_nat i + 1 >= Zlength s) by lia.
  - rewrite !(sublist_split 0 (Z.of_nat i) (Z.of_nat i + 1)); try lia; last first.
      rewrite Zlength_map; lia.
    rewrite !sublist_len_1; try(rewrite Zlength_map); try lia.
    rewrite !filter_cat !Zlength_app IH /=. f_equal.
    rewrite !Znth_map; try lia.
    by case : (Znth (Z.of_nat i) s).
  - rewrite !sublist_same_gen; try (rewrite Zlength_map); try lia.
    (*Case for whole list - easiest to do another induction here*)
    rewrite {IH Hout i}. elim : s => [//= | h t /= IH].
    case : h => [//= a | //=]. by rewrite !Zlength_cons IH.
Qed. 

Lemma proj_sumbool_false: forall {P Q: Prop} (a: {P} + {Q}), Coqlib.proj_sumbool a = false -> Q.
Proof.
  move => P Q a.
  by case: a.
Qed. 

(*TODO: CommonSSR?*)
Lemma nat_pred_bound: forall (m n: nat),
  (m < n)%N ->
  (m.-1 < n)%N.
Proof.
  move => m n Hmn.
  apply (leq_ltn_trans (leq_pred m) Hmn).
Qed.

Definition nat_pred_ord {n : nat} (x: 'I_n) : 'I_n :=
  Ordinal (nat_pred_bound (ltn_ord x)).
  
(*The condition we need for [decoder_list_correct]*)
Lemma find_decoder_list_param_correct_aux: forall (b: block),
  recoverable b ->
  0 <= find_decoder_list_param b <= (Zlength (parity_packets b)) /\
  Zlength (filter (fun x => Z.eq_dec (Byte.signed x) 1) (stats b)) =
  Zlength (filter isSome (sublist 0 (find_decoder_list_param b) (parity_mx b))).
Proof.
  move => b.
  rewrite /recoverable => Hge. apply proj_sumbool_true in Hge.
  rewrite /find_decoder_list_param.
  case: (pick (fun (i: ordinal (Z.to_nat (Zlength (parity_packets b) + 1))) => 
    Z.eq_dec (Zlength (filter isSome (sublist 0 (Z.of_nat i) (parity_packets b)))) 
    (Zlength (filter isNone (data_packets b))))) /pickP =>[i Hpick |Hpick].
  - apply proj_sumbool_true in Hpick.
    rewrite /stats filter_map /= !Zlength_map /preim. 
    rewrite (@eq_in_filter _ _ isNone); last first.
    + move => x. case : x => [x' /= Hinx| /=Hinx]. 
      * by rewrite /isNone Byte.signed_zero.
      * by rewrite /isNone Byte.signed_one.
    + split.
      * have: 0 <= Z.of_nat i < Zlength (parity_packets b) + 1 by apply ListMatrix.Z_ord_bound; list_solve. lia.
      * rewrite -Hpick /parity_mx.
      (*prove this case in separate lemma*)
      apply parity_mx_sublist_length.
  - (*Now we show that such a value has to exist*)
    (*Let's show that for all i, the length is smaller, not just non-equal
      TODO: generalize this? Doesn't depend on blocks/parities, etc. Is it useful?*)
    have Hlt: (forall (i:'I_(Z.to_nat (Zlength (parity_packets b) + 1) )), 
      (Zlength [seq x <- sublist 0 (Z.of_nat i) (parity_packets b) | isSome x]) <
           (Zlength [seq x <- data_packets b | isNone x])). {
      move => i. remember (nat_of_ord i) as x. move: i Heqx. elim : x => [/= i Hi|n IH i Hi].
      - (*if length 0, then we use 0 for Hpick - get contradiction*) 
        rewrite Zlength_nil. have [//|Heq]: (0 < Zlength [seq x <- data_packets b | isNone x] \/
          Zlength [seq x <- data_packets b | isNone x] = 0) by list_solve.
        move: Hpick => /(_ i). rewrite Heq =>Hpick. apply proj_sumbool_false in Hpick.
        move: Hpick. by rewrite -Hi /= Zlength_nil.
      - (*ok: use n=i.-1 (as ord), then split into sublist 0 n and last elt, 
          get from IH that lt, since +1, has to be < or <=, but cant be equal bf of Hpick, contradiction*)
        have Hi1n: n = (nat_pred_ord i) by rewrite /= -Hi -pred_Sn.
        move: IH => /(_ (nat_pred_ord i) Hi1n) => Hlens.
        have->:(Z.of_nat n.+1) = Z.of_nat n + 1 by lia.
        have Hbound: Z.of_nat n + 1 <= Zlength (parity_packets b). {
          have /ltP: (n.+1 < Z.to_nat (Zlength (parity_packets b) + 1))%N by rewrite Hi. lia. }
        rewrite (sublist_split 0 (Z.of_nat n) (Z.of_nat n + 1)); try lia.
        rewrite filter_cat Zlength_app sublist_len_1 /=; try lia.
        case Hnth: (Znth (Z.of_nat n) (parity_packets b)) => [y //= |//=].
        + rewrite Zlength_cons Zlength_nil /=. 
          have[//|Heq]: (Zlength [seq x <- sublist 0 (Z.of_nat n) (parity_packets b) | isSome x] + 1 < 
            Zlength [seq x <- data_packets b | isNone x] \/
             Zlength [seq x <- sublist 0 (Z.of_nat n) (parity_packets b) | isSome x] + 1 = 
            Zlength [seq x <- data_packets b | isNone x]) by lia.
          move: Hpick => /(_ i). (*TODO: better way than repeating this again*)
          rewrite -Hi. have->:(Z.of_nat n.+1) = Z.of_nat n + 1 by lia.
          rewrite (sublist_split 0 (Z.of_nat n) (Z.of_nat n + 1)); try lia.
          rewrite filter_cat Zlength_app sublist_len_1 /=; try lia.
          rewrite Hnth /= Zlength_cons Zlength_nil /= => Hneq.
          by apply proj_sumbool_false in Hneq.
      + rewrite Zlength_nil. lia. }
    (*Now we know that |found packets| + |found parities | >= k
      and |found packets| = k - |missing packets|, so
        |found parities| >= |missing packets|, a contradiction of Hlt
      when we instantiate with (Zlength parities)*)
    have Hpacklen: Zlength [seq x <- data_packets b | isSome x] + Zlength [seq x <- data_packets b | isNone x] =
      Zlength (data_packets b). {
      (*I will be lazy and prove by induction*)
      rewrite {Hge Hpick Hlt}. elim : (data_packets b) => [// | h t /= IH].
        case : h => [a /= | /=]; rewrite !Zlength_cons; lia. }
    have Hgeq: Zlength [seq x <- (parity_packets b) | isSome x] >= 
      Zlength [seq x <- data_packets b | isNone x]. {
      move: Hge. rewrite -Hpacklen => Hge.
      apply Z.ge_le in Hge. apply Zplus_le_reg_l in Hge. by apply Z.le_ge. (*why doesnt lia work?*) }
      have Hi: (Z.to_nat (Zlength (parity_packets b)) < (Z.to_nat (Zlength (parity_packets b) + 1)))%N. {
        apply /ltP. rewrite Z2Nat.inj_add; try lia. list_solve. }
      move: Hlt => /(_ (Ordinal Hi)) /=. rewrite Z2Nat.id; [| list_solve].
      rewrite sublist_same; lia.
Qed.

(*For convenience*)
Lemma find_decoder_list_param_correct: forall (b: block),
  recoverable b ->
  Zlength (filter (fun x => Z.eq_dec (Byte.signed x) 1) (stats b)) =
  Zlength (filter isSome (sublist 0 (find_decoder_list_param b) (parity_mx b))).
Proof.
  move => b Hrec. by apply find_decoder_list_param_correct_aux.
Qed.

Lemma find_decoder_list_param_correct_bound: forall (b: block),
  recoverable b ->
  0 <= find_decoder_list_param b <= (Zlength (parity_packets b)).
Proof.
  move => b Hrec. by apply find_decoder_list_param_correct_aux.
Qed.

(*Now we use [find_decoder_list_param] to find the appropriate sublist of parities*)
Definition decoder_list_block (b: block) : list (list byte) :=
  decoder_list (blk_k b) (blk_c b) (packet_mx b) (parity_mx b) (stats b) (lengths b) (find_decoder_list_param b).

(*NOTE: in black actuator, does NOT regenerate sequence number. We could figure it out from fecData if we needed*)
Definition packet_from_bytes (l: list byte) (i: int) : packet :=
  let (header, contents) := recover_packet l in
  mk_pkt header contents i.

(*If the block is well-formed, all the packets will be valid. But we prove this later*)
Definition decode_block (b: block) : list packet :=
  (*Only add missing packets*)
  foldl (fun acc i => let bytes := (Znth i (decoder_list_block b)) in
                      if isNone (Znth i (data_packets b)) && (Znth 0 bytes != Byte.zero) then 
                      acc ++ [packet_from_bytes (Znth i (decoder_list_block b)) Int.zero] else acc) 
    nil (Ziota 0 (blk_k b)).

(*TODO: deduce headers?*)

(*TODO: parity/ordering issue - for now assume it is correct*)

(*1. create block with packet*)
Definition create_block_with_fec_packet (p: fec_packet_act) (time : Z) : block :=
  let k := fd_k p in
  let h := fd_h p in
  let allPackets := upd_Znth (Int.unsigned (fd_blockIndex p)) (zseq (k + h) None) (Some p) in
  mk_blk (fd_blockId p) (sublist 0 k allPackets) (sublist k (k+h) allPackets) k h false time.

Definition create_block_with_packet_black (p: fec_packet_act) (time: Z) : block * list packet :=
  let new_block := create_block_with_fec_packet p time in
  let packets := (if (fd_isParity p) then nil else [p_packet p]) ++
    (if Z.eq_dec (fd_k p) 1 then (decode_block new_block) else nil) in
  let marked_block := if Z.eq_dec (fd_k p) 1 then new_block <| black_complete := true |> else new_block in
  (marked_block, packets).

(*2. add packet to block*)
Definition add_fec_packet_to_block (p: fec_packet_act) (b: block) : block :=
  let new_packets := upd_Znth (Int.unsigned (fd_blockIndex p)) 
    (data_packets b ++ parity_packets b) (Some p) in
  b <| data_packets := sublist 0 (blk_k b) new_packets |> 
      <| parity_packets := sublist (blk_k b) (blk_k b + blk_h b) new_packets |>.

Definition add_packet_to_block_black (p: fec_packet_act) (b: block) : block * list packet :=
  if black_complete b then (b, nil) else (*TODO: if this is a data packet, should it still be released?*)
    let new_block := add_fec_packet_to_block p b in 
    let packets := (if (fd_isParity p) then nil else [p_packet p]) ++
      (if recoverable new_block then (decode_block new_block) else nil) in
    let marked_block := if recoverable new_block then new_block <| black_complete := true |> else new_block in
    (marked_block, packets).

(*The decoder is more complicated because of timeouts. We include a list of values indicating whether a timeout
  has occurred*)
Definition int_le (x y: int) := Int.lt x y || Int.eq x y.

(*The timeout part: we take in the state representing whether each block is timed out or not
  and we update the state as the actuator does*)
(*Note: since the state is abstract, we will assume it is long enough*)
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

(*The decoder simply repeatedly applies the above function, generating output packets and updating the state*)
Definition decoder_all_steps (received: list fec_packet_act) (times: list Z) : (list block * list packet) :=
  foldl (fun (acc: list block * list packet) (x: fec_packet_act * Z) =>
    let t := update_dec_state acc.1 x.1 x.2 in
    (t.1, acc.2 ++ t.2)) (nil, nil) (combine received times).

Definition decoder_block_state (received: list fec_packet_act) (times: list Z) :=
  (decoder_all_steps received times).1.

(*Now we can define the decoder function and predicate*)
Definition rse_decode_func (received: list fec_packet_act) (curr: fec_packet_act) 
  (times: list Z) (time: Z) : list packet :=
  (update_dec_state (decoder_all_steps received times).1 curr time).2.

Definition rse_decoder : (@decoder fec_data) :=
  fun (received: list fec_packet_act) (decoded: list (list packet)) (curr: fec_packet_act) (new: list packet) =>
    exists (times: list Z) (time: Z),
      Zlength times = Zlength received /\
      new = rse_decode_func received curr times time.

End Decoder.

(*TODO: figure out what to do with this*)
Definition rse_decoder_list := AbstractEncoderDecoder.decoder_list fec_packet_act_inhab rse_decoder.

(*This shows that the rse_decoder_list definition is usable: for any possible states, if we 
  decode using those states, we still get the predicate*)
(*NOTE (TODO): This actually indicates a problem, I think - this is such a weak spec that we don't
  even have to add states that are consistent with the previous.
  I think the other definition should really be used - TODO: figure this out*)
Lemma rse_decoder_list_add: forall (received : list fec_packet_act) (curr: fec_packet_act)
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

(** Correctness Theorem **)

Section Correctness.

(*We can only give a weak correctness theorem: all packets produced by the decoder were in the original list.
  We would like to be able to say more, but timeouts ensure that there is little that can be guaranteed (unless
  we reason about specific sequences of timeouts)

  To prove the theorem, we need to show 3 main results
  1. Suppose we have a recoverable subblock of a well-formed, complete block. Then, decode_block gives back
     all the data packets that are missing from the subblock but found in the original block.
  2. Every block in the decoder's state is a subblock of a block that was produced by the encoder.
  3. Every block produced by the encoder is well formed, and is recoverable if it is complete.

  Together, these imply the result that we want. We start with Part 1:*)

(*Prove that if we have ANY recoverable subblock of a completed, well-formed block, 
  then decoder_list_block b gives the original packets. This is the core
  correctness theorem where we use [decoder_list_correct] *)
Section SubblockDecode.

Lemma subblock_add: forall h b1 b2,
  subblock b1 b2 ->
  subblock (add_fec_packet_to_block h b1) (add_fec_packet_to_block h b2).
Proof.
  move => h b1 b2. rewrite /subblock /add_fec_packet_to_block/= => [[Hid [Hopt1 [Hopt2 [Hk Hh]]]]].
  split_all => //; rewrite Hk ?Hh; apply subseq_option_sublist; apply subseq_option_upd_Znth; by apply subseq_option_app.
Qed.

(* A nontrivial theorem to prove that uses [decode_list_correct_full] to show that for ANY
  subblock of a well formed, complete block that has received at least k packets, we get 
  the packets of the original packet matrix, possibly padded with some zeroes*)
Theorem subblock_recoverable_correct: forall (b1 b2: block),
  block_wf b2 ->
  block_encoded b2 ->
  subblock b1 b2 ->
  recoverable b1 ->
  decoder_list_block b1 = pad_packets (packet_mx b2) (lengths b1) (blk_c b2). 
Proof.
  move => b1 b2 Hwf Hcomp Hsub Hrec. rewrite /decoder_list_block.
  have Hc: blk_c b1 = blk_c b2 by rewrite (blk_c_recoverable Hcomp Hsub Hrec).
  have Hwf': block_wf b1 by apply (subblock_wf Hwf Hsub). rewrite Hc.
  apply (decoder_list_correct_full (h:=(blk_h b1)) (xh:=Zlength [seq x <- (stats b1) | Z.eq_dec (Byte.signed x) 1])
    (data:=(packet_mx b2))); try (move: Hwf'; rewrite /block_wf !Zlength_map; list_solve).
  - move: Hwf'. by rewrite /block_wf => [[Hk _]].
  - by apply blk_c_pos.
  - move: Hwf'. by rewrite /block_wf => [[_ [Hh _]]].
  - rewrite find_decoder_list_param_correct //. eapply Z.le_trans. apply Zlength_filter.
    eapply Z.le_trans. apply sublist_max_length. rewrite /parity_mx Zlength_map.
    move: Hwf'. rewrite /block_wf. lia.
  - eapply Z.le_trans. apply Zlength_filter. rewrite /stats Zlength_map.
    move: Hwf'. rewrite /block_wf. lia.
  - have->:blk_h b1 = Zlength (parity_packets b1) by (move: Hwf'; rewrite /block_wf; lia).
    by apply find_decoder_list_param_correct_bound.
  - by [].
  - by rewrite find_decoder_list_param_correct.
  - move: Hwf Hsub; rewrite /block_wf /subblock /packet_mx Zlength_map; list_solve.
  - have Hcomp':=Hcomp. move: Hcomp'. rewrite /block_encoded => [[[p [Hinp Hlenp]] [_ [Hleq _]]]].
    rewrite Forall_forall /packet_mx => s. rewrite in_map_iff => [[x]].
    case : x => [p' [Hs Hinp'] |[Hs _]].
    + rewrite -Hs. by apply Hleq.
    + rewrite -Hs. have Hc':=(blk_c_pos Hwf Hcomp). list_solve.
  - move => i Hi. move: Hwf' Hsub Hwf; rewrite /block_wf /subblock => Hwf' Hsub Hwf.
    rewrite /stats /packet_mx !Znth_map; try lia.
    case Hnth: (Znth i (data_packets b1)) => [p |//].
    move => _. move: Hsub  => [_ [Hsub _]]. move: Hsub. rewrite /subseq_option.
    have Hi': 0 <= i < Zlength (data_packets b1) by lia.
    move => [Hlen H]; move: H => /(_ _ Hi') [Hith | Hith].
    by rewrite -Hith Hnth. by rewrite Hith in Hnth.
  - move => l. rewrite /parity_mx in_map_iff => [[o [Ho Hin]]].
    move: Ho Hin. case : o => [p |//] [Hl] Hin.
    have Hin': In (Some p) (parity_packets b2). { move: Hsub. rewrite /subblock => Hsub.
      eapply subseq_option_in. apply Hsub. by []. }
    rewrite -Hl.
    move: Hcomp. rewrite /block_encoded => [[ _ [Hlens _]]]. 
    by apply Hlens.
  - have Hlen: Zlength (parity_mx b1) = Zlength (parity_mx b2) by
      move: Hwf' Hwf Hsub; rewrite /block_wf /subblock /parity_mx !Zlength_map; list_solve.
    move: Hcomp. rewrite /block_encoded => [[_ [ _ [ _ Hval]]]].
    move: Hval Hsub. rewrite /subblock /parities_valid => Hval [ _ [ _ [Hsub Hlens]]].
    move => i j Hi Hj.
    move: Hval => /(_ i j). rewrite -Hc in Hj. rewrite -Hlen -(proj1 Hlens) -Hc => /(_ Hi Hj).
    move: Hsub; rewrite /subseq_option => [[_ Hsub]] Hb2.
    case Hnth: (Znth i (parity_mx b1)) => [p | //].
    have Hnth': Znth i (parity_mx b2) = Some p. { move: Hnth. rewrite /parity_mx !Znth_map.
      case Hith : (Znth i (parity_packets b1)) => [o |//] [Ho]. 
      move: Hsub. move: Hi. rewrite /parity_mx Zlength_map => Hi. move => /(_ i  Hi) [Hitheq | Hcon//].
        by rewrite -Hitheq Hith Ho.
        by rewrite Hcon in Hith.
      rewrite Hlen in Hi; move: Hi; rewrite /parity_mx Zlength_map; list_solve.
      move: Hi; rewrite /parity_mx Zlength_map; list_solve.
    }
    rewrite Hnth' in Hb2. by [].
Qed.


(*From two blocks, get the packets that are in 1 but not the other*)
Definition get_diff {A: Type} (l1 l2: list (option A)) : list A :=
 pmap id (map (fun (x: option A * option A) =>
    match x with
    | (None, Some y) => Some y
    | (_, _) => None
    end) (zip l1 l2)).

Definition get_block_diff (b1 b2: block) : list packet :=
  map (fun p => p <| p_seqNum := Int.zero |>) (map (@p_packet _) (get_diff (data_packets b1) (data_packets b2))).

(*An alternate formation of [decode_block] - TODO: is this better to use originally?*)
Definition decode_block' (b: block) : list packet :=
  pmap id (map (fun i =>
      let bytes := (Znth i (decoder_list_block b)) in
      if isNone (Znth i (data_packets b)) && (Znth 0 bytes != Byte.zero) then
        Some (packet_from_bytes bytes Int.zero) 
      else None) (Ziota 0 (blk_k b))).

Lemma decode_block_equiv: forall b,
  decode_block b = decode_block' b.
Proof.
  move => b. rewrite /decode_block /decode_block'.
  rewrite -(cat0s (pmap _ _)). remember (@nil packet) as base eqn : Hb. rewrite {1}Hb {Hb}. 
  move: base.
  elim (Ziota 0 (blk_k b)) => [//= base | h t /= IH base].
  - by rewrite cats0.
  - rewrite IH {IH}. case : (Znth h (data_packets b)) => [p// | /=].
    case : (Znth 0 (Znth h (decoder_list_block b)) == Byte.zero) => [//|/=].
    by rewrite -catA.
Qed.

Lemma subblock_c: forall (b1 b2: block),
  block_encoded b2 ->
  subblock b1 b2 ->
  (forall p, In (Some p) (data_packets b1) -> Zlength (packet_bytes (f_packet p)) <= blk_c b2) /\
  (forall p, In (Some p) (parity_packets b1) -> Zlength (p_contents (f_packet p)) = blk_c b2).
Proof.
  move => b1 b2. rewrite /block_encoded /subblock => [[_ [Hpars [Hdata _]]]] [_ [Hsubdata [Hsubpar _]]].
  split; move => p Hinp.
  - move: Hsubdata; rewrite /subseq_option => [[Hlens His]]. move: Hinp. rewrite In_Znth_iff => [[i [Hi Hp]]].
    have Hi':=Hi.
    apply His in Hi. rewrite Hp in Hi. case: Hi => [Hp'|//].
    apply Hdata. rewrite Hp'. apply Znth_In. lia.
  - move: Hsubpar; rewrite /subseq_option => [[Hlens His]]. move: Hinp. rewrite In_Znth_iff => [[i [Hi Hp]]].
    have Hi':=Hi.
    apply His in Hi. rewrite Hp in Hi. case: Hi => [Hp'|//].
    apply Hpars. rewrite Hp'. apply Znth_In. lia.
Qed.

(*We extend this to show that [decode_block] gives all packets in the original block not in the subblock*)
Theorem decode_block_correct: forall (b1 b2: block),
  block_wf b2 ->
  block_encoded b2 ->
  subblock b1 b2 ->
  recoverable b1 ->
  decode_block b1 = get_block_diff b1 b2.
Proof.
  move => b1 b2 Hwf Hcomp Hsub Hrec. rewrite decode_block_equiv /decode_block' /get_block_diff /get_diff.
  rewrite !map_pmap_id. f_equal.
  rewrite (subblock_recoverable_correct Hwf Hcomp Hsub Hrec).
  (*some results about lengths*)
  have H0k: 0 <= blk_k b1. move: Hwf Hsub. rewrite /block_wf /subblock. lia.
  have Hwf': block_wf b1 by apply (subblock_wf Hwf).
  have Hlenb1: Zlength (data_packets b1) = blk_k b1. move: Hwf'. rewrite /block_wf. lia.
  have Hb12: blk_k b1 = blk_k b2. move: Hsub. rewrite /subblock. lia.
  have Hlenb2: Zlength (data_packets b2) = blk_k b2. move: Hwf. rewrite /block_wf. lia.
  have Hlenzip: Zlength (zip (data_packets b1) (data_packets b2)) = blk_k b1.
    rewrite zip_combine Zlength_combine. lia. 
  apply Znth_eq_ext; rewrite Zlength_map; rewrite Zlength_Ziota; try lia. 
  - by rewrite !Zlength_map.
  - move => i Hi. rewrite Znth_map; [|rewrite Zlength_Ziota; lia].
    rewrite Znth_Ziota; try lia. rewrite Z.add_0_l pad_packets_nth.
    2 : { rewrite /packet_mx. rewrite Zlength_map. lia. }
    2 : { rewrite /packet_mx /lengths. rewrite !Znth_map; try lia.
      case Hith: (Znth i (data_packets b1)) => [p/=|//=].
      - have->: Znth i (data_packets b2) = Some p. {
          move: Hsub. rewrite /subblock => [[_ [Hsub _]]]. move: Hsub. rewrite /subseq_option => [[_ His]].
          have Hi': 0 <= i < Zlength (data_packets b1). apply Znth_inbounds. by rewrite Hith.
          apply His in Hi'. by case : Hi'; rewrite Hith. }
        split; try lia. apply (proj1 (subblock_c Hcomp Hsub)). rewrite -Hith.
        apply Znth_In. lia.
      - have->:blk_c b1 = blk_c b2. by apply blk_c_recoverable. split; try lia.
        case Hp: (Znth i (data_packets b2)) => [p|].
        + move: Hcomp. rewrite /block_encoded => [[_ [_ [Hin _]]]]. apply Hin. rewrite -Hp.
          apply Znth_In. lia.
        + rewrite Zlength_nil. by apply blk_c_nonneg. }
    rewrite !Znth_map; try lia. 2: by rewrite Zlength_map; lia.
    rewrite zip_combine Znth_combine; try lia.
    (*Now, we can prove the actual equivalence*)
    case Hib1 : (Znth i (data_packets b1)) => [p1 // | /=].
    case Hib2: (Znth i (data_packets b2)) => [p2 /= | /=].
    + rewrite /packet_from_bytes. 
      case Hre: (recover_packet (packet_bytes (f_packet p2) ++ 
        zseq (blk_c b1 - Zlength (packet_bytes (f_packet p2))) Byte.zero)) => [h con].
      have Hval: valid_packet (p_header (f_packet p2)) (p_contents (f_packet p2)). { apply Hwf.
        left. rewrite -Hib2. apply Znth_In. lia. }
      move: Hre.
      rewrite {1}/packet_bytes -catA recover_packet_correct. 2: by rewrite Hval.
      move => [Hh] Hcon. have Hval':=Hval.
      apply valid_not_zero in Hval. move: Hval => /eqP Hval. rewrite catA Znth_app1.
      rewrite Hval. by rewrite -Hh -Hcon.
      move: Hval'. rewrite /valid_packet => /andP[Hlen _]. solve_sumbool.
      (*[list_solve] should be able to handle this*) rewrite Zlength_app. list_solve.
    + have->:(blk_c b1 - Zlength [::]) = blk_c b1 by list_solve.
      have->//: Znth 0 (zseq (blk_c b1) Byte.zero) == Byte.zero.
      have Hc2 := (blk_c_pos Hwf Hcomp). have Hc1 := (blk_c_recoverable Hcomp Hsub Hrec).
      rewrite zseq_Znth //; lia.
    + rewrite !Zlength_map. lia.
Qed.

Lemma zip_nil: forall {A B: Type} (l: list B),
  zip (@nil A) l = nil.
Proof.
  move => A B l. by case: l.
Qed.

Lemma in_zip: forall {A B: eqType} (x: A * B) (s1: seq A) (s2: seq B),
  x \in (zip s1 s2) ->
  (x.1 \in s1) && (x.2 \in s2).
Proof.
  move => A B x s1. elim : s1 => [// s2 | h1 t1 /= IH s2].
  - by rewrite zip_nil.
  - case : s2 => [// | h2 t2 /=].
    rewrite !in_cons. move: IH. case: x => [x1 x2]/= => IH. move => /orP[/eqP[Hx1 Hx2] | Hinz]; subst.
    by rewrite !eq_refl.
    apply IH in Hinz. move: Hinz => /andP[Hinx1 Hinx2]. by rewrite Hinx1 Hinx2 !orbT.
Qed.

(*As a corllary, any packet in [decode_block] was in the original block's data packets*)
Corollary in_decode_block_in_data: forall (b1 b2: block) (p: packet),
  block_wf b2 ->
  block_encoded b2 ->
  subblock b1 b2 ->
  recoverable b1 ->
  p \in (decode_block b1) ->
  exists (p': fec_packet_act), (Some p') \in (data_packets b2) /\ remove_seqNum p = remove_seqNum (p_packet p').
Proof.
  move => b1 b2 p Hwf Henc Hsub Hrec. rewrite (decode_block_correct Hwf) //= /get_block_diff => /mapP [f Hinf Hf].
  subst. move: Hinf => /mapP [p' Hinp' Hp']. subst. move: Hinp'. rewrite /get_diff -pmap_id_some => /mapP [o].
  case : o => [o1 o2]. case: o1 => [// |]. case : o2 => [p2 |//]. move => Hinzip. apply in_zip in Hinzip.
  move: Hinzip => /= /andP[_ Hinp2] [Hp2]; subst. by exists p2.
Qed.

End SubblockDecode.

(*Now we prove part 2: every block in the decoder is a subblock of a block produced by the encoder.
  We need 2 parts: first, that the blocks in received are subblocks of those of encoded, second, that
  the blocks in the decoder state are subblocks of those in received (because of timeouts). Then, we
  can use the transitivity of the subblock relation.
  
  Proving these is the main benefit of the [get_block_lists] approach; it would be very difficult to
  prove these by induction directly*)

Section DecoderSubblocks.


(*The decoder has several intermediate functions we need to handle first*)

(*TODO: move these?*)
Lemma perm_rev': forall {T: eqType} (s: seq T),
  perm_eq s (rev s).
Proof.
  move => T s. have /(_ s):=(perm_rev s). by rewrite perm_refl perm_sym.
Qed.

Lemma zip_nil_r: forall {A B: Type} (s: seq A),
  zip s (@nil B) = [::].
Proof.
  move => A B s. by case: s.
Qed. 

(*Intermediate case 1: create a new block*)
Lemma create_block_subblock: forall (l: list fec_packet_act) (h: fec_packet_act) (time: Z),
  wf_packet_stream l ->
  In h l ->
  exists b': block, In b' (get_blocks l) /\ subblock (create_block_with_packet_black h time).1 b'.
Proof.
  move => l h t Hwf Hinhl.
  (*the real result*)
  have [b' [Hinb' Hsubb']]: exists b' : block, In b' (get_blocks l) /\ subblock (create_block_with_fec_packet h t) b'; last first.
    exists b'. rewrite /create_block_with_packet_black; split => //=. by case: (Z.eq_dec (fd_k h) 1).
  rewrite /subblock/= /get_blocks/=.
  have [Hallin [Hnonemp [Hlen [Heq Huniq]]]] := (get_block_lists_spec Hwf).
  have Hex := Hinhl. apply Hallin in Hex. case: Hex => [pkts Hinpkts].
  exists (btuple_to_block (fd_blockId h, pkts)).
  split.
    rewrite in_map_iff. by exists (fd_blockId h, pkts).
  rewrite (btuple_to_block_eq Hwf Hinpkts Hinhl erefl)/=.
  (*most are trivial, only 2 are interesting. We prove the stronger claim:*)
  have Hsub: subseq_option (upd_Znth (Int.unsigned (fd_blockIndex h)) (zseq (fd_k h + fd_h h) None) (Some h))
    pkts. {
    rewrite (Heq _ _ Hinpkts).
    have Hbound: 0 <= Int.unsigned (fd_blockIndex h) < fd_k h + fd_h h. apply (proj2 (proj2 Hwf)).
      by rewrite in_mem_In.
    rewrite /subseq_option upd_Znth_Zlength !zseq_Zlength; try lia.
    rewrite !mkseqZ_Zlength;[|list_solve].
    have Hinh:= (get_blocks_list_all_id Hwf Hinpkts Hinhl erefl).
    rewrite (Hlen _  _ _ Hinpkts Hinh).
    split => //. move => i Hi.
    rewrite !(upd_Znth_lookup'(fd_k h + fd_h h)); try lia; last first.
      rewrite zseq_Zlength; lia.
    rewrite mkseqZ_Znth //.
    case: (Z.eq_dec i (Int.unsigned (fd_blockIndex h))) => [Hih | Hneqih]; last first.
      right. rewrite zseq_Znth //. lia.
    left. case_pickSeq l. 
    (*here, we rely on uniqueness of (id, idx) pairs*)
    - solve_sumbool. f_equal. apply (proj1 (proj2 Hwf)) => //. by rewrite in_mem_In.
      rewrite e in Hih. by apply int_unsigned_inj in Hih.
    - move => /(_ h); rewrite eq_refl -Hih/=. case: (Z.eq_dec i i) => //= _ Hcon.
      have//:true = false by apply Hcon; rewrite in_mem_In.
  }
  split_all => //; by apply subseq_option_sublist.
Qed. 


(*Intermediate case 2: add packet to existing block. This one is quite complicated because if the block
  is complete, we don't add anything at all, so must show b1 is a subblock*)
Lemma add_to_block_subblock: forall (l: list fec_packet_act) (h: fec_packet_act)  (b1 b2: block),
  wf_packet_stream (h :: l) ->
  fd_blockId h = blk_id b1 ->
  In b2 (get_blocks l) ->
  subblock b1 b2 ->
  In (add_fec_packet_to_block h b2) (get_blocks (h :: l)) /\
  subblock (add_packet_to_block_black h b1).1 (add_fec_packet_to_block h b2).
Proof.
  move => l h b1 b2 Hwf Hidh Hinb2 Hsub.
  have Hpos: (forall p, In p (h :: l) -> 0 <= fd_k p /\ 0 <= fd_h p). { move => p. rewrite -in_mem_In. apply Hwf. }
  move: Hinb2. rewrite /get_blocks !in_map_iff => [[t [Hb2 Hint]]]. rewrite -Hb2.
  have [Hallin [Hnonemp [Hlen [Heq Huniq]]]] := (get_block_lists_spec (wf_packet_stream_tl Hwf)).
  move: Hb2 Hint. case : t => [i pkts] Hb2 Hint.
  have Hex:=Hint. apply Hnonemp in Hex. case: Hex => [p Hinp].
  have [Hidp Hinpl]: fd_blockId p = i /\ In p l by apply (@get_block_lists_prop_packets _ (get_block_lists l) i pkts p).
  have Hidi: fd_blockId h = i. { have->:i = blk_id b2
    by rewrite -Hb2 (btuple_to_block_eq (wf_packet_stream_tl Hwf) Hint Hinpl Hidp).
    move: Hsub => [Hsub _]. by rewrite -Hsub. }
  (*some results will be useful in multiple parts*)
  split.
  - (*TODO: separate lemmas? maybe*)
    exists (i, upd_Znth (Int.unsigned (fd_blockIndex h)) pkts (Some h)).
    (*second part is useful for both*)
    have Hnewin: In (i, upd_Znth (Int.unsigned (fd_blockIndex h)) pkts (Some h)) (get_block_lists (h :: l)). {
      have [Hallin2 [Hnonemp2 [Hlen2 [Heq2 Huniq2]]]] := (get_block_lists_spec Hwf).
      have Hex: In h (h :: l) by left. apply Hallin2 in Hex. case: Hex => [pkts' Hin'].
      rewrite -Hidi. have->//: upd_Znth (Int.unsigned (fd_blockIndex h)) pkts (Some h) = pkts'.
      have Hpkts' := Hin'. apply Heq2 in Hpkts'. rewrite Hpkts' {Hpkts'}.
      have Hpkts := Hint. apply Heq in Hpkts. rewrite Hpkts {Hpkts}.
      (*first, need to deal with lengths*)
      rewrite (Hlen _ _ _ Hint Hinp).
      have Hinh:=(get_blocks_list_all_id Hwf Hin' (in_eq _ _) erefl).
      rewrite (Hlen2 _ _ _ Hin' Hinh).
      have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. { apply Hwf.
        rewrite in_cons. have ->/=:p \in l by rewrite in_mem_In. by rewrite orbT. by rewrite in_cons eq_refl.
        by rewrite Hidp. }
      rewrite Hk Hh. have Hinht: h \in h :: l  by rewrite in_cons eq_refl.
      case : Hwf => [_ [Hinj [/(_ h Hinht)]]] Hbound _.
      apply Znth_eq_ext; rewrite Zlength_upd_Znth !mkseqZ_Zlength; try lia. move => j Hj.
        rewrite mkseqZ_Znth // (upd_Znth_lookup' (fd_k h + fd_h h)); try lia; last first.
          by rewrite mkseqZ_Zlength; lia.
        case : (Z.eq_dec j (Int.unsigned (fd_blockIndex h))) => [Hjh | Hjh].
        - case_pickSeq (h :: l).
          (*here, we rely on uniqueness of (id, idx) pairs*)
          + f_equal. apply Hinj => //. solve_sumbool.
            rewrite e in Hjh. apply (f_equal Int.repr) in Hjh. by rewrite !Int.repr_unsigned in Hjh.
          + move => /(_  h Hinht). rewrite eq_refl/= -Hjh. by case : (Z.eq_dec j j).
        - rewrite mkseqZ_Znth //. case_pickSeq (h :: l); case_pickSeq l => [|//].
          + f_equal. apply Hinj => //. by rewrite in_cons Hinx0 orbT. by rewrite Hxid0 Hxid.
            solve_sumbool. rewrite e in e0. apply (f_equal Int.repr) in e0. by rewrite !Int.repr_unsigned in e0.
          + have Hinxl: x \in l. move: Hinx; rewrite in_cons => /orP[/eqP Hxh | //]. solve_sumbool.
            by subst. move => /(_ x Hinxl). by rewrite Hxid Hidi eq_refl/= Hidx.
          + have Hinxl: x \in h :: l by rewrite in_cons Hinx orbT. move => /(_ x Hinxl).
            by rewrite Hxid Hidi eq_refl/= Hidx. }
    split => [|//]. 
    rewrite (btuple_to_block_eq (wf_packet_stream_tl Hwf) Hint Hinpl Hidp)/=.
    rewrite (btuple_to_block_eq Hwf Hnewin (in_eq _ _)) //. 
    rewrite /add_fec_packet_to_block /=.
    have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. { apply Hwf.
      rewrite in_cons. have ->/=:p \in l by rewrite in_mem_In. by rewrite orbT. by rewrite in_cons eq_refl.
      by rewrite Hidp. }
    rewrite Hk Hh.
    have Hlenpkts: Zlength pkts = fd_k h + fd_h h. { rewrite -Hk -Hh. apply (Hlen _ _ _ Hint Hinp). }
    have->: (forall (A: Type) (a1 a2: seq A), a1 ++ a2 = (a1 ++ a2)%list) by [].
    move: Hpos => /( _ h (in_eq _ _ )) => Hpos.
    rewrite -!sublist_split; try lia. by rewrite (sublist_same 0 (fd_k h + fd_h h)).
  - rewrite /add_packet_to_block_black. case Hcomp: (black_complete b1); last first.
      case Hrec: (recoverable (add_fec_packet_to_block h b1)).
      apply subblock_add. by rewrite Hb2. apply subblock_add. by rewrite Hb2.
    (*If it was complete, we don't change anything. Proving the subblock relation is a bit harder*)
    (*TODO: separate lemma?*) move: Hb2.
    rewrite !(btuple_to_block_eq (wf_packet_stream_tl Hwf) Hint Hinpl Hidp)/= => Hb2.
    have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. { apply Hwf.
      rewrite in_cons. have ->/=:p \in l by rewrite in_mem_In. by rewrite orbT. by rewrite in_cons eq_refl.
      by rewrite Hidp. } rewrite Hk Hh.
    have Hlenpkts: Zlength pkts = fd_k h + fd_h h. rewrite -Hk -Hh. apply (Hlen _ _ _ Hint Hinp).
    rewrite /subblock/=. split.
      move: Hsub. by rewrite /subblock -Hb2 //= => [[H _]].
    move: Hpos => /( _ h (in_eq _ _)) => Hbounds.
    rewrite !cat_app -sublist_split; try lia.
    rewrite !(sublist_same 0 (fd_k h + fd_h h)) //.
    move: Hsub. rewrite /subblock => [[Hid [Hdat [Hpars [Hks Hhs]]]]].
    have Hbounds': 0 <= Int.unsigned (fd_blockIndex h) < fd_k h + fd_h h. apply Hwf. by rewrite in_cons eq_refl.
    (*we need to know the relationship between data_packets, parity_packets, etc*)
    subst; simpl in *.
    (*Do this so we don't need to prove same things twice:*)
    have Hsubupd: forall lo hi l, 0 <= Int.unsigned (fd_blockIndex h) < Zlength pkts -> 0 <= lo <= hi ->
        hi <= Zlength pkts ->
        subseq_option l (sublist lo hi pkts) ->
        subseq_option l (sublist lo hi (upd_Znth (Int.unsigned (fd_blockIndex h)) pkts (Some h))). {
      move => lo hi l1 Hhhi Hlohi Hhilen. 
      rewrite /subseq_option !Zlength_sublist; try lia; [|list_solve] => [[Hlens Hith]]. split. lia.
      move => j Hj.
      have [Hin | [Hout1 | Hout2]]: lo <= Int.unsigned (fd_blockIndex h) < hi \/
        0 <= Int.unsigned (fd_blockIndex h) < lo \/ hi <= Int.unsigned (fd_blockIndex h) < Zlength pkts by lia.
      * rewrite sublist_upd_Znth_lr; try lia.
        rewrite (upd_Znth_lookup' (hi - lo)); try lia; [|list_solve].
        case : (Z.eq_dec j (Int.unsigned (fd_blockIndex h) - lo)) => Hjh.
        -- (*the key part: Znth j (data_packets b1) MUST be None or Some h, since if it is anything else,
             pkts will not a well-formeed packet list -conradicts uniquenss*)
          case Hjth: (Znth j l1) => [p' |//]; last first. by right.
          left. f_equal.
          move : Hith => /(_ j Hj). rewrite Znth_sublist; try lia.
          have->: j + lo = Int.unsigned (fd_blockIndex h) by lia.
          rewrite Hjth => [[Hjth' | //]]. apply esym in Hjth'.
          have Hinj: In (Some p') pkts. rewrite -Hjth'. apply Znth_In. lia.
          have [Hidp' Hinlp']: fd_blockId p' = fd_blockId p /\ In p' l by 
            apply (@get_block_lists_prop_packets l (get_block_lists l) (fd_blockId p) pkts).
          apply Hwf.
          ++ rewrite in_cons. have->//: p' \in l by rewrite in_mem_In. by rewrite orbT.
          ++ by rewrite in_cons eq_refl.
          ++ by rewrite Hidp'.
          ++ move: Hjth'. rewrite (Heq _ _ Hint). rewrite mkseqZ_Znth; try lia.
             case_pickSeq l => [[Hxp]|//]. rewrite -Hxp. solve_sumbool. 
             by apply int_unsigned_inj in e.
        -- by apply Hith.
      * rewrite sublist_upd_Znth_r; try lia. by apply Hith.
      * rewrite sublist_upd_Znth_l; try lia. by apply Hith.
    } 
    split_all.
    + apply Hsubupd; try lia. by rewrite -Hk.
    + apply Hsubupd; try lia. by rewrite -Hh -Hk.
    + lia.
    + lia.
Qed.

Lemma int_eqP: forall (i1 i2: int),
  reflect (i1 = i2) (Int.eq i1 i2).
Proof.
  move => i1 i2. case Hint: (Int.eq i1 i2).
  - apply ReflectT. by apply Int.same_if_eq.
  - apply ReflectF. by apply forward_lemmas.int_eq_false_e.
Qed.

Opaque create_block_with_packet_black.

(*Intermediate case 3: we need a separate inductive lemma for [update_past_blocks]*)
Lemma update_past_blocks_subblocks: forall l blks curr time,
  wf_packet_stream (curr:: l) ->
  (forall b, In b blks -> exists b', In b' (get_blocks l) /\ subblock b b') ->
  forall b, In b (update_past_blocks blks curr time).1 ->
    exists b', In b' (get_blocks (curr :: l)) /\ subblock b b'.
Proof.
  move => l blks curr. elim: blks => [//= | h t /= IH time Hwf Hsubs b].
  (*case : st => [//| s stl].*)
  have Hht: (forall x, x \in l -> x \in curr :: l) by move => x Hx; rewrite in_cons Hx orbT.
  case Hc1: ((black_time h <? time) && int_le (fd_blockId curr) (blk_id h)) => [/= | //=].
  - move => Hin. (*use [get_blocks_sublist] here*)
    have [b1 [Hinb1 Hsub1]]: exists b' : block, In b' (get_blocks l) /\ subblock b b' by apply Hsubs; right.
    have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1).
    exists b2. split => //. by apply (subblock_trans Hsub1).
  - case Hc2: (Int.lt (fd_blockId curr) (blk_id h)) => /=.
    + move => [Hnew | Hold]; last first.
      * move : Hsubs => /( _ _ Hold) [b1 [Hinb1 Hsub1]].
        have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1).
        exists b2. split => //. by apply (subblock_trans Hsub1).
      * move: Hnew. case: (Z.eq_dec (fd_k curr) 1) => /= _ <-; apply create_block_subblock => //;by left.
    + case : (Int.eq (fd_blockId curr) (blk_id h)) /int_eqP => Hcurrh/= => [[Hb | Hin] |[Hhb | Hin]].
      * rewrite -Hb. move: Hsubs => /( _ h (in_eq _ _)) [b1 [Hinb1 Hsub1]].
        exists (add_fec_packet_to_block curr b1). by apply add_to_block_subblock.
      * move: Hsubs => /(_ b (or_intror Hin)) [b1 [Hinb1 Hsub1]].
        have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1).
        exists b2. split => //. by apply (subblock_trans Hsub1).
      * move: Hsubs => /(_ b (or_introl Hhb)) [b1 [Hinb1 Hsub1]].
        have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1).
        exists b2. split => //. by apply (subblock_trans Hsub1).
      * apply (IH time) => //. move => b' Hinb'. apply Hsubs. by right.
Qed.

(*Now, finally we can show that every block in the decoder state is a subblock of some
  block from the received stream.*)
Theorem decoder_all_steps_state_subblocks: forall (received: seq fec_packet_act) (times: seq Z) (b: block),
  wf_packet_stream received ->
  size received = size times ->
  In b (decoder_block_state received times) ->
  exists b', In b' (get_blocks received) /\ subblock b b'.
Proof.
  move => r times b Hwf Hsz. rewrite /decoder_block_state /decoder_all_steps -(revK (combine _ _)) 
    foldl_rev -zip_combine rev_zip // {Hsz}. forget (rev times) as tms. rewrite {times}.
  (*want to use (rev r) everywhere to simplify induction. Luckily rev is a permutation, so we can safely
    switch get_blocks'*)
  move => Hin.
  have: exists b', In b' (get_blocks (rev r)) /\ subblock b b'; last first.
    move => [b' [Hinb Hsub]]. exists b'. split => //. move: Hinb. rewrite -!in_mem_In.
    rewrite /get_blocks => /mapP [ t Hint Htup]. rewrite Htup. apply map_f.
    by rewrite (perm_mem (get_blocks_lists_perm Hwf (perm_rev' r))).
  move: Hin.
  have: wf_packet_stream (rev r) by apply (wf_perm Hwf); apply perm_rev'.
  rewrite {Hwf}.
  forget (rev r) as r'. rewrite {r}. rename r' into r.
  move: tms b.
  elim : r => [//= tms b Hwf | h t /= IH tms b Hwf].
  - by rewrite zip_nil.
  - case : tms => [| time tms].
    + by rewrite zip_nil_r.
    + rewrite /=. move: IH => /(_ tms). set blks := (foldr
      (fun (x0 : fec_packet_act * Z) (z : seq block * seq packet) =>
       ((update_dec_state z.1 x0.1 x0.2).1, z.2 ++ (update_dec_state z.1 x0.1 x0.2).2)) 
      ([::], [::]) (zip t tms)). move => IH.
      rewrite /update_dec_state. (*we don't actually care what blks is anymore; only that the IH applies*)
      move: IH.
      case : blks => [blks pkts]/=.
      have [Hallin [Hnonemp [Hlen [Heq Huniq]]]] := (get_block_lists_spec Hwf).
      (*Some additional results we need multiple times*)
      have Hwft: wf_packet_stream t by apply (wf_packet_stream_tl Hwf). 
      case: blks => [| blkh blkt]/=.
      * move => IH/=. move: Hallin => /( _ h (in_eq _ _)) => [[ps Hinps]].
        move => [Hb | Hf//]. rewrite -Hb. apply create_block_subblock => //=. by left.
      * move => IH/=. set lastblk := (Znth (Zlength (blkh :: blkt) - 1) (blkh :: blkt)).
        have Hlastin: In lastblk (blkh :: blkt). { subst lastblk. rewrite In_Znth_iff. 
          exists (Zlength (blkh :: blkt) - 1). list_solve. }
        (*case 1: we are in the last block*)
        case: (Int.eq (fd_blockId h) (blk_id lastblk)) /int_eqP => Hhlast.
        -- move =>/= Hin. apply In_upd_Znth in Hin. case: Hin => [Hb | Hin].
          ++ rewrite Hb. move: IH => /(_ lastblk Hwft Hlastin) [b' [Hinb' Hsub]].
             exists (add_fec_packet_to_block h b').
             by apply add_to_block_subblock.
          ++ (*for IH, we use [get_blocks_sublist] and transitivity*)
            move: IH => /(_ b Hwft Hin) [b1 [Hinb1 Hsub1]].
            have Hht: forall x, x \in t -> x \in h :: t. { move => x Hx. by rewrite in_cons Hx orbT. }
            have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1). exists b2. split => //.
            by apply (subblock_trans Hsub1).
        -- (*case 2: we are in a future block*)
          case Hfut: (Int.lt (blk_id lastblk) (fd_blockId h)).
          ++ rewrite -cat_cons cat_app in_app_iff => [[Hold | Hnew]].
            ** (*IH case again - TODO: less copy and paste*)
               move: IH => /(_ b Hwft Hold) [b1 [Hinb1 Hsub1]].
               have Hht: forall x, x \in t -> x \in h :: t. { move => x Hx. by rewrite in_cons Hx orbT. }
               have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1). exists b2. split => //.
               by apply (subblock_trans Hsub1).
            ** move : Hnew => /= [Hb |//]. rewrite -Hb. apply create_block_subblock => //=. by left.
          ++ (*Now, need result for update_past_blocks*)
            move => Hinpast.
            apply (update_past_blocks_subblocks Hwf) in Hinpast => //. move => b' Hinsub.
            apply sublist_In in Hinsub. by apply IH.
Qed. 

(*One other result we need: every packet in the decoder output is either the current packet or in the [decode_block]
  of a block in the decoder's state*)

(*TODO: did I prove something like this*)
Lemma sublist_nth: forall {A: Type} `{Inhabitant A} (l: list A) (i: Z),
  0 <= i < Zlength l ->
  l = sublist 0 i l ++ [Znth i l] ++ sublist (i+1) (Zlength l) l.
Proof.
  move => A Hinhab l i Hi. have Hl1: l = sublist 0 i l ++ sublist i (Zlength l) l. {
    rewrite cat_app -sublist_split; try lia. by rewrite sublist_same. }
  rewrite {1}Hl1. rewrite (sublist_next i (Zlength l)); try lia. by rewrite catA.
Qed.

(*Actually, the general theorem is not true: we might remove some blocks so a previous packet does not
  correspond to a block. We can only prove the weaker spec:*)
Transparent create_block_with_packet_black.

(*TODO: move*)
Lemma create_black_recover: forall (curr : fec_packet_act) (time: Z),
  fd_k curr = 1 ->
  0 <= fd_h curr ->
  0 <= Int.unsigned (fd_blockIndex curr) < fd_k curr + fd_h curr ->
  recoverable (create_block_with_fec_packet curr time).
Proof.
  move => curr time Hk Hh Hidx.
  rewrite /recoverable/= -Zlength_app -cat_app -filter_cat cat_app -sublist_split; zlist_simpl.
  rewrite sublist_same; zlist_simpl. rewrite Zlength_sublist; zlist_simpl. rewrite Z.sub_0_r Hk.
  solve_sumbool => /=; subst. rewrite Hk in Hidx. simpl in *.
  have: [seq x <- upd_Znth (Int.unsigned (fd_blockIndex curr)) (zseq (1 + fd_h curr) None) (Some curr)
         | isSome x] = nil. { (*why cant list_solve do this? Should be super easy*) 
    apply Zlength_nil_inv. have H:=(Zlength_nonneg 
      [seq x <- upd_Znth (Int.unsigned (fd_blockIndex curr)) (zseq (1 + fd_h curr) None) (Some curr) | isSome x]).
    (*WTF, why can't lia do this?*)
    have H10: forall z, 0 <= z -> z < 1 -> z = 0. lia. by apply H10.  }
  move => Hfilt.
  have Hhas: has isSome (upd_Znth (Int.unsigned (fd_blockIndex curr)) (zseq (1 + fd_h curr) None) (Some curr)). {
    apply /hasP. exists (Some curr) => //. rewrite in_mem_In In_Znth_iff; zlist_simpl.
    exists (Int.unsigned (fd_blockIndex curr)). split => //.
    by rewrite upd_Znth_same; zlist_simpl. }
  rewrite has_filter in Hhas. by rewrite Hfilt in Hhas.
Qed.

Lemma in_create_black: forall (curr : fec_packet_act) (time: Z) p,
  0 <= Int.unsigned (fd_blockIndex curr) < fd_k curr + fd_h curr ->
  0 <= fd_h curr ->
  p \in (create_block_with_packet_black curr time).2 ->
  (exists b : block,
    b \in [:: (create_block_with_packet_black curr time).1 ] /\ recoverable b /\ p \in decode_block b) \/ 
  (p_packet curr = p /\ fd_isParity curr = false).
Proof.
  move => curr time p Hidx Hh /=.
  have Hcase1: p
      \in (if proj_sumbool (Z.eq_dec (fd_k curr) 1)
           then decode_block (create_block_with_fec_packet curr time)
           else [::]) ->
    (exists b : block,
       b
         \in [:: if proj_sumbool (Z.eq_dec (fd_k curr) 1)
                 then create_block_with_fec_packet curr time <| black_complete := true |>
                 else create_block_with_fec_packet curr time ] /\ recoverable b /\ p \in decode_block b). {
    case: (Z.eq_dec (fd_k curr) 1) => //= Hk1 Hpin.
    exists (create_block_with_fec_packet curr time <| black_complete := true |>). split => //.
    by rewrite in_cons eq_refl. split => //.
    by apply create_black_recover. }
  case Hpar: (fd_isParity curr) => //=.
  - move => Hin. apply Hcase1 in Hin. by left. 
  - rewrite in_cons => /orP[/eqP Hp | Hin]; subst. by right. left.
    by apply Hcase1.
Qed.

Opaque create_block_with_packet_black.

Lemma in_add_to_black: forall curr b p,
  p \in (add_packet_to_block_black curr b).2 ->
  (p \in (decode_block (add_packet_to_block_black curr b).1) /\
    recoverable (add_packet_to_block_black curr b).1) \/ p_packet curr = p /\ fd_isParity curr = false.
Proof.
  move => curr b p. rewrite /add_packet_to_block_black.
  case Hcomp: (black_complete b) => //=.
  have Hcase2: p
      \in (if recoverable (add_fec_packet_to_block curr b)
              then decode_block (add_fec_packet_to_block curr b)
              else [::]) ->
    p
      \in decode_block
            (if recoverable (add_fec_packet_to_block curr b)
             then add_fec_packet_to_block curr b <| black_complete := true |>
             else add_fec_packet_to_block curr b) /\
    recoverable
      (if recoverable (add_fec_packet_to_block curr b)
       then add_fec_packet_to_block curr b <| black_complete := true |>
       else add_fec_packet_to_block curr b)
    by case Hrec: (recoverable (add_fec_packet_to_block curr b)).
  case Hpar: (fd_isParity curr) => //=.
  - move => Hin. left. by apply Hcase2.
  - rewrite in_cons => /orP[/eqP Hp | Hin]; subst. by right. left. by apply Hcase2.
Qed.

Lemma in_update_past_blocks: forall blks (curr: fec_packet_act) time p,
  0 <= Int.unsigned (fd_blockIndex curr) < fd_k curr + fd_h curr ->
  0 <= fd_h curr ->
  p \in (update_past_blocks blks curr time).2 ->
  (exists b0 : block,
     b0 \in (update_past_blocks blks curr time).1 /\ recoverable b0 /\
     p \in decode_block b0) \/ p_packet curr = p /\ fd_isParity curr = false.
Proof.
  move => blks curr time p Hidx Hh. move: time. elim : blks => [//= time | b blks /= IH time].
  - case Hpar: (fd_isParity curr) => //=.
    rewrite in_cons => /orP[/eqP Hp | //]; subst. by right.
  - case Htime: (black_time b <? time) => //=.
    + case Hle: (int_le (fd_blockId curr) (blk_id b)).
      * case Hpar: (fd_isParity curr) => //=.
        rewrite in_cons => /orP[/eqP Hp | //]; subst. by right.
      * case Hlt: (Int.lt (fd_blockId curr) (blk_id b)) => /=.
        -- move => Hin. apply in_create_black in Hin => //. case: Hin => [[b' [Hb' Hp]] | Hp].
          ++ left. exists b'. move: Hb'; rewrite in_cons => /orP[Hb' |//]. by rewrite in_cons Hb'.
          ++ by right.
        -- case Heq: (Int.eq (fd_blockId curr) (blk_id b)) => /=.
          ++ move => Hin. apply in_add_to_black in Hin. case : Hin => [[Hdec Hrec] | Hp].
            ** left. exists (add_packet_to_block_black curr b).1. split => //. by rewrite in_cons eq_refl.
            ** by right.
          ++ move => Hin. apply IH in Hin. case : Hin => [[b' [Hbin Hp]] | Hp].
            ** left. exists b'. by rewrite in_cons Hbin orbT.
            ** by right.
    + case Hlt: (Int.lt (fd_blockId curr) (blk_id b)) => /=.
      * move => Hin. apply in_create_black in Hin => //. case: Hin => [[b' [Hb' Hp]] | Hp].
        -- left. exists b'. move: Hb'; rewrite in_cons => /orP[Hb' |//]. by rewrite in_cons Hb'.
        -- by right.
      * case Heq: (Int.eq (fd_blockId curr) (blk_id b)) => /=.
        -- move => Hin. apply in_add_to_black in Hin. case : Hin => [[Hdec Hrec] | Hp].
          ++ left. exists (add_packet_to_block_black curr b).1. split => //. by rewrite in_cons eq_refl.
          ++ by right.
        -- move => Hin. apply IH in Hin. case : Hin => [[b' [Hbin Hp]] | Hp].
          ++ left. exists b'. by rewrite in_cons Hbin orbT.
          ++ by right.
Qed.

Lemma in_update_dec_state: forall blks (curr: fec_packet_act) time p,
  0 <= Int.unsigned (fd_blockIndex curr) < fd_k curr + fd_h curr ->
  0 <= fd_h curr ->
  p \in (update_dec_state blks curr time).2 ->
  (exists b : block,
    b \in (update_dec_state blks curr time).1 /\ recoverable b /\ p \in decode_block b) \/ 
  (p_packet curr = p /\ fd_isParity curr = false).
Proof.
  move => blks curr time p Hidx Hh. rewrite /update_dec_state.
  case : blks => [/= | b btl/=].
  - by apply in_create_black.
  - case Heq: (Int.eq (fd_blockId curr) (blk_id (Znth (Zlength (b :: btl) - 1) (b :: btl)))) => /=.
    + move => Hin. apply in_add_to_black in Hin. case: Hin => [[Hdec Hrec] | Hp].
      * left. exists (add_packet_to_block_black curr (Znth (Zlength (b :: btl) - 1) (b :: btl))).1.
        split => //. rewrite in_mem_In In_Znth_iff; simpl in *; zlist_simpl.
        exists (Zlength (b :: btl) - 1). split. list_solve. rewrite upd_Znth_same //. list_solve.
      * by right.
    + case Hlt: (Int.lt (blk_id (Znth (Zlength (b :: btl) - 1) (b :: btl))) (fd_blockId curr)) => /=.
      * move => Hin. apply in_create_black in Hin => //. case: Hin => [Hdec | Hp].
        -- case Hdec => [b' [Hbin [Hrec Hp]]]. left. exists b'. by rewrite in_cons mem_cat Hbin !orbT.
        -- by right.
      * by apply in_update_past_blocks.
Qed.

Theorem in_decode_func_in_block: forall received (curr: fec_packet_act) times time (p: packet),
  size received = size times ->
  0 <= Int.unsigned (fd_blockIndex curr) < fd_k curr + fd_h curr ->
  0 <= fd_h curr ->
  p \in (rse_decode_func received curr times time) ->
  (exists b, b \in (decoder_all_steps (received ++ [:: curr]) (times ++ [:: time])).1 /\ recoverable b /\
    (p \in (decode_block b))) \/ 
    (p_packet curr = p /\ fd_isParity curr = false).
Proof.
  move => r curr sts st p Hsz Hidx Hh. rewrite /rse_decode_func /decoder_all_steps -!zip_combine zip_cat // foldl_cat/=.
  by apply in_update_dec_state.
Qed.

Lemma Zlength_rev: forall {A: Type} (s: seq A),
  Zlength (rev s) = Zlength s.
Proof.
  move => A s. by rewrite !Zlength_correct -!size_length size_rev.
Qed.

(*TODO: encoder version is in Abstract file - and it is the exact same proof - TODO: generalize to only need 1*)
Lemma decoder_all_steps_concat: forall received times,
  Zlength received = Zlength times ->
  (decoder_all_steps received times).2 = concat (mkseqZ 
    (fun i => (rse_decode_func (sublist 0 i received) (Znth i received) (sublist 0 i times) (Znth i times)))
    (Zlength received)).
Proof.
  move => r times Hsz. rewrite /rse_decode_func /decoder_all_steps.
  remember (@nil packet) as base. rewrite -(cat0s (concat _)) -Heqbase. rewrite {Heqbase}.
  remember (@nil block) as base1. rewrite {Heqbase1}. move: times Hsz base base1.
  elim: r => [//= states Hlen b1 b2 | h t /= IH states Hlen b1 b2].
  - by rewrite cats0.
  - move: Hlen. case : states => [|st1 st2 Hlen/=]. list_solve.
    rewrite IH;[|list_solve]. have->: Zlength (h::t) = Zlength t + 1 by list_solve.
    rewrite mkseqZ_1_plus/=; [|list_solve]. rewrite !Znth_0_cons catA. f_equal.
    f_equal. have Hpos: 0 <= Zlength t by list_solve. apply Znth_eq_ext; rewrite !mkseqZ_Zlength //. 
    move => i Hi. rewrite !mkseqZ_Znth// !Znth_pos_cons; try lia. rewrite !sublist_0_cons; try lia.
    by rewrite !Z.add_simpl_r.
Qed.  

End DecoderSubblocks.

(*Part 3: All blocks from the encoder are well formed and are complete if they are recoverable*)
Section EncoderBlocks.

(*The following tactic will be helpful. First, we have a few lemmas to avoid unfolding*)
Lemma populate_packets_Zlength: forall i model s,
  Zlength (populate_packets i model s) = Zlength s.
Proof.
  move => i model s. by rewrite Zlength_map.
Qed.

Lemma encoder_list_Zlength: forall h k c packets,
  0 <= h ->
  0 <= c ->
  Zlength (encoder_list h k c packets) = h.
Proof.
  move => h k c pkts Hh Hc. 
  by rewrite /encoder_list (proj1 (ListMatrix.lmatrix_multiply_wf _ _ _ _ _)); rep_lia.
Qed.

Lemma encoder_list_Znth_Zlength: forall h k c packets i,
  0 <= c ->
  0 <= i < h ->
  Zlength (Znth i (encoder_list h k c packets)) = c.
Proof.
  move => h k c pkts i Hc Hi. 
  have: ListMatrix.wf_lmatrix (encoder_list h k c pkts) h c. {
    apply encoder_wf; lia. }
  rewrite /ListMatrix.wf_lmatrix/ListMatrix.rect => [[Hlen [_ Hnth]]].
  move: Hnth. by rewrite Forall_Znth Hlen => /(_ _ Hi).
Qed. 

Ltac len_encode :=
  zlist_simpl;
  repeat match goal with
  | [H: context [Zlength (populate_packets _ _ _) ] |- _] => move: H
  | |- context [Zlength (populate_packets ?i ?p ?s) ]  => rewrite populate_packets_Zlength
  | |- context [Zlength (encoder_list _ _ _ _) ] => rewrite encoder_list_Zlength
  | |- context [Zlength (Znth ?x (encoder_list _ _ _ _)) ] => rewrite encoder_list_Znth_Zlength
  | |- 0 <= blk_c ?b => apply blk_c_nonneg
  end; try rep_lia.

(** Lemmas about [encode_block]*)

(*If we give a valid packet as a template and start with a well-formed, in-progress block,
  encoding this block with p as the template gives a well-formed block*)
Lemma encode_block_aux_wf: forall b p,
  packet_valid p ->
  block_in_progress b ->
  block_wf b ->
  block_wf (encode_block_aux b p).1.
Proof.
  move => b p Hpval Hprog. rewrite /block_wf/encode_block_aux/= => 
    [[Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc [Hvalid [Hdats Hpars]]]]]]]]]]].
  split_all => //; try lia.
  - move => p' [Hdat | Hpar].
    + apply Hkh. by left.
    + move: Hpar. rewrite -in_mem_In mem_map; last first. apply some_inj.
      by move => /mapWithIdxP[ j [y [Hj [Hjth Hp']]]]; subst.
  - move => p' [Hdat | Hpar].
    + apply Hid. by left.
    + move: Hpar. rewrite -in_mem_In mem_map; last first. apply some_inj.
      by move => /mapWithIdxP[ j [y [Hj [Hjth Hp']]]]; subst.
  - (*the hard step*)
    move => p' i [Hdat | Hpar].
    + have Hin:=Hdat. move: Hin. rewrite In_Znth_iff => [[j [Hj Hjth]]].
      split.
      * have [Hi | [Hi | Hout]]: 0 <= i < blk_k b \/ blk_k b <= i < blk_k b + blk_h b \/
          (0 > i \/ i >= blk_k b + blk_h b) by lia.
        -- rewrite Znth_app1; try lia. move: Hidx => /(_ p' i (or_introl Hdat)). rewrite Znth_app1; try lia. move => H.
           by apply H.
        -- rewrite Znth_app2; try lia. len_encode. 
           move => [Hp']. subst => //=. rewrite Int.unsigned_repr; rep_lia.
        -- rewrite Znth_outofbounds // Zlength_app. len_encode.
      * move ->. have Hj': j = Int.unsigned (fd_blockIndex p'). apply Hidx. by left. by rewrite Znth_app1 //; lia.
        rewrite Znth_app1; try lia. by subst.
    + move: Hpar. rewrite in_map_iff => [[x [[Hxp] Hinx]]]. subst. move: Hinx.
      rewrite -in_mem_In => /mapWithIdxP[ j [y [Hj [Hjth Hp']]]]; subst => //=. have Hj': 0 <= j < blk_h b by len_encode.
      rewrite {Hj}. split.
      * have [Hi | [Hi | Hout]]: 0 <= i < blk_k b \/ blk_k b <= i < blk_k b + blk_h b \/
          (0 > i \/ i >= blk_k b + blk_h b) by lia.
        -- rewrite Znth_app1; try lia. set p':= {|
            p_packet :=
              Znth j (populate_packets (blk_id b) p (encoder_list (blk_h b) (blk_k b) (blk_c b) (packet_mx b)));
            p_fec_data :=
              {|
                fd_k := blk_k b;
                fd_h := blk_h b;
                fd_isParity := true;
                fd_blockId := blk_id b;
                fd_blockIndex := Int.repr (blk_k b + j)
              |}
            |}. move => Hith. have Hin: In (Some p') (data_packets b). rewrite In_Znth_iff. exists i. split => //.
            by rewrite Hk. (*why doesnt lia work*)
            move: Hith. subst p'.
            rewrite -((Znth_app1 _ _ _ (parity_packets b))); try lia.
            rewrite Hidx/=. rep_lia. by left.
        -- rewrite Znth_app2; try lia. len_encode.
           move => [Heq].
           rewrite !Int.Z_mod_modulus_eq !Zmod_small; try rep_lia. rewrite Int.unsigned_repr; rep_lia.
        -- rewrite Znth_outofbounds // Zlength_app. len_encode.
      * move ->. rewrite Znth_app2; rewrite Int.unsigned_repr; try rep_lia.
        have->:(blk_k b + j - Zlength (data_packets b)) = j by lia. by len_encode.
  - len_encode.
  - move => p' [Hdat | Hpar].
    + apply Hvalid. by left.
    + move: Hpar. rewrite -in_mem_In mem_map; last first. apply some_inj.
      move => /mapWithIdxP[ j [y [Hj [Hjth Hp']]]]; subst.
      rewrite Znth_map;[|len_encode] => /=.
      rewrite /packet_valid/=. apply copy_fix_header_valid with(con1:=(p_contents p)).
      * have: 0 <= j < blk_h b by len_encode. move: Hj => _ Hj. len_encode.
        (*need in_progress for bound here*)
        have Hc: blk_c b <= fec_max_cols by apply blk_c_bound.
        move: Hpval. rewrite /packet_valid /valid_fec_packet => Hval. apply header_bound in Hval.
        rep_lia'.
      * apply Hpval.
  - move => p'. rewrite in_map_iff => [[x]] [[Hx]]; subst. rewrite In_Znth_iff; len_encode.
    move => [i] [Hi]. len_encode. by move <-. 
Qed.

Lemma encode_block_some_wf: forall b p,
  packet_valid p ->
  block_in_progress b ->
  block_wf b ->
  block_wf (encode_block b (Some p)).1.
Proof.
  move => b p Hval Hprog Hwf. rewrite /encode_block.
  case Hdat: (pmap id (data_packets b)) => [|h t];
  by apply encode_block_aux_wf.
Qed.

Lemma encode_block_aux_comp: forall b p,
  black_complete (encode_block_aux b p).1 = black_complete b.
Proof.
  move => b p. by [].
Qed.

Lemma encode_block_black_comp: forall b o,
  black_complete (encode_block b o).1 = black_complete b.
Proof.
  move => b o. rewrite /encode_block/=. case : (pmap id(data_packets b)) => [/= | h t]; case : o => [x|//];
  apply encode_block_aux_comp.
Qed.

Lemma encode_block_time: forall b o,
  black_time (encode_block b o).1 = black_time b.
Proof.
  move => b o. rewrite /encode_block/=. by case : (pmap id(data_packets b)) => [/= | h t]; case : o => [x|//].
Qed.

Lemma data_packets_encode: forall b o,
  data_packets (encode_block b o).1 = data_packets b.
Proof.
  move => b o. rewrite /encode_block/=.
  by case Hmpap: (pmap id (data_packets b)) => [/=|h t /=]; case : o.
Qed.

Lemma encode_block_nonempty: forall b o,
  data_elt b ->
  data_elt (encode_block b o).1.
Proof.
  move => b o. by rewrite /data_elt data_packets_encode.
Qed.

Lemma encode_some: forall b p,
  encode_block b (Some p) = encode_block_aux b p.
Proof.
  move => b p. rewrite /encode_block. by case: (pmap id (data_packets b)).
Qed.

Lemma c_encode_aux: forall (b: block) (p: packet),
  0 <= blk_h b ->
  block_in_progress b ->
  blk_c (encode_block_aux b p).1 = blk_c b.
Proof.
  move => b p Hh Hprog. rewrite /encode_block_aux/= {1}/blk_c/= {2}/blk_c/=.
  rewrite pars_in_progress //.
  case Hpars:   [seq x <- [seq Some i
               | i <- map_with_idx
                        (populate_packets (blk_id b) p
                           (encoder_list (blk_h b) (blk_k b) (blk_c b) (packet_mx b)))
                        (fun (p0 : packet) (i : Z) =>
                         {|
                           p_packet := p0;
                           p_fec_data :=
                             {|
                               fd_k := blk_k b;
                               fd_h := blk_h b;
                               fd_isParity := true;
                               fd_blockId := blk_id b;
                               fd_blockIndex := Int.repr (blk_k b + i)
                             |}
                         |})]
     | isSome x] => [//| h t /=]. move: Hpars.
  case : h => [p' /= | //]. move => Hpars'.
  have: (Some p') \in   [seq x <- [seq Some i
             | i <- map_with_idx
                      (populate_packets (blk_id b) p
                         (encoder_list (blk_h b) (blk_k b) (blk_c b) (packet_mx b)))
                      (fun (p0 : packet) (i : Z) =>
                       {|
                         p_packet := p0;
                         p_fec_data :=
                           {|
                             fd_k := blk_k b;
                             fd_h := blk_h b;
                             fd_isParity := true;
                             fd_blockId := blk_id b;
                             fd_blockIndex := Int.repr (blk_k b + i)
                           |}
                       |})]
   | isSome x].
  move => Heq. rewrite Hpars'. by rewrite in_cons eq_refl.
  move => /(_ fec_data_eq_dec). (*why do i get these weird goals?*)
  rewrite mem_filter/=. rewrite (@mem_map fec_packet_act_eqType); last first.
    by apply some_inj.
  rewrite in_mem_In In_Znth_iff. len_encode. move => [i [Hi Hith]]. subst.
  len_encode => /=. rewrite Znth_map; len_encode => /=. len_encode.
  by rewrite /blk_c pars_in_progress.
Qed.

Lemma encode_block_aux_encoded: forall b p,
  0 <= blk_h b ->
  block_in_progress b ->
  data_elt b ->
  block_encoded (encode_block_aux b p).1.
Proof.
  move => b p Hh Hprog Helt. rewrite /block_encoded c_encode_aux //.
  split_all.
  - rewrite /= blk_c_in_progress //.
    move: Helt. rewrite /data_elt.
    case Hpmap: (pmap id (data_packets b)) => [// | hd tl /=].
    have Hhd': (Some hd) \in (data_packets b) by rewrite pmap_id_some Hpmap in_cons eq_refl.
    have Hhd: In (Some hd) (data_packets b) by rewrite -in_mem_In.
    have Hfhd: 0 <= Zlength (p_header hd ++ p_contents hd)  by list_solve.
    have [o ] := (@list_max_nonneg_exists _ (fun o : option fec_packet_act =>
     match o with
     | Some p1 => Zlength (p_header p1 ++ p_contents p1)
     | None => 0
     end) _ _ Hhd Hfhd).
    case : o => [y |//=].
    + (*normal case*)
      move => [Hiny Hymax] _. by exists y.
    + (*weird case where all packets empty*)
      move => [Hin Hmax] _. exists hd. split => //.
      have [H0 | Hgt]: 0 = Zlength (p_header hd ++ p_contents hd) \/
        0 < Zlength (p_header hd ++ p_contents hd) by lia.
      * lia.
      * have//: 0 < 0. have: Zlength (p_header hd ++ p_contents hd) <= 0; last first. lia.
        rewrite -Hmax.
        have Hmax' := (@list_max_nonneg_in _(fun o : option fec_packet_act =>
         match o with
         | Some p1 => Zlength (p_header p1 ++ p_contents p1)
         | None => 0
         end) (data_packets b) (Some hd) Hfhd Hhd). lia.
  - move => p'/=. rewrite In_Znth_iff; len_encode. move => [i [Hi]]. len_encode. move => [Hp']. subst => /=.
    by rewrite Znth_map/=; len_encode.
  - move => p'/=. rewrite blk_c_in_progress //. move => Hin. rewrite /packet_bytes.
    have Hnonneg: 0 <= Zlength (p_header p' ++ p_contents p') by list_solve.
    have Hb:= (@list_max_nonneg_in _ (fun o : option fec_packet_act =>
     match o with
     | Some p1 => Zlength (p_header p1 ++ p_contents p1)
     | None => 0
     end) (data_packets b) (Some p') Hnonneg Hin). lia.
  - (*the key one: parities are valid*)
    rewrite /= /packet_mx/= -/(packet_mx b) /parity_mx/=/parities_valid; len_encode.
    move => i j Hi Hj.
    len_encode. f_equal. by rewrite Znth_map/=; len_encode.
Qed.

Lemma encode_block_encoded: forall b o,
  0 <= blk_h b ->
  block_in_progress b ->
  data_elt b ->
  block_encoded (encode_block b o).1.
Proof.
  move => b o Hh Hprog Helt. rewrite /encode_block. have Helt':=Helt.
  move: Helt. rewrite /data_elt.
  case Hpmap: (pmap id (data_packets b)) => [//|hd tl/=].
  move => _.
  case : o => [p|]; by apply encode_block_aux_encoded.
Qed.

Lemma encode_block_id: forall (b: block) o,
  blk_id (encode_block b o).1 = blk_id b.
Proof.
  move => b o. rewrite /encode_block. by case : o => /=[p|]; case: (pmap id (data_packets b)).
Qed.

Lemma encode_in_aux: forall b m (p: fec_packet_act),
  (p \in (encode_block_aux b m).2) =
  ((Some p) \in (parity_packets (encode_block_aux b m).1)).
Proof.
  move => b m p. rewrite /= mem_map //. apply some_inj.
Qed.

Lemma encode_in: forall b o (p: fec_packet_act),
  p \in (encode_block b o).2 ->
  (Some p) \in (parity_packets (encode_block b o).1).
Proof.
  move => b o p. rewrite /encode_block.
  by case Hpmap:(pmap id (data_packets b)) => [//= | hd tl /=]; case o => [p' | //]; rewrite encode_in_aux.
Qed.

Lemma in_encode: forall b o (p: fec_packet_act),
  data_elt b ->
  (Some p) \in (parity_packets (encode_block b o).1) ->
  p \in (encode_block b o).2.
Proof.
  move => b o p. rewrite /data_elt /encode_block.
  by case Hmap: (pmap id (data_packets b)) => [//= | hd tl /=] _; case o => [p' |//]; rewrite encode_in_aux.
Qed.

Lemma encode_block_k: forall (b: block) (o: option packet),
  blk_k (encode_block b o).1 = blk_k b.
Proof.
  move => b o. rewrite /encode_block. case : (pmap id (data_packets b)) => [/=| Hd tl /=]; by case : o.
Qed.

Lemma encode_block_h: forall (b: block) (o: option packet),
  blk_h (encode_block b o).1 = blk_h b.
Proof.
  move => b o. rewrite /encode_block. case : (pmap id (data_packets b)) => [/=| Hd tl /=]; by case : o.
Qed.

Lemma encode_parities_Zlength_aux: forall (b: block) p,
  block_wf b ->
  Zlength (parity_packets (encode_block_aux b p).1) = blk_h b.
Proof.
  move => b p Hwf/=. len_encode. case : Hwf. lia.
Qed.

Lemma encode_parities_Zlength: forall (b: block) o,
  block_wf b ->
  Zlength (parity_packets (encode_block b o).1) = blk_h b.
Proof.
  move => b o Hwf. rewrite /encode_block.
  case : (pmap id (data_packets b)) => [//= | h t /=]; case : o => [p|]//; try by apply encode_parities_Zlength_aux.
  rewrite /=. apply Hwf.
Qed.

(*We can switch between None and Some for encode_block*)
Lemma encode_block_none_some: forall (b: block),
  data_elt b ->
  exists model, In (Some model) (map (omap (@p_packet _)) (data_packets b)) /\
  encode_block b None = encode_block b (Some model).
Proof.
  move => b. rewrite /data_elt /encode_block.
  case Hmap: (pmap id (data_packets b)) => [// | h t /=] _.
  exists (last h t). split => //.
  rewrite in_map_iff. exists (Some (last h t)).
  split => //. by rewrite -in_mem_In pmap_id_some Hmap mem_last.
Qed.

(** Lemmas about [create_block_with_packet_red]*)

Lemma create_block_red_wf: forall p k h,
  packet_valid p ->
  encodable p ->
  0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h ->
  0 < h <= ByteFacts.fec_max_h ->
  block_wf (create_block_with_packet_red p k h).
Proof.
  move => p k h Hval Henc Hk Hh. rewrite /create_block_with_packet_red/block_wf/=.
  (*These will help with a bunch:*)
  have Hin1: forall p',
    In (Some p') (upd_Znth 0 (zseq k None) (Some (new_fec_packet p k h))) -> p' = (new_fec_packet p k h). {
    move => p' Hin. apply In_upd_Znth in Hin. case : Hin => [[Hp']// | Hin].
    move: Hin. rewrite In_Znth_iff => [[i]]. rewrite zseq_Zlength; try lia; move => [Hi]. by zlist_simpl. }
  have Hin2: forall p', 
    In (Some p') (upd_Znth 0 (zseq k None) (Some (new_fec_packet p k h))) \/ In (Some p') (zseq h None) ->
    p' = (new_fec_packet p k h). {
    move => p' [Hinp' | Hinp']. by apply Hin1. move: Hinp'. rewrite In_Znth_iff => [[i]]. 
    rewrite zseq_Zlength; try lia; move => [Hi]. by zlist_simpl. }
  split_all => //; try lia.
  - move => p' Hinp'. apply Hin2 in Hinp'. by subst.
  - move => p' Hinp'. apply Hin2 in Hinp'. by subst.
  - move => p' i Hinp'. apply Hin2 in Hinp'. subst => /=.
    rewrite Int.unsigned_zero. split.
    + have [Hi1 | [Hi2 | Hiout]]: (0 <= i < k \/ k <= i < k + h \/ (i < 0 \/ i >= k + h)) by lia.
      * rewrite Znth_app1; zlist_simpl.
        rewrite (upd_Znth_lookup' k); zlist_simpl.
        by case : (Z.eq_dec i 0).
      * by rewrite Znth_app2; zlist_simpl. 
      * rewrite Znth_outofbounds // Zlength_app. by zlist_simpl.
    + move ->. rewrite Znth_app1; zlist_simpl.
      rewrite upd_Znth_same //. by zlist_simpl. 
  - by zlist_simpl.
  - by zlist_simpl.
  - move => p' Hinp'. apply Hin1 in Hinp'. by subst.
  - move => p' Hinp'. apply Hin2 in Hinp'. by subst.
  - move => p' Hinp'. apply Hin1 in Hinp'. by subst.
  - move => p'. rewrite In_Znth_iff => [[i] [Hi]]. have Hi': 0 <= i < h by move: Hi; zlist_simpl.
    by zlist_simpl.
Qed.

Lemma create_red_nonempty: forall p h k,
  0 < h ->
  data_elt (create_block_with_packet_red p h k).
Proof.
  move => p h k Hh. rewrite /data_elt/=.
  have Hin: (new_fec_packet p h k) \in pmap id (upd_Znth 0 (zseq h None) (Some (new_fec_packet p h k))). {
    rewrite -pmap_id_some in_mem_In In_Znth_iff. exists 0. zlist_simpl. split; try lia.
    rewrite (upd_Znth_lookup' h); zlist_simpl. by case (Z.eq_dec 0 0).
  }
  move: Hin. by case : ( pmap id (upd_Znth 0 (zseq h None) (Some (new_fec_packet p h k)))).
Qed.

Lemma create_red_in_progress: forall p k h,
  0 <= h ->
  block_in_progress (create_block_with_packet_red p k h).
Proof.
  move => p k h Hh. rewrite /block_in_progress/=. apply /allP => x.
  rewrite in_mem_In In_Znth_iff => [[i [Hi]]]. zlist_simpl. by move <-. move: Hi; zlist_simpl.
Qed.

Lemma create_red_Zindex: forall p k h,
  1 <= k ->
  Zindex None (data_packets (create_block_with_packet_red p k h)) = 1.
Proof.
  move => p k h Hk. rewrite /Zindex /index/=.
  rewrite zseq_hd; try lia. rewrite upd_Znth0.
  simpl find.
  have [Hk1 | Hk1]: k = 1 \/ k > 1 by lia.
  - subst. by have->:1-1 = 0 by [].
  - by rewrite zseq_hd; try lia.
Qed.

Lemma create_block_in: forall p k h,
  0 < k ->
  In (Some p) (map (omap (@p_packet _)) (data_packets (create_block_with_packet_red p k h))).
Proof.
  move => p k h Hk. rewrite /create_block_with_packet_red/= in_map_iff. exists (Some (new_fec_packet p k h)).
  split =>//. apply upd_Znth_In. zlist_simpl.
Qed.


(** Lemmas about [add_packet_to_block_red]*)

Lemma add_red_k: forall p b,
  blk_k (add_packet_to_block_red p b) = blk_k b.
Proof.
  by [].
Qed.

Lemma add_red_h: forall p b,
  blk_h (add_packet_to_block_red p b) = blk_h b.
Proof.
  by [].
Qed.

Lemma add_red_id: forall p b,
  blk_id (add_packet_to_block_red p b) = blk_id b.
Proof.
  by [].
Qed.

Lemma add_red_parity: forall p b,
  parity_packets (add_packet_to_block_red p b) = parity_packets b.
Proof.
  by [].
Qed.

Lemma add_black_comp: forall b p,
  black_complete (add_packet_to_block_red p b) = black_complete b.
Proof.
  by [].
Qed.

Lemma add_red_wf: forall p b,
  block_wf b ->
  packet_valid p ->
  encodable p ->
  Zindex None (data_packets b) < blk_k b ->
  block_wf (add_packet_to_block_red p b).
Proof.
  move => p b Hwf Hval Henc Hzidx. rewrite /block_wf add_red_k add_red_h add_red_parity/=.
  case : Hwf => [Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc' [Hvalid [Hdats Hpars]]]]]]]]]].
  have Hnonneg:=(@Zindex_nonneg _ None (data_packets b)).
  split_all => //; try lia.
  - move => p' [Hinp | Hinp]; last first. by apply Hkh; right.
    apply In_upd_Znth in Hinp. case: Hinp => [[Hp'] | Hinp']; subst => //. by apply Hkh; left.
  - move => p' [Hinp | Hinp]; last first. by apply Hid; right.
    apply In_upd_Znth in Hinp. case: Hinp => [[Hp'] | Hinp']; subst => //. by apply Hid; left.
  - simpl in *.
    setoid_rewrite <- in_app_iff. rewrite -!upd_Znth_app1; try lia. setoid_rewrite <- upd_Znth_app1; try lia.
    apply block_wf_list_upd_Znth. move => p' i Hin. apply Hidx. by apply in_app_or. list_solve.
    rewrite Znth_app1; try lia. apply Znth_Zindex. apply Zindex_In. simpl in *; lia.
    rewrite/= Int.unsigned_repr; rep_lia.
  - rewrite upd_Znth_Zlength; simpl in *; try lia.
  - move => p' Hinp. apply In_upd_Znth in Hinp. case: Hinp => [[Hp'] | Hinp']; subst => //. by apply Henc'.
  - move => p' [Hinp | Hinp]; last first. by apply Hvalid; right.
    apply In_upd_Znth in Hinp. case: Hinp => [[Hp'] | Hinp']; subst => //. by apply Hvalid; left.
  - move => p' Hinp. apply In_upd_Znth in Hinp. case: Hinp => [[Hp'] | Hinp']; subst => //.
    by apply Hdats.
Qed.

(*not the strongest spec, but OK for us*)
Lemma add_red_nonempty: forall (b: block) p,
  data_elt b ->
  data_elt (add_packet_to_block_red p b).
Proof.
  move => b p. rewrite /data_elt.
  case Hpmap: (pmap id (data_packets b)) => [// | h t /=] _.
  have Hin: In (Some h) (data_packets b) by rewrite -in_mem_In pmap_id_some Hpmap in_cons eq_refl.
  have Hidxlen:=(@Zindex_leq_Zlength _  (data_packets b) None). apply Zle_lt_or_eq in Hidxlen.
  have: h \in pmap id (upd_Znth (Zindex None (data_packets b)) (data_packets b) (Some (get_fec_packet p b))). {
    rewrite -pmap_id_some in_mem_In. case: Hidxlen => [Hlt | Heq].
    - apply In_upd_Znth_old => //. rewrite Znth_Zindex //. by apply Zindex_In.
      have H:=(@Zindex_nonneg _ None (data_packets b)). lia.
    - rewrite upd_Znth_out_of_range //=. right. rewrite Heq/=. lia.
  }
  by case: (pmap id (upd_Znth (Zindex None (data_packets b)) (data_packets b) (Some (get_fec_packet p b)))).
Qed. 

(*When we add a packet to a red block, it gets 1 packet bigger*)
Lemma add_red_size: forall b p,
  Zindex None (data_packets b) < Zlength (data_packets b) ->
  Zlength [seq x <- data_packets b | isSome x] + 1  = 
  Zlength [seq x <- (data_packets (add_packet_to_block_red p b)) | isSome x ].
Proof.
  move => b p Hidx. rewrite /= upd_Znth_Zindex_Zlength //. apply Z.add_comm.
Qed.

Lemma add_block_in: forall (p: packet) (b: block),
  Zindex None (data_packets b) < Zlength (data_packets b) ->
  In (Some p) [seq omap (p_packet (fec_data:=fec_data)) i | i <- data_packets (add_packet_to_block_red p b)].
Proof.
  move => p b Hidx. rewrite /= in_map_iff. exists (Some (get_fec_packet p b)). split =>//.
  apply upd_Znth_In. split => //. apply Zindex_nonneg.
Qed.

(*Some small results we need, not sure where to put them*)

(*deal with generic preds of the form: forall x, x \in l -> p x*)
Lemma in_pred_rev: forall {A: eqType} (s: seq A) (p: pred A),
  (forall x, x \in s -> p x) ->
  (forall x, x \in (rev s) -> p x).
Proof.
  move => A s p Hall x Hinx. apply Hall. move: Hinx. by rewrite mem_rev.
Qed.

Lemma in_pred_tl: forall {A: eqType} (h: A) (s: seq A)  (p: pred A),
  (forall x, x \in (h :: s) -> p x) ->
  (forall x, x \in s -> p x).
Proof.
  move => A s h p Hall x Hxin. apply Hall. by rewrite in_cons Hxin orbT.
Qed.

Lemma cons_app: forall {A: Type} (x : A) (l: seq A),
  x :: l = [x] ++ l.
Proof.
  by [].
Qed.

(** Encoder properties *)

(*To prove the main theorem about the encoder, we need to show that a number of properties are preserved in
  each run of rse_encode_gen. To reduce repetition and make things
  cleaner, we group the properties together and prove the 3 different cases we need before proving the full theorem*)

Definition block_option_list (x: list block * option block) : list block :=
  match x.2 with
  | None => x.1
  | Some b => b :: x.1
  end.

Definition encoder_props (orig: list packet) (blks: list block) (currBlock: option block) 
  (pkts: seq fec_packet_act) : Prop :=
  perm_eq (get_blocks pkts) (block_option_list (blks, currBlock)) /\
  (forall b, In b (block_option_list (blks, currBlock)) -> block_wf b) /\
  (forall b, In b (block_option_list (blks, currBlock)) -> black_complete b = false) /\
  (forall b, In b (block_option_list (blks, currBlock)) -> black_time b = 0) /\
  (forall b, In b (block_option_list (blks, currBlock)) -> data_elt b) /\
  (forall b p, In b (block_option_list (blks, currBlock)) -> In (Some p) (data_packets b) ->
    In (p_packet p) orig) /\
  (forall b, In b (block_option_list (blks, currBlock)) -> exists p,
      In (Some p) (data_packets b) /\ blk_id b = p_seqNum p) /\
  (*All previous blocks are done; the current is either done (with k packets) or has no parities*)
  (forall b, In b blks -> block_encoded b) /\
  (forall b, currBlock = Some b -> block_in_progress b) /\
  wf_packet_stream pkts.

Lemma encoder_props_orig_rev: forall orig blks currBlock pkts,
  encoder_props orig blks currBlock pkts ->
  encoder_props (rev orig) blks currBlock pkts.
Proof.
  move => orig blks currBlock pkts. rewrite /encoder_props => Henc; split_all; try apply Henc.
  move => b p Hinp Hin. rewrite -in_mem_In mem_rev in_mem_In. move: Hinp Hin. by apply Henc.
Qed.

Lemma encoder_props_orig_rev_iff: forall orig blks currBlock pkts,
  encoder_props orig blks currBlock pkts <->
  encoder_props (rev orig) blks currBlock pkts.
Proof.
  move => orig blks currBlock pkts. split; move => Henc.
  - by apply encoder_props_orig_rev.
  - rewrite -(revK orig). by apply encoder_props_orig_rev.
Qed.


(** Lemmas for main theorem *)

(* Overall, we need 3 cases to prove the theorem:
  1. the properties are preserved when we start a new block
  2. the properties are preserved when we encode the current block
  3. the properties are preserved when we add a packet to the current block

  We prove these properties after several helper lemmas below:*)

Lemma create_red_encode_block_lists: forall (p: packet) h k,
  0 < h <= fec_max_h ->
  0 < k <= fec_n - 1 - fec_max_h ->
  packet_valid p ->
  encodable p ->
  al (get_block_lists (new_fec_packet p k h :: (encode_block (create_block_with_packet_red p k h) (Some p)).2)) =
  [:: block_to_btuple (encode_block (create_block_with_packet_red p k h) (Some p)).1 ].
Proof.
  move => p h k Hh0 Hk0 Hval Henc.
  apply get_block_lists_single.
  - apply encode_block_some_wf => //.
    apply create_red_in_progress; lia.
    by apply create_block_red_wf.
  - apply data_block_elt. apply encode_block_nonempty.
    apply create_red_nonempty; lia.
  - move => p'. rewrite encode_some/= in_cons mem_cat.
    split.
    + move => /orP[/eqP Hp' | Hin].
      * subst. apply /orP. left. rewrite in_mem_In. apply upd_Znth_In. by zlist_simpl.
      * apply /orP. right. by apply map_f.
    + move => /orP[ Hinp | Hinp].
      * apply /orP. left. apply /eqP. move: Hinp. rewrite in_mem_In => Hinp.
        apply In_upd_Znth in Hinp. case: Hinp => [[Hp']// | Hinp'].
        move: Hinp'. rewrite In_Znth_iff => [[i [Hlen]]]. zlist_simpl => //.
        move: Hlen; zlist_simpl.
      * apply /orP. right. rewrite mem_map in Hinp => //. apply some_inj.
Qed.

(*Extend this easily*)
Lemma create_red_encode_blocks: forall (p: packet) h k,
  0 < h <= fec_max_h ->
  0 < k <= fec_n - 1 - fec_max_h ->
  packet_valid p ->
  encodable p ->
  get_blocks (new_fec_packet p k h :: (encode_block (create_block_with_packet_red p k h) (Some p)).2) =
  [:: (encode_block (create_block_with_packet_red p k h) (Some p)).1 ].
Proof.
  move => p h k Hh Hk Hvalid Henc. rewrite /get_blocks create_red_encode_block_lists //= btuple_block_inv //=.
  - apply encode_block_some_wf => //. apply create_red_in_progress; lia.
    by apply create_block_red_wf.
  - by rewrite encode_block_black_comp.
  - by rewrite encode_block_time.
  - apply data_block_elt. apply encode_block_nonempty. apply create_red_nonempty; lia.
Qed. 

(*An easier case*)
Lemma create_red_block: forall (p: packet) h k,
  0 < k ->
  0 <= h ->
  get_blocks [:: new_fec_packet p k h] = [:: create_block_with_packet_red p k h].
Proof.
  move => b h k Hk Hh. rewrite /get_blocks/=/create_block_with_packet_red/new_packet_list/new_fec_packet/=.
  set p:= {|
               p_packet := b;
               p_fec_data :=
                 {|
                   fd_k := k;
                   fd_h := h;
                   fd_isParity := false;
                   fd_blockId := p_seqNum b;
                   fd_blockIndex := Int.zero
                 |}
             |}.
  rewrite Int.unsigned_zero. rewrite /btuple_to_block/=.
  rewrite {1}zseq_hd; try lia. rewrite upd_Znth0/=.
  f_equal. f_equal.
  - rewrite sublist_upd_Znth_lr; zlist_simpl => //=. f_equal.
    rewrite zseq_sublist; try lia. f_equal. lia.
  - rewrite sublist_upd_Znth_r; zlist_simpl.
    rewrite zseq_sublist; try lia. f_equal. lia.
Qed.


(*If there is no block in progress, we can get useful information about the sequence numbers of all
  packets in pkts*)
Lemma in_pkts_id_new_block: forall orig blks pkts h,
  encoder_props orig blks None pkts ->
  p_seqNum h \notin (map p_seqNum orig) ->
  forall (p: fec_packet_act),
  p \in pkts ->
  fd_blockId p != p_seqNum h.
Proof.
  move => orig blks pkts h [IHperm [IHallwf [IHblackcomp [IHtime [IHdata [IHinorig [IHids [IHencoded [IHprog IHwfpkts]]]]]]]]] 
  Hht p Hpin.
  have Hpin': In p pkts by rewrite -in_mem_In.
  have Hprop: get_block_lists_prop pkts (map block_to_btuple blks). {
    eapply perm_get_block_lists_prop. by apply get_block_lists_spec. have Hperm':=IHperm.
    move: Hperm'. rewrite /get_blocks => Hperm'. apply (perm_map (block_to_btuple)) in Hperm'.
    rewrite -map_comp in Hperm'. rewrite (btuple_block_inv_list IHwfpkts) in Hperm' => //.
    by apply get_block_lists_spec.
  }
  have [pkts' [Hinpkts Hinp]] :=(get_block_lists_allin_in IHwfpkts Hprop Hpin').
  move: Hinpkts. rewrite in_map_iff.
  (*idea: p is in a block b which is in blks. We know by IH that blk_id b = seqNum of some
    packet (which must be in pkts). Thus, by uniqueness of sequence numbers, different than h's*)
  rewrite /block_to_btuple/= => [[b] [[Hid Hpkts']] Hinb]. rewrite -Hid.
  move: IHids => /(_ _ Hinb) [p'] [Hinp' Hidp']. rewrite Hidp'.
  move: IHinorig => /(_ _ _ Hinb Hinp'). rewrite -in_mem_In => Hint.
  case: (p_seqNum p' == p_seqNum h) /eqP => Heq //. move: Hht.
  have->//: p_seqNum h \in [seq p_seqNum i | i <- orig]. rewrite -Heq.
  by apply map_f.
Qed.

(*Case 1: If there is no block in progress, we can add a new block and packet, preserving the invariant*)
Lemma encoder_props_new_block: forall p orig blks pkts k h,
  0 < k <= fec_n - 1 - fec_max_h ->
  0 < h <= fec_max_h ->
  packet_valid p ->
  encodable p ->
  p_seqNum p \notin (map p_seqNum orig) ->
  encoder_props orig blks None pkts ->
  encoder_props (p :: orig) blks (Some (create_block_with_packet_red p k h))
    (pkts ++ [:: new_fec_packet p k h]).
Proof.
  move => p orig blks pkts k h Hk Hh Hval Henc Hhnum Hprops.
  have Hpktsid:=(in_pkts_id_new_block Hprops Hhnum).
  case: Hprops => [IHperm [IHallwf [IHblackcomp [IHtime [IHdata [IHinorig [IHids [IHencoded [IHprog IHwfpkts]]]]]]]]] .
  (*We need to prove wf_packet_stream first*)
  have Hwf: wf_packet_stream (pkts ++ [:: new_fec_packet p k h]). {
    rewrite /wf_packet_stream; split_all.
    - move => p1 p2. rewrite !mem_cat !in_cons/= => /orP[Hp1 | /orP[/eqP Hp1 |//]] 
        /orP[Hp2 | /orP[/eqP Hp2|//]]; subst => //=.
      + by apply IHwfpkts.
      + move => Heq. apply Hpktsid in Hp1. move: Hp1. by rewrite Heq eq_refl.
      + move => Heq. apply Hpktsid in Hp2. move: Hp2. by rewrite Heq eq_refl.
    - move => p1 p2. rewrite !mem_cat !in_cons/= => /orP[Hp1 | /orP[/eqP Hp1 |//]] 
        /orP[Hp2 | /orP[/eqP Hp2|//]]; subst => //=.
      + by apply IHwfpkts.
      + move => Heq. apply Hpktsid in Hp1. move: Hp1. by rewrite Heq eq_refl.
      + move => Heq. apply Hpktsid in Hp2. move: Hp2. by rewrite Heq eq_refl.
      (*literally same proof*)
    - move => p'. rewrite !mem_cat !in_cons/= => /orP[Hp1 | /orP[/eqP Hp1 |//]]; subst => //=.
      + by apply IHwfpkts.
      + rewrite Int.unsigned_zero. lia.
    - move => p'. rewrite !mem_cat !in_cons/= => /orP[Hp1 | /orP[/eqP Hp1 |//]]; subst => //=.
      + by apply IHwfpkts.
      + lia.
  }
  (*Now we can complete this case*)
  rewrite /encoder_props /block_option_list/=; split_all =>//.
  { rewrite get_blocks_app //. eapply perm_trans. rewrite perm_catC. apply perm_refl.
    rewrite (cons_app _ blks). apply perm_cat => //. by rewrite create_red_block //; lia.
    move => p1 p2 Hp1. apply Hpktsid in Hp1. rewrite in_cons => /orP[/eqP Hp2 | //]. by subst. 
  }
  { move => b [Hb | Hinb//]; last first. by apply IHallwf. subst.
    by apply create_block_red_wf.
  }
  { move => b [Hb | Hinb]; last first. by apply IHblackcomp. by subst. }
  { move => b [Hb | Hinb]; last first. by apply IHtime. by subst. }
  { move => b [Hb | Hinb]; last first. by apply IHdata. subst. apply create_red_nonempty; lia. }
  { move => b p' [Hb | Hinb] Hinp; last first. right. by apply (IHinorig _ _ Hinb).
    subst. apply In_upd_Znth in Hinp.
    case : Hinp => [[Hpnew] | Hin].
    - subst. by left.
    - move: Hin. rewrite In_Znth_iff; zlist_simpl. move => [i [Hi]]. by zlist_simpl.
  }
  { move => b [Hb | Hinb]; last first. by apply IHids. subst.
    rewrite /=. exists (new_fec_packet p k h).
    split => //. apply upd_Znth_In. zlist_simpl.
  }
  { move => b [Hb]. rewrite -Hb/=. apply create_red_in_progress. lia. }
Qed.

(*This is needed in several cases*)
Lemma in_old_block: forall pkts blks b,
  wf_packet_stream pkts ->
  perm_eq (get_blocks pkts) (b :: blks) ->
  block_in_progress b ->
  block_wf b ->
  forall (x: fec_packet_act), x \in pkts -> fd_blockId x = blk_id b ->
     In (Some x) (data_packets b).
Proof.
  move => pkts blks b Hwf Hperm Hprog Hwfb x Hinx Hidx.
  apply (perm_map block_to_btuple) in Hperm. move: Hperm. rewrite -map_comp.
  rewrite (btuple_block_inv_list Hwf) //; last first.
    by apply get_block_lists_spec.
  move => Hperm.
  have Hinx1: In x pkts by rewrite -in_mem_In.
  have Hprop:=(perm_get_block_lists_prop (get_block_lists_spec Hwf) Hperm).
  have [pkts' [Hinpkts' Hinxp]]: exists pkts', In (fd_blockId (p_fec_data' x), pkts')
    (block_to_btuple b :: [seq block_to_btuple i | i <- blks]) /\ In (Some x) pkts' by
    apply (get_block_lists_allin_in Hwf).
  move: Hinpkts' => /= [Hinpkts' | Hinpkts'].
  - move: Hinpkts'. rewrite /block_to_btuple/= => [[Hid Hpkts']]; subst.
    (*has to be in data packets because block is in progress*)
    apply in_app_or in Hinxp; case: Hinxp => [Hindat // | Hinpar].
    move: Hprog. rewrite /block_in_progress => /allP Hprog.
    rewrite -in_mem_In in Hinpar. by move: Hprog => /(_ _ Hinpar).
  - (*problem - ids are unique*)
    case Hprop => [_ [_ [_ [_ Huniq]]]].
    move: Huniq. rewrite /=.
    have->//:(blk_id b \in [seq i.1 | i <- [seq block_to_btuple i | i <- blks]]).
    rewrite in_mem_In in_map_iff. by exists (fd_blockId x, pkts').
Qed.

(*The most difficult part of Cases 2 and 3 is dealing with the [get_blocks]. Both cases are broadly similar,
  so we generalize with the following lemma and prove each case as a corollary. This is quite a long, ugly proof*)
Lemma get_blocks_expand: forall pkts p1 blks b b1,
  wf_packet_stream (pkts ++ p1) ->
  (forall b', b = b' \/ In b' blks -> block_wf b') ->
  (forall b', b = b' \/ In b' blks -> black_complete b' = false) ->
  (forall b', b = b' \/ In b' blks -> black_time b' = 0) ->
  (forall b', b = b' \/ In b' blks -> data_elt b') ->
  block_in_progress b ->
  (*If b1 and p1 satisfy some reasonable properties with b and each other:*)
  block_wf b1 ->  
  blk_id b1 = blk_id b ->
  blk_k b1 = blk_k b ->
  blk_h b1 = blk_h b ->
  black_complete b1 = false ->
  black_time b1 = 0 ->
  (forall p, In (Some p) (data_packets b) -> In (Some p) (data_packets b1))  ->
  (forall p, In p p1 -> In (Some p) (data_packets b1 ++ parity_packets b1)) ->
  (forall p, In (Some p) (data_packets b1 ++ parity_packets b1) -> In (Some p) (data_packets b) \/ In p p1) ->
  (forall p p', In (Some p) (data_packets b) -> In p' p1 -> fd_blockIndex p != fd_blockIndex p') ->
  perm_eq (get_blocks pkts) (b :: blks) ->
  perm_eq (get_blocks (pkts ++ p1)) (b1 :: blks).
Proof.
  move => pkts p1 blks b b1 Hwf Hallwf Hallblack Htimes Hnonemp Hprog Hwfb1 Hidb1 Hkb1 Hhb1 Hblackb1 Htimeb1 Hinb Hinp1 
    Hiniff Hdisj Hperm.
  have Hwfb : block_wf b by apply Hallwf; left.
  have Hwfp: wf_packet_stream pkts. apply (wf_substream Hwf). move => x Hinx. by rewrite mem_cat Hinx.
  have Hinpkts: forall (x: fec_packet_act), x \in pkts -> fd_blockId x = blk_id b ->
    In (Some x) (data_packets b). {
    move => x Hpkts Hid. by apply (in_old_block Hwfp Hperm). }
    (*Int.unsigned (fd_blockIndex x) < blk_k b. {
    move => x Hinx Hidx. apply (in_data_idx_bound Hwfb). by apply (in_old_block Hwfp Hperm). }*)
  have Hinp1': forall (x: fec_packet_act), x \in p1 -> fd_blockId x = blk_id b /\
    fd_k x = blk_k b /\ fd_h x = blk_h b. {
    move => x. rewrite in_mem_In => Hin. apply Hinp1 in Hin. rewrite -Hidb1 -Hkb1 -Hhb1.
    by split; apply Hwfb1; apply in_app_or. }
  have Hdatab1: data_elt b1. { have: data_elt b by apply Hnonemp; left. rewrite /data_elt.
    case Hmap: (pmap id (data_packets b)) => [// | h t /=] _.
    have: h \in pmap id (data_packets b1). rewrite -pmap_id_some in_mem_In. apply Hinb.
      by rewrite -in_mem_In pmap_id_some Hmap in_cons eq_refl.
    by case: (pmap id (data_packets b1)).
  }
  move: Hperm. rewrite /get_blocks. move => Hperm.
  apply (perm_map block_to_btuple) in Hperm. move: Hperm. rewrite -map_comp.
  rewrite (btuple_block_inv_list Hwfp) //; last first.
    by apply get_block_lists_spec. (*NOTE: Hwfb1 <-> Hwfenc*)
  rewrite -(@block_btuple_inv_list (b1 :: blks)).
  2 : { move => b' /= [Hb |Hin// ]; subst => //. by apply Hallwf; right.  }
  2 : { move => b'/= [Hb' |Hin]; subst => //. by apply Hallblack; right. }
  2 : { move => b'/= [Hb' |Hin]; subst => //. by apply Htimes; right. }
  2 : { move => b'/= [Hb' |Hin]; subst => //; apply data_block_elt => //.
        by apply Hnonemp; right.  }
  move => Hperm. rewrite (map_comp btuple_to_block). apply perm_map.
  (*Now we finally have things just in terms of block lists*)
  move: Hperm => /=Hperm.
  apply (get_block_lists_prop_perm Hwf). by apply get_block_lists_spec.
  apply (perm_get_block_lists_prop (get_block_lists_spec Hwfp)) in Hperm.
  (*We have now reduced this to a problem just about [get_block_lists_prop], which is tedious
    but possible to work with*)
  case Hperm => [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]].
  (*One more lemma before continuing case-by-case*)
  have Hinborig: forall (x: fec_packet_act), In (Some x) (data_packets b ++ parity_packets b) ->
    In x pkts. {
    have Hinb': In (blk_id b, data_packets b ++ parity_packets b) 
      (block_to_btuple b :: [seq block_to_btuple i | i <- blks]) by left.
    move => x Hinx. apply (get_block_lists_prop_packets Hperm Hinb' Hinx). }
  rewrite /get_block_lists_prop; split_all.
  - move => p Hinp. apply in_app_or in Hinp. case: Hinp => [Hinp | Hinp].
    + apply Hallin1 in Hinp. case: Hinp => /=[pkts' [Hinb' | Hinb']].
      * exists (block_to_btuple b1).2. left.
        move: Hinb'. rewrite /block_to_btuple/= Hidb1 => [[Hid Hpkts]]. by rewrite Hid.
      * exists pkts'. by right.
    + exists (block_to_btuple b1).2. left.
      rewrite /block_to_btuple/= Hidb1.
      f_equal. rewrite -in_mem_In in Hinp. apply Hinp1' in Hinp. by case: Hinp => [Hinp _].
  - move => i' pkts'/= [Hin1 | Hin2].
    + move: Hin1. rewrite /block_to_btuple/= Hidb1 => [[Hid Hpkts']].
      subst. move: Hdatab1. rewrite /data_elt.
      case Hmap: (pmap id (data_packets b1)) => [//| h tl /=] _.
      exists h. apply in_or_app. left. by rewrite -in_mem_In pmap_id_some Hmap in_cons eq_refl.
    + apply (Hnonemp1 i' pkts'). by right.
  - move => i' pkts' p/= [Hin1 | Hin2] Hinp.
    + move: Hin1. rewrite /block_to_btuple/= Hidb1 => [[Hid Hpkts']].
      subst. apply in_app_or in Hinp.
      rewrite Zlength_app //.
      have->:Zlength(data_packets b1) = blk_k b1 by apply Hwfb1.
      have->:Zlength(parity_packets b1) = blk_h b1 by apply Hwfb1.
      have [Hkeq Hheq]: fd_k p = blk_k b /\ fd_h p = blk_h b. {
        rewrite -Hkb1 -Hhb1. by apply Hwfb1.  }
      by rewrite Hkeq Hheq Hkb1 Hhb1.
    + apply (Hlen1 i') => //. by right.
  - case Hwfb1 => [Hhbound [Hkbound [_ [_ [_ [Hdat1 [Hpar1 _]]]]]]].
    (*Now we can prove this*)
    move => i' pkts'/= [Hin1 | Hin2].
    + move: Hin1. rewrite /block_to_btuple/= Hidb1.
      have Hinb': In (blk_id b, data_packets b ++ parity_packets b) 
        (block_to_btuple b :: [seq block_to_btuple i | i <- blks]) by left.
      apply Heq1 in Hinb'.
      move => [Hid Hpkts']; subst.
      apply Znth_eq_ext; zlist_simpl.
      rewrite Hdat1 Hpar1 => i Hi. zlist_simpl.
      case_pickSeq (pkts ++ p1).
      { move: Hinx. rewrite mem_cat => /orP[Hinx | Hinx].
        { case Hwfb1 => [_ [_ [_ [_ [Hidxb1 _]]]]].
          solve_sumbool. apply Hidxb1 in e => //.
          apply Hinpkts in Hinx. left. by apply Hinb. by [].
        }
        { case Hwfb1 => [_ [_ [_ [_ [Hidxb1 _]]]]].
          solve_sumbool. apply Hidxb1 in e => //.
          apply in_app_or. apply Hinp1. by rewrite -in_mem_In.
        }
      }
      { move => Hall. case Hith: (Znth i (data_packets b1 ++ parity_packets b1)) => [p' |//].
        have Hinp': In (Some p') (data_packets b1 ++ parity_packets b1). { 
          rewrite -Hith. apply Znth_In. rewrite Zlength_app; lia. }
        have Hidp': fd_blockId p' = blk_id b. { rewrite -Hidb1. apply Hwfb1. by apply in_app_or. }
        have Hidxp': i = (Int.unsigned (fd_blockIndex p')). { apply Hwfb1 => //. by apply in_app_or. }
        have Hincat: p' \in (pkts ++ p1). { (*NOTE: here is where we need iff condition*)
          have [Hinpb | Hinpp1]: In (Some p') (data_packets b) \/ In p' p1. apply Hiniff => //.
          - rewrite mem_cat. apply /orP. left. rewrite in_mem_In. apply Hinborig. apply in_or_app. by left.
          - rewrite mem_cat. apply /orP. right. by rewrite in_mem_In.
        }
        move: Hall => /( _ _ Hincat). rewrite -Hidxp' Hidp' eq_refl. by case: (Z.eq_dec i i).
      }
    +  (*now at the other case, just need to know no tuple has this id*)
      have Hin2': In (i', pkts') (block_to_btuple b :: [seq block_to_btuple i | i <- blks]) by right.
      apply Heq1 in Hin2'. rewrite {1}Hin2'. apply Znth_eq_ext; zlist_simpl. move => i Hi.
      zlist_simpl. case_pickSeq pkts.
      * case_pickSeq (pkts ++ p1).
        { move: Hinx0. rewrite mem_cat => /orP[Hinx0 | Hinx0].
          { f_equal. apply Hwfp => //. congruence. solve_sumbool. subst.
            apply (f_equal Int.repr) in e. by rewrite !Int.repr_unsigned in e.
          }
          { have Hinx0':=Hinx0. apply Hinp1' in Hinx0'. case: Hinx0' => [Hblkidx0 [Hkx0 Hhx0]].
            apply Hinpkts in Hinx => //; [|congruence]. solve_sumbool. subst.
            apply (f_equal Int.repr) in e. rewrite !Int.repr_unsigned in e.
            rewrite in_mem_In in Hinx0.
            move: Hdisj => /( _ _ _ Hinx Hinx0). by rewrite e eq_refl.
          }
        }
        { have Hinxapp: x \in pkts ++ p1 by rewrite mem_cat Hinx.
          move => /(_  _ Hinxapp). by rewrite Hxid Hidx eq_refl.
        }
      * case_pickSeq (pkts ++ p1) => //.
        move: Hinx. rewrite mem_cat => /orP[Hinx0 | Hinx0].
        { move => /( _ _ Hinx0). by rewrite Hxid Hidx eq_refl. }
        { apply Hinp1' in Hinx0. case : Hinx0 => [Hxblkid [Hxk Hxh]].
          (*by uniqueness of idx*)
          move: Huniq1 => /=.
          have->//: (blk_id b \in [seq i.1 | i <- [seq block_to_btuple i | i <- blks]]).
          rewrite in_mem_In in_map_iff. exists (i', pkts') => /=. split => //. congruence.
        }
  - rewrite /= Hidb1. apply Huniq1.
Qed.

(*The property we need (derived from previous) for case 2*)
Lemma get_blocks_encode: forall pkts blks b model,
  wf_packet_stream (pkts ++ (encode_block b (Some model)).2) ->
  (forall b', b = b' \/ In b' blks -> block_wf b') ->
  (forall b', b = b' \/ In b' blks -> black_complete b' = false) ->
  (forall b', b = b' \/ In b' blks -> black_time b' = 0) ->
  (forall b', b = b' \/ In b' blks -> data_elt b') ->
  packet_valid model ->
  block_in_progress b ->
  perm_eq (get_blocks pkts) (b :: blks) ->
  perm_eq (get_blocks (pkts ++ (encode_block b (Some model)).2)) ((encode_block b (Some model)).1 :: blks).
Proof.
  move => pkts blks b model Hwf Hallwf Hallblack Htimes Hnonemp Hvalid Hprog Hperm.
  have Hwfb : block_wf b by apply Hallwf; left.
  apply (get_blocks_expand Hwf Hallwf) => //.
  - by apply encode_block_some_wf.
  - by rewrite encode_block_id.
  - by rewrite encode_block_k.
  - by rewrite encode_block_h.
  - rewrite encode_block_black_comp. by apply Hallblack; left.
  - rewrite encode_block_time. by apply Htimes; left.
  - move => p Hinp. by rewrite data_packets_encode.
  - move => p Hinp. apply in_or_app. right.
    rewrite -in_mem_In. apply encode_in. by rewrite in_mem_In.
  - move => p'. rewrite data_packets_encode => Hin. apply in_app_or in Hin.
    case : Hin => [Hin // | Hin].  by left. right. rewrite -in_mem_In.
    apply in_encode. by apply Hnonemp; left. by rewrite in_mem_In. 
  - move => p p' Hinp Hinp'.
    apply in_data_idx_bound in Hinp => //.
    rewrite -in_mem_In in Hinp'. apply encode_in in Hinp'. rewrite in_mem_In in Hinp'.
    apply in_parity_idx_bound in Hinp'; [| by apply encode_block_some_wf].
    move: Hinp'. rewrite encode_block_k encode_block_h => Hidx.
    apply /eqP => Hc. rewrite Hc in Hinp. lia.
Qed.


(*The property we need (derived from previous) for case 3*)
Lemma get_block_add: forall pkts blks b p,
  wf_packet_stream (pkts ++ [:: get_fec_packet p b]) ->
  (forall b', b = b' \/ In b' blks -> block_wf b') ->
  (forall b', b = b' \/ In b' blks -> black_complete b' = false) ->
  (forall b', b = b' \/ In b' blks -> black_time b' = 0) ->
  (forall b', b = b' \/ In b' blks -> data_elt b') ->
  block_in_progress b ->
  packet_valid p ->
  encodable p ->
  Zindex None (data_packets b) < blk_k b ->
  perm_eq (get_blocks pkts) (b :: blks) ->
  perm_eq (get_blocks (pkts ++ [:: get_fec_packet p b])) (add_packet_to_block_red p b :: blks).
Proof.
  move => pkts blks b p Hwf Hallwf Hallblack Htimes Hnonemp Hprog Hvalid Henc Hnotdone Hperm.
  have Hwfb : block_wf b by apply Hallwf; left.
  case Hwfb => [Hkbound [Hhbound [ _ [ _ [ _ [Hdatlen [Hparlen _]]]]]]].
  have Hzidxb: 0 <= Zindex None (data_packets b) < Zlength (data_packets b). {
     have Hnonneg:=(@Zindex_nonneg _ None (data_packets b)). lia. }
  apply (get_blocks_expand Hwf Hallwf) => //.
  - by apply add_red_wf.
  - rewrite add_black_comp. by apply Hallblack; left.
  - rewrite /=. by apply Htimes; left. 
  - move => p' Hinp'. rewrite /=. apply In_upd_Znth_old => //; simpl in *; try lia.
    rewrite Znth_Zindex //. apply Zindex_In. simpl in *; lia.
  - move => p'/= [Hp' |//]. subst. apply in_or_app. left. apply upd_Znth_In. apply Hzidxb.
  - move => p'. rewrite add_red_parity. move => Hin. apply in_app_or in Hin. case: Hin => [/=Hdat | Hpar]; last first.
      move: Hprog. rewrite /block_in_progress => /allP Hall. rewrite -in_mem_In in Hpar.
      by move: Hall => /( _ _ Hpar).
    apply In_upd_Znth in Hdat.
    case: Hdat => [[Hp'] | Hin]; subst. by right; left. by left.
  - move => p1 p2 Hinp1/= [Hp2 |//]. subst.
    rewrite /=.
    apply blockIndex_Znth_data in Hinp1 => //.
    apply /eqP => Hidxeq. move: Hinp1.
    rewrite Hidxeq Int.unsigned_repr; simpl in *; try rep_lia. rewrite Znth_Zindex //.
    apply Zindex_In; simpl in *; lia.
Qed.

(*Case 2: We can encode the current block and add all such packets to the output, preserving the invariant*)
Lemma encoder_props_encode: forall orig b blks pkts model,
  In (Some model) (map (omap (@p_packet _)) (data_packets b)) ->
  encoder_props orig blks (Some b) pkts ->
  encoder_props orig ((encode_block b (Some model)).1 :: blks) None
    (pkts ++ ((encode_block b (Some model)).2)).
Proof.
  move => orig b blks pkts model Hinmodel.
  rewrite {1}/encoder_props/block_option_list/= =>
  [[IHperm [IHallwf [IHblackcomp [IHtimes [IHdata [IHinorig [IHids [IHencoded [IHprog IHwfpkts]]]]]]]]]].
  (*First, prove wf*)
  have Hvalmod: packet_valid model. {
    have Hwfb: block_wf b by apply IHallwf; left. 
    case: Hwfb => [_ [_ [_ [_ [_ [_ [_ [_ Hvalid]]]]]]]].
    move: Hinmodel. rewrite in_map_iff /= => [[o]]. case : o => //= [fp [[Hmodel]] Hin |[Hc]//]; subst.
    apply Hvalid. by left.
  }
  (*These are useful to have in context*)
  have Hprog': block_in_progress b by apply IHprog.
  have Hwfb: block_wf b by apply IHallwf; left.
  have Hwf: wf_packet_stream (pkts ++ (encode_block b (Some model)).2). {
    rewrite /wf_packet_stream.
    have Hinpkts: forall (p' : fec_packet_act), p' \in pkts -> (fd_blockId p' != blk_id b) \/ 
    ( In (Some p') (data_packets b) /\ fd_blockId p' = blk_id b /\ fd_k p' = blk_k b /\
      fd_h p' = blk_h b /\ (Int.unsigned (fd_blockIndex p') < blk_k b)). {
      move => p' Hp'. case: (fd_blockId p' == blk_id b) /eqP => [Hbp | Hbp //]; last first. by left.
      right. have Hin: In (Some p') (data_packets b). by apply (in_old_block IHwfpkts IHperm).
      split. by []. split. apply Hwfb. by left. rewrite -and_assoc. split.
      apply Hwfb. by left. by apply in_data_idx_bound.
  }
  have Hwfenc: block_wf (encode_block b (Some model)).1 by apply encode_block_some_wf. 
  have Hinenc: forall (p': fec_packet_act), p' \in (encode_block b (Some model)).2 -> 
      fd_blockId p' =  blk_id b /\ fd_k p' = blk_k b /\ fd_h p' = blk_h b /\
      blk_k b <= Int.unsigned (fd_blockIndex p'). {
      move => p' Hinp'. apply encode_in in Hinp'. rewrite in_mem_In in Hinp'.
      case Hwfenc => [Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc' Hvalid]]]]]]]].
      split; [|rewrite -and_assoc; split].
      - rewrite Hid;[| by right]. by rewrite encode_block_id.
      - rewrite encode_block_k in Hkh. rewrite encode_block_h in Hkh. apply Hkh. by right.
      - rewrite -(encode_block_k b (Some model)). by apply in_parity_idx_bound.
  }
  (*Ok, now we can prove wf*)
  split_all.
  - move => p1 p2. rewrite !mem_cat => /orP[Hinp1 | Hinp1] /orP[Hinp2 | Hinp2].
    + by apply IHwfpkts.
    + apply Hinpkts in Hinp1. apply Hinenc in Hinp2. case Hinp1 => [Hidp1 | [Hinbp1 [Hidp1 [Hkp1 [Hhp1 _]]]]];
      case Hinp2 => [Hidp2 [Hkp2 [Hhp2 _]]].
      * move => Heq. move: Hidp1. by rewrite Heq Hidp2 eq_refl.
      * lia.
    + (*exact reverse*)
      apply Hinpkts in Hinp2. apply Hinenc in Hinp1. case Hinp2 => [Hidp2 | [Hinbp2 [Hidp2 [Hkp2 [Hhp2 _]]]]];
      case Hinp1 => [Hidp1 [Hkp1 [Hhp1 _]]].
      * move => Heq. move: Hidp2. by rewrite -Heq Hidp1 eq_refl.
      * lia.
    + apply Hinenc in Hinp1. apply Hinenc in Hinp2. lia.
  - move => p1 p2. rewrite !mem_cat => /orP[Hinp1 | Hinp1] /orP[Hinp2 | Hinp2].
    + by apply IHwfpkts.
    + apply Hinpkts in Hinp1. have Hinp2':=Hinp2.
      apply Hinenc in Hinp2'. case Hinp1 => [Hidp1 | [Hin[Hidp1 [Hkp1 [Hhp1 _]]]]];
      case Hinp2' => [Hidp2 [Hkp2 [Hhp2 _]]].
      * move => Heq. move: Hidp1. by rewrite Heq Hidp2 eq_refl.
      * move => Hideq Hidxeq. apply (in_wf_blockIndex_inj Hwfenc) => //; apply in_or_app.
        rewrite data_packets_encode. by left. right; rewrite -in_mem_In. by apply encode_in.
    + (*basically same*)
      apply Hinpkts in Hinp2. have Hinp1':=Hinp1.
      apply Hinenc in Hinp1'. case Hinp2 => [Hidp2 | [Hin[Hidp2 [Hkp2 [Hhp2 _]]]]];
      case Hinp1' => [Hidp1 [Hkp1 [Hhp1 _]]].
      * move => Heq. move: Hidp2. by rewrite -Heq Hidp1 eq_refl.
      * move => Hideq Hidxeq. apply (in_wf_blockIndex_inj Hwfenc) => //; apply in_or_app.
        right; rewrite -in_mem_In. by apply encode_in.
        rewrite data_packets_encode. by left.
    + move => _ Hidxeq.
      by apply (in_wf_blockIndex_inj Hwfenc) => //; apply in_or_app; right; rewrite -in_mem_In; apply encode_in.
  - move => p'. rewrite !mem_cat => /orP[Hinp' | Hinp'].
    + by apply IHwfpkts.
    + apply (in_wf_blockIndex_bound Hwfenc). apply in_or_app. right. rewrite -in_mem_In. by apply encode_in.
  - move => p'. rewrite !mem_cat => /orP[Hinp' | Hinp'].
    + by apply IHwfpkts.
    + move: Hwfenc. rewrite /block_wf; rewrite encode_block_k encode_block_h => [[Hkbound [Hhbound [Hkh _]]]].
      have Hkh':fd_k p' = blk_k b /\ fd_h p' = blk_h b. apply Hkh. right. by rewrite -in_mem_In; apply encode_in. lia.
  }
  (*Now we prove the full props*)
  rewrite /encoder_props/block_option_list/=; split_all => //.
  - by apply get_blocks_encode. (*separate lemma makes things nice*)
  - move => b' [Hb' | Hinb']; last first. by apply IHallwf; right.
    subst. by apply encode_block_some_wf.
  - move => b' [Hb' | Hinb']; last first. by apply IHblackcomp; right.
    subst. rewrite encode_block_black_comp. by apply IHblackcomp; left.
  - move => b' [Hb' | Hinb']; last first. by apply IHtimes; right.
    subst. rewrite encode_block_time. by apply IHtimes; left.
  - move => b' [Hb' | Hinb']; last first. by apply IHdata; right.
    subst. apply encode_block_nonempty. by apply IHdata; left.
  - move => b' p' [Hb' | Hinb'] Hinp'; last first. apply (IHinorig b') => //. by right.
    subst. rewrite data_packets_encode in Hinp'.
    apply (IHinorig b) => //. by left.
  - move => b' [Hb' | Hinb']; last first. by apply IHids; right.
    subst. rewrite data_packets_encode encode_block_id. apply IHids. by left.
  - move => b' [Hb' | Hinb']; last first. by apply IHencoded.
    subst. apply encode_block_encoded=> //. case: Hwfb; lia.
    by apply IHdata; left.
Qed.
 
(*Case 3: Add packet to existing block (that is not yet finished)*)
Lemma encoder_props_add: forall p orig b blks pkts,
  packet_valid p ->
  encodable p ->
  Zindex None (data_packets b) < blk_k b ->
  encoder_props orig blks (Some b) pkts ->
  encoder_props (p :: orig) blks (Some (add_packet_to_block_red p b)) (pkts ++ [:: get_fec_packet p b]).
Proof.
  move => p orig b blks pkts Hval Henc  Hzidx.
  rewrite {1}/encoder_props/block_option_list/= =>
  [[IHperm [IHallwf [IHblackcomp [IHtimes [IHdata [IHinorig [IHids [IHencoded [IHprog IHwfpkts]]]]]]]]]].
  (*Some helpful results*)
  have Hprog: block_in_progress b by apply IHprog.
  have Hwfb: block_wf b by apply IHallwf; left.
  have Hinpkts: forall (x: fec_packet_act), x \in pkts -> fd_blockId x = blk_id b ->
     In (Some x) (data_packets b) by apply (in_old_block IHwfpkts IHperm).
  (*1 similar result*)
  have Hinpktsidx:  forall (x: fec_packet_act), x \in pkts -> fd_blockId x = blk_id b ->
    Int.unsigned (fd_blockIndex x) <> Zindex None (data_packets b). {
    move => x Hinx Hidx. apply (Hinpkts _ Hinx) in Hidx.
    have: Znth (Int.unsigned (fd_blockIndex x)) (data_packets b ++ parity_packets b) = Some x. {
      apply Hwfb => //. by left. }
    rewrite Znth_app1; last first.
      have->: Zlength (data_packets b) = blk_k b by apply Hwfb.
      by apply in_data_idx_bound.
    move => Hznth Hc. rewrite Hc in Hznth. rewrite Znth_Zindex in Hznth => //.
    apply Zindex_In. by have->: Zlength (data_packets b) = blk_k b by apply Hwfb.
  }
  case Hwfb => [Hkbound [Hhbound [_ [_ [_ [Hdatlen [Hparlen _]]]]]]].
  have Hidxb: 0 <= (Zindex None (data_packets b)) <= blk_k b. { split.
      apply Zindex_nonneg. rewrite -Hdatlen. apply Zindex_leq_Zlength. }
  have Hinget: forall (x: fec_packet_act), x \in [:: get_fec_packet p b] ->
    fd_blockId x = blk_id b /\ fd_k x = blk_k b /\ fd_h x = blk_h b /\
    Int.unsigned (fd_blockIndex x) = Zindex None (data_packets b). {
    move => x. rewrite /= in_cons => /orP[/eqP Hx |//]. subst =>//=. split_all => //.
    rewrite Int.unsigned_repr //; simpl in *; rep_lia.
  }
  (*First, prove wf*)
  have Hwf: wf_packet_stream (pkts ++ [:: get_fec_packet p b]). {
    rewrite /wf_packet_stream; split_all.
  - move => p1 p2. rewrite !mem_cat => /orP[Hp1 | Hp1] /orP[Hp2 | Hp2].
    + by apply IHwfpkts.
    + apply Hinget in Hp2. case : Hp2 => [Hp2id [Hp2k [Hp2h Hp2idx]]].
      move => Heqid. apply Hinpkts in Hp1 => //=. 2: congruence.
      rewrite Hp2k Hp2h. apply Hwfb. by left.
    + apply Hinget in Hp1. case : Hp1 => [Hp1id [Hp1k [Hp1h Hp1idx]]].
      move => Heqid. apply Hinpkts in Hp2 => //=. 2: congruence.
      rewrite Hp1k Hp1h. split; symmetry; apply Hwfb; by left.
    + move: Hp1 Hp2. rewrite in_cons => /orP[/eqP Hp1 |//] /orP[/eqP Hp2|//]. by subst.
  - move => p1 p2. rewrite !mem_cat => /orP[Hp1 | Hp1] /orP[Hp2 | Hp2].
    + by apply IHwfpkts.
    + apply Hinget in Hp2. case : Hp2 => [Hp2id [Hp2k [Hp2h Hp2idx]]].
      move => Heqid Heqidx. apply Hinpktsidx in Hp1 => //=; congruence.
    + apply Hinget in Hp1. case : Hp1 => [Hp1id [Hp1k [Hp1h Hp1idx]]].
      move => Heqid Heqidx. apply Hinpktsidx in Hp2 => //=; congruence.
    + move: Hp1 Hp2. rewrite in_cons => /orP[/eqP Hp1 |//] /orP[/eqP Hp2|//]. by subst.
  - move => p'. rewrite mem_cat => /orP[ Hp' | Hp'].
    + by apply IHwfpkts.
    + apply Hinget in Hp'. case : Hp' => [Hpid [Hpk [Hph Hpidx]]].
      rewrite Hpk Hph Hpidx. lia.
  - move => p'. rewrite mem_cat => /orP[ Hp' | Hp'].
    + by apply IHwfpkts.
    + apply Hinget in Hp'. case : Hp' => [Hpid [Hpk [Hph Hpidx]]]. lia.
  }
  (*Now we can prove the rest*)
  rewrite /encoder_props/block_option_list/=; split_all => //.
  - by apply get_block_add.
  - move => b' [Hb' | Hinb']; last first. by apply IHallwf; right.
    subst. by apply add_red_wf.
  - move => b' [Hb' | Hinb']; last first. by apply IHblackcomp; right.
    subst. rewrite add_black_comp. by apply IHblackcomp; left.
  - move => b' [Hb' | Hinb']; last first. by apply IHtimes; right.
    subst => /=. by apply IHtimes; left.
  - move => b' [Hb' | Hinb']; last first. by apply IHdata; right.
    subst. apply add_red_nonempty. by apply IHdata; left.
  - move => b' p' [Hb' | Hinb'] Hinp'; last first. right. apply (IHinorig b') => //. by right.
    subst. rewrite /= in Hinp'. apply In_upd_Znth in Hinp'.
    case: Hinp' => [[Hp'] | Hinp'].
    + subst. by left.
    + right. apply (IHinorig b) => //. by left.
  - move => b' [Hb' | Hinb']; last first. by apply IHids; right.
    subst. rewrite add_red_id.
    have [p' [Hinp' Hidp']]: exists p : fec_packet_act, In (Some p) (data_packets b) /\ blk_id b = p_seqNum p
      by apply IHids; left.
    exists p'. split => //. rewrite /=. apply In_upd_Znth_old => //.
    rewrite Znth_Zindex //. apply Zindex_In. all: simpl in *; lia.
  - move => b' [Hb']; subst. rewrite /block_in_progress add_red_parity. apply Hprog.
Qed. 

(*The key theorem about the encoder: encoder_props holds. We need all of these properties for a strong enough
  IH, even though only a few are important in the final theorem we need (TODO: reference*)
(*We have 1 other statement (about Zindex). We don't have this in [encoder_props] because it doesn't hold at
  all the intermediate steps*)
Theorem rse_encode_all_blocks: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, In (k, h) params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  encoder_props orig (rse_encode_all orig params).1.1 (rse_encode_all orig params).1.2 (rse_encode_all orig params).2 /\
  (forall b, (rse_encode_all orig params).1.2 = Some b -> Zindex None (data_packets b) < blk_k b).
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz.
  (*First, switch to foldr*)
  rewrite /rse_encode_all -(revK (combine _ _)) foldl_rev -zip_combine rev_zip // {Hsz}.
  have Hparam': forall k h, In (k, h) (rev params) -> 0 < k <= fec_n - 1 - fec_max_h /\ 0 < h <= fec_max_h. {
    move => k h Hin. apply Hparam. move: Hin. by rewrite -!in_mem_In mem_rev. }
  move: Hparam Hparam' => _ Hparam. forget (rev params) as p. rewrite {params}.
  have: forall p, p \in rev (orig) -> packet_valid p by apply in_pred_rev.
  have: forall p, p \in rev orig -> encodable p by apply in_pred_rev.
  have: uniq (map p_seqNum (rev orig)) by rewrite map_rev rev_uniq. 
  move: Hvalid Henc Huniq => _ _ _ Huniq Henc Hvalid. rewrite encoder_props_orig_rev_iff.
  forget (rev orig) as o. rewrite {orig}. move: p Hparam Huniq Henc Hvalid.
  elim : o => [//= p Hp Henc Hvalid | h t /= IH p Hp /andP[Hht Huniq] Henc Hvalid].
  - by rewrite zip_nil.
  - move: Hp. case : p => [|ph pt] Hp.
    + by rewrite zip_nil_r.
    + rewrite /=. have Hpt: forall k h : Z, In (k, h) pt -> 0 < k <= fec_n - 1 - fec_max_h /\ 0 < h <= fec_max_h. {
        move => k' h' Hin. apply Hp. by right. }
      move: IH => /(_ _ Hpt Huniq (in_pred_tl Henc) (in_pred_tl Hvalid)). rewrite {Hpt}.
      set ind := (foldr
         (fun (x : packet * (Z * Z)) (z : seq block * option block * seq fec_packet_act) =>
          ((rse_encode_gen z.1.1 z.1.2 x.1 x.2.1 x.2.2).1.1,
          (rse_encode_gen z.1.1 z.1.2 x.1 x.2.1 x.2.2).1.2,
          z.2 ++ (rse_encode_gen z.1.1 z.1.2 x.1 x.2.1 x.2.2).2)) ([::], None, [::]) 
         (zip t pt)). (*once again, don't care what ind is, just that we can use IH*)
      rewrite /rse_encode_gen/encode_new/encode_exist.
      case : ind => [[blks currBlock] pkts]/=.
      have [Hph1 Hph2]: 0 < ph.1 <= fec_n - 1 - fec_max_h /\ 0 < ph.2 <= fec_max_h. {
        apply Hp. move: Hp. by case: ph; left. }
      have Hhval: packet_valid h. { apply Hvalid. by rewrite in_cons eq_refl. }
      have Hhenc: encodable h. { apply Henc. by rewrite in_cons eq_refl. }
      case currBlock => [/= b | /=]; last first.
      * move => [IH Hzindex]. case: (Z.eq_dec ph.1 1) => HHl1/=; last first.
          split. by apply encoder_props_new_block. move => b [Hb]. subst.
          rewrite create_red_Zindex/=; lia.
        apply (@encoder_props_new_block h t _ _ ph.1 ph.2) in IH => //.
        set b := (create_block_with_packet_red h ph.1 ph.2).
        have->:(pkts ++ new_fec_packet h ph.1 ph.2 :: (encode_block b (Some h)).2) =
          (pkts ++ [:: new_fec_packet h ph.1 ph.2]) ++ (encode_block b (Some h)).2 by rewrite -catA.
        split => //. apply encoder_props_encode => //. subst b. apply create_block_in. lia.
      * move => [IH Hzindex].
        case Hchange : (~~ Z.eq_dec (blk_k b) ph.1 || ~~ Z.eq_dec (blk_h b) ph.2) => /=.
        -- have Hdat: data_elt b. apply IH => /=. by left.
           apply encode_block_none_some in Hdat. case : Hdat => [model [Hinmod Hencns]].
           rewrite Hencns. apply (encoder_props_encode Hinmod) in IH.
           (*similar cases as before now*)
           case: (Z.eq_dec ph.1 1) => HHl1/=; last first.
              rewrite catA.  split. by apply encoder_props_new_block. move => b' [Hb']. subst.
              rewrite create_red_Zindex/=; lia.
           apply (@encoder_props_new_block h t _ _ ph.1 ph.2) in IH => //. move: IH.
           set b' := (create_block_with_packet_red h ph.1 ph.2) => IH.
           rewrite (cons_app (new_fec_packet _ _ _)) (catA _ _ (encode_block b' (Some h)).2).
           apply (@encoder_props_encode _ _ _ _ h) in IH.
           rewrite -!catA in IH. rewrite -!catA. split => //.
           subst b'. apply create_block_in. lia.
        -- (*last case - add packet to existing block*)
          have Hidx: Zindex None (data_packets b) < blk_k b by apply Hzindex.
          have->:(Zlength
             [seq x <- upd_Znth (Zindex None (data_packets b)) (data_packets b)
                         (Some (get_fec_packet h b))
                | isSome x]) = Zlength [seq x <- (data_packets b) | isSome x] + 1.
          { rewrite upd_Znth_Zindex_Zlength //. apply Z.add_comm.
            have Hwf: block_wf b by apply IH; left.
            have->: Zlength (data_packets b) = blk_k b by apply Hwf. by apply Hzindex.
          }
          case: (Z.eq_dec (Zlength [seq x <- data_packets b | isSome x] + 1) (blk_k b)) => /= Hfinish; last first.
          ++ split. apply encoder_props_add => //.
            move => b' [Hb']; subst.
            have Hdatlen: Zlength(data_packets (add_packet_to_block_red h b)) = blk_k (add_packet_to_block_red h b). {
              have Hwfb: block_wf (add_packet_to_block_red h b). apply add_red_wf => //. apply IH. by left.
              apply Hwfb. } rewrite -Hdatlen.
            have Hleqlt: forall (z1 z2 : Z), z1 <= z2 -> z1 <> z2 -> z1 < z2. lia.
            apply Hleqlt. apply Zindex_leq_Zlength. move => Hlen.
            have: Zlength [seq x <- data_packets (add_packet_to_block_red h b) | isSome x] =
              blk_k b. { rewrite -Hdatlen. apply filter_all_Zlength. apply /allP.
              apply Zindex_notin in Hlen. move => x. case: x => [//|]. by rewrite in_mem_In.
            }
            rewrite -add_red_size //. have->//: Zlength(data_packets b) = blk_k b.
            have Hwfb: block_wf b by apply IH; left. apply Hwfb.
          ++ split => //.
            have Hwfb: block_wf b by apply IH; left.
            (*Once again, we apply 2 cases*)
            apply (encoder_props_add Hhval) in IH => //.
            apply (encoder_props_encode) with(model:=h) in IH. by rewrite -catA in IH.
            apply add_block_in.  have->//: Zlength(data_packets b) = blk_k b.
            apply Hwfb.
Qed.

(*Corollaries: the specific properties we need*)

(*1. The resulting packet stream is well formed*)
Corollary rse_encode_stream_wf: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, In (k, h) params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  wf_packet_stream (rse_encode_all orig params).2.
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz.
  by apply rse_encode_all_blocks.
Qed.

(*2. Every data packet in the output came from the input*)
Corollary rse_encode_stream_from_orig: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, In (k, h) params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  (forall (p: fec_packet_act), p \in (rse_encode_all orig params).2 -> 
    fd_isParity p = false -> 
    p_packet p \in orig).
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz p Hp Hpar.
  (*It's not quite as trivial as the last one*)
  have [Hprops _]:=(rse_encode_all_blocks Hparam Hvalid Henc Huniq Hsz).
  case Hprops => [Hperm [Hallwf [_ [_ [_ [Hinorig [_ [_ [_ Hwf]]]]]]]]].
  have [b /andP[Hb Hpb]]:= get_blocks_allin Hwf Hp.
  rewrite in_mem_In. apply (Hinorig b).
  - by rewrite -in_mem_In -(perm_mem Hperm).
  - have Hwfb: block_wf b. apply Hallwf. by rewrite -in_mem_In -(perm_mem Hperm).
    move: Hpb. rewrite mem_cat => /orP[Hdat // | Hinpar].
    by rewrite -in_mem_In.
    have: fd_isParity p. apply Hwfb. by rewrite -in_mem_In. by rewrite Hpar.
Qed.

(*3. Every block in [get_blocks] of the output is well-formed*)
Corollary rse_encode_stream_blocks_wf: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, In (k, h) params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  (forall b, b \in (get_blocks (rse_encode_all orig params).2) -> block_wf b).
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz b Hb.
  have [Hprops _]:=(rse_encode_all_blocks Hparam Hvalid Henc Huniq Hsz).
  apply Hprops. rewrite -in_mem_In. case Hprops => [Hperm _].
  by rewrite -(perm_mem Hperm).
Qed.

(*4. Every recoverable block in [get_blocks] of the output is encoded. This one does not appear
  directly in [encoded_props] but can be derived without too much trouble*)
Corollary rse_encode_stream_recoverable_encoded: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, In (k, h) params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  (forall b, b \in (get_blocks (rse_encode_all orig params).2) -> recoverable b -> block_encoded b).
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz b Hb.
  have [Hprops Hinprog]:=(rse_encode_all_blocks Hparam Hvalid Henc Huniq Hsz).
  move => Hrec. apply Hprops. rewrite -in_mem_In. move: Hb. case Hprops => [Hperm _].
  rewrite (perm_mem Hperm)/block_option_list/=.
  case Hb: (rse_encode_all orig params).1.2 => [b' |//].
  rewrite in_cons => /orP[/eqP Hb' | //]. subst. 
  have Hprog: block_in_progress b' by apply Hprops. have Hzidx:=Hb. 
  apply Hinprog in Hzidx.
  move: Hrec. rewrite /recoverable.
  have->: Zlength [seq x <- parity_packets b' | isSome x] = 0. {
    have->//:[seq x <- parity_packets b' | isSome x] = nil. by apply pars_in_progress. }
  rewrite Z.add_0_r. move => Hsum. solve_sumbool.
  have Hgt:=(@Zlength_filter _ isSome (data_packets b')).
  have: Zlength [seq x <- data_packets b' | isSome x] = Zlength (data_packets b'). {
  (*again, why won't lia work?*)
  have Halleq: forall z1 z2, z1 <= z2 -> z1 >= z2 -> z1 = z2 by lia.
  by apply Halleq. }
  rewrite {g Hgt} filter_all_Zlength => /allP Hall.
  have Hwfb': block_wf b'. apply Hprops. rewrite /block_option_list/= Hb. by left.
  have Hlen: Zlength (data_packets b') = blk_k b' by apply Hwfb'. move: Hzidx.
  rewrite -Hlen Zindex_In -in_mem_In => Hnone. by move: Hall => /(_ _ Hnone).
Qed.

End EncoderBlocks.

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

Theorem all_decoded_in: forall (orig : list packet) (encoded received: list fec_packet_act)
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
Require Import AbstractEncoderDecoder. (*TODO move*)

(*The key difference is that we need to know that we can get the list of encoder params to show that the encoded 
  outputs actually come from repeated (consistent) iterations of the encoder. We do so with
  the following alternate version of the encoder which outputs a list (list packet) rather than just
  the full concatenated list*)

Definition rse_encode_concat (orig: seq packet) (params: seq (Z * Z)) :=
  foldl
  (fun (acc : seq block * option block * seq (seq (fec_packet_act))) (x : packet * (Z * Z)) =>
   let t := rse_encode_gen acc.1.1 acc.1.2 x.1 x.2.1 x.2.2 in (t.1.1, t.1.2, acc.2 ++ [t.2]))
  ([::], None, [::]) (combine orig params).

Opaque rse_encode_gen.

Lemma rse_encode_all_concat_aux: forall orig params,
  (rse_encode_all orig params).1 = (rse_encode_concat orig params).1 /\ 
  (rse_encode_all orig params).2 = concat (rse_encode_concat orig params).2.
Proof.
  move => orig params. rewrite /rse_encode_all/rse_encode_concat/= -(revK (combine _ _)) !foldl_rev. 
  remember (rev (combine orig params)) as l. rewrite {orig params Heql}. elim : l => [// | h t /= [IH1 IH2]]. 
  by rewrite !IH1 !IH2//= !concat_app/= !cat_app app_nil_r.
Qed.

Lemma rse_encode_all_concat: forall orig params,
  (rse_encode_all orig params).2 = concat (rse_encode_concat orig params).2.
Proof.
  move => orig params. by apply rse_encode_all_concat_aux.
Qed.

(*TODO: move*)
Lemma mkseqZ_0: forall {A: Type} (f: Z -> A),
  mkseqZ f 0 = nil.
Proof.
  move => A f. apply Zlength_nil_inv. by rewrite mkseqZ_Zlength.
Qed.

(*This lemma will actually be quite easy with previous result*)
(*From here, we can describe each element of [rse_encode_concat] purely in terms of [rse_encode_func])*)
Lemma rse_concat_mkseqZ: forall orig params,
  Zlength orig = Zlength params ->
  (rse_encode_concat orig params).2 = mkseqZ (fun i => rse_encode_func (sublist 0 i orig) (sublist 0 i params)
    (Znth i orig) (Znth i params).1 (Znth i params).2) (Zlength orig).
Proof.
  move => orig params Hlens. rewrite /rse_encode_concat /rse_encode_func /rse_encode_all.
  remember (@nil block) as b1. remember (@None block) as b2. remember (@nil fec_packet_act) as b3.
  remember (@nil (seq fec_packet_act)) as b4. rewrite {1}Heqb4. rewrite -(cat0s (mkseqZ _ _)). rewrite -{2}Heqb4.
  rewrite {Heqb1 Heqb2 Heqb3 Heqb4}. move: b1 b2 b3 b4 params Hlens.
  elim : orig => [//= b1 b2 b3 b4 params Hlen | h t /= IH b1 b2 b3 b4 params].
  - have->/=:Zlength [::] = 0 by list_solve. rewrite mkseqZ_0. by rewrite cats0.
  - case: params => [| [k' h'] tl/=]; [list_solve |].
    move => Hlen. erewrite IH. 2: list_solve.
    have->: Zlength (h::t) = Zlength t + 1 by list_solve.
    rewrite mkseqZ_1_plus/=; [|list_solve]. rewrite !Znth_0_cons -catA/=. f_equal. f_equal.
    have Hpos: 0 <= Zlength t by list_solve. apply Znth_eq_ext; rewrite !mkseqZ_Zlength //. 
    move => i Hi. rewrite !mkseqZ_Znth// !Znth_pos_cons; try lia. rewrite !sublist_0_cons; try lia.
    by rewrite !Z.add_simpl_r.
Qed.

Corollary rse_concat_nth: forall orig params i,
  Zlength orig = Zlength params ->
  0 <= i < Zlength orig ->
  Znth i (rse_encode_concat orig params).2 = 
  rse_encode_func (sublist 0 i orig) (sublist 0 i params) (Znth i orig) (Znth i params).1 (Znth i params).2.
Proof.
  move => orig params i Hi Hlens. by rewrite rse_concat_mkseqZ //; zlist_simpl.
Qed.

Corollary rse_concat_Zlength: forall orig params,
  Zlength orig = Zlength params ->
  Zlength (rse_encode_concat orig params).2 = Zlength orig.
Proof.
  move => orig params Hlen. by rewrite rse_concat_mkseqZ //; zlist_simpl.
Qed.

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
  fec_packet_act_inhab rse_encoder rse_decoder.
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
