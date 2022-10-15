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


(** The Decoder *)

(*First, we provide the building blocks and intermediate functions
  for any decoder (irrespective of timeouts, etc)*)

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
Lemma parity_mx_sublist_length: forall (i: nat) (s: seq (option fpacket)),
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
Definition packet_from_bytes (l: list byte) (i: nat) : packet :=
  let (header, contents) := recover_packet l in
  mk_pkt header contents i.

(*If the block is well-formed, all the packets will be valid. But we prove this later*)
Definition decode_block (b: block) : list packet :=
  (*Only add missing packets*)
  foldl (fun acc i => let bytes := (Znth i (decoder_list_block b)) in
                      if isNone (Znth i (data_packets b)) && (Znth 0 bytes != Byte.zero) then 
                      acc ++ [packet_from_bytes (Znth i (decoder_list_block b)) 0] else acc) 
    nil (Ziota 0 (blk_k b)).

(*TODO: deduce headers?*)

(*1. create block with packet*)
Definition create_block_with_fec_packet (p: fpacket) (time : Z) : block :=
  let k := fd_k p in
  let h := fd_h p in
  let allPackets := upd_Znth (Z.of_nat (fd_blockIndex p)) (zseq (k + h) None) (Some p) in
  mk_blk (fd_blockId p) (sublist 0 k allPackets) (sublist k (k+h) allPackets) k h false time.

Definition create_block_with_packet_black (p: fpacket) (time: Z) : block * list packet :=
  let new_block := create_block_with_fec_packet p time in
  let packets := (if (fd_isParity p) then nil else [p_packet p]) ++
    (if Z.eq_dec (fd_k p) 1 then (decode_block new_block) else nil) in
  let marked_block := if Z.eq_dec (fd_k p) 1 then new_block <| black_complete := true |> else new_block in
  (marked_block, packets).

(*2. add packet to block*)
Definition add_fec_packet_to_block (p: fpacket) (b: block) : block :=
  let new_packets := upd_Znth (Z.of_nat (fd_blockIndex p)) 
    (data_packets b ++ parity_packets b) (Some p) in
  b <| data_packets := sublist 0 (blk_k b) new_packets |> 
      <| parity_packets := sublist (blk_k b) (blk_k b + blk_h b) new_packets |>.

Definition add_packet_to_block_black (p: fpacket) (b: block) : block * list packet :=
  if black_complete b then (b, if (fd_isParity p) then nil else [p_packet p]) else 
    (*NOTE: theirs does not release data packet here*)
    let new_block := add_fec_packet_to_block p b in 
    let packets := (if (fd_isParity p) then nil else [p_packet p]) ++
      (if recoverable new_block then (decode_block new_block) else nil) in
    let marked_block := if recoverable new_block then new_block <| black_complete := true |> else new_block in
    (marked_block, packets).

(*With these building blocks, we can now define the decoder.
  We do this in several stages and forms
  1. First, we give a generic decoder parameterized by the way
    of updating time and timing out blocks. This implementation
    does not match the C code; it is simpler but inefficient, and it
    makes multiple passes to separate each part of the code.
  2. We then instantiate this generic decoder with the specific
    timeout mechanism used (as well as a version with no timeouts).
    This comprises our idealized functional model.
  3. We (TODO: will) give a version that works on machine-length
    integers and one that matches more closely with the (revised)
    C code.

  This approach allows us to separate the proofs and reduce repetition.
  We prove that the idealized model satisfies 2 properties:
  1. All outputted packets are valid data packets (ie: they came
    from the input to the encoder).
  2. If the packet stream has some (relatively small) amount of reordering
    and duplication, and not too many packets are lost, then all packets
    are recovered. We do this by relating the decoder to one with
    no timeouts.
  
  Then we prove the following of the machine-integer decoder:
  1. If the packet stream has a (very large) bound on reordering/
    duplication, then this is equivalent to the idealized model.
  2. No matter what, the decoder outputs all data packets it receives.

  Finally, we combine these results to get 3 levels of specification:
  1. No matter what, all data packets the decoder sees are outputted.
  2. If the stream is not too badly behaved (ie: not so much reordering
    that we run into integer wraparound issues), then all packets
    the decoder produces are valid.
  3. If the stream is nicely behaved and not too many packets are lost,
    then the decoder recovers all packets.

  TODO: put the file names for each*)
  
(*First, we give a generalized version of the decoder, which enables
  us to prove theorems about versions with different (or no) timeout
  mechanism*)
Section GenDecode.

(*We can update the time, in general, by looking at the current time,
  the list of blocks, and the current packet*)
Variable upd_time: Z -> fpacket -> list block -> Z.
Variable not_timeout : Z -> block -> bool.

Fixpoint update_dec_state_gen (blocks: list block) (curr: fpacket)
    (time: Z) : list block * list packet:=
  match blocks with
  | nil => let t := create_block_with_packet_black curr time in 
      ([:: t.1], t.2)
  | bl :: tl =>
    let currSeq := fd_blockId curr in
    if currSeq == (blk_id bl) then
      let t := add_packet_to_block_black curr bl in
      (t.1 :: tl, t.2)
    else if (currSeq < (blk_id bl))%N then 
      let t := create_block_with_packet_black curr time in 
        (t.1 :: blocks, t.2)
    else update_dec_state_gen tl curr time
  end.

Definition decoder_one_step_gen (blocks: list block) curr time :
  list block * list packet * Z :=
  (*First, we process timeouts; this covers the case when the packet
    which makes the block timeout is the kth packet; we should not
    recover this block (it makes our invariants much harder).*)
  let tm := upd_time time curr blocks in
  let blks := filter (not_timeout tm) blocks in
  let t := update_dec_state_gen blks curr tm in
  (t, tm).

Definition decoder_multiple_steps_gen 
  (prev_packs packs: list fpacket)
  (state: list block) (sent: list packet) (time: Z) :
  list block * list packet * Z * list fpacket :=
  foldl (fun (acc: list block * list packet * Z * list fpacket) 
    (p: fpacket) =>
    let t := decoder_one_step_gen acc.1.1.1 p acc.1.2 in
    (t.1.1, acc.1.1.2 ++ t.1.2, t.2, acc.2 ++ [:: p])) 
  (state, sent, time, prev_packs) packs.

Definition decoder_all_steps_gen (received: list fpacket) :
  (list block * list packet * Z) :=
  (decoder_multiple_steps_gen nil received nil nil 0).1.

(*Now we can define the decoder function*)
Definition decoder_func_gen (received: list fpacket) (curr: fpacket) : 
  list packet :=
  let t := decoder_all_steps_gen received in
  (decoder_one_step_gen t.1.1 curr t.2).1.2.

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
  (P: list fpacket -> list block -> Z -> Prop) 
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
  (fun x y => ((blk_id x) < (blk_id y))%N).
(*Should make block IDs nats, do everything in terms of nats*)
Lemma decoder_one_step_sorted: forall blocks curr time,
  sorted blk_order blocks ->
  sorted blk_order
    (decoder_one_step_gen blocks curr time).1.1.
Proof.
  move=> blocks curr time.
  rewrite /blk_order /decoder_one_step_gen/= => Hsort.
  move: (upd_time time curr blocks) => t.
  move: (not_timeout t) => f.
  rewrite {time}.
  
  (*apply sorted_filter.
    move => b1 b2 b3. apply ltn_trans. *)
  move: Hsort. elim: blocks => [// | bhd btl /= IH Hpath].
  have Htl: sorted (fun x y : block => (blk_id x < blk_id y)%N) btl.
    rewrite {IH}. move: Hpath. by case: btl => //= a b /andP[_].
  case Hfhd: (f bhd)=>/=; last by apply IH.
  have Htrans: {in xpredT & &, transitive (fun x y : block => (blk_id x < blk_id y)%N)} by
    move => b1 b2 b3 _ _ _; apply ltn_trans.
  have Hallpred: all xpredT btl by apply /allP.
  case: ((fd_blockId curr) == (blk_id bhd)) /eqP => Heq.
  - rewrite /= {IH Htl}. apply (path_filter_in Htrans) =>//=.
    rewrite {Hallpred}. 
    (*Now filter is gone*)
    move: Hpath.
    case: btl => //= bhd' btl /andP[Hlt Hpath].
    rewrite Hpath andbT. by rewrite add_packet_to_block_black_id.
  - case Hlt: ((fd_blockId curr) < (blk_id bhd))%N; last by apply IH.
    by case Hk1: (proj_sumbool (Z.eq_dec (fd_k curr) 1))=>/=; rewrite Hlt/=;
    apply (@path_filter_in _ xpredT).
Qed.

(*From this, we get uniqueness for free*)

Lemma decoder_one_step_uniq: forall blocks curr time,
  sorted blk_order blocks ->
  uniq (decoder_one_step_gen blocks curr time).1.1.
Proof.
  move=> blocks curr time Hsort.
  apply sorted_uniq_in with(leT:=blk_order).
  - move => b1 b2 b3 _ _ _. apply ltn_trans.
  - move=> b1 _. by apply ltnn.
  - by apply decoder_one_step_sorted.
Qed.

(*Now we want to prove several structural results about the 
  generic decoder which will enable us to prove that it always
  produces valid packets. (TODO: put in different section because
  it is complete independent of timeouts) *)


(*Prove that if we have ANY recoverable subblock of a completed, well-formed block, 
  then decoder_list_block b gives the original packets. This is a core
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
    + rewrite -Hs. apply Hleq. by apply /inP.
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
    have Hin': packet_in_parity p b2. { move: Hsub. rewrite /subblock => Hsub.
      eapply subseq_option_in. apply Hsub. by apply /inP. }
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
  map (fun p => p <| p_seqNum := 0%N |>) (map (@p_packet _) (get_diff (data_packets b1) (data_packets b2))).

(*An alternate formation of [decode_block] - TODO: is this better to use originally?*)
Definition decode_block' (b: block) : list packet :=
  pmap id (map (fun i =>
      let bytes := (Znth i (decoder_list_block b)) in
      if isNone (Znth i (data_packets b)) && (Znth 0 bytes != Byte.zero) then
        Some (packet_from_bytes bytes 0) 
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
  (forall p, packet_in_data p b1 -> 
    Zlength (packet_bytes (f_packet p)) <= blk_c b2) /\
  (forall p, packet_in_parity p b1 -> 
    Zlength (p_contents (f_packet p)) = blk_c b2).
Proof.
  move => b1 b2. rewrite /block_encoded /subblock => [[_ [Hpars [Hdata _]]]] [_ [Hsubdata [Hsubpar _]]].
  split; move => p Hinp.
  - move: Hsubdata; rewrite /subseq_option => [[Hlens His]].
    move: Hinp => /inP. rewrite In_Znth_iff => [[i [Hi Hp]]].
    have Hi':=Hi.
    apply His in Hi. rewrite Hp in Hi. case: Hi => [Hp'|//].
    apply Hdata. apply /inP. rewrite Hp'. apply Znth_In. simpl in *; lia.
  - move: Hsubpar; rewrite /subseq_option => [[Hlens His]].
    move: Hinp => /inP. rewrite In_Znth_iff => [[i [Hi Hp]]].
    have Hi':=Hi.
    apply His in Hi. rewrite Hp in Hi. case: Hi => [Hp'|//].
    apply Hpars. apply /inP. rewrite Hp'. apply Znth_In. simpl in *; lia.
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
        split; try lia. apply (proj1 (subblock_c Hcomp Hsub)).
        apply /inP. rewrite -Hith. apply Znth_In. simpl in *; lia.
      - have->:blk_c b1 = blk_c b2. by apply blk_c_recoverable. split; try lia.
        case Hp: (Znth i (data_packets b2)) => [p|].
        + move: Hcomp. rewrite /block_encoded => [[_ [_ [Hin _]]]]. apply Hin.
          apply /inP. rewrite -Hp. apply Znth_In. simpl in *; lia.
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
        apply data_in_block. apply /inP. rewrite -Hib2. apply Znth_In.
        simpl in *; lia. }
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
  exists (p': fpacket), packet_in_data p' b2 /\ 
    remove_seqNum p = remove_seqNum (p_packet p').
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

(*TODO*)
Lemma zip_nil_r: forall {A B: Type} (s: seq A),
  zip s (@nil B) = [::].
Proof.
  move => A B s. by case: s.
Qed. 

(*Intermediate case 1: create a new block*)
Lemma create_block_subblock: forall (l: list fpacket) (h: fpacket) (time: Z),
  wf_packet_stream l ->
  h \in l ->
  exists b': block, b' \in (get_blocks l) /\ subblock (create_block_with_packet_black h time).1 b'.
Proof.
  move => l h t Hwf Hinhl.
  (*the real result*)
  have [b' [Hinb' Hsubb']]: exists b' : block, b' \in (get_blocks l) /\ subblock (create_block_with_fec_packet h t) b'; last first.
    exists b'. rewrite /create_block_with_packet_black; split => //=. by case: (Z.eq_dec (fd_k h) 1).
  rewrite /subblock/= /get_blocks/=.
  have [Hallin [Hnonemp [Hlen [Heq Huniq]]]] := (get_block_lists_spec Hwf).
  have Hex := Hinhl. apply Hallin in Hex. case: Hex => [pkts Hinpkts].
  exists (btuple_to_block (fd_blockId h, pkts)).
  split.
    apply /mapP. by exists (fd_blockId h, pkts).
  rewrite (btuple_to_block_eq Hwf Hinpkts Hinhl erefl)/=.
  (*most are trivial, only 2 are interesting. We prove the stronger claim:*)
  have Hsub: subseq_option (upd_Znth (Z.of_nat (fd_blockIndex h)) (zseq (fd_k h + fd_h h) None) (Some h))
    pkts. {
    rewrite (Heq _ _ Hinpkts).
    have Hbound: 0 <= Z.of_nat (fd_blockIndex h) < fd_k h + fd_h h
      by split; try lia; apply (proj1 (proj2 (proj2 Hwf))).
    rewrite /subseq_option upd_Znth_Zlength !zseq_Zlength; try lia.
    rewrite !mkseqZ_Zlength;[|list_solve].
    have Hinh:= (get_blocks_list_all_id Hwf Hinpkts Hinhl erefl).
    rewrite (Hlen _  _ _ Hinpkts Hinh).
    split => //. move => i Hi.
    rewrite !(upd_Znth_lookup'(fd_k h + fd_h h)); try lia; last first.
      rewrite zseq_Zlength; lia.
    rewrite mkseqZ_Znth //.
    case: (Z.eq_dec i (Z.of_nat (fd_blockIndex h))) => [Hih | Hneqih]; last first.
      right. rewrite zseq_Znth //. lia.
    left. case_pickSeq l. 
    (*here, we rely on uniqueness of (id, idx) pairs*)
    - solve_sumbool. f_equal. apply (proj1 (proj2 Hwf)) => //.
      rewrite e in Hih. by apply Nat2Z.inj in Hih.
    - move => /(_ h); rewrite eq_refl -Hih/=. case: (Z.eq_dec i i) => //= _ Hcon.
      have//:true = false by apply Hcon.
  }
  split_all => //; by apply subseq_option_sublist.
Qed. 


(*Intermediate case 2: add packet to existing block. This one is quite complicated because if the block
  is complete, we don't add anything at all, so must show b1 is a subblock*)
Lemma add_to_block_subblock: forall (l: list fpacket) (h: fpacket)  (b1 b2: block),
  wf_packet_stream (h :: l) ->
  fd_blockId h = blk_id b1 ->
  b2 \in (get_blocks l) ->
  subblock b1 b2 ->
  (add_fec_packet_to_block h b2) \in (get_blocks (h :: l)) /\
  subblock (add_packet_to_block_black h b1).1 (add_fec_packet_to_block h b2).
Proof.
  move => l h b1 b2 Hwf Hidh Hinb2 Hsub.
  have Hpos: (forall (p: fpacket), p \in (h :: l) -> 0 <= fd_k p /\ 0 <= fd_h p) by
    move => p; apply Hwf.
  move: Hinb2. rewrite /get_blocks => /mapP [t Hint Hb2]. rewrite Hb2.
  have [Hallin [Hnonemp [Hlen [Heq Huniq]]]] := (get_block_lists_spec (wf_packet_stream_tl Hwf)).
  move: Hb2 Hint. case : t => [i pkts] Hb2 Hint.
  have Hex:=Hint. apply Hnonemp in Hex. case: Hex => [p Hinp].
  have [Hidp Hinpl]: fd_blockId p = i /\ p \in l by apply (@get_block_lists_prop_packets _ (get_block_lists l) i pkts p).
  have Hidi: fd_blockId h = i. { have->:i = blk_id b2 by
    rewrite Hb2 (btuple_to_block_eq (wf_packet_stream_tl Hwf) Hint Hinpl Hidp).
    move: Hsub => [Hsub _]. by rewrite -Hsub. }
  (*some results will be useful in multiple parts*)
  split.
  - (*TODO: separate lemmas? maybe*)
    (*second part is useful for both*)
    have Hnewin: (i, upd_Znth (Z.of_nat (fd_blockIndex h)) pkts (Some h)) 
      \in al (get_block_lists (h :: l)). {
      have [Hallin2 [Hnonemp2 [Hlen2 [Heq2 Huniq2]]]] := (get_block_lists_spec Hwf).
      have Hex: h \in (h :: l) by rewrite in_cons eq_refl. 
      apply Hallin2 in Hex. case: Hex => [pkts' Hin'].
      rewrite -Hidi. have->//: upd_Znth (Z.of_nat (fd_blockIndex h)) pkts (Some h) = pkts'.
      have Hpkts' := Hin'. apply Heq2 in Hpkts'. rewrite Hpkts' {Hpkts'}.
      have Hpkts := Hint. apply Heq in Hpkts. rewrite Hpkts {Hpkts}.
      (*first, need to deal with lengths*)
      rewrite (Hlen _ _ _ Hint Hinp).
      have Hinh:=(get_blocks_list_all_id Hwf Hin' (mem_head _ _) erefl).
      rewrite (Hlen2 _ _ _ Hin' Hinh).
      have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. { apply Hwf.
        by rewrite in_cons Hinpl orbT. by rewrite mem_head.
        by rewrite Hidp. }
      rewrite Hk Hh. have Hinht: h \in h :: l  by rewrite in_cons eq_refl.
      case : Hwf => [_ [Hinj [/(_ h Hinht)]]] Hbound _.
      apply Znth_eq_ext; rewrite Zlength_upd_Znth !mkseqZ_Zlength; try lia. move => j Hj.
        rewrite mkseqZ_Znth // (upd_Znth_lookup' (fd_k h + fd_h h)); try lia; last first.
          by rewrite mkseqZ_Zlength; lia.
        case : (Z.eq_dec j (Z.of_nat (fd_blockIndex h))) => [Hjh | Hjh].
        - case_pickSeq (h :: l).
          (*here, we rely on uniqueness of (id, idx) pairs*)
          + f_equal. apply Hinj => //. solve_sumbool.
            rewrite e in Hjh. by apply Nat2Z.inj in Hjh. 
          + move => /(_  h Hinht). rewrite eq_refl/= -Hjh. by case : (Z.eq_dec j j).
        - rewrite mkseqZ_Znth //. case_pickSeq (h :: l); case_pickSeq l => [|//].
          + f_equal. apply Hinj => //. by rewrite in_cons Hinx0 orbT. by rewrite Hxid0 Hxid.
            solve_sumbool. rewrite e in e0. by apply Nat2Z.inj in e0.
          + have Hinxl: x \in l. move: Hinx; rewrite in_cons => /orP[/eqP Hxh | //].
              solve_sumbool. by subst. 
            move => /(_ x Hinxl). by rewrite Hxid Hidi eq_refl/= Hidx.
          + have Hinxl: x \in h :: l by rewrite in_cons Hinx orbT. move => /(_ x Hinxl).
            by rewrite Hxid Hidi eq_refl/= Hidx. }
    apply /mapP.
    exists (i, upd_Znth (Z.of_nat (fd_blockIndex h)) pkts (Some h)) => //.
    rewrite (btuple_to_block_eq (wf_packet_stream_tl Hwf) Hint Hinpl Hidp)/=.
    rewrite (btuple_to_block_eq Hwf Hnewin (mem_head _ _)) //. 
    rewrite /add_fec_packet_to_block /=.
    have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. { apply Hwf.
      by rewrite in_cons Hinpl orbT. by rewrite mem_head.
      by rewrite Hidp. }
    rewrite Hk Hh.
    have Hlenpkts: Zlength pkts = fd_k h + fd_h h. { rewrite -Hk -Hh. apply (Hlen _ _ _ Hint Hinp). }
    have->: (forall (A: Type) (a1 a2: seq A), a1 ++ a2 = (a1 ++ a2)%list) by [].
    move: Hpos => /( _ h (mem_head _ _ )) => Hpos.
    rewrite -!sublist_split; simpl in *; try lia. by rewrite (sublist_same 0 (fd_k h + fd_h h)).
  - rewrite /add_packet_to_block_black. case Hcomp: (black_complete b1); last first.
      case Hrec: (recoverable (add_fec_packet_to_block h b1)).
      apply subblock_add. by rewrite -Hb2. apply subblock_add. by rewrite -Hb2.
    (*If it was complete, we don't change anything. Proving the subblock relation is a bit harder*)
    (*TODO: separate lemma?*) move: Hb2.
    rewrite !(btuple_to_block_eq (wf_packet_stream_tl Hwf) Hint Hinpl Hidp)/= => Hb2.
    have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. { apply Hwf.
      by rewrite in_cons Hinpl orbT. by rewrite mem_head.
      by rewrite Hidp. } rewrite Hk Hh.
    have Hlenpkts: Zlength pkts = fd_k h + fd_h h. rewrite -Hk -Hh. apply (Hlen _ _ _ Hint Hinp).
    rewrite /subblock/=. split.
      move: Hsub. by rewrite /subblock Hb2 //= => [[H _]].
    move: Hpos => /( _ h (mem_head _ _)) => Hbounds.
    rewrite !cat_app -sublist_split; try lia.
    rewrite !(sublist_same 0 (fd_k h + fd_h h)) //.
    move: Hsub. rewrite /subblock => [[Hid [Hdat [Hpars [Hks Hhs]]]]].
    have Hbounds': 0 <= Z.of_nat (fd_blockIndex h) < fd_k h + fd_h h.
      split; try lia; apply Hwf. by rewrite in_cons eq_refl.
    (*we need to know the relationship between data_packets, parity_packets, etc*)
    subst; simpl in *.
    (*Do this so we don't need to prove same things twice:*)
    have Hsubupd: forall lo hi l, 0 <= Z.of_nat (fd_blockIndex h) < Zlength pkts -> 0 <= lo <= hi ->
        hi <= Zlength pkts ->
        subseq_option l (sublist lo hi pkts) ->
        subseq_option l (sublist lo hi (upd_Znth (Z.of_nat (fd_blockIndex h)) pkts (Some h))). {
      move => lo hi l1 Hhhi Hlohi Hhilen. 
      rewrite /subseq_option !Zlength_sublist; try lia; [|list_solve] => [[Hlens Hith]]. split. lia.
      move => j Hj.
      have [Hin | [Hout1 | Hout2]]: lo <= Z.of_nat (fd_blockIndex h) < hi \/
        0 <= Z.of_nat (fd_blockIndex h) < lo \/ hi <= Z.of_nat (fd_blockIndex h) < Zlength pkts by lia.
      * rewrite sublist_upd_Znth_lr; try lia.
        rewrite (upd_Znth_lookup' (hi - lo)); try lia; [|list_solve].
        case : (Z.eq_dec j (Z.of_nat (fd_blockIndex h) - lo)) => Hjh.
        -- (*the key part: Znth j (data_packets b1) MUST be None or Some h, since if it is anything else,
              pkts will not a well-formeed packet list -conradicts uniquenss*)
          case Hjth: (Znth j l1) => [p' |//]; last first. by right.
          left. f_equal.
          move : Hith => /(_ j Hj). rewrite Znth_sublist; try lia.
          have->: j + lo = Z.of_nat (fd_blockIndex h) by lia.
          rewrite Hjth => [[Hjth' | //]]. apply esym in Hjth'.
          have Hinj: (Some p') \in pkts. rewrite -Hjth'. apply /inP. 
            apply Znth_In. simpl in *; lia.
          have [Hidp' Hinlp']: fd_blockId p' = fd_blockId p /\ p' \in l by 
            apply (@get_block_lists_prop_packets l (get_block_lists l) (fd_blockId p) pkts).
          apply Hwf.
          ++ by rewrite in_cons Hinlp' orbT.
          ++ by rewrite mem_head.
          ++ by rewrite Hidp'.
          ++ move: Hjth'. rewrite (Heq _ _ Hint). rewrite mkseqZ_Znth; try lia.
              case_pickSeq l => [[Hxp]|//]. rewrite -Hxp. solve_sumbool.
              by apply Nat2Z.inj in e. 
        -- by apply Hith.
      * rewrite sublist_upd_Znth_r; try lia. by apply Hith.
      * rewrite sublist_upd_Znth_l; try lia. by apply Hith.
    } 
    split_all.
    + apply Hsubupd; try lia. by rewrite -Hk.
    + apply Hsubupd; try lia. by rewrite -Hh -Hk.
    + lia.
    + lia.
    + simpl in *; lia.
Qed.

Opaque create_block_with_packet_black.

(*TODO: see what we need*)
(*Intermediate case 3: we need a separate inductive lemma for 
  [update_dec_state_gen]. This is a straightforward application
  of the previous 2 cases*)
Lemma update_dec_state_gen_subblocks: forall l blks curr time,
  wf_packet_stream (curr :: l) ->
  (forall b, b \in blks -> exists b', b' \in (get_blocks l) /\ subblock b b') ->
  forall b, b \in (update_dec_state_gen blks curr time).1 ->
    exists b', b' \in (get_blocks (curr :: l)) /\ subblock b b'.
Proof.
  move=>l blks curr. elim: blks => [//= time Hwf Hsub b | h t /= IH time Hwf Hsubs b].
  - rewrite in_cons orbF => /eqP ->.
    apply create_block_subblock => //. by rewrite mem_head.
  - have Hht: (forall x, x \in l -> x \in curr :: l) by (*for IH*)
      move => x Hx; rewrite in_cons Hx orbT. 
    case: (fd_blockId curr == blk_id h) /eqP => HcurrH /=.
    + rewrite in_cons => /orP[/eqP Hb | Hin].
      * rewrite Hb. move: Hsubs => /(_ h (mem_head _ _)) [b1 [Hinb1 Hsub1]].
        exists (add_fec_packet_to_block curr b1). 
        by apply add_to_block_subblock.
      * have Hin': b \in (h:: t) by rewrite in_cons Hin orbT. 
        move: Hsubs => /(_ b Hin') [b1 [Hinb1 Hsub1]].
        have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1).
        exists b2. split => //. by apply (subblock_trans Hsub1).
    + case Hlt: (fd_blockId curr < blk_id h)%N; last by
        apply IH =>// b' Hin; apply Hsubs; rewrite in_cons Hin orbT.
      rewrite in_cons => /orP[/eqP Hb | Hin].
      * rewrite Hb. apply create_block_subblock => //. 
        by rewrite mem_head.
      * move: Hsubs => /(_ b Hin) [b1 [Hinb1 Hsub1]].
        have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1).
        exists b2. split => //. by apply (subblock_trans Hsub1).
Qed.

  (*NOTE: one reason why this is better is because we no longer have
    external state in the decoder that we have to reason about*)


(*Now, finally we can show that every block in the decoder state is a subblock of some
  block from the received stream. This is easy after the previous
  lemma*)
Theorem decoder_all_steps_state_subblocks: forall (received: seq fpacket) (b: block),
  wf_packet_stream received ->
  b \in (decoder_all_steps_gen received).1.1 ->
  exists b', b' \in (get_blocks received) /\ subblock b b'.
Proof.
  move => r b Hwf. rewrite /decoder_all_steps_gen
    /decoder_multiple_steps_gen -(revK r) foldl_rev.
  (*We reverse the list so that we can use foldr. We want to use (rev r)
  everywhere to simplify induction. Luckily rev is a permutation, so
  we can safely switch get_blocks*)
  move=> Hin.
  have: exists b', b' \in (get_blocks (rev r)) /\ subblock b b'; last first.
    move => [b' [Hinb Hsub]]. exists b'. split => //. move: Hinb.
    rewrite /get_blocks => /mapP [ t Hint Htup]. rewrite Htup. apply map_f.
    by rewrite revK (perm_mem (get_blocks_lists_perm Hwf (perm_rev' r))).
  move: Hin.
  have: wf_packet_stream (rev r) by apply (wf_perm Hwf); apply perm_rev'.
  rewrite {Hwf}.
  forget (rev r) as r'. (*now more rev*) rewrite {r}. rename r' into r.
  move: b.
  elim : r => [//= b Hwf | h t /= IH b Hwf].
  move: IH. set blks := (foldr
  (fun (x0 : fpacket) (z : seq block * seq packet * Z * seq fpacket) =>
   ((update_dec_state_gen
       [seq x <- z.1.1.1 | not_timeout (upd_time z.1.2 x0 z.1.1.1) x] x0
       (upd_time z.1.2 x0 z.1.1.1)).1,
   z.1.1.2 ++
   (update_dec_state_gen
      [seq x <- z.1.1.1 | not_timeout (upd_time z.1.2 x0 z.1.1.1) x] x0
      (upd_time z.1.2 x0 z.1.1.1)).2, upd_time z.1.2 x0 z.1.1.1, 
   z.2 ++ [:: x0])) ([::], [::], 0, [::]) t).
  (*We don't care what blks is. It is long and ugly, so we generalize*)
  move: blks => blks IH Hinb.
  eapply (update_dec_state_gen_subblocks Hwf). 2: apply Hinb.
  move => b'. rewrite mem_filter => /andP[_ Hinb'].
  apply IH =>//. exact (wf_packet_stream_tl Hwf).
Qed.

(*The other general result we need: we need to relate the output
  to the blocks; ie: every packet in the decoder 
  current output is either the current packet or in the [decode_block]
  of a block in the decoder's state. It is not true of the whole 
  output, since we might have removed the block corresponding to a 
  previous packet.*)

(*TODO: did I prove something like this*)
Lemma sublist_nth: forall {A: Type} `{Inhabitant A} (l: list A) (i: Z),
  0 <= i < Zlength l ->
  l = sublist 0 i l ++ [Znth i l] ++ sublist (i+1) (Zlength l) l.
Proof.
  move => A Hinhab l i Hi. have Hl1: l = sublist 0 i l ++ sublist i (Zlength l) l. {
    rewrite cat_app -sublist_split; try lia. by rewrite sublist_same. }
  rewrite {1}Hl1. rewrite (sublist_next i (Zlength l)); try lia. by rewrite catA.
Qed.

Transparent create_block_with_packet_black.

(*TODO: move*)
Lemma create_black_recover: forall (curr : fpacket) (time: Z),
  fd_k curr = 1 ->
  0 <= fd_h curr ->
  0 <= Z.of_nat (fd_blockIndex curr) < fd_k curr + fd_h curr ->
  recoverable (create_block_with_fec_packet curr time).
Proof.
  move => curr time Hk Hh Hidx.
  rewrite /recoverable/= -Zlength_app -cat_app -filter_cat cat_app -sublist_split; zlist_simpl.
  rewrite sublist_same; zlist_simpl. rewrite Zlength_sublist; zlist_simpl. rewrite Z.sub_0_r Hk.
  solve_sumbool => /=; subst. rewrite Hk in Hidx. simpl in *.
  have: [seq x <- upd_Znth (Z.of_nat (fd_blockIndex curr)) (zseq (1 + fd_h curr) None) (Some curr)
         | isSome x] = nil. { (*why cant list_solve do this? Should be super easy*) 
    apply Zlength_nil_inv. have H:=(Zlength_nonneg 
      [seq x <- upd_Znth (Z.of_nat (fd_blockIndex curr)) (zseq (1 + fd_h curr) None) (Some curr) | isSome x]).
    (*WTF, why can't lia do this?*)
    have H10: forall z, 0 <= z -> z < 1 -> z = 0. lia. by apply H10.  }
  move => Hfilt.
  have Hhas: has isSome (upd_Znth (Z.of_nat (fd_blockIndex curr)) (zseq (1 + fd_h curr) None) (Some curr)). {
    apply /hasP. exists (Some curr) => //. rewrite in_mem_In In_Znth_iff; zlist_simpl.
    exists (Z.of_nat (fd_blockIndex curr)). split => //.
    by rewrite upd_Znth_same; zlist_simpl. }
  rewrite has_filter in Hhas. by rewrite Hfilt in Hhas.
Qed.

(*The intermediate lemma for [create_block_with_packet_black]*)
Lemma in_create_black: forall (curr : fpacket) (time: Z) p,
  0 <= Z.of_nat (fd_blockIndex curr) < fd_k curr + fd_h curr ->
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
(*The intermediate lemma for [add_packet_to_block_black]*)
Lemma in_add_to_black: forall curr b p,
  p \in (add_packet_to_block_black curr b).2 ->
  (p \in (decode_block (add_packet_to_block_black curr b).1) /\
    recoverable (add_packet_to_block_black curr b).1) \/ p_packet curr = p /\ fd_isParity curr = false.
Proof.
  move => curr b p. rewrite /add_packet_to_block_black.
  case Hcomp: (black_complete b) => //=.
  - case : (fd_isParity curr) =>//=; rewrite in_cons orbF => /eqP ->.
    by right.
  - have Hcase2: p
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
    + move => Hin. left. by apply Hcase2.
    + rewrite in_cons => /orP[/eqP Hp | Hin]; subst. by right. left. by apply Hcase2.
Qed.

Lemma in_update_dec_state_gen: forall blks (curr: fpacket) time p,
  0 <= Z.of_nat (fd_blockIndex curr) < fd_k curr + fd_h curr ->
  0 <= fd_h curr ->
  p \in (update_dec_state_gen blks curr time).2 ->
  (exists b: block, b \in (update_dec_state_gen blks curr time).1 /\
    recoverable b /\ p \in decode_block b) \/
  (p_packet curr = p /\ fd_isParity curr = false).
Proof.
  move => blks curr time p Hidx Hh. 
  move: time. elim : blks => [//= time | b blks /= IH time].
  - move => Hin. by apply in_create_black in Hin.
  - case: (fd_blockId curr == blk_id b) /eqP => Heq/=.
    + move=> Hin. apply in_add_to_black in Hin.
      case: Hin => [[Hin Hrec] | [Hp Hpar]].
      * left.
        exists ((add_packet_to_block_black curr b).1).
        repeat split =>//. by rewrite mem_head.
      * by right.
    + case Hlt : (fd_blockId curr < blk_id b)%N =>/= Hin.
      * apply in_create_black in Hin =>//.
        case: Hin => [[b' [Hin [Hrec Hdec]]] | [Hp Hpar]].
        -- left. exists b'; split_all =>//. 
          move: Hin; rewrite !in_cons orbF => /eqP->.
          by rewrite eq_refl.
        -- by right.
      * by apply IH.
Qed. 

Theorem in_decode_func_in_block: forall received (curr: fpacket) (p: packet),
  0 <= Z.of_nat (fd_blockIndex curr) < fd_k curr + fd_h curr ->
  0 <= fd_h curr ->
  p \in (decoder_func_gen received curr) ->
  (exists b, b \in (decoder_all_steps_gen (received ++ [:: curr])).1.1
    /\ recoverable b /\
    (p \in (decode_block b))) \/ 
    (p_packet curr = p /\ fd_isParity curr = false).
Proof.
  move => r curr p Hidx Hh. rewrite /decoder_func_gen 
    /decoder_all_steps_gen/decoder_multiple_steps_gen foldl_cat /= => Hin.
  by apply in_update_dec_state_gen in Hin.
Qed.


Lemma Zlength_rev: forall {A: Type} (s: seq A),
  Zlength (rev s) = Zlength s.
Proof.
  move => A s. by rewrite !Zlength_correct -!size_length size_rev.
Qed.

(*TODO: prove this later when needed*)
(*TODO: encoder version is in Abstract file - and it is the exact same proof - TODO: generalize to only need 1*)
Lemma decoder_all_steps_concat: forall received,
  (decoder_all_steps_gen received ).1.2 = concat (mkseqZ 
    (fun i => (decoder_func_gen (sublist 0 i received) (Znth i received)))
    (Zlength received)).
Proof.
  move => r. rewrite /decoder_func_gen /decoder_all_steps_gen
  /decoder_multiple_steps_gen.
  (*doesn't depend on specifics of one step function*)
  move: decoder_one_step_gen => one_step.
  remember (@nil packet) as base. rewrite -(cat0s (concat _)) -Heqbase.
  rewrite {Heqbase}.
  move: (@nil block).
  remember 0%Z as time. rewrite !Heqtime. rewrite -{ 1 2 4}Heqtime.
  rewrite {Heqtime}. move: time.
  remember (@nil fpacket) as base1. rewrite {1 3 5}Heqbase1.
  rewrite {Heqbase1}. move: base1.
  move: base.
  elim: r => [//=  b1 b2 time prev | h t /= IH b1 b2 time prev].
  - by rewrite cats0.
  - rewrite IH {IH} -catA. f_equal.
    have->: Zlength (h::t) = Zlength t + 1 by list_solve.
    rewrite mkseqZ_1_plus/=; [|list_solve]. 
    rewrite !Znth_0_cons -!cat_app.
    f_equal. f_equal.
    have Hpos: 0 <= Zlength t by list_solve. apply Znth_eq_ext; rewrite !mkseqZ_Zlength //. 
    move => i Hi. rewrite !mkseqZ_Znth// !Znth_pos_cons; try lia.
    rewrite !sublist_0_cons; try lia.
    by rewrite !Z.add_simpl_r.
Qed. 

End DecoderSubblocks.


(*TODO (later) - full theorems of correctness - wait until end*)


End GenDecode.
