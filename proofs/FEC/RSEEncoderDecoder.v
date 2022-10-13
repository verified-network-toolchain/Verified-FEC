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
Variable not_timeout : block -> bool.

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
  let t := update_dec_state_gen blocks curr time in
  let tm := upd_time time curr blocks in
  let blks := filter not_timeout t.1 in
  (blks, t.2, tm).

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
  exists (p': fpacket), (Some p') \in (data_packets b2) /\ remove_seqNum p = remove_seqNum (p_packet p').
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
Lemma create_block_subblock: forall (l: list fpacket) (h: fpacket) (time: Z),
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
Lemma add_to_block_subblock: forall (l: list fpacket) (h: fpacket)  (b1 b2: block),
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
Theorem decoder_all_steps_state_subblocks: forall (received: seq fpacket) (times: seq Z) (b: block),
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
      (fun (x0 : fpacket * Z) (z : seq block * seq packet) =>
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
Lemma create_black_recover: forall (curr : fpacket) (time: Z),
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

Lemma in_create_black: forall (curr : fpacket) (time: Z) p,
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

Lemma in_update_past_blocks: forall blks (curr: fpacket) time p,
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

Lemma in_update_dec_state: forall blks (curr: fpacket) time p,
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

Theorem in_decode_func_in_block: forall received (curr: fpacket) times time (p: packet),
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

Definition rse_encode_concat (orig: seq packet) (params: seq (Z * Z)) :=
  foldl
  (fun (acc : seq block * option block * seq (seq (fpacket))) (x : packet * (Z * Z)) =>
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

(*This lemma will actually be quite easy with previous result*)
(*From here, we can describe each element of [rse_encode_concat] purely in terms of [rse_encode_func])*)
Lemma rse_concat_mkseqZ: forall orig params,
  Zlength orig = Zlength params ->
  (rse_encode_concat orig params).2 = mkseqZ (fun i => rse_encode_func (sublist 0 i orig) (sublist 0 i params)
    (Znth i orig) (Znth i params).1 (Znth i params).2) (Zlength orig).
Proof.
  move => orig params Hlens. rewrite /rse_encode_concat /rse_encode_func /rse_encode_all.
  remember (@nil block) as b1. remember (@None block) as b2. remember (@nil fpacket) as b3.
  remember (@nil (seq fpacket)) as b4. rewrite {1}Heqb4. rewrite -(cat0s (mkseqZ _ _)). rewrite -{2}Heqb4.
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
