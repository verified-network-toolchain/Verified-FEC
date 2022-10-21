Require Import AbstractEncoderDecoder.
Require Import DecoderGeneric.
Require Import VST.floyd.functional_base.
Require Import ByteFacts.
Require Import Block.


From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.

Definition triv_upd_time : Z -> fpacket -> list block -> Z :=
  fun z _ _ => 0.

Definition triv_timeout : Z -> block -> bool :=
  fun _ _ => true.

Definition decoder_one_step_nto :=
  decoder_one_step_gen triv_upd_time triv_timeout.

Definition decoder_multiple_steps_nto:=
  decoder_multiple_steps_gen triv_upd_time triv_timeout.
Definition decoder_all_steps_nto:=
  decoder_all_steps_gen triv_upd_time triv_timeout.

(*First we prove that with this decoder, it doesn't matter what
  time updating mechanism you use as long as you never timeout.
  Neither the intermediate functions nor the state are affected
  beyond just having different time information.*)
Section TimeDoesntMatter.

(*This is not quite as trivial as it may appear, since we need to prove
  that all the intermediate steps (creating/adding to blocks, decoding,
  etc) are all not affected by time.*)

(*An obvious lemma but one that doesn't just compute automatically*)
Lemma black_time_eq: forall b1 b2,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  blk_id b1 = blk_id b2 /\
  data_packets b1 = data_packets b2 /\
  parity_packets b1 = parity_packets b2 /\
  blk_k b1 = blk_k b2 /\
  blk_h b1 = blk_h b2 /\
  black_complete b1 = black_complete b2.
Proof.
  by move=> [id1 dat1 par1 k1 h1 comp1 t1] [id2 dat2 par2 k2 h2 comp2 t2] []/=.
Qed.

Lemma block_eq: forall b1 b2,
  blk_id b1 = blk_id b2 ->
  data_packets b1 = data_packets b2 ->
  parity_packets b1 = parity_packets b2 ->
  blk_k b1 = blk_k b2 ->
  blk_h b1 = blk_h b2 ->
  black_complete b1 = black_complete b2 ->
  black_time b1 = black_time b2 ->
  b1 = b2.
Proof.
  by move=> [id1 dat1 par1 k1 h1 comp1 t1] 
  [id2 dat2 par2 k2 h2 comp2 t2]/=->->->->->->->.
Qed.

Lemma create_black_time_eq: forall p t1 t2,
  (create_block_with_packet_black p t1).1 <| black_time := 0 |> =
  (create_block_with_packet_black p t2).1 <| black_time := 0 |>.
Proof.
  move=> p t1 t2/=. by case: (Z.eq_dec (fd_k p) 1).
Qed.

Lemma add_fec_packet_time_eq: forall b1 b2 p,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  (add_fec_packet_to_block p b1) <| black_time := 0 |> =
  (add_fec_packet_to_block p b2) <| black_time := 0 |>.
Proof.
  move=> b1 b2 p Heq.
  have [Hid [Hdat [Hpar [Hk [Hh Hcomp]]]]] := (black_time_eq Heq).
  rewrite /add_fec_packet_to_block Hk Hh Hdat Hpar.
  by apply block_eq.
Qed.

Lemma recoverable_time_eq: forall b1 b2,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  recoverable b1 = recoverable b2.
Proof.
  move=> b1 b2 Heq.
  have [Hid [Hdat [Hpar [Hk [Hh Hcomp]]]]] := (black_time_eq Heq).
  rewrite /recoverable.
  by rewrite Hdat Hpar.
Qed.

Lemma add_black_time_eq: forall b1 b2 p,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  (add_packet_to_block_black p b1).1 <| black_time := 0 |> =
  (add_packet_to_block_black p b2).1 <| black_time := 0 |>.
Proof.
  move=> b1 b2 p Heq.
  have [Hid [Hdat [Hpar [Hk [Hh Hcomp]]]]] := (black_time_eq Heq).
  rewrite /add_packet_to_block_black.
  rewrite Hcomp. case: (black_complete b2)=>/=.
  - by apply add_fec_packet_time_eq.
  - rewrite (@recoverable_time_eq _ (add_fec_packet_to_block p b2));
    last by apply add_fec_packet_time_eq.
    case: (recoverable (add_fec_packet_to_block p b2)).
    + by apply block_eq=>//=; rewrite Hk Hdat Hpar // Hh.
    + by apply add_fec_packet_time_eq.
Qed.

(*[decoder_list_block] is not affected by times*)
Lemma decoder_list_block_time_eq:  forall b1 b2,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  decoder_list_block b1 = decoder_list_block b2.
Proof.
  move=> b1 b2 Heq.
  have [Hid [Hdat [Hpar [Hk [Hh Hcomp]]]]] := (black_time_eq Heq).
  rewrite /decoder_list_block. f_equal=>//=.
  - by rewrite /blk_c Hpar Hdat.
  - by rewrite /packet_mx Hdat.
  - by rewrite /parity_mx Hpar.
  - by rewrite /stats Hdat.
  - by rewrite /lengths/blk_c Hpar Hdat .
  - by rewrite /find_decoder_list_param Hpar Hdat.
Qed.

(*[decode_block] is not affected by times*)
Lemma decode_block_time_eq: forall b1 b2,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  decode_block b1 = decode_block b2.
Proof.
  move=> b1 b2 Heq.
  have [Hid [Hdat [Hpar [Hk [Hh Hcomp]]]]] := (black_time_eq Heq).
  by rewrite /decode_block Hdat (decoder_list_block_time_eq Heq) Hk.
Qed. 

Lemma add_black_time_eq_packets:  forall b1 b2 p,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  (add_packet_to_block_black p b1).2 =
  (add_packet_to_block_black p b2).2.
Proof.
  move=> b1 b2 p Heq.
  have [Hid [Hdat [Hpar [Hk [Hh Hcomp]]]]] := (black_time_eq Heq).
  rewrite /add_packet_to_block_black.
  rewrite Hcomp. case: (black_complete b2)=>//=. f_equal.
  rewrite (@recoverable_time_eq _ (add_fec_packet_to_block p b2));
    last by apply add_fec_packet_time_eq.
  case: (recoverable (add_fec_packet_to_block p b2))=>//.
  apply decode_block_time_eq.
  by apply add_fec_packet_time_eq.
Qed.

(*Any timing mechanism will result in the same output if we never
  timeout packets*)

Lemma decoder_notimeout_upd_time:
  forall u1 u2 blks1 blks2 prev packs time1 time2 sent,
  map (fun b => b <| black_time := 0 |>) blks1 =
  map (fun b => b <| black_time := 0|> ) blks2 ->
  (decoder_multiple_steps_gen u1 triv_timeout prev 
    packs blks1 sent time1).1.1.2 =
  (decoder_multiple_steps_gen u2 triv_timeout prev 
    packs blks2 sent time2).1.1.2.
Proof.
  move=> u1 u2 blks1 blks2 prev packs. move: blks1 blks2 prev.
  rewrite /decoder_multiple_steps_gen.
  elim: packs => [//= | p ptl /= 
    IH blks1 blks2 prev time1 time2 sent Heqblks].
  (*All of the interesting stuff is in this proof, we separate it
    to reduce duplication*)
  have [Hupd1 Hupd2]: 
  (update_dec_state_gen blks1 p (u1 time1 p blks1)).2 =
  (update_dec_state_gen blks2 p (u2 time2 p blks2)).2 /\
  [seq b <| black_time := 0 |>
    | b <- (update_dec_state_gen blks1 p (u1 time1 p blks1)).1] =
  [seq b <| black_time := 0 |>
    | b <- (update_dec_state_gen blks2 p (u2 time2 p blks2)).1]. {
    rewrite {IH}.
    move: (u1 time1 p blks1) => t1.
    move: (u2 time2 p blks2) => t2.
    clear -Heqblks.
    move: blks2 t1 t2 Heqblks. elim: blks1 => 
      [// [//= | bhd2 btl2 //] t1 t2 _ | bhd1 btl1 /= IH].
    - split; f_equal. 
      apply create_black_time_eq. 
    - move=> [// | bhd2 btl2 /= t1 t2  Heq].
      apply cons_inv in Heq. case: Heq => [Hhd Htl].
      have Hideq: blk_id bhd1 = blk_id bhd2 by apply black_time_eq.
      rewrite -!Hideq.
      case: (fd_blockId p == blk_id bhd1) /eqP => Heq/=.
      + rewrite /=. f_equal=>//. split. by apply add_black_time_eq_packets.
        f_equal=>//. by apply add_black_time_eq.
      + case Hlt: (fd_blockId p < blk_id bhd1)%N.
        * rewrite /=. split=>//. f_equal=>//. apply create_black_time_eq.
          by f_equal.
        * rewrite /=. split. by apply IH. f_equal=>//. by apply IH.
  }
  (*The rest of the proof is basically trivial*)
  rewrite (IH _ ((update_dec_state_gen
  [seq x <- blks2 | triv_timeout (u2 time2 p blks2) x] p
  (u2 time2 p blks2)).1) _ _ (u2 time2 p blks2) _ ) // {IH}
  /triv_timeout/= !filter_predT/=.
  - by rewrite Hupd1.
  - by rewrite Hupd2.
Qed.

(*Lift this result to all packets*)
Lemma decoder_notimeout_upd_time_all:
  forall u1 u2 packs,
  (decoder_all_steps_gen u1 triv_timeout packs).1.2 =
  (decoder_all_steps_gen u2 triv_timeout packs).1.2.
Proof.
  move=> u1 u2 packs. rewrite /decoder_all_steps_gen.
  by apply decoder_notimeout_upd_time.
Qed.

End TimeDoesntMatter.