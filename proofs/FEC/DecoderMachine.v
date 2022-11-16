(*A decoder that does arithmetic on machine-length integers, not nats*)
(*TODO: also provide a version with some efficiency/speedups closer
  to C code (or maybe wait until VST see)*)
(*Here, we prove that under certain generous conditions of the
  input packet stream, this is equivalent to the idealized decoder.*)
Require Import VST.floyd.functional_base.
Require Import AbstractEncoderDecoder.
Require Import ZSeq.
Require Import Block.
Require Import DecoderTimeouts.
Require Import DecoderGeneric.
Require Import SeqCmp.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.

Module S64:=SeqCmp Wordsize_64.
Module S32:=SeqCmp Wordsize_32.

(*Coq module weirdness: it does not recognize
  S32.I.int and Int.int as equal, though they are.
  We can give a trivial conversion function*)
Definition sint (i: int) : S32.I.int :=
  S32.I.mkint (Int.intval i) (Int.intrange i).

(*Ugh, has to be better way - TODO: ask about this*)
Lemma s32_inj (i1 i2: S32.I.int):
  S32.I.unsigned i1 = S32.I.unsigned i2 ->
  i1 = i2.
Proof.
  move=> Heq. 
  by rewrite -(S32.I.repr_unsigned i1) -(S32.I.repr_unsigned i2) Heq.
Qed.

Lemma sint_repr (z: Z):
  sint (Int.repr z) = S32.I.repr z.
Proof.
  rewrite /sint/=.
  eapply eq_trans.
  2: apply s32_inj. 
  reflexivity. by [].
Qed.

Definition sint64 (i: int64) : S64.I.int :=
  S64.I.mkint (Int64.intval i) (Int64.intrange i).

Lemma s64_inj (i1 i2: S64.I.int):
  S64.I.unsigned i1 = S64.I.unsigned i2 ->
  i1 = i2.
Proof.
  move=> Heq. 
  by rewrite -(S64.I.repr_unsigned i1) -(S64.I.repr_unsigned i2) Heq.
Qed.

Lemma sint64_repr (z: Z):
  sint64 (Int64.repr z) = S64.I.repr z.
Proof.
  rewrite /sint64/=.
  eapply eq_trans.
  2: apply s64_inj.
  reflexivity. by [].
Qed.

Section Machine.

(*Hmm, let's think about this - can have time as Z because all
  operations are in terms of Int.repr time - but I think we
  want the _m versions with Znth because otherwise we need to
  prove in VST proof
  TODO: make sure*)


Definition create_block_with_fec_packet_m (p: fpacket) (time : Z) : 
  block :=
  let k := fd_k p in
  let h := fd_h p in
  let allPackets := upd_Znth 
    (Int.unsigned (Int.repr (Z.of_nat (fd_blockIndex p)))) 
    (zseq (k + h) None) (Some p) in
  mk_blk (fd_blockId p) (sublist 0 k allPackets) 
    (sublist k (k+h) allPackets) k h false time.

Lemma create_m_eq (p: fpacket) (time: Z) :
  (Z.of_nat (fd_blockIndex p) <= Int.max_unsigned) ->
  create_block_with_fec_packet_m p time =
  create_block_with_fec_packet p time.
Proof.
  move=> Hidx. 
  rewrite /create_block_with_fec_packet_m/create_block_with_fec_packet.
  by rewrite Int.unsigned_repr; try rep_lia.
Qed.

Definition create_block_with_packet_black_m (p: fpacket) (time: Z) : block * list packet :=
  let new_block := create_block_with_fec_packet_m p time in
  let packets  := (if (fd_isParity p) then nil else 
    [:: p_packet p ]) ++
    (if Int.eq (Int.repr (fd_k p)) Int.one then 
      (decode_block new_block) else nil) in
  let marked_block := if Int.eq (Int.repr (fd_k p)) Int.one then 
    new_block <| black_complete := true |> else new_block in
  (marked_block, packets).

Lemma create_black_m_eq (p: fpacket) (time: Z) : 
  (Z.of_nat (fd_blockIndex p) <= Int.max_unsigned) ->
  (0 <= fd_k p <= Int.max_unsigned) ->
  create_block_with_packet_black_m p time =
  create_block_with_packet_black p time.
Proof.
  move=> Hidx Hk.
  rewrite /create_block_with_packet_black_m
    /create_block_with_packet_black.
  rewrite /Int.eq Int.unsigned_repr=>[|//].
  rewrite Int.unsigned_one /zeq.
  by case: Z.eq_dec=> [Heq/=| Hneq/=];
  rewrite create_m_eq.
Qed.

(*2. add packet to block*)
Definition add_fec_packet_to_block_m (p: fpacket) (b: block) : block :=
  let new_packets := upd_Znth 
    (Int.unsigned (Int.repr (Z.of_nat (fd_blockIndex p)) ))
    (data_packets b ++ parity_packets b) (Some p) in
  b <| data_packets := sublist 0 (blk_k b) new_packets |> 
      <| parity_packets := sublist (blk_k b) (blk_k b + blk_h b) new_packets |>.

Lemma add_m_eq (p: fpacket) (b: block) :
  (Z.of_nat (fd_blockIndex p) <= Int.max_unsigned) ->
  add_fec_packet_to_block_m p b =
  add_fec_packet_to_block p b.
Proof.
  move=> Hidx. rewrite /add_fec_packet_to_block_m/add_fec_packet_to_block.
  by rewrite !Int.unsigned_repr //; rep_lia.
Qed.

Definition add_packet_to_block_black_m (p: fpacket) (b: block) : block * list packet :=
  (*NOTE: we still must add the packet even if the block is complete
    to keep the time correctly updated. But we don't need to output anything*)
  let new_block := add_fec_packet_to_block_m p b in
  if black_complete b then (new_block, if (fd_isParity p) then nil else 
    [:: p_packet p]) else 
    (*NOTE: theirs does not release data packet here - we can do either, the
      block has been recovered so this would just be a duplicate. But
      not returning anything does violate their stated spec*)
    let packets := (if (fd_isParity p) then nil else [:: p_packet p]) ++
      (if recoverable new_block then (decode_block new_block) else nil) in
    let marked_block := if recoverable new_block then 
      new_block <| black_complete := true |> else new_block in
    (marked_block, packets).

Lemma add_black_m_eq (p: fpacket) (b: block) :
  (Z.of_nat (fd_blockIndex p) <= Int.max_unsigned) ->
  add_packet_to_block_black_m p b =
  add_packet_to_block_black p b.
Proof.
  move=> Hidx.
  rewrite /add_packet_to_block_black_m/add_packet_to_block_black.
  by rewrite !add_m_eq.
Qed.

Variable threshold : int.

(*Once again, will have more efficient version like C code, 
  for now just prove equivalence*)
(*TODO: is it nontrivial to prove equivalence? Probably not
  because we can easily prove everything is within required bounds*)
(*TODO: use from before?*)
(*Definition block_notin_packet block packet : bool :=
    ~~ (packet_in_block packet block).*)

(*NOTE: We are changing the code to use 64 bit integers and thus
  Int64 comparison operations. Then, we can assume that all
  packets have unique sequence numbers (at current network speeds,
  it would take around 600,000 years before we run into problems).
  Otherwise, we need to deal with wraparound, which is highly 
  nontrivial, because we would need to reason both about
  reorder/duplication as well as loss, in a different way from 
  the stronger conditions for ensuring packet recovery.
  TOOD: write this somewhere
  *)
(*I think: shouldn't need this or any: still store Z, just
  do comparisons on Int.repr time*)
(*The check to update the time*)
Fixpoint upd_time_m (time: Z) (curr: fpacket) (blocks: list block) :
  Z := 
  match blocks with
  | nil => time + 1 (*Int.add (Int.repr time) Int.one*)
  | bl :: tl =>
    let currSeq := Int64.repr (Z.of_nat (fd_blockId curr)) in
    let blkid := Int64.repr (Z.of_nat (blk_id bl)) in
    if S64.seq_eq (sint64 currSeq) (sint64 blkid) then
      if (block_notin_packet bl curr) 
      then time + 1 (*Int.add (Int.repr time) Int.one*)
      else time
    else if S64.seq_lt (sint64 currSeq) (sint64 blkid) 
      then time + 1 (*Int.add time Int.one*)
    else upd_time_m time curr tl
  end.

(*TODO: may need to add to SeqCmp.v - SEE*)
(*
Definition seq_leq (i1 i2: int) : bool :=
  Int.eq i1 i2 || S32.seq_lt (sint i1) (sint i2).*)

(*Timeouts if threshold exceeded*)
(*Hmm, what happens if time wraps around? - maybe for this 
we should do sequence number comparison because times will 
always be within threshold?*)
Definition not_timed_out_m: Z -> block -> bool := fun currTime =>
  (fun b => S32.seq_leq (sint (Int.repr currTime)) 
    (sint (Int.add (Int.repr(black_time b)) threshold))).

Fixpoint update_dec_state_m (blocks: list block) (curr: fpacket)
  (time: Z) : list block * list packet:=
match blocks with
| nil => let t := create_block_with_packet_black curr time in 
    ([:: t.1], t.2)
| bl :: tl =>
  let currSeq := Int64.repr (Z.of_nat (fd_blockId curr)) in
  let blkid := Int64.repr (Z.of_nat (blk_id bl)) in
  if S64.seq_eq (sint64 currSeq) (sint64 blkid) then
    let t := add_packet_to_block_black_m curr bl in
    (t.1 :: tl, t.2)
    else if S64.seq_lt (sint64 currSeq) (sint64 blkid) then
    let t := create_block_with_packet_black curr time in 
      (t.1 :: blocks, t.2)
  else 
    let t := update_dec_state_m tl curr time
    in (bl :: t.1, t.2)
end.

Definition decoder_one_step_m (blocks: list block) curr (time : Z) :
list block * list packet * Z :=
(*First, we process timeouts; this covers the case when the packet
  which makes the block timeout is the kth packet; we should not
  recover this block (it makes our invariants much harder).*)
let tm := upd_time_m time curr blocks in
let blks := filter (not_timed_out_m tm) blocks in
let t := update_dec_state_m blks curr tm in
(t, tm).

Definition decoder_multiple_steps_m
(prev_packs packs: list fpacket)
(state: list block) (sent: list packet) (time: Z) :
list block * list packet * Z * list fpacket :=
foldl (fun (acc: list block * list packet * Z * list fpacket) 
  (p: fpacket) =>
  let t := decoder_one_step_m acc.1.1.1 p acc.1.2 in
  (t.1.1, acc.1.1.2 ++ t.1.2, t.2, acc.2 ++ [:: p])) 
(state, sent, time, prev_packs) packs.

Definition decoder_all_steps_m (received: list fpacket) :
(list block * list packet * Z) :=
(decoder_multiple_steps_m nil received nil nil 0).1.

(*Now we have to prove equivalence. This means we have to show that
  every comparison between unsigned ints occurs between those
  representing a nat within 2^31 of each other, and likewise for
  longs.*)

(*To do this, we use an assumption that all packet sequence
  numbers are between 0 and 2^63-1, and they are unique. This is
  not at all a restrictive assumption - if we could send
  10^9 packets per second (already at least 2-3 orders of
  magnitude above current speeds), it would take us nearly
  300 years to run out of sequence numbers. This also assumes
  we send no parity packets and have no other traffic on the
  network.*)
Section Equiv.

Local Open Scope nat_scope.

(*TODO: formulate bound for orig packets, prove that stream
  respects this property in encoder*)
(*Definition seqnum_range_bound (s: seq packet) : bool :=
  all (fun p => (p_seqNum p) < Z.to_nat (Int64.half_modulus)) s. *)
Definition fpacket_seqnum_range (s: seq fpacket) : bool :=
  all (fun (p: fpacket) => (p_seqNum p) < Z.to_nat Int64.half_modulus) s.

(*We also assume that the threshold is less than 2^31-1. This is also
  safe: if each block was 100 bytes (it can be much larger depending on
  packet sizes), a larger threshold would require storing at least
  200 GB *)

(*Our invariant:*)
Definition dec_machine_invar (blks: seq block)
  (time: Z) : Prop :=
  (*All black times are no more than [threshold] behind the
    current time*)
  (forall (b: block), b \in blks ->
    (0 <= time - (black_time b) <= Int.unsigned threshold)%Z) /\
    (*(Z.abs (black_time b - time) <= Int.unsigned threshold)%Z) /\*)
  (*All block ids are smaller than 2^61-1*)
  (forall (b: block), b \in blks -> 
    Z.of_nat (blk_id b) < Int64.half_modulus)%Z.

(*First, show this invariant implies equality*)

Local Definition convert_tuple {A B: Type} (x: (A * B * Z)) :
  A * B * int :=
  match x with
  | (a, b, z) => (a, b, Int.repr z)
  end.

(*Helpful here*)
Lemma znat_eq (n1 n2 : nat) :
  Z.eqb (Z.of_nat n1) (Z.of_nat n2) = (n1 == n2).
Proof.
  case: (Z.of_nat n1 =? Z.of_nat n2)%Z /Z.eqb_spec => [Heq | Hneq];
  symmetry; apply /eqP; lia.
Qed. 

Lemma znat_lt (n1 n2: nat):
  Z.ltb (Z.of_nat n1) (Z.of_nat n2) = (n1 < n2).
Proof.
  case: ((Z.of_nat n1 <? Z.of_nat n2)%Z) /Z.ltb_spec => [Hlt | Hge];
  symmetry; apply /ltP; lia.
Qed.

(*TODO: dont need anymore, but we will need in VST proofs*)
Lemma int_add_one (z: Z):
  Int.add (Int.repr z) Int.one = Int.repr (z + 1).
Proof.
  apply Endian.int_unsigned_inj. (*TODO: move*)
  by rewrite /Int.add/Int.one !Int.unsigned_repr_eq -Zplus_mod.
Qed.

(*TODO: move*)
Lemma upd_time_bound (time: Z) (curr: fpacket) (blks: seq block) :
  (time <= upd_time time curr blks <= time + 1)%Z.
Proof.
  elim: blks => [/= | b btl IH /=]; try lia.
  case: (fd_blockId curr == blk_id b).
  - by case: (block_notin_packet b curr); lia.
  - by case: (fd_blockId curr < blk_id b)%N; lia.
Qed.

Variable thresh_bound: 
  (Int.unsigned threshold < Int.half_modulus / 2)%Z.

Lemma decoder_one_step_m_eq (blks: seq block) (time: Z) 
  (curr: fpacket) :
  (Z.of_nat (fd_blockId curr) < Int64.half_modulus)%Z ->
  (Z.of_nat (fd_blockIndex curr) <= Int.max_unsigned)%Z ->
  (0 <= fd_k curr < Int.modulus)%Z ->
  dec_machine_invar blks time ->
  decoder_one_step_m blks curr time =
  decoder_one_step (Int.unsigned threshold) blks curr time.
Proof.
  move=> Hcurr Hidx Hkbound [Hthresh Hallid].
  rewrite /decoder_one_step_m/decoder_one_step/decoder_one_step_gen/=.
  have Htime: upd_time_m time curr blks = 
    upd_time time curr blks. {
    rewrite {Hthresh}. move: Hallid. elim: blks => [_ //=|b btl IH Hallid /=].
      have Hbound: (z_abs_diff 
      (Z.of_nat (fd_blockId curr)) (Z.of_nat (blk_id b)) <
        S64.I.half_modulus)%Z. {
        (*Easy: both are smaller than half_modulus*)
        rewrite /z_abs_diff.
        move: Hallid => /(_ _ (mem_head _ _)).
        have->:S64.I.half_modulus = Int64.half_modulus by [].
        rep_lia.
      }
      rewrite !sint64_repr S64.seq_eq_eq. 
      + rewrite znat_eq.
        case: (fd_blockId curr == blk_id b) /eqP => Hbcurr.
        * by case: (block_notin_packet b curr).
        * rewrite S64.seq_lt_lt // znat_lt.
          case: (fd_blockId curr < blk_id b) =>//. 
          apply IH => b' Hinb'. apply Hallid. 
          by rewrite in_cons Hinb' orbT.
      + have: (S64.I.half_modulus < S64.I.modulus)%Z by []. lia.
  }
  f_equal=>//.
  rewrite Htime.
  have->: [seq x <- blks | 
    not_timed_out_m (upd_time time curr blks) x] =
    [seq x <- blks | 
    not_timed_out (Int.unsigned threshold) (upd_time time curr blks) x]. 
    {
    apply eq_in_filter => b Hinb.
    rewrite /not_timed_out_m/not_timed_out.
    rewrite -S32.seq_leq_leq.
    - rewrite sint_repr. f_equal.
      rewrite /Int.add sint_repr.
      apply s32_inj; 
      rewrite !S32.I.unsigned_repr_eq !Int.unsigned_repr_eq.
      by rewrite Zplus_mod_idemp_l.
    - (*Here, use fact that upd_time increases by at most 1
        and that before, all were within threshold. So here,
        should be ok*)
        have:=(upd_time_bound time curr blks).
        rewrite /z_abs_diff.
        move: Hthresh => /(_ b Hinb).
        have->: S32.I.half_modulus = Int.half_modulus by [].
        move: thresh_bound=>/=. rep_lia.
    }
    move: (upd_time time curr blks) => tm.
    have: forall b, b \in 
    [seq x <- blks | not_timed_out (Int.unsigned threshold) tm x] ->
    (Z.of_nat (blk_id b) < Int64.half_modulus)%Z. {
      move=> b'. rewrite mem_filter => /andP[_ Hinb]. by apply Hallid.
    }
    rewrite {Htime Hthresh Hallid}.
    move: ([seq x <- blks | not_timed_out (Int.unsigned threshold) tm x] ) => bs.
    (*Now show equality - similar to time proof above*)
    elim: bs => [ _ // | b btl IH Hallid //=].
    have Hbound: (z_abs_diff 
      (Z.of_nat (fd_blockId curr)) (Z.of_nat (blk_id b)) <
        S64.I.half_modulus)%Z. {
        (*Easy: both are smaller than half_modulus*)
        rewrite /z_abs_diff.
        move: Hallid => /(_ _ (mem_head _ _)).
        have->:S64.I.half_modulus = Int64.half_modulus by [].
        rep_lia.
      }
    rewrite !sint64_repr S64.seq_eq_eq.
    - rewrite znat_eq.
      case: (fd_blockId curr == blk_id b) /eqP => [Heq|Hneq].
      + by rewrite add_black_m_eq.
      + rewrite S64.seq_lt_lt // znat_lt.
        case: (fd_blockId curr < blk_id b) =>//.
        rewrite IH // => b' Hinb'. 
        apply Hallid. 
        by rewrite in_cons Hinb' orbT.
    - have: (S64.I.half_modulus < S64.I.modulus)%Z by []. lia.
Qed.

(*TODO; move*)
Lemma add_black_m_id (curr: fpacket) (b: block) :
  blk_id (add_packet_to_block_black_m curr b).1 =
  blk_id b.
Proof.
  rewrite /add_packet_to_block_black_m.
  case: (black_complete b)=>//=.
  by case: (recoverable (add_fec_packet_to_block_m curr b)).
Qed.


(*Now, we have to prove preservation of the invariant.
  We use the equality lemma to help (TODO: maybe)*)
(*Here, we prove for the non-machine version, then use
  the previous lemma to show the invariant for the machine one*)
Lemma decoder_m_invar_one_step (blks: seq block) (time: Z) 
  (curr: fpacket) :
  (Z.of_nat (fd_blockId curr) < Int64.half_modulus)%Z ->
  dec_machine_invar blks time ->
  dec_machine_invar (decoder_one_step (Int.unsigned threshold) 
    blks curr time).1.1
    (decoder_one_step (Int.unsigned threshold) blks curr time).2.
Proof.
  rewrite /dec_machine_invar => Hid [Hthresh Hallid].
  (*First try to do without lemma (so we dont need more
    assumptions), otherwise, do with lemma - may be easier*)
  rewrite /decoder_one_step/=.
  split.
  - move=> b.

    have: forall b, b \in [seq x <- blks
    | not_timed_out (Int.unsigned threshold)
        (upd_time time curr blks) x] ->
    ((upd_time time curr blks) <= 
      black_time b + Int.unsigned threshold)%Z /\
      (0 <= time - black_time b)%Z. {
      move=> b'. rewrite mem_filter => /andP. 
      rewrite /not_timed_out => [[]] /Z.leb_spec0 Hle Hinb'.
      move: Hthresh => /(_ _ Hinb').
      lia.
    }
    have:=(upd_time_bound time curr blks).
    move: (upd_time time curr blks) => tm.
    move: [seq x0 <- blks | not_timed_out (Int.unsigned threshold) tm x0] => bs.
    rewrite {Hthresh Hallid blks}.
    elim: bs => [// Htm Hallid /=|bhd btl IH Htm Hallid /=].
    + rewrite in_cons orbF => /eqP ->.
      case: Z.eq_dec=>//=; rep_lia.
    + have Hhd: (0 <= tm - black_time bhd <= Int.unsigned threshold)%Z by
      move: Hallid => /( _ _ (mem_head _ _)); rep_lia.
      have Htl: forall b, b \in btl ->
      (0 <= tm - black_time b <= Int.unsigned threshold)%Z. {
        move=> b' Hinb.
        move: Hallid => /(_ b'). rewrite in_cons Hinb orbT => /(_ isT).
        rep_lia.
      }
    case: (fd_blockId curr == blk_id bhd).
      * rewrite in_cons => /orP[/eqP -> | Hinb].
        -- by rewrite add_black_time.
        -- by apply Htl.
      * case: (fd_blockId curr < blk_id bhd)=>/=.
        -- case: Z.eq_dec=>/= Hk1;
          rewrite !in_cons => /orP[/eqP -> /= | /orP[/eqP -> | Hinb]];
            try rep_lia; by apply Htl.
        -- rewrite in_cons => /orP[/eqP -> // | Hinb].
          apply IH =>//. move=> b' Hinb'. apply Hallid.
          by rewrite in_cons Hinb' orbT.
  - (*This invariant is a bit easier*)
     have: forall b, b \in 
     [seq x <- blks
     | not_timed_out (Int.unsigned threshold)
         (upd_time time curr blks) x] ->
    (Z.of_nat (blk_id b) < Int64.half_modulus)%Z. {
      move=> b'. rewrite mem_filter=> /andP[_ Hinb'].
      by apply Hallid.
    }
    rewrite {Hthresh Hallid}.
    move: (upd_time time curr blks) => tm.
    move: [seq x <- blks | not_timed_out (Int.unsigned threshold) tm x] => bs.
    elim: bs => [Hallid b/=|b bs IH Hallid /=].
    + rewrite in_cons orbF => /eqP ->. by case: Z.eq_dec => Hk1//=.
    + move=> b'.
      case: (fd_blockId curr == blk_id b).
      * rewrite in_cons => /orP[/eqP -> | Hinb']; last by
        apply Hallid; rewrite in_cons Hinb' orbT.
        rewrite add_black_id. apply Hallid. by rewrite mem_head.
      * case: (fd_blockId curr < blk_id b).
        -- rewrite in_cons => /orP[/eqP -> | Hinb']; last by apply Hallid.
          by case: Z.eq_dec.
        -- rewrite in_cons => /orP[/eqP -> | Hin]; first by apply Hallid;
          rewrite mem_head. apply IH=>//.
          move=> b'' Hinb''. apply Hallid. by rewrite in_cons Hinb'' orbT.
Qed.
        
(*TODO: connect lemmas to show full preservation of
  invariant + prove full equality*)