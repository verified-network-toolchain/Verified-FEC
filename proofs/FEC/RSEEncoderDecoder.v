(*Implement the abstract encoder/decoder relations from AbstractEncoderDecoder with RSE algorithm *)
Require Import VST.floyd.functional_base.
Require Import EquivClasses.
Require Import IP.
Require Import AbstractEncoderDecoder.
Require Import CommonSSR.
Require Import ReedSolomonList.
Require Import ZSeq.
Require Import Endian.
Require Import ByteFacts.
Require Import ByteField. (*For byte equality - TODO: move to ByteFacts*)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.

(*TODO: move*)
(*Construct Inhabitant instance automatically*)
Ltac solve_inhab :=
  repeat match goal with
  | |- Z => apply 0%Z
  | |- int => apply Int.zero
  | |- byte => apply Byte.zero
  | |- ?A list => apply nil
  | |- seq ?A => apply nil
  | |- ?A option => apply None
  | |- bool => apply false
  end.

(*TODO: move
  Decide equality for types and records made of primitives and machine sized ints*)
Ltac eq_dec_tac :=
  decide equality;
  repeat match goal with
  | [a : int, b : int |- {?a = ?b} + {?a <> ?b} ] => apply Int.eq_dec
  | [a : byte, b : byte |- {?a = ?b} + {?a <> ?b} ] => apply Byte.eq_dec
  | [a : list ?t, b : list ?t |- {?a = ?b} + {?a <> ?b} ] => apply list_eq_dec
  | [ |- forall x y : ?t, {x = y} + {x <> y}] => intros x y
  end.

(** IP/UDP Packets *)
(*Here, we require our packets to be valid IP/UDP packets*)

Definition valid_fec_packet (header: list byte) (contents: list byte) :=
  valid_packet header contents.

Definition packet_valid (p:packet) := valid_fec_packet (p_header p) (p_contents p).

Definition encodable (p: packet) : bool :=
  Z_le_lt_dec (Zlength ((p_header p) ++ (p_contents p))) fec_max_cols.

(*(k, isParity, block id, blockIndex*)
Record fec_data : Type := mk_data { fd_k : Z; fd_h : Z; fd_isParity : bool; fd_blockId: int; fd_blockIndex : int }.

Lemma fec_data_eq_dec: forall (f1 f2: fec_data), {f1 = f2} + {f1 <> f2}.
Proof.
  repeat eq_dec_tac.
Qed.

#[export]Instance fec_data_inhab: Inhabitant fec_data.
Proof.
constructor; solve_inhab.
Defined.

Definition fec_packet_act := fec_packet fec_data.

Definition f_packet : fec_packet_act -> packet := (@p_packet fec_data).

Coercion f_packet : fec_packet_act >-> packet.

Definition fec_packet_act_eq_axiom  := (@fec_packet_eqP _ fec_data_eq_dec).

Definition fec_packet_act_eqMixin := EqMixin fec_packet_act_eq_axiom.
Canonical fec_packet_act_eqType := EqType fec_packet_act fec_packet_act_eqMixin.
(*TODO: this if needed*)

#[export]Instance fec_packet_act_inhab : Inhabitant fec_packet_act := 
  mk_fecpkt packet_inhab fec_data_inhab.

Definition p_fec_data' : fec_packet_act -> fec_data := @p_fec_data fec_data.
Coercion p_fec_data' : fec_packet_act >-> fec_data.

(** Representing Blocks *)

Record block := mk_blk { blk_id: int;
  data_packets: list (option fec_packet_act); parity_packets: list (option fec_packet_act); blk_k : Z; blk_h : Z;
  complete: bool}.

#[export]Instance eta_block: Settable _ := 
  settable! mk_blk <blk_id; data_packets; parity_packets; blk_k; blk_h; complete>.

(*Need an eqType*)
Lemma reflect_proj_sumbool: forall (P: Prop) (H: {P} + {~P}),
  reflect P H.
Proof.
  move => P H. case : H => [Hy | Hn].
  by apply ReflectT. by apply ReflectF.
Qed.

(*First, show int has an eqType*)
Definition int_eqMixin := EqMixin (fun i1 i2 => reflect_proj_sumbool (Int.eq_dec i1 i2)).
Canonical int_eqType := EqType int int_eqMixin.
(*Then Z*)
Definition Z_eqMixin := EqMixin (fun z1 z2 => reflect_proj_sumbool (Z.eq_dec z1 z2)).
Canonical Z_eqType := EqType Z Z_eqMixin.

Definition block_to_tuple (b: block) : (int * seq (option fec_packet_act) * seq (option fec_packet_act) * 
  Z * Z * bool) :=
  (blk_id b, data_packets b, parity_packets b, blk_k b, blk_h b, complete b).

Definition tuple_to_block (t: (int * seq (option fec_packet_act) * seq (option fec_packet_act) * Z * Z * bool)) :
  block :=
  mk_blk (t.1.1.1.1.1) (t.1.1.1.1.2) (t.1.1.1.2) (t.1.1.2) (t.1.2) (t.2).

Lemma block_tuple_cancel: cancel block_to_tuple tuple_to_block.
Proof.
  move => b. by case: b. 
Qed.

Lemma tuple_block_cancel: cancel tuple_to_block block_to_tuple.
Proof.
  move => t. by repeat match goal with | x : ?A * ?B |- _ => destruct x end.
Qed.

Definition block_eqMixin := CanEqMixin block_tuple_cancel.
Canonical block_eqType := EqType block block_eqMixin.

(*Well-formed block *)
Definition block_wf (b: block) : Prop :=
  (*k and h are within the required bounds*)
  0 < blk_k b <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
  0 < blk_h b <= ByteFacts.fec_max_h /\
  (*All packets store correct values of k and h*)
  (forall p, In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) -> 
    (fd_k p) = blk_k b /\ (fd_h p) = blk_h b) /\
  (*All packets have same blockId (TODO: is this needed?*)
  (forall p, In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) ->
    fd_blockId (p_fec_data p) = blk_id b) /\
  (*Packet sequence numbers are correct*)
  (forall p (i: Z), 
    In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) ->
    Znth i (data_packets b ++ parity_packets b) = Some p <-> i = Int.unsigned (fd_blockIndex p)) /\
  (*Lengths are correct*)
  Zlength (data_packets b) = blk_k b /\
  Zlength (parity_packets b) = blk_h b /\
  (*All data packets are encodable*)
  (forall p, In (Some p) (data_packets b) -> encodable p) /\
  (*All packets are valid packets*)
  (forall p, In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) -> packet_valid p).

Definition range_lt_le_dec: forall (x y z: Z),
  { x < y <= z} + {~(x < y <= z)}.
Proof.
  intros. destruct (Z_lt_ge_dec x y).
  - destruct (Z_le_gt_dec y z).
    + left. auto.
    + right. lia.
  - right. lia.
Defined.

(*Decidable version of [block_wf]*)
Definition block_wf_bool (b: block) : bool :=
  range_lt_le_dec 0 (blk_k b) (ByteFacts.fec_n - 1 - ByteFacts.fec_max_h) &&
  range_lt_le_dec 0 (blk_h b) (ByteFacts.fec_max_h) &&
  forallb (fun (o: option fec_packet_act) =>
    match o with
    | None => true
    | Some p => 
                Z.eq_dec (fd_k p) (blk_k b) &&
                Z.eq_dec (fd_h p) (blk_h b) &&
                Int.eq_dec (fd_blockId p) (blk_id b) &&
                (Znth (Int.unsigned (fd_blockIndex p)) (data_packets b ++ parity_packets b) == Some p) &&
                [ forall (x : 'I_(Z.to_nat (Zlength (data_packets b ++ parity_packets b))) |
                            nat_of_ord x != Z.to_nat (Int.unsigned (fd_blockIndex p)) ),
                    Znth (Z.of_nat x) (data_packets b ++ parity_packets b) != Some p ] &&
                packet_valid (f_packet p)
    end) (data_packets b ++ parity_packets b) &&
  Z.eq_dec (Zlength (data_packets b)) (blk_k b) &&
  Z.eq_dec (Zlength (parity_packets b)) (blk_h b) &&
  forallb (fun o =>
    match o with
    | None => true
    | Some p => encodable (f_packet p)
    end) (data_packets b).

Ltac solve_sumbool :=
  repeat match goal with
  | [ H: is_true (proj_sumbool ?x) |- _] => destruct x; [clear H | solve [inversion H]]
  | [ |- is_true (proj_sumbool ?x)] => destruct x; auto; try lia
  end.

Lemma is_true_true: forall (b: bool),
  is_true b <-> b = true.
Proof.
  move => b. by case: b.
Qed.

Lemma block_wf_bool_reflect: forall b,
  reflect (block_wf b) (block_wf_bool b).
Proof.
  move => b. apply iff_reflect. rewrite /block_wf /block_wf_bool. split.
  - move => [Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh Henc]]]]]]]. 
    do 5 (try(apply /andP; split)); try solve_sumbool.
    + rewrite is_true_true forallb_forall => o. case: o => [p |//]. rewrite in_app_iff => Hin.
      apply /andP; split; [repeat (apply /andP; split)|].
      * apply Hkh in Hin. solve_sumbool.
      * apply Hkh in Hin. solve_sumbool.
      * apply Hid in Hin. solve_sumbool.
      * apply (Hidx _ (Int.unsigned (fd_blockIndex p))) in Hin. apply /eqP. by apply Hin.
      * apply /forallP => x. apply /implyP => Hx.
        case: (Znth (Z.of_nat x) (data_packets b ++ parity_packets b) == Some p) /eqP => [Hnth|//].
        apply Hidx in Hnth. apply (f_equal Z.to_nat) in Hnth. rewrite Nat2Z.id in Hnth.
        move: Hx. by rewrite Hnth eq_refl. by [].
      * by apply Henc. 
    + rewrite is_true_true forallb_forall => o. case: o => [p |//]. apply Henc.
  - move => /andP [/andP[/andP[/andP[/andP[Hhbound Hkbound] Hall] Hk] Hh] Henc].
    solve_sumbool. move: Hall. rewrite is_true_true forallb_forall => Hall.
    repeat split; try lia.
    + rewrite -in_app_iff in H. apply Hall in H. move: H => /andP[/andP[/andP[/andP[/andP [H _] _] _] _ ] _].
      by solve_sumbool.
    + rewrite -in_app_iff in H. apply Hall in H. move: H => /andP[/andP[/andP[/andP[/andP [_ H] _] _] _] _].
      by solve_sumbool.
    + move => p. rewrite -in_app_iff => Hin. apply Hall in Hin. move: Hin => /andP[/andP[/andP[/andP[_ H] _] _] _].
      by solve_sumbool.
    + rewrite -in_app_iff in H. apply Hall in H. move: H => /andP[/andP[_ Hp2] _].
      move => Hith.
      have Hi: 0 <= i < Zlength (data_packets b ++ parity_packets b). { apply Znth_inbounds.
        by rewrite Hith. }
      move: Hp2 => /forallP Hp2.
      case: (Z.eq_dec i (Int.unsigned (fd_blockIndex p))) => [//|Hneq].
      (*Now need to construct ordinal*)
      have Hibound: (Z.to_nat i < (Z.to_nat (Zlength (data_packets b ++ parity_packets b))))%N. {
        apply /ltP. lia. }
      move: Hp2 => /(_ (Ordinal Hibound))/= => /implyP Hp2. move: Hp2. rewrite Z2Nat.id; try lia. 
      rewrite Hith eq_refl /=. move => Hp2. have: false. apply Hp2.
        case : (Z.to_nat i == Z.to_nat (Int.unsigned (fd_blockIndex p))) /eqP => [Heq|//].
        apply Z2Nat.inj in Heq; try rep_lia. by [].
    + move->. rewrite -in_app_iff in H. apply Hall in H. by move: H => /andP[/andP[/andP[_ /eqP Hp1] _] _].
    + move: Henc. rewrite is_true_true forallb_forall => Henc p Hp. by apply Henc in Hp.
    + move => p Hp. rewrite -in_app_iff in Hp. apply Hall in Hp. by move: Hp => /andP[ _ Hval].
Qed. 

(*From a block, we can generate what is needed*)
Definition packet_mx (b: block): list (list byte) :=
  map (fun x => match x with
                 | None => nil
                 | Some p => (packet_bytes (f_packet p))
                 end) (data_packets b).

Definition parity_mx (b: block) : list (option (list byte)) :=
  map (fun x => match x with
                | None => None
                | Some p => Some (p_contents (f_packet p))
                end) (parity_packets b).

Definition stats (b: block) : list byte :=
  map (fun x => match x with
                | None => Byte.one
                | Some _ => Byte.zero
                end) (data_packets b).

Definition num_receieved (b: block) : Z :=
  Zlength (filter isSome (data_packets b)) + Zlength (filter isSome (parity_packets b)).

(*Max of list of nonnegative integers*)
Definition list_max_nonneg {A: Type} (f: A -> Z) (l: list A) : Z :=
  fold_right (fun x y => Z.max (f x) y) 0 l.

Lemma list_max_nonneg_in: forall {A: Type} (f: A -> Z) (l: list A) (x: A),
  0 <= f x ->
  In x l ->
  0 <= f x <= (list_max_nonneg f l).
Proof.
  move => A f l x. rewrite /list_max_nonneg. elim : l => [//= | h t /= IH Hfx [Hhx | Hin]].
  - rewrite Hhx. split. by []. apply Z.le_max_l.
  - split. by []. eapply Z.le_trans. apply IH. by []. by []. apply Z.le_max_r.
Qed.

Lemma list_max_nonneg_lb: forall {A: Type} (f: A -> Z) (l: list A),
  0 <= list_max_nonneg f l.
Proof.
  move => A f l. elim: l => [// | h t /= IH]. lia.
Qed.

Lemma list_max_nonneg_ub: forall {A: Type} (f: A -> Z) (l: list A) n,
  0 <= n ->
  (forall y, In y l -> f y <= n) ->
  list_max_nonneg f l <= n.
Proof.
  move => A f l n Hn. elim : l => [/= Hall | h t /= IH Hall]. lia.
  apply Z.max_lub. apply Hall. by left. apply IH. move => y Hy. apply Hall. by right.
Qed.

Lemma list_max_nonneg_eq: forall {A: Type} (f: A -> Z) (l: list A) (x: A) n,
  In x l ->
  0 <= f x ->
  f x = n ->
  (forall y, In y l -> f y <= n) ->
  list_max_nonneg f l = n.
Proof.
  move => A f l x n Hin Hfx Hn Hall.
  have Hlb:= (list_max_nonneg_in Hfx Hin). rewrite Hn in Hfx.
  have Hub:=(list_max_nonneg_ub Hfx Hall). lia.
Qed. 

  
(*Get value of c for the block. If a parity packet exists, take the length of its payload.
  Otherwise, find the largest packet (with header). We need both cases: if we do not include
  the parity, our value for incomplete blocks will be wrong, if we do not include the data
  packet, we cannot calculate c for a completed block with no parities.
  However, it makes the definition quite ugly*)
Definition blk_c (b: block) : Z :=
  match [ seq x <- parity_packets b | isSome x] with
  | Some h :: _ => Zlength (p_contents (f_packet h))
  | _ => list_max_nonneg (fun o => match o with
                            | None => 0
                            | Some p => Zlength (p_header(f_packet p) ++ p_contents (f_packet p))
                            end) (data_packets b)
  end.

Lemma blk_c_nonneg: forall b,
  0 <= blk_c b.
Proof.
  move => b. rewrite /blk_c.
  case : [seq x <- parity_packets b | isSome x] => [| a t/=].
  - apply list_max_nonneg_lb.
  - case: a => [p|].
    + apply Zlength_nonneg.
    + apply list_max_nonneg_lb.
Qed.

Definition lengths (b: block) : list Z :=
  map (fun o => match o with
                | None => blk_c b
                | Some p => Zlength (packet_bytes (f_packet p))
                end) (data_packets b). 

(*A block is complete (these imply that parities are nonempty if data is*)
(*TODO: could make bool, have to make bool (decidable) version of parities_valid*)
Definition block_complete (b: block) : Prop :=
  (*The block has a data packet that has length c (so c is actually the max, not just an upper bound)*)
  (exists p, In (Some p) (data_packets b) /\ Zlength (p_header (f_packet p) ++ p_contents (f_packet p)) = blk_c b) /\
  (*All parities have length c*)
  (forall p, In (Some p) (parity_packets b) -> Zlength (p_contents (f_packet p)) = blk_c b) /\
  (*All data packets (including headers) have length <= c*)
  (forall p, In (Some p) (data_packets b) -> Zlength (packet_bytes (f_packet p)) <= blk_c b) /\
  parities_valid (blk_k b) (blk_c b) (parity_mx b) (packet_mx b).

Definition isNone {A: Type} (o: option A) :=
  negb (isSome o).

Definition block_in_progress (b: block) : bool :=
  forallb isNone (parity_packets b).

(* Getting blocks from stream (encoded/received)*)

(*This is a bit complicated, since we want to filter by blockIndex, then build the block from this list.*)
(*
Definition get_val {A B : Type} (l: list A) (f: A-> B) (default : B) :=
  match l with
  | nil => default
  | x :: _ => f x
  end.

Definition int_min (x y: int) : int :=
  Int.repr (Z.min (Int.unsigned x) (Int.unsigned y)).

Definition list_int_min {A : Type} (f: A -> int) (l: list A) : int :=
  fold_right (fun x acc => int_min (f x) acc) (Int.repr (Int.max_unsigned)) l.

(*Takes a list of packets with the same blockIndex, build a block*)
Definition build_block (l: list fec_packet_act) : block :=
  let k := get_val l (fun p => fd_k p) 0 in
  let h := get_val l (fun p => fd_h p) 0 in
  let id := list_int_min (fun p => p_seqNum (f_packet p)) l in
  let data := foldr 
    (fun (p: fec_packet_act) acc => upd_Znth (Int.unsigned (fd_blockIndex p)) acc (Some p)) (zseq k None) l in
  let parities := foldr
    (fun p acc => upd_Znth (Int.unsigned (fd_blockIndex p) - k) acc (Some p)) (zseq h None) l in
  mk_blk id data parities k h false.
*)
(*Get the blocks from the stream TODO replace with get_blocks' *)
(*Definition get_blocks (l: list fec_packet_act) : list block.
Admitted.
(*
  let classes := equiv_classes (fun p => fd_blockIndex p) Int.eq_dec l in
  map build_block classes.
*)
(*TODO: prove that get_blocks is invariant under permutation assuming that
  1. All packets with same blockIndex have same k
  2. All packets with same blockIndex have same h
  Then we can reason about permutation, not subseq*)
*)
Definition map_with_idx {A B: Type} (l: list A) (f: A -> Z -> B) : list B :=
  map (fun (t : A * Z) => let (x, z) := t in f x z) (combine l (Ziota 0 (Zlength l))).

Lemma map_with_idx_Znth: forall {A B} `{Inhabitant A} `{Inhabitant B} (l: list A) (f: A -> Z -> B) i,
  0 <= i < Zlength l ->
  Znth i (map_with_idx l f) = f (Znth i l) i.
Proof.
  move => A B HA HB l f i Hi. rewrite /map_with_idx Znth_map.
  - rewrite Znth_combine.
    + by rewrite Znth_Ziota; try lia.
    + by rewrite Zlength_Ziota; lia.
  - rewrite Zlength_combine Z.min_l; try lia.
    by rewrite Zlength_Ziota; lia.
Qed.

(** Encoder function *)

Definition populate_packets (id: int) (model : packet) (contents: list (list byte)) : list packet :=
  map (fun l => let newHeader := copy_fix_header (p_header model) l in mk_pkt newHeader l id) contents.

(*Finally, we can define what it means to encode a block with a model*)
Definition encode_block_aux (b: block) (model: packet) :=
  let packetsNoFec := populate_packets (blk_id b) model 
     (encoder_list (blk_h b) (blk_k b) (blk_c b) (packet_mx b))  in
  map_with_idx packetsNoFec (fun p i => 
    mk_fecpkt p (mk_data (blk_k b) (blk_h b) true (blk_id b) (Int.repr ((blk_k b) + i)))).

(*Encoding a block chooses an appropriate model packet - either the inputted packet
  or the last packet in the block*)
Definition encode_block (b: block) (o: option packet) : list fec_packet_act :=
  match (pmap id (data_packets b)), o with
  | nil, None => nil (*can't happen*)
  | _, Some p => encode_block_aux b p
  | h :: t, _ => encode_block_aux b (f_packet (last h (h :: t)))
  end.

(*From here, we need a few utility functions for block so we can create the encoder predicate*)
Definition get_fec_packet (p: packet) (b: block) : fec_packet_act :=
   mk_fecpkt p (mk_data (blk_k b) (blk_h b) false (blk_id b) (Int.sub (p_seqNum p) (blk_id b))).

Definition new_fec_packet (p: packet) (k: Z) (h: Z) : fec_packet_act :=
  mk_fecpkt p (mk_data k h false (p_seqNum p) Int.zero).

Definition add_packet_to_block_red (p: packet) (b: block) : block :=
  let f := get_fec_packet p b in
  b <| data_packets := upd_Znth (Int.unsigned (fd_blockIndex f)) (data_packets b) (Some f) |>.

Definition create_block_with_packet_red (p: packet) (k: Z) (h: Z) : block :=
  let f := new_fec_packet p k h in
  mk_blk (p_seqNum p) (upd_Znth 0 (zseq k None) (Some f)) (zseq h None) k h false.

(** Encoder predicate*)

(*TODO: should we change overall predicates so that we have a function that
  takes in orig, encoded, curr, and some (variable) state and produces a list of packets.
  Then, we say that all steps just takes in list of states and foldl's over
  Then, for the whole thing: exists a list of states such that equality holds
  Might be nicer to work with
  Can we prove that the current paradigm is, in some sense, equivalent?*)



(*We first write our encoder as a function (inputted with k and h). We do this in a slightly more
  complicated way than needed - utilizing a 

(*We will write our encoder first as a function (with inputted k and h), then write the predicate, where
  we quantify over k and h*)
Definition rse_encode_func (orig: list packet) (encoded: list fec_packet_act) (curr: packet)
  (k h: Z) : list fec_packet_act :=

  (*For the situations when we start a new block*)
  let encode_new (p: packet) (k' h': Z) :=
    new_fec_packet p k' h' ::
    if Z.eq_dec k' 1 then (encode_block (create_block_with_packet_red p k' h') (Some p)) else nil
  in

  (*For the situation when we add to an existing block*)
  let encode_exist (p :packet) (b: block) :=
    let newBlock := add_packet_to_block_red p b in
    get_fec_packet p b ::
    if Z.eq_dec (Zlength (filter isSome (data_packets newBlock))) (blk_k newBlock) then
      encode_block newBlock (Some p) else nil
  in

  let blocks := get_blocks encoded in
  match blocks with
  | nil => (*no blocks, need to create a new one*) encode_new curr k h
  | b :: _ => 
    let currBlock := last b blocks in
    let init :=
      if ~~(Z.eq_dec (blk_k currBlock) k) || ~~(Z.eq_dec (blk_h currBlock) h)
        then encode_block currBlock None else nil
    in

    let newPackets :=
      if Z.eq_dec (Zlength (filter isSome (data_packets currBlock))) (blk_k currBlock) then
        encode_new curr k h
      else 
        if Z.eq_dec (Zlength (filter isSome (data_packets currBlock)) + 1) (blk_k currBlock) then
          encode_exist curr currBlock
        else 
          [get_fec_packet curr b]
      in
    init ++ newPackets
    end.

(*The final predicate is simple*)

Definition rse_encoder : (@encoder fec_data) :=
  fun (orig: list packet) (encoded: list fec_packet_act) (curr: packet) (new: list fec_packet_act) =>
    exists (k: Z) (h: Z),
    new = rse_encode_func orig encoded curr k h.

(** The Decoder*)

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

Lemma nat_pred_bound: forall (m n: nat),
  (m < n)%N ->
  (m.-1 < n)%N.
Proof.
  move => m n Hmn.
  apply (leq_ltn_trans (leq_pred m) Hmn).
Qed.

Definition nat_pred_ord {n : nat} (x: 'I_n) : 'I_n :=
  Ordinal (nat_pred_bound (ltn_ord x)).

(*A block is "recoverable" if we have at least k total packets*)
Definition recoverable (b: block) : bool :=
  Z_ge_lt_dec (Zlength (filter isSome (data_packets b)) + Zlength (filter isSome (parity_packets b))) 
    (Zlength (data_packets b)) .
  
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

(*TODO: have to deal with deduce headers once I hear back from Peraton people*)

(*Now we define the different parts, we want several functions that update state (blocks) and give packets to return*)

(*TODO: need to deal with isParity/ordering issue - here we assume that issue doesnt exist*)

(*1. create block with packet*)
Definition create_block_with_fec_packet (p: fec_packet_act) : block :=
  let k := fd_k (p_fec_data p) in
  let h := fd_h (p_fec_data p) in
  let allPackets := upd_Znth (Int.unsigned (fd_blockIndex p)) (zseq (k + h) None) (Some p) in
  mk_blk (fd_blockId p) (sublist 0 k allPackets) (sublist k (k+h) allPackets) k h false.

Definition create_block_with_packet_black (p: fec_packet_act) : block * list packet :=
  let new_block := create_block_with_fec_packet p in
  let packets := (if (fd_isParity p) then nil else [p_packet p]) ++
    (if Z.eq_dec (fd_k (p_fec_data p)) 1 then (decode_block new_block) else nil) in
  let marked_block := if Z.eq_dec (fd_k p) 1 then new_block <| complete := true |> else new_block in
  (marked_block, packets).

(*2. add packet to block*)
Definition add_fec_packet_to_block (p: fec_packet_act) (b: block) : block :=
  let new_packets := upd_Znth (Int.unsigned (fd_blockIndex p)) 
    (data_packets b ++ parity_packets b) (Some p) in
  b <| data_packets := sublist 0 (blk_k b) new_packets |> 
      <| parity_packets := sublist (blk_k b) (blk_k b + blk_h b) new_packets |>.

Definition add_packet_to_block_black (p: fec_packet_act) (b: block) : block * list packet :=
  if complete b then (b, nil) else (*TODO: if this is a data packet, should it still be released?*)
    let new_block := add_fec_packet_to_block p b in 
    let packets := (if (fd_isParity p) then nil else [p_packet p]) ++
      (if recoverable new_block then (decode_block new_block) else nil) in
    let marked_block := if recoverable new_block then new_block <| complete := true |> else new_block in
    (marked_block, packets).

(*The decoder is more complicated because of timeouts. We include a list of values indicating whether a timeout
  has occurred*)
Definition int_le (x y: int) := Int.lt x y || Int.eq x y.

(*The timeout part: we take in the state representing whether each block is timed out or not
  and we update the state as the actuator does*)
(*Note: since the state is abstract, we will assume it is long enough*)
Fixpoint update_past_blocks (blocks: list block) (curr: fec_packet_act) (state: list bool) :
  (list block * list packet) :=
  match blocks, state with
  | bl :: tl, s :: stl =>
    if s && int_le (fd_blockIndex curr) (blk_id bl) then
      (tl, if fd_isParity curr then nil else [p_packet curr])
    else if Int.lt (fd_blockIndex curr) (blk_id bl) then
      let (b, l) := create_block_with_packet_black curr in
      (b :: blocks, l)
    else if Int.eq (fd_blockIndex curr) (blk_id bl) then
      let (b, l) := add_packet_to_block_black curr bl in
      (b :: tl, l)
    else
      let (bs, l) := update_past_blocks tl curr stl in
      (bl :: bs, l)
  | _ :: _, _ => (nil, nil) (*should never reach here*)
  | _, _ => (*not sure we can reach here - should prove*)
      (nil,  if fd_isParity curr then nil else [p_packet curr])
  end. 
  
(*TODO: move*)
#[export]Instance block_inhab: Inhabitant block :=
  mk_blk Int.zero nil nil 0 0 false.

(*We cannot build the blocks in 1 go since we must take into account timeouts. Instead, we build it up
  incrementally*)
Definition update_dec_state (blocks: list block) (curr: fec_packet_act) (state: list bool) : 
  (list block * list packet) :=
  match blocks with
  | nil => let (b, l) := create_block_with_packet_black curr in ([b], l)
  | bl :: tl => 
    let currBlock := Znth (Zlength blocks - 1) blocks in
    let currSeq := fd_blockIndex curr in
    if Int.eq currSeq (blk_id currBlock) then
      let (b, l) := add_packet_to_block_black curr currBlock in
      (upd_Znth (Zlength blocks - 1) blocks b, l)
    else if Int.lt (blk_id currBlock) currSeq then 
      let (b, l) := create_block_with_packet_black curr in (blocks ++ [b], l)
    else
      (*here we have to deal with timeouts*)
      update_past_blocks (sublist 0 (Zlength blocks - 1) blocks) curr state
  end.

(*The decoder simply repeatedly applies the above function, generating output packets and updating the state*)
Definition decoder_all_steps (received: list fec_packet_act) (states: list (list bool)) : (list block * list packet) :=
  foldl (fun (acc: list block * list packet) (x: fec_packet_act * list bool) =>
    let (blks, pkts) := update_dec_state acc.1 x.1 x.2 in
    (blks, acc.2 ++ pkts)) (nil, nil) (combine received states).

(*Now we can define the decoder function and predicate*)
Definition rse_decode_func (received: list fec_packet_act) (curr: fec_packet_act) 
  (states: list (list bool)) (state: list bool) : list packet :=
  let (blocks, _) := decoder_all_steps received states in
  let (_, pkts) := update_dec_state blocks curr state in
  pkts.

Definition rse_decoder : (@decoder fec_data) :=
  fun (received: list fec_packet_act) (decoded: list packet) (curr: fec_packet_act) (new: list packet) =>
    exists (states: list (list bool)) (state: list bool),
      new = rse_decode_func received curr states state.

(** Correctness Theorems*)

(*It is difficult to say much about the correctness of the decoder, since because of timeouts we cannot be
  sure of much. However, we can prove 2 basic theorems:
  1. The decoder does not produce any bad packets - ie: all returned packets were originally sent.
  2. Subject to (TODO) some conditions on h and k, each original packet is returned at most twice
*)

(*Part 1: Prove that all outputted packets are from the original input*)

(*Basic argument is: we will prove that each block formed in the decoder is a subblock of a
  block from the encoder, and any recoverable subblock must be a subblock of a completed block.
  We will show that decode_block of any recoverable subblock of a completed block gives back
  the original data packets (possibly with some extra zeroes at the end), and thus we can 
  recover the original missing packets. This takes a lot of steps*)

(*1. Define a subblock of a block*)

(*Special sublist for list of options*)
Definition subseq_option {A: Type} (l1 l2: list (option A)) : Prop :=
  Zlength l1 = Zlength l2 /\
  forall (i: Z), 0 <= i < Zlength l1 ->
  Znth i l1 = Znth i l2 \/ Znth i l1 = None.

Lemma subseq_option_tl: forall {A: Type} (h1 h2: option A) (l1 l2 : list (option A)),
  subseq_option (h1 :: l1) (h2 :: l2) ->
  subseq_option l1 l2.
Proof.
  intros A h1 h2 l1 l2. rewrite /subseq_option => [[Hlen Hin]].
  split. list_solve.
  move => i Hi. have Hi1: 0 <= (i+1) < Zlength (h1 :: l1) by list_solve.
  apply Hin in Hi1. rewrite !Znth_pos_cons in Hi1; try lia.
  move: Hi1. by have->:(i + 1 - 1 = i) by lia.
Qed.

Lemma subseq_option_in: forall {A: Type} (l1 l2: list (option A)) (x: A),
  subseq_option l1 l2 ->
  In (Some x) l1 ->
  In (Some x) l2.
Proof.
  move => A l1 l2 x. rewrite /subseq_option => [[Hlens Hsub]].
  rewrite !In_Znth_iff => [[i [Hi Hnth]]]. exists i. split; try lia.
  move: Hsub => /(_ i Hi). by rewrite Hnth => [[H|H]].
Qed.

(*This particular form will be more helpful*)
Lemma subseq_option_in': forall {A: Type} (l1 l2 l3 l4: list(option A)) (x: A),
  subseq_option l1 l2 ->
  subseq_option l3 l4 ->
  In (Some x) l1 \/ In (Some x) l3 ->
  In (Some x) l2 \/ In (Some x) l4.
Proof.
  move => A l1 l2 l3 l4 x Ho1 Ho2 [Hin1 | Hin2].
  - left. apply (subseq_option_in Ho1 Hin1).
  - right. apply (subseq_option_in Ho2 Hin2).
Qed.

Lemma subseq_option_app: forall {A: Type} (l1 l2 l3 l4: list(option A)),
  subseq_option l1 l2 ->
  subseq_option l3 l4 ->
  subseq_option (l1 ++ l3) (l2 ++ l4).
Proof.
  move => A l1 l2 l3 l4. rewrite /subseq_option => [[Hlen1 Hnth1] [Hlen2 Hnth2]]. split.
  - rewrite !Zlength_app. congruence.
  - move => i. rewrite Zlength_app => Hi.
    have [Hi1 | Hi2]: (0 <= i < Zlength l1 \/ Zlength l1 <= i < Zlength l1 + Zlength l3) by lia.
    + rewrite !Znth_app1; try lia. by apply Hnth1.
    + rewrite !Znth_app2; try lia. rewrite Hlen1. apply Hnth2. lia.
Qed.

Lemma subseq_option_trans: forall {A: Type} (l1 l2 l3: list (option A)),
  subseq_option l1 l2 ->
  subseq_option l2 l3 ->
  subseq_option l1 l3.
Proof.
  move => A l1 l2 l3. rewrite /subseq_option => [[Hlen12 Hin12] [Hlen23 Hin23]].
  split. by rewrite Hlen12.
  move => i Hi. have Hi': 0 <= i < Zlength l2 by rewrite -Hlen12.
  apply Hin12 in Hi. case : Hi => [Hin1 | Hnone]; last first.
    by right.
  rewrite Hin1. by apply Hin23.
Qed.

(*The [list_max_nonneg] of a [subseq_option] is smaller*)
Lemma subseq_option_list_max_nonneg: forall {A: Type} (f: option A -> Z) (s1 s2: seq (option A)),
  subseq_option s1 s2 ->
  f None <= 0 ->
  list_max_nonneg f s1 <= list_max_nonneg f s2.
Proof.
  move => A f s1. elim : s1 => [/= s2 | h t /= IH s2].
  - rewrite /subseq_option => Hopt. by have->: s2 = [::] by list_solve.
  - move => Hsub. have Hsub':=Hsub. move: Hsub Hsub'. rewrite {1}/subseq_option.
    case : s2 => [|h1 t1 [Hlen Hin] Hsub Hf]; [list_solve |].
    rewrite /=. have H0: 0 <= 0 < Zlength (h :: t) by list_solve.
    apply Hin in H0. rewrite !Znth_0_cons in H0. case : H0 => [Hh1 | Hh].
    + rewrite Hh1. apply Z.max_le_compat_l. apply IH.
      by apply subseq_option_tl in Hsub. by [].
    + rewrite Hh. have Hlb:=(@list_max_nonneg_lb _ f t).
      have Htle: (list_max_nonneg f t <= list_max_nonneg f t1) by
        apply IH; [ apply (subseq_option_tl Hsub) | by []]. lia.
Qed.

(*TODO: make bool instead?*)
Definition subblock (b1 b2: block) : Prop :=
  blk_id b1 = blk_id b2 /\
  subseq_option (data_packets b1) (data_packets b2) /\
  subseq_option (parity_packets b1) (parity_packets b2) /\
  blk_k b1 = blk_k b2 /\
  blk_h b1 = blk_h b2.

(*Key lemma: subblocks of well-formed blocks are well-formed*)
Lemma subblock_wf: forall (b1 b2: block),
  block_wf b2 ->
  subblock b1 b2 ->
  block_wf b1.
Proof.
  move => b1 b2. 
  rewrite /block_wf /subblock => [[Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc Hvalid]]]]]]]]] [Hsubid [Hsubdata [Hsubpar [Hsubk Hsubh]]]].
  repeat match goal with | |- ?p /\ ?q => split; try by []; try lia end.
  - move => p Hp. rewrite Hsubk Hsubh. apply Hkh. by apply (subseq_option_in' Hsubdata Hsubpar).
  - move => p Hp. rewrite Hsubid. apply Hid. by apply (subseq_option_in' Hsubdata Hsubpar).
  - move => p i Hin. (*This one is a bit harder*)
    split; move => Hi.
    + have Hibound: 0 <= i < Zlength (data_packets b1 ++ parity_packets b1) by (apply Znth_inbounds; rewrite Hi).
      pose proof (subseq_option_app Hsubdata Hsubpar) as Hsub'. move: Hsub'.
      rewrite /subseq_option => [[_ Hnth]]. move: Hnth => /(_ i Hibound) [Hsome | Hnone].
      * apply Hidx. by apply (subseq_option_in' Hsubdata Hsubpar). by rewrite -Hsome.
      * by rewrite Hnone in Hi.
    + (*The complicated part: WLOG suppose p in data_packets, then p in data_packets b2
          there exists a j such that Znth j (data_packets b1) = Some p
          by def of subseq_seq, Znth j (data_packets b2) = Some p
          therefore, by wf of b1, j = blockIndex, which is what we want to show*)
      have Hinb2: In (Some p) (data_packets b2) \/ In (Some p) (parity_packets b2) by
      apply (subseq_option_in' Hsubdata Hsubpar). move: Hin.
      (*TODO: these are very similar*)
      rewrite !In_Znth_iff => [[[j [Hj Hnth]] | [j [Hj Hnth]]]].
      * move: Hsubdata. rewrite /subseq_option => [[Hlen Hall]]. move: Hall => /(_ j Hj).
        rewrite !Hnth => [[Hjb2 | //]]. symmetry in Hjb2.
        have<-: j = i. { rewrite Hi. apply Hidx. by []. rewrite Znth_app1 //. lia. }
        rewrite Znth_app1 //. lia.
      * move: Hsubpar. rewrite /subseq_option => [[Hlen Hall]]. move: Hall => /(_ j Hj).
        rewrite !Hnth => [[Hjb2 |//]]. symmetry in Hjb2.
        move: Hsubdata. rewrite /subseq_option => [[Hlen' _]]. 
        have<-: (Zlength (data_packets b1) + j) = i. { rewrite Hi. apply Hidx. by [].          
          rewrite Znth_app2 //; try lia. rewrite -Hjb2. f_equal. lia. }
        rewrite Znth_app2; try lia. rewrite -Hnth. f_equal. lia.
  - move: Hsubdata. rewrite /subseq_option. lia.
  - move: Hsubpar. rewrite /subseq_option. lia.
  - move => p Hp. apply Henc. by apply (subseq_option_in Hsubdata).
  - move => h Hp. apply Hvalid. by apply (subseq_option_in' Hsubdata Hsubpar).
Qed.

Lemma subblock_trans: forall b1 b2 b3,
  subblock b1 b2 ->
  subblock b2 b3 ->
  subblock b1 b3.
Proof.
  move => b1 b2 b3. rewrite /subblock => [[Hid1 [Ho1 [Ho1' [Hk1 Hh1]]]] [Hid2 [Ho2 [Ho2' [Hk2 Hh2]]]]].
  repeat match goal with [ |- ?p /\ ?q ] => split; try congruence end. 
  by apply (subseq_option_trans Ho1).
  by apply (subseq_option_trans Ho1').
Qed.

(*2. Prove that if we have ANY recoverable subblock of a completed, well-formed block, 
  then decoder_list_block b gives the original packets. This is the core
  correctness theorem where we use [decoder_list_correct] *)

(*TODO: move*)
Lemma Zlength_filter: forall {A: Type} (p: pred A) (l: list A),
  Zlength (filter p l) <= Zlength l.
Proof.
  move => A p l. rewrite Zlength_correct -size_length size_filter.
  rewrite -(Z2Nat.id (Zlength l)); [| list_solve]. apply inj_le. apply /leP.
  by rewrite ZtoNat_Zlength -size_length count_size.
Qed.

(*For complete blocks, we can calculate blk_c just by taking max length of data packets*)
Lemma blk_c_complete: forall b,
  block_complete b ->
  blk_c b = list_max_nonneg
      (fun o : option fec_packet_act =>
       match o with
       | Some p => Zlength (p_header (f_packet p) ++ p_contents (f_packet p))
       | None => 0
       end) (data_packets b).
Proof.
  move => b. rewrite /block_complete => [[[p [Hinp Hlenp]] [Hparc [Hdatac _]]]].
  symmetry. eapply list_max_nonneg_eq. apply Hinp. list_solve.
  - by [].
  - move => y. case : y => [y /= Hiny | _].
    + by apply Hdatac.
    + rewrite /blk_c. case : [seq x <- parity_packets b | isSome x] => [|/= h t].
      apply list_max_nonneg_lb. case : h.
      move => ?. list_solve. apply list_max_nonneg_lb.
Qed.

(*First, we need to know that blk_c of a recoverable subblock of a complete block is the same as the
  superblock. This is surprisingly nontrivial to prove*)
Lemma blk_c_recoverable: forall (b1 b2: block),
  block_complete b2 ->
  subblock b1 b2 ->
  recoverable b1 ->
  blk_c b1 = blk_c b2.
Proof.
  move => b1 b2 Hc. have Hcomp:=Hc. move: Hc. 
  rewrite /block_complete /subblock /blk_c => [[[def [Hindef Hlendef] [Hparc [Hdatac _]]]]].
  remember (fun o : option fec_packet_act => match o with
                                    | Some p => Zlength (p_header (f_packet p) ++ p_contents (f_packet p))
                                    | None => 0
                                    end) as f eqn : Hf.
  rewrite /recoverable => [[_ [Hsubdata [Hsubpar _]]] Hk].
  case Hpar: [seq x <- parity_packets b1 | isSome x] => [| pa tl]; last first.
  (*If there is a parity packet, we must show it has the same length as the parity packet in b2*)
  - move: Hpar. case : pa => [pa Hfilt |Hfilt].
    + have: (Some pa) \in [seq x <- parity_packets b1 | isSome x]
        by rewrite Hfilt in_cons eq_refl orTb.
      rewrite mem_filter. move => /andP[_ Hinpa].
      have Hinpa': (Some pa) \in parity_packets b2. { move: Hinpa.
        rewrite !in_mem_In. by apply subseq_option_in. }
      have: (Some pa) \in [seq x <- parity_packets b2 | isSome x] by rewrite mem_filter.
      case Hpar': [seq x <- parity_packets b2 | isSome x] => [//|h t]. move => _.
      move: Hpar'. case: h => [a /= Hfilt' | // Hcon]; last first.
        have: None \in [seq x <- parity_packets b2 | isSome x] by rewrite Hcon in_cons orTb.
        by rewrite mem_filter.
      rewrite in_mem_In in Hinpa'.
      move: Hparc => /(_ _ Hinpa'). by rewrite Hfilt'.
    + have: None \in [seq x <- parity_packets b1 | isSome x] by rewrite Hfilt in_cons orTb.
      by rewrite mem_filter.
  - (*In the other case, we need to show list_max of (packets b1) and (packets b2) are equal*)
    have->//: list_max_nonneg f (data_packets b1) = blk_c b2; last first.
      by rewrite /blk_c Hf.
    rewrite (blk_c_complete Hcomp) -Hf.
    move: Hk. case : (Z_ge_lt_dec 
      (Zlength [seq x <- data_packets b1 | isSome x] + Zlength [seq x <- parity_packets b1 | isSome x])
      (Zlength (data_packets b1))) => [Hk _ |//].
    (*The real goal we have to prove - prove by showing <= and >=*)
    have Hub: list_max_nonneg f (data_packets b1) <=  list_max_nonneg f (data_packets b2). {
    apply subseq_option_list_max_nonneg. by []. by rewrite Hf. }
    (*To show >=, need to show that all data packets in b2 are in b1 (from recoverable), so the longest
      packet is too*)
    move: Hk. rewrite Hpar Zlength_nil Z.add_0_r => Hlenge.
    have: Zlength [seq x <- data_packets b1 | isSome x] = Zlength (data_packets b1). {
      have H:=(@Zlength_filter _ isSome (data_packets b1)). (*why doesnt lia work?*)
      have Htemp: forall (z1 z2 : Z), z1 >= z2 -> z1 <= z2 -> z1 = z2 by lia. by apply Htemp. }
    rewrite {Hlenge} !Zlength_correct -!size_length => Hlens. apply Nat2Z.inj in Hlens.
    move: Hlens => /eqP Hlens. move: Hlens. rewrite size_filter -all_count => Hall.
    have Hallin: forall o, In o (data_packets b2) -> In o (data_packets b1). {
      move => o. rewrite !In_Znth_iff. move: Hsubdata. rewrite /subseq_option => [[Hlendata Hnth] [i [Hi Hith]]].
      have Hi':=Hi. rewrite -Hlendata in Hi. apply Hnth in Hi. case : Hi => [Hi | Hi].
        exists i. split. by rewrite Hlendata. by rewrite Hi Hith.
      move: Hall. rewrite all_in.
      have Hn: None \in data_packets b1. rewrite in_mem_In In_Znth_iff. exists i. split.
        by rewrite Hlendata. by [].
      by move => /(_ _ Hn). }
    have Hfp': 0 <= f (Some def) by rewrite Hf; list_solve.
    have Hinp: In (Some def) (data_packets b1) by apply Hallin.
    have Hlb:=(list_max_nonneg_in Hfp' Hinp).
    have: f(Some def) = list_max_nonneg f (data_packets b2)
      by rewrite Hf Hlendef Hf -/(blk_c b2) blk_c_complete.
    lia.
Qed.

(*TODO: is this in ssreflect?*)
Lemma boolP: forall (b: bool),
  reflect (is_true b) b.
Proof.
  move => b. case : b. by apply ReflectT. by apply ReflectF.
Qed.

(*We need to know that c is positive - ie: some packet has nonzero length. This is a weak bound;
  we know that each packet really has length at least 28 for IP/UDP header*)
Lemma blk_c_pos: forall (b: block),
  block_wf b ->
  block_complete b ->
  0 < blk_c b.
Proof.
  move => b. rewrite /block_wf /block_complete => 
    [[Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc Hvalid]]]]]]]]] [[p [Hinp Hlenp]] _].
  rewrite -Hlenp. have: packet_valid p. apply Hvalid. by left. rewrite /packet_valid /valid_fec_packet.
  move => /andP[ /boolP Hle _]. move: Hle. 
  case : (Z_le_lt_dec 8 (Zlength (p_header p))) => Hle//=. 
  rewrite Zlength_app. list_solve.
Qed.

(* A nontrivial theorem to prove that uses [decode_list_correct_full] to show that for ANY
  subblock of a well formed, complete block that has received at least k packets, we get 
  the packets of the original packet matrix, possibly padded with some zeroes*)
Theorem subblock_recoverable_correct: forall (b1 b2: block),
  block_wf b2 ->
  block_complete b2 ->
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
  - have Hcomp':=Hcomp. move: Hcomp'. rewrite /block_complete => [[[p [Hinp Hlenp]] [_ [Hleq _]]]].
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
    move: Hcomp. rewrite /block_complete => [[ _ [Hlens _]]]. 
    by apply Hlens.
  - have Hlen: Zlength (parity_mx b1) = Zlength (parity_mx b2) by
      move: Hwf' Hwf Hsub; rewrite /block_wf /subblock /parity_mx !Zlength_map; list_solve.
    move: Hcomp. rewrite /block_complete => [[_ [ _ [ _ Hval]]]].
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

Lemma map_pmap_id: forall {A B: Type} (f: A -> B) (l: list (option A)),
  map f (pmap id l) = pmap id (map (omap f) l).
Proof.
  move => A B f l. elim : l => [//| h t /= IH].
  case : h => [a //= | //=]. by rewrite IH.
Qed.

Lemma subblock_c: forall (b1 b2: block),
  block_complete b2 ->
  subblock b1 b2 ->
  (forall p, In (Some p) (data_packets b1) -> Zlength (packet_bytes (f_packet p)) <= blk_c b2) /\
  (forall p, In (Some p) (parity_packets b1) -> Zlength (p_contents (f_packet p)) = blk_c b2).
Proof.
  move => b1 b2. rewrite /block_complete /subblock => [[_ [Hpars [Hdata _]]]] [_ [Hsubdata [Hsubpar _]]].
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

(*TODO: move to CommonSSR*)
Lemma zip_combine: forall {A B: Type} (l1 : list A) (l2: list B),
  zip l1 l2 = combine l1 l2.
Proof.
  move => A B l1. elim : l1 => [//= l2 | h t /= IH l2].
  - by case : l2.
  - case : l2 => [//|h' t'/=]. by rewrite IH.
Qed.

(*We extend this to show that [decode_block] gives all packets in the original block not in the subblock*)
Theorem decode_block_correct: forall (b1 b2: block),
  block_wf b2 ->
  block_complete b2 ->
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
        + move: Hcomp. rewrite /block_complete => [[_ [_ [Hin _]]]]. apply Hin. rewrite -Hp.
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
      have Hval: valid_packet (p_header (f_packet p2)) (p_contents (f_packet p2)). {
        move: Hwf. rewrite /block_wf. rewrite -!and_assoc => [[_ Hvalid]]. apply Hvalid.
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

(*The next big step is to show that, at all points, the blocks in the decoder are subblocks of
  some completed block produced by the encoder. This requires many steps*)

(*1. At all points during the decoder, all of the blocks in the current state of subblocks
  of the blocks formed directly from the received list*)

(*TODO: cannot find in ssreflect, I think it should exist: finType for elements in list*)
(*Since we don't have that, write "pick" directly:*)
Definition pickSeq {A: eqType} (p: pred A) (s: seq A) : option A :=
  foldr (fun x acc => if p x then Some x else acc) None s.

Print pick_spec.

Variant pickSeq_spec (T: finType) (p: pred T) (s: seq T) : option T -> Type :=
  | Pick : forall x : T, x \in s -> p x -> pickSeq_spec p s (Some x)
  | Nopick: { in s, p =1 xpred0 } -> pickSeq_spec p s None.

Lemma pickSeqP: forall {T: finType} (p: pred T) (s: seq T),
  pickSeq_spec p s (pickSeq p s).
Proof.
  move => T p s. elim : s => [//= | h t /= IH].
  - by apply Nopick.
  - case Hp: (p h).
    + apply Pick. by rewrite in_cons eq_refl orTb. by apply Hp.
    + case : IH.
      * move => x Hinx Hpx. apply Pick. by rewrite in_cons Hinx orbT. by [].
      * move => Hin. apply Nopick. move => y. rewrite in_cons => /orP[/eqP Hyh | Hyt].
        by rewrite Hyh. by apply Hin.
Qed.

Definition decoder_block_state (received: list fec_packet_act) (states: list (list bool)) :=
  (decoder_all_steps received states).1.

(*TODO: replace encoder once we get there*)
Definition get_blocks' (l: list fec_packet_act) : list block :=
  foldl (fun acc (p: fec_packet_act) =>
    match [ pick i in ordinal (size acc) | Int.eq_dec (blk_id (Znth (Z.of_nat i) acc)) (fd_blockId p) ] with
    | None => acc ++ [create_block_with_fec_packet p]
    | Some i => upd_Znth (Z.of_nat i) acc (add_fec_packet_to_block p (Znth (Z.of_nat i) acc))
    end) nil l.

Lemma let_tuple_fst {A B: Type}: forall (t: A * B) (f: B -> B),
  (let (x, y) := t in (x, f y)).1 = t.1.
Proof.
  move => t f. by case : t.
Qed.

Check subseq_option.
(*TODO: move*)
Lemma subseq_option_refl: forall {A: Type} (s : seq (option A)),
  subseq_option s s.
Proof.
  move => A s. rewrite /subseq_option. split. by []. move => i Hi. by left.
Qed.

(*TODO: move*)

Lemma subblock_eq_complete: forall (b1 b2 : block),
  b1 <| complete := true |> = b2 <| complete := true |> ->
  subblock b1 b2.
Proof.
  move => b1 b2. case : b1; case : b2 => [id1 dat1 par1 k1 h1 c1] id2 dat2 par2 k2 h2 c2 /= => 
    [[]]->->->->->. rewrite /subblock /=. split => [//|].
  split. apply subseq_option_refl. split => [|//]. apply subseq_option_refl.
Qed.

Lemma or_impl_right: forall (P Q R: Prop),
  (P -> R) ->
  (P \/ Q) ->
  R \/ Q.
Proof.
  tauto.
Qed.


(*TODO: move to above maybe*)
(*TODO: this is getting super ugly, let's think about this better - maybe reformulate
  block_wf condition instead of that iff and everything*)
Lemma add_fec_packet_to_block_wf: forall (p: fec_packet_act) (b: block),
  fd_blockId p = blk_id b ->
  fd_k p = blk_k b ->
  fd_h p = blk_h b ->
  Int.unsigned (fd_blockIndex p) < fd_k p + fd_h p ->
  packet_valid p ->
  (forall (p': fec_packet_act), (Some p') \in (data_packets b ++ parity_packets b) -> fd_blockIndex p != fd_blockIndex p') ->
  block_wf b ->
  block_wf (add_fec_packet_to_block p b).
Proof.
  move => p b Hids Hks Hhs Hidxb Hval Hidxdiff. rewrite /block_wf /add_fec_packet_to_block /= =>
    [[Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc Hvalid]]]]]]]]].
  have [Hidx1 | Hindx2]: (0 <= Int.unsigned (fd_blockIndex p) < fd_k p \/ 
    fd_k p <= Int.unsigned (fd_blockIndex p) < fd_k p + fd_h p) by rep_lia.
  - rewrite !upd_Znth_app1;[|lia]. rewrite !(sublist_app1 _ 0);[|lia|list_solve].
    rewrite !sublist_app2;[|list_solve].
    have->: Zlength (upd_Znth (Int.unsigned (fd_blockIndex (p_fec_data' p))) (data_packets b) (Some p)) =
      blk_k b by list_solve.
    rewrite !Z.sub_diag !Z.add_simpl_l !sublist_same; try lia; [|list_solve].
    repeat match goal with | |- ?x /\ ?y => split; try by [] end. 4: list_solve.
    all: move => p'.
    (*3 of the cases are nearly identical*)
    all: try solve [move => Hin; apply (or_impl_right (In_upd_Znth _ _ _ _)) in Hin; rewrite or_assoc in Hin;
      case: Hin => [Hp' | Hold]; last first; [ eauto |  by case: Hp' => ->]].
    + move => i Hin.
(*  case (Z.eq_dec i (Int.unsigned (fd_blockIndex (p_fec_data' p')))) => [Hieq | Hineq].*)
      apply (or_impl_right (In_upd_Znth _ _ _ _)) in Hin; rewrite or_assoc in Hin.
      case: Hin => [Hp' | Hold]. case : Hp' => ->. split.
      have [Hi | [Hi | Hi]]: (0 <= i < blk_k b \/ blk_k b <= i < blk_k b + blk_h b \/ (i < 0 \/ i >= blk_k b + blk_h b)) by lia.
      rewrite Znth_app1; [|list_solve].
      case : (Z.eq_dec i (Int.unsigned (fd_blockIndex (p_fec_data' p)))) => [// | Hneq].
      rewrite upd_Znth_diff; try list_solve. 
      move => Hnth. have Hnth': Znth i (data_packets b ++ parity_packets b) = Some p by list_solve.
      apply (Hidx _ i) in Hnth'. by []. left. rewrite -Hnth. apply Znth_In. list_solve.
      rewrite Znth_app2. list_simplify. apply Hidx. right. rewrite -H. apply Znth_In. list_solve. list_solve.
      list_solve. rewrite Znth_outofbounds. by []. rewrite Zlength_app; list_solve. (*list_solve should do this*)
      move ->. rewrite Znth_app1; [|list_solve]. rewrite upd_Znth_same //. list_solve. (*should fix levels - also
      lots of repetition, should fix*)
      case : (Z.eq_dec i (Int.unsigned (fd_blockIndex (p_fec_data' p)))) => [// | Hneq].
      * move ->. rewrite Znth_app1; [|list_solve]. rewrite upd_Znth_same; [|list_solve].
        (*OH: this causes problems if block indices are not unique - but that should be ok, need assumption*)
        split


 tauto.
        intuition.
        eauto.
      
        by [].



 rewrite upd_Znth_same.



 Search Znth (_ < _).


 list_solve. 



 2: list_solve.


 apply In_Znth.



 list_solve. by left.



 apply Hidx.
      Check Znth_upd_Znth_diff.
     rewrite (Znth_upd_Znth_diff _  _ i (Int.unsigned (fd_blockIndex (p_fec_data' p)))).
      Search upd_Znth Znth.



Znth_upd_Znth_diff:
  forall (A : Type) (d : Inhabitant A) (i j : Z) (l : seq A) (x : A),
  i <> j -> Znth i (upd_Znth j l x) = Znth i l
      rewrite upd_Znth_diff.
      






 Search ( (?P -> ?R) -> (?P \/ ?Q)). apply In_upd_Znth in Hin. [Hupd | Hpar]. apply In_upd_Znth in Hupd.
      case : Hupd


 case (Z.eq_dec i (Int.unsigned (fd_blockIndex (p_fec_data p')))) => [Hieq | Hineq].
      * rewrite Hieq. upd_Znth_same.



 move => i [Hupd | Hpar]; last first.



 apply Hidx. by right.
      apply In_upd_Znth in Hupd. case : Hupd => [Hp' | Hinp'].
      case: Hp' => ->. by []. apply Hkh. by left.

    Search In upd_Znth.


In_upd_Znth



 Search (?x + ?y - ?x).



 list_simplify.



 try list_solve.



 2: { rewrite Hk -Hks. lia. apply Hidx1.


 [|rep_lia].
  


block_wf (add_fec_packet_to_block h (Znth (Z.of_nat i) base))

(*First, we need results about get_blocks*)
Lemma get_blocks_wf: forall (l: list fec_packet_act),
  (forall (p1 p2 : fec_packet_act), p1 \in l -> p2 \in l -> fd_blockId p1 = fd_blockId p2 ->
    fd_k p1 = fd_k p2 /\ fd_h p1 = fd_h p2) ->
  forall b, b \in (get_blocks' l) -> block_wf b.
Proof.
  move => l Hall b. rewrite /get_blocks'. remember (@nil block) as base eqn : Hb.
  rewrite {1}Hb. have Hbase: forall bl, bl \in base -> block_wf bl by move => bl; rewrite Hb.
  rewrite {Hb}. move: Hall base Hbase.
  elim : l => [//= Hall base Hbase | h t /= IH Hall base Hbase].
  - apply Hbase.
  - apply IH.
    + move => p1 p2 Hin1 Hin2 Hid. apply Hall. by rewrite in_cons Hin1 orbT.
      by rewrite in_cons Hin2 orbT. by [].
    + move => bl.
      case Hpick: [pick i | Int.eq_dec (blk_id (Znth (Z.of_nat (nat_of_ord i)) base)) (fd_blockId (p_fec_data h)) ] 
        => [i|].
        * rewrite in_mem_In. move => Hin. apply In_upd_Znth in Hin. case : Hin => [Hbl | Hinbl].
          { rewrite Hbl.



block_wf (add_fec_packet_to_block h (Znth (Z.of_nat i) base))



 Search In upd_Znth.
    



 forget [::] as base.
  have: (forall b b \in

 move: Hall. elim : l => .


        (*basically - only problem is that we need to know that k(block) = k(packet)
          should say: assumption: forall p1 p2, p1 \in r -> p2 \in r -> k(p1) = k(p2)
          then have other lemma: IF this condition holds, then getBlocks creates well-formed blocks
          furthermore, for all blocks in getBlocks, there is a packet in it - then compose to prove this


Lemma decoder_blocks_subblock_received: forall (received: list fec_packet_act) (states: list (list bool)),
  size received = size states ->
  forall (b: block), b \in (decoder_block_state received states) ->
  exists b', (b' \in get_blocks' received) /\ subblock b b'.
Proof.
  move => received states Hsz b. rewrite /decoder_block_state /decoder_all_steps /get_blocks'.
  rewrite -zip_combine. rewrite -(revK (zip _ _)) -{2}(revK received) !foldl_rev rev_zip //.
  (*TODO: OK?*) forget (rev states) as s. rewrite {Hsz states}. move: s.
  elim : (rev received) => [//= s | h t /= IH s].
  - by case : s.
  - move: IH. case : s => [//=| sh st /=]. 
    (*move => Hin.*) 
    set acc := (foldr
                 (fun (x : fec_packet fec_data) (z : seq block) =>
                  match
                    [pick i0 | Int.eq_dec (blk_id (Znth (Z.of_nat (nat_of_ord i0)) z))
                                 (fd_blockId (p_fec_data x)) ]
                  with
                  | Some i0 =>
                      upd_Znth (Z.of_nat i0) z
                        (add_fec_packet_to_block x (Znth (Z.of_nat i0) z))
                  | None => z ++ [:: create_block_with_fec_packet x]
                  end) [::] t).
    rewrite -/(zip t (sh :: st)) => IH/=.
    rewrite let_tuple_fst.
    remember (foldr
            (fun (x : fec_packet_act * seq bool) (z : seq block * seq packet) =>
             let (blks, pkts) := update_dec_state z.1 x.1 x.2 in (blks, z.2 ++ pkts)) 
            ([::], [::]) (zip t st)) as rest eqn : Hr.
    rewrite /update_dec_state. move: Hr. case : rest => [blocks packs]/=.
    case : blocks => [|blockshd blockstl] Hr/=.
    + case: (Z.eq_dec (fd_k (p_fec_data h)) 1) => /= [Hk1 | Hknot1]; rewrite in_cons orbF => /eqP Hb.
      * (*TODO: order of cases?*)
        case Hpick : [pick i | Int.eq_dec (blk_id (Znth (Z.of_nat (nat_of_ord i)) acc)) 
          (fd_blockId (p_fec_data h)) ] => [i|]; last first.
          exists (create_block_with_fec_packet h). rewrite mem_cat in_cons eq_refl orTb orbT //= Hb.
          split => [//|]. by apply subblock_eq_complete.
        exists (add_fec_packet_to_block h (Znth (Z.of_nat i) acc)).
        split. rewrite in_mem_In. apply upd_Znth_In.
        rewrite Zlength_correct -size_length. have /ltP Hi: (i < size acc)%N by [].
        split; try lia. by apply inj_lt.
        (*Need to prove that this is a subblock of adding - relies on fact that input
          stream is well-formed*)
         rewrite /subblock.

        (*basically - only problem is that we need to know that k(block) = k(packet)
          should say: assumption: forall p1 p2, p1 \in r -> p2 \in r -> k(p1) = k(p2)
          then have other lemma: IF this condition holds, then getBlocks creates well-formed blocks
          furthermore, for all blocks in getBlocks, there is a packet in it - then compose to prove this

        (forall p1 p2, p1 \in received -> p2 \in received -> 


        need to prove that get_blocks is uniq

           



           rewrite Hb /subblock /=.


 Search Z.of_nat (_ < _).



 list_solve. lia.


 lia.
           Search Zlength length.
           Search Zlength size.
 
           Search Z ordinal.



 Search upd_Znth In.


 Search In in_mem. rewrite In_in_iff.
    -


 case: (rest.1).
    

    case: (rest.1).


 move: rest. case : rest.


 Print update_dec_state.




 {1}/update_dec_state. 




 move: IH.
    



 
    have Hin': b \in (update_dec_state (foldr
                    (fun (x : fec_packet_act * seq bool) (z : seq block * seq packet) =>
                     let (blks, pkts) := update_dec_state z.1 x.1 x.2 in (blks, z.2 ++ pkts))
                    ([::], [::]) (zip t st)).1 h sh).1. {
      



      case : apply Hin.
    


 Print zip.


 simpl zip. rewrite /zip /=. Print zip. rewrite /=. 


 Search foldl foldr.


 Search zip rev.


 Search combine rev.



 pickSeq (fun b => Int.eq_dec (blk_id b) (fd_blockId (p_fec_data p))) acc with
    | None => acc ++ [create_new_block_with_fec_packet p]
    | Some b => 
    end) nil l.

Lemma decoder_blocks_subblocks


Definition rse_decode_func (received: list fec_packet_act) (curr: fec_packet_act) 
  (states: list (list bool)) (state: list bool) : list packet :=
  let (blocks, _) := decoder_all_steps received states in
  let (_, pkts) := update_dec_state blocks curr state in
  pkts.


  blocks produced by the encoder. With a few aditional



(*Show that if received is a subseq of encoded, then the blocks of received are each
  subblocks of blocks in encoded*)

(*Let's see - want to show that [get_blocks decoded] and blocks formed by decoder function are the same (really permutations)*)
Print rse_decode_func.
Print decoder_all_steps.

(*TODO: I think it would be easier to do the encoder like the decoder (in terms of updating state, folding over, continue)
  I believe for induction that would make things nicer

becase with decoder: can give alternate version where we append all lists
then prove decoder_list is equivalent to this function

what is it that we want to show ultimately?

1. in decoder, the blocks that we work with (from decoder_all_steps and update_dec_state) are each a subblock of some block in
  (get_blocks received)
2. Since received is a subseq_gen of encoded, each of these blocks is a subblock of some block from (get_blocks encoded)
3. If a block is recoverable, its parent must be complete (we will prove for encoder - every block is either <k or complete)
4. Therefore, at every step, the decoder produces valid packets (using above lemma)

question: for get_blocks, why cant we just iterate over a list, add each one to its block in correct place
then prove - resulting blocks are well formed, every packet is in a block, no duplicate blocks

for lemma #1, I think we can prove by induction for decoder_all_steps, can prove for update_dec_state
for lemma #2, we will need to prove this about [equiv_classes]
for lemma #3, this is difficult, and we might need a different version of the encoder for this (similar to decoder, then we
  again prove with induction like lemma #1)
lemma #4 should be a relatively simple extnesion of this result, prove by induction over all steps of decoder*)


(*Compose these to get the final theorem*)
