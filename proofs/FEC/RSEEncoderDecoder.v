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
(*Definition Z_eqMixin := EqMixin (fun z1 z2 => reflect_proj_sumbool (Z.eq_dec z1 z2)).
Canonical Z_eqType := EqType Z Z_eqMixin.*)

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

Definition get_blocks (l: list fec_packet_act) : list block.
Admitted.



(*We first write our encoder as a function (inputted with k and h). We do this in a slightly more
  complicated way than needed - utilizing a 
TODO*)

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
  (update_dec_state (decoder_all_steps received states).1 curr state).2.

Definition rse_decoder : (@decoder fec_data) :=
  fun (received: list fec_packet_act) (decoded: list packet) (curr: fec_packet_act) (new: list packet) =>
    exists (states: list (list bool)) (state: list bool),
      new = rse_decode_func received curr states state.

Definition rse_decoder_list := AbstractEncoderDecoder.decoder_list fec_packet_act_inhab rse_decoder.

(*This shows that the rse_decoder_list definition is usable: for any possible states, if we 
  decode using those states, we still get the predicate*)
(*NOTE (TODO): This actually indicates a problem, I think - this is such a weak spec that we don't
  even have to add states that are consistent with the previous.
  I think the other definition should really be used - TODO: figure this out*)
Lemma rse_decoder_list_add: forall (received : list fec_packet_act) (curr: fec_packet_act)
  (decoded: list packet),
  rse_decoder_list received decoded ->
  forall (s: list bool) (sts: list (list bool)),
    rse_decoder_list (received ++ [curr]) (decoded ++ rse_decode_func received curr sts s).
Proof.
  move => received curr decoded. rewrite /rse_decoder_list /AbstractEncoderDecoder.decoder_list 
    => [[l [Hdec [Hllen Hith]]]] s sts. exists (l ++ [rse_decode_func received curr sts s]).
  split; [|split].
  - by rewrite concat_app Hdec //= app_nil_r.
  - rewrite !Zlength_app. list_solve.
  - move => i. rewrite Zlength_app Zlength_cons /= => Hi. have Hi' := (z_leq_n_1 (proj2 Hi)). (*why cant lia do this*)
    case Hi' => [Hiprev | Hicurr].
    + rewrite !sublist_app1; try lia. rewrite !Znth_app1; try lia. apply Hith. lia.
    + rewrite Hicurr. rewrite !sublist_app1; try lia. rewrite !sublist_same //.
      rewrite !Znth_app2; try lia. rewrite Hllen !Z.sub_diag !Znth_0_cons.
      rewrite /rse_decoder. exists sts. exists s. by [].
Qed.


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

(*The idea is to be smart in our characterization of [get_blocks] - the function that takes a list of
  fec packets and divides up into blocks appropriately. We need to prove 3 main results
  1. get_blocks of the encoded list gives back the original blocks produced by the encoder
  2. after some packets are lost/duplicated in transit, get_blocks of the resulting list
     gives subblocks of the original list
  3. at all points in the decoder, the current decoder state consists of subblocks of
      get_blocks (received)

  Since things can be reordered, it is difficult to prove these directly (as in, it is hard to
  get a good IH). Instead, we do the following:
  1. Note that a block can be uniquely defined by its id and its contents list (assuming the stream of
      fec packets is well formed - all packets with same id have same k and h, and so on)
    So we focus on just constructing these lists appropriately
  2. We give a list of propositions that (get_block_lists) should satisfy, and show that any list
    which satisfies these conditions must be a permutation of (get_block_lists). This allows us to
    use these propositions, which describe the contents of all of the blocks, rather than needing to
    prove everything inductively every time*)

(*TODO: cannot find in ssreflect, I think it should exist: finType for elements in list*)
(*Since we don't have that, write "pick" directly:*)

Definition pickSeq {A: eqType} (p: pred A) (s: seq A) : option A :=
  foldr (fun x acc => if p x then Some x else acc) None s.

(*Could use pick with ordinal, but dependent types are VERY messy*)

Variant pickSeq_spec (T: eqType) (p: pred T) (s: seq T) : option T -> Type :=
  | Pick : forall x : T, x \in s -> p x -> pickSeq_spec p s (Some x)
  | Nopick: { in s, p =1 xpred0 } -> pickSeq_spec p s None.

Lemma pickSeqP: forall {T: eqType} (p: pred T) (s: seq T),
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

(*First, we want to define a special association list with 1 operation: update_or_add, which updates
  an element if there using some function or adds if not*)
Section AssocList.

Variable K: eqType.
Variable V : Type.

Definition assoc_list := list (K * V).

Definition empty': assoc_list := nil.

Lemma empty_uniq: uniq (map fst empty').
Proof.
  by [].
Qed.

Fixpoint updateWith (k: K) (f: V -> V) (a: assoc_list) : assoc_list :=
  match a with
  | nil => nil
  | (k', v') :: tl => if k == k' then (k, f v') :: tl else (k', v') :: updateWith k f tl
  end.

Lemma updateWith_same: forall k f a v',
  uniq (map fst a) ->
  In (k, v') (updateWith k f a) ->
  exists v, In (k, v) a /\ v' = f v.
Proof.
  move => k f a v'. elim : a => [//= | h t /= IH]. case : h => [kh vh]/=.
  move => /andP[Hnotin Huniq]. case: (k == kh) /eqP => Hkkh/=.
  - move => [Heq | Hin].
    + case : Heq =><-. rewrite Hkkh. exists vh. split. by left. by [].
    + move: Hnotin. rewrite -Hkkh.
      have->//: k \in [seq i.1 | i <- t]. rewrite in_mem_In in_map_iff. by exists (k, v').
  - move => [Heq | Hin]. case: Heq => Hkkh'. by rewrite Hkkh' in Hkkh.
    apply IH in Hin. case : Hin => [v [Hinv Hv']]. exists v. split. by right. by []. by [].
Qed.

Lemma updateWith_diff: forall k f a k' v',
  k != k' ->
  In (k', v') (updateWith k f a) <->
  In (k', v') a.
Proof.
  move => k f a k' v'. elim : a => [//= | h t /= IH]. case : h => [kh vh]/=.
  move => (*/andP[Hnotin Huniq]*) Hkk'. case: (k == kh) /eqP => Hkkh/=.
  - split; move => [Heq | Hin].
    + case: Heq => Hk. move: Hkk'. by rewrite Hk eq_refl.
    + by right.
    + case : Heq => Hk. subst. by rewrite eq_refl in Hkk'.
    + by right.
  - split; move => [Heq | Hin]; try (by left); by (right; apply IH).
Qed.

Lemma updateWith_keys: forall k f a,
  map fst a = map fst (updateWith k f a).
Proof.
  move => k f a. elim : a => [//= | h t /= IH].
  case : h => [kh kt]/=. case Hkkh: (k == kh) => /=.
  - f_equal. symmetry. by apply /eqP.
  - by rewrite IH.
Qed. 

Definition get (k: K) (a: assoc_list) : option V :=
  foldr (fun x acc => if k == x.1 then Some x.2 else acc) None a.

Lemma get_some: forall (k: K) (v: V) (a: assoc_list),
  uniq (map fst a) ->
  get k a = Some v <-> In (k, v) a.
Proof.
  move => k v a. elim : a => [//= | h t /= IH]. case : h => [kh vh]/=.
  move => /andP[Hnotin Huniq]. case Hkkh: (k == kh).
  - move: Hkkh => /eqP Hkkh. rewrite Hkkh. split.
    + move => [Hvh]. rewrite Hvh. by left.
    + move => [[Heq] | Hin]. by rewrite Heq. 
      move: Hnotin. have->//: kh \in [seq i.1 | i <- t]. rewrite in_mem_In in_map_iff.
      by exists (kh, v).
  - move: Hkkh => /eqP Hkkh. rewrite IH //. split.
    + move => Hin //. by right.
    + move => [[Heq] | Hin //]. by rewrite Heq in Hkkh.
Qed.

Lemma get_none: forall (k: K) (a: assoc_list),
  get k a = None <-> (forall v, ~In(k, v) a).
Proof.
  move => k a. elim : a => [//= | h t /= IH].
  - split => //. auto.
  - case : h => [kh vh]/=. case Hkkh: (k == kh).
    + move : Hkkh => /eqP Hkkh. split => //.
      move => /(_ vh). rewrite Hkkh. tauto.
    + rewrite IH. move : Hkkh => /eqP Hkkh. split => Hallin v.
      * move => [[Heq] | Hc]. auto. by apply (Hallin v).
      * move => Hc. move: Hallin => /(_ v) Hor. apply Decidable.not_or in Hor. by apply (proj2 Hor).
Qed.

(*Add entry (k, v) to front of list*)
Definition add (k: K) (v: V) (a: assoc_list) : assoc_list :=
  (k, v) :: a.

Lemma add_uniq: forall (k: K) (v: V) (a: assoc_list),
  uniq (map fst a) ->
  get k a = None ->
  uniq (map fst (add k v a)).
Proof.
  move => k v a Huniq Hget. rewrite /add/=. apply /andP. split => //.
  case Hin: (k \in [seq i.1 | i <- a]) => //.
  move: Hin. rewrite -is_true_true in_mem_In in_map_iff => [[x [Hx1 Hin]]].
  move: Hx1 Hin. case : x => [k' v']/=-> => Hin.
  rewrite get_none in Hget. exfalso. by apply (Hget v').
Qed.

Lemma add_in_same: forall (k: K) (v: V) (a: assoc_list) (v': V),
  uniq (map fst a) ->
  get k a = None ->
  In (k, v') (add k v a) ->
  v = v'.
Proof.
  move => k v a v' Huniq Hget. rewrite /add /= => [[[Heq] // | Hin]].
  rewrite get_none in Hget. exfalso. by apply (Hget v').
Qed.

(*If (k, v1) is in list, update with (k, f v1). Otherwise, add (k, v) to list*)
Definition update_or_add' (k: K) (v: V) (f: V -> V) (a: assoc_list) : assoc_list :=
  match (get k a) with
  | None => add k v a
  | Some _ => updateWith k f a
  end.

Lemma update_or_add_same': forall (k: K) (v: V) (f: V -> V) (a: assoc_list) (v': V),
  uniq (map fst a) ->
  In (k, v') (update_or_add' k v f a) ->
  (exists oldV, In (k, oldV) a /\ v' = f oldV) \/
  (v' = v /\ (forall oldV, ~In(k, oldV) a)).
Proof.
  move => k v f a v' Huniq. rewrite /update_or_add'. case Hget : (get k a) => [vd | ].
  - move => Hin. apply (updateWith_same Huniq) in Hin. by left.
  - move => Hin. apply (add_in_same Huniq Hget) in Hin. right. split => //.
    by apply get_none.
Qed.

Lemma update_or_add_diff': forall (k: K) (v: V) (f: V -> V) (a: assoc_list) k' v',
  k != k' ->
  In (k', v') (update_or_add' k v f a) <->
  In (k', v') a.
Proof.
  move => k v f a k' v' Hkk'. rewrite /update_or_add'. case Hget: (get k a) => [vd |].
  - by apply updateWith_diff.
  - rewrite /add/=. split.
    + move => [[Heq] | Hin //]. move: Hkk'. by rewrite Heq eq_refl.
    + move => Hin. by right.
Qed.

Lemma update_or_add_uniq: forall (k: K) (v: V) (f: V -> V) (a: assoc_list),
  uniq (map fst a) ->
  uniq (map fst (update_or_add' k v f a)).
Proof.
  move => k v f a. rewrite /update_or_add' /=. case Hget : (get k a).
  - by rewrite -updateWith_keys.
  - move => Huniq. by apply add_uniq.
Qed.

Lemma update_or_add_exists': forall (k: K) (v: V) (f: V -> V) (a: assoc_list),
  uniq (map fst a) -> (*technically don't need but makes proofs easier*)
  exists v', In (k, v') (update_or_add' k v f a).
Proof.
  move => k v f a Huniq. rewrite /update_or_add'. case Hget: (get k a) => [d |].
  - rewrite (get_some _ _ Huniq) in Hget. have: k \in map fst a. { rewrite in_mem_In in_map_iff. by exists (k, d). }
    rewrite (updateWith_keys k f a) in_mem_In in_map_iff => [[[k1 v1]/= [Hk Hin]]]. rewrite Hk in Hin.
    by exists v1.
  - rewrite /add. exists v. by left.
Qed.

(*Now we should package this into a nicer association list that has uniq keys*)

Inductive alist := Alist (al: assoc_list) of (uniq (map fst al)).
Coercion al (a: alist) : list (K * V) := let: Alist x _ := a in x.
Definition al_uniq (a: alist) : uniq (map fst a) := let :Alist _ x := a in x.
Canonical alist_subType := [subType for al].

Definition empty : alist := Alist empty_uniq.
Definition update_or_add (k: K) (v: V) (f: V -> V) (a: alist) : alist :=
  Alist (update_or_add_uniq k v f (al_uniq a)).

(*Now, we provide lemmas for export*)
Lemma update_or_add_same: forall (k: K) (v: V) (f: V -> V) (a: alist) (v': V),
  In (k, v') (update_or_add k v f a) ->
  (exists oldV, In (k, oldV) a /\ v' = f oldV) \/
  (v' = v /\ (forall oldV, ~In(k, oldV) a)).
Proof.
  move => k v f a v' Hin. apply update_or_add_same'. apply (al_uniq a).
  by [].
Qed.

Lemma update_or_add_diff: forall (k: K) (v: V) (f: V -> V) (a: alist) k' v',
  k != k' ->
  In (k', v') (update_or_add k v f a) <->
  In (k', v') a.
Proof.
  move => k v f a k' v'.
  apply update_or_add_diff'.
Qed.

Lemma update_or_add_exists: forall (k: K) (v: V) (f: V -> V) (a: alist),
  exists v', In (k, v') (update_or_add' k v f a).
Proof.
  move => k v f a. apply update_or_add_exists'. apply (al_uniq a).
Qed.

End AssocList.

Opaque update_or_add.

(*A valid stream of packets that will eventually produce well-formed blocks*)
Definition wf_packet_stream (l: list fec_packet_act) :=
  (forall (p1 p2 : fec_packet_act), p1 \in l -> p2 \in l -> 
    fd_blockId p1 = fd_blockId p2 -> fd_k p1 = fd_k p2 /\ fd_h p1 = fd_h p2) /\
  (forall (p1 p2: fec_packet_act), p1 \in l -> p2 \in l -> 
    fd_blockId p1 = fd_blockId p2 -> fd_blockIndex p1 = fd_blockIndex p2 -> p1 = p2) /\
  (forall (p: fec_packet_act), p \in l -> 0 <= Int.unsigned (fd_blockIndex p) < fd_k p + fd_h p).

Lemma wf_packet_stream_tl: forall h t,
  wf_packet_stream (h :: t) ->
  wf_packet_stream t.
Proof.
  move => h t. rewrite /wf_packet_stream => [[Hkh [Huniq Hidx]]].
  split; [|split].
  - move => p1 p2 Hp1 Hp2. apply Hkh; rewrite in_cons. by rewrite Hp1 orbT. by rewrite Hp2 orbT.
  - move => p1 p2 Hp1 Hp2. apply Huniq; rewrite in_cons. by rewrite Hp1 orbT. by rewrite Hp2 orbT.
  - move => p Hp. apply Hidx. by rewrite in_cons Hp orbT.
Qed. 

(*This implies the following useful condition*)
Lemma wf_all_nonneg: forall (l: list fec_packet_act),
  wf_packet_stream l ->
  (forall (x: fec_packet_act), x \in l -> 0 <= fd_k x + fd_h x).
Proof.
  move => l [_ [_ Hbounds]] x Hinx. move: Hbounds => /(_ x Hinx). lia.
Qed. 

(*Here, we reason about the lists for each block, not the full structure*)
Section BlockList.

Definition block_list := alist int_eqType (list (option fec_packet_act)).

(*Packet should have same blockId*)
Definition update_packet_list (p: fec_packet_act) (l: list (option fec_packet_act)) :=
  upd_Znth (Int.unsigned (fd_blockIndex p)) l (Some p).

Definition new_packet_list (p: fec_packet_act) : list (option fec_packet_act) :=
  upd_Znth (Int.unsigned (fd_blockIndex p)) (zseq (fd_k p + fd_h p) None) (Some p).

Definition update_block_list (idx: int) (p: fec_packet_act) (b: block_list) :=
  update_or_add idx (new_packet_list p) (update_packet_list p) b.

(*Use this to get lists for each block*)
Definition get_block_lists (l: list fec_packet_act) : block_list :=
  foldr (fun (p: fec_packet_act) acc => update_block_list (fd_blockId p) p acc) (@empty _ _) l.

(*Theorems about this*)

(*TODO: move block stuff to different file probably*)
(*The above function is unwieldy to use directly for all the theorems we need. Instead, we give 5 
  conditions that (get_blocks l) satisfies. Then we prove that any 2 lists that satisfy these 5
  conditions are equal up to permutation. With only 1 exception (TODO: ensure), we will only need
  these 5 conditions for all subsequent proofs; it is much nicer than needing induction and to
  reason about association lists for everything*)

(*Prop1: Every packet in the input belongs to some (unique, as we will show) list in the output. We need this
  first to prove the second property*)
Lemma get_blocks_list_allin: forall (l: list fec_packet_act) (p: fec_packet_act),
  In p l ->
  exists pkts, In (fd_blockId p, pkts) (get_block_lists l).
Proof.
  move => l p. rewrite /get_block_lists. elim : l => [//= | h t /=].
  rewrite /update_block_list => IH. move => Hor.
  case Hhp: (fd_blockId h == fd_blockId p).
  - move: Hhp => /eqP Hhp. rewrite Hhp. apply update_or_add_exists.
  - move: Hhp => /eqP Hhp. case : Hor => [Heq // | Hin]. by rewrite Heq in Hhp.
    setoid_rewrite update_or_add_diff; last first. by apply /eqP.
    by apply IH.
Qed.

(*We need a few auxilliary lemmas to prove the rest*)

(*This will follow from later propositions, but we need it now first*)
Lemma get_blocks_list_from_src: forall (l: list fec_packet_act) (i: int) (pkts: list (option (fec_packet_act)))
  (p: fec_packet_act),
  (forall (x: fec_packet_act), x \in l -> 0 <= fd_k x + fd_h x) ->
  In (i, pkts) (get_block_lists l) ->
  In (Some p) pkts ->
  In p l.
Proof.
  move => l i pkts p. move: pkts. elim : l => [//= | h t /=].
  rewrite /update_block_list. move => IH pkts Hbound.
  case: (Int.eq_dec i (fd_blockId h)) => [Hih | Hih].
  - rewrite -Hih/=. move => Hin. apply update_or_add_same in Hin.
    case : Hin => [[oldV [Hin Hpkts]] | [Hpkts Hnotin]].
    + rewrite Hpkts. rewrite /update_packet_list. move => Hinp.
      apply In_upd_Znth in Hinp. case : Hinp => [[Hhp] // | Hinp]. by left.
      right. apply (IH oldV) => //. move => x Hinx. apply Hbound. by rewrite in_cons Hinx orbT.
    + rewrite Hpkts /new_packet_list => Hin. apply In_upd_Znth in Hin.
      case : Hin => [[Hinp] // | Hinp]. by left. move: Hinp.
      have H0kh: 0 <= fd_k h + fd_h h. apply Hbound. by rewrite in_cons eq_refl.
      rewrite In_Znth_iff zseq_Zlength // => [[j [Hj Hnth]]]. 
      by rewrite zseq_Znth in Hnth.
  - move => Hin. apply update_or_add_diff in Hin; last first. rewrite eq_sym. by apply /eqP. 
    move => Hinp. right. apply (IH pkts) => //. move => x Hinx. apply Hbound. by rewrite in_cons Hinx orbT.
Qed.

(*1.5: all lists are nonempty; this element also has the same blockId and can be used to calculate the length*)
Lemma get_blocks_list_nonempty: forall (l: list fec_packet_act) (i: int) (pkts: list (option (fec_packet_act))),
  wf_packet_stream l ->
  In (i, pkts) (get_block_lists l) ->
  exists (p: fec_packet_act), In (Some p) pkts /\ fd_blockId p = i /\ Zlength pkts = fd_k p + fd_h p.
Proof.
  move => l i. elim : l => [//= | h t /=].
  rewrite /update_block_list. move => IH pkts Hwf. 
  case: (Int.eq_dec i (fd_blockId h)) => [Hih | Hih].
  - rewrite -Hih/=. move => Hin. apply update_or_add_same in Hin.
    case : Hin => [[oldV [Hin Hpkts]] | [Hpkts Hnotin]].
    + have Hin':=Hin. apply IH in Hin => //; last first. by apply (wf_packet_stream_tl Hwf).
      case : Hin => [p [Hinp [Hidp Hlenp]]]. rewrite Hpkts /update_packet_list Zlength_upd_Znth.
      have Hinpt: p \in t. { rewrite in_mem_In. apply (@get_blocks_list_from_src t i oldV) => //.
        apply wf_all_nonneg. apply (wf_packet_stream_tl Hwf). } 
      exists h. have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. {
        move: Hwf; rewrite /wf_packet_stream => [[Hkh _]].
        apply Hkh. by rewrite in_cons Hinpt orbT. by rewrite in_cons eq_refl.
        by rewrite -Hih Hidp. }
      repeat split => //; try lia. apply upd_Znth_In. move: Hwf.
      rewrite /wf_packet_stream => [[_ [_ /(_ h)]]]. rewrite in_cons eq_refl/= => Hb.
      rewrite Hlenp Hk Hh. by apply Hb.
    + rewrite Hpkts /new_packet_list. exists h.
      have Hbound: 0 <= Int.unsigned (fd_blockIndex h) < fd_k h + fd_h h. {
        move: Hwf; rewrite /wf_packet_stream => [[_ [_ /(_ h)]]]. rewrite in_cons eq_refl/= => Hb.
        by apply Hb. }
      repeat split => //. 2: rewrite upd_Znth_Zlength zseq_Zlength.
      apply upd_Znth_In. rewrite zseq_Zlength. all: lia.
  - move => Hin. apply update_or_add_diff in Hin; last first. by rewrite eq_sym; apply /eqP.
    apply IH => //. by apply (wf_packet_stream_tl Hwf).
Qed.

(*Prop2: All lists are nonempty (each contains at least 1 packet). We need extra information which will be
  useful later, so we first prove a larger auxilliary lemma. We just proved a stronger version of this*)

(*Prop3: for every entry in the block list, its length is k+h for ANY packet in it*)
Lemma get_blocks_lists_lens: forall (l: list fec_packet_act) (i: int) (pkts: list (option (fec_packet_act)))
  (p: fec_packet_act),
  wf_packet_stream l ->
  In (i, pkts) (get_block_lists l) ->
  In (Some p) pkts ->
  Zlength pkts = (fd_k p + fd_h p).
Proof.
  move => l i pkts p. move: pkts p. elim : l => [//= | h t /=].
  rewrite /update_block_list. move => IH pkts p Hwf.
  case: (Int.eq_dec i (fd_blockId h)) => [Hih | Hih].
  - rewrite -Hih/=. move => Hin. apply update_or_add_same in Hin.
    case : Hin => [[oldV [Hin Hpkts]] | [Hpkts Hnotin]].
    + rewrite Hpkts /update_packet_list Zlength_upd_Znth => Hinp.
      apply In_upd_Znth in Hinp. case : Hinp => [[Hhp] | Hinp].
      * rewrite Hhp.
        have Hin':=Hin.
        apply get_blocks_list_nonempty in Hin; last first. by apply (wf_packet_stream_tl Hwf).
        case : Hin => [p' [Hinp' [Hidp' Hlenold]]]. rewrite Hlenold.
        have [Hk Hh]: fd_k p' = fd_k h /\ fd_h p' = fd_h h. { have Hwf':=Hwf.
          move: Hwf' => [Hkh [_ Hbounds]]. apply Hkh.
          - rewrite in_cons. have->: p' \in t; last first. by rewrite orbT.
            rewrite in_mem_In. eapply (get_blocks_list_from_src).
            apply wf_all_nonneg. apply (wf_packet_stream_tl Hwf).
            apply Hin'. by [].
          - by rewrite in_cons eq_refl.
          - by rewrite Hidp'. }
        by rewrite Hk Hh.
      * apply IH => //. by apply (wf_packet_stream_tl Hwf).
    + have H0kh: 0 <= fd_k h + fd_h h. move: Hwf => [_[_ Hbound]].
        have: 0 <= Int.unsigned (fd_blockIndex h) < fd_k h + fd_h h. apply Hbound. by rewrite in_cons eq_refl. lia.
      rewrite Hpkts /new_packet_list Zlength_upd_Znth zseq_Zlength // => Hin.
      apply In_upd_Znth in Hin. move: Hin => [[Hph] |]. by rewrite Hph.
      rewrite In_Znth_iff zseq_Zlength //. move => [j [Hj Hnth]].
      by rewrite zseq_Znth in Hnth.
  - move => Hin. rewrite update_or_add_diff in Hin; last first. rewrite eq_sym. by apply /eqP.
    apply IH => //. apply (wf_packet_stream_tl Hwf).
Qed.

(*Prop3: For every entry in the block list, we give the list explicitly: (this is the most important one)*)
Lemma get_block_lists_in: forall (l: list fec_packet_act) (i: int) (pkts: list (option (fec_packet_act))),
  wf_packet_stream l ->
  In (i, pkts) (get_block_lists l) ->
  pkts = mkseqZ (fun j => 
    pickSeq (fun (p': fec_packet_act) => (fd_blockId p' == i) &&
      Z.eq_dec j (Int.unsigned (fd_blockIndex p'))) l) (Zlength pkts).
Proof.
  move => l i pkts. move: pkts. elim : l => [//=| h t /=].
  rewrite /update_block_list. move => IH pkts Hwf. case: (Int.eq_dec i (fd_blockId h)) => [Hih | Hih].
  - rewrite -Hih eq_refl /=. move => Hin. apply update_or_add_same in Hin.
    case : Hin => [[oldV [Holdv Hpkts]] | Hnew].
    + have Holdv':=Holdv. apply IH in Holdv.
      * rewrite {1}Hpkts Holdv /update_packet_list. 
        (*To show these are equal, we will compare element-wise*)
        have Hnonneg: 0 <= Zlength oldV by list_solve.
        have Hlens: Zlength oldV = Zlength pkts. { rewrite Hpkts. rewrite /update_packet_list. list_solve. }
        apply Znth_eq_ext; rewrite Zlength_upd_Znth !mkseqZ_Zlength //. list_solve.
        move => j Hj. rewrite mkseqZ_Znth; [|lia]. rewrite (upd_Znth_lookup' (Zlength oldV)); try lia. 
        rewrite mkseqZ_Znth; try lia.
        by case : (Z.eq_dec j (Int.unsigned (fd_blockIndex h))). rewrite mkseqZ_Zlength. lia. list_solve.
        (*to prove length, we use fact that there is some element there*)
        have Holdv'':=Holdv'.
        apply get_blocks_list_nonempty in Holdv'; last first.
          apply (wf_packet_stream_tl Hwf).
        case : Holdv' => [p [Hinp [Hpid Holdlen]]].
        rewrite Holdlen. have Hwf':=Hwf. move: Hwf' => [Hkh [_ Hbounds]].
        have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. { apply Hkh.
          rewrite in_cons. have->: p \in t; last first. by apply orbT.
          rewrite in_mem_In. eapply get_blocks_list_from_src. apply wf_all_nonneg.
          apply (wf_packet_stream_tl Hwf). apply Holdv''. by []. by rewrite in_cons eq_refl.
          by rewrite Hpid. }
        rewrite Hk Hh. apply Hbounds. by rewrite in_cons eq_refl.
      * apply (wf_packet_stream_tl Hwf).
    + case : Hnew => [Hpkts Hnotin].
      have Hidxb: 0 <= Int.unsigned (fd_blockIndex h) < fd_k h + fd_h h. {
        move: Hwf => [_ [_ Hbounds]]. apply Hbounds. by rewrite in_cons eq_refl. }
      rewrite Hpkts /new_packet_list Zlength_upd_Znth zseq_Zlength; try lia.
      (*once again, compare elementwise*)
      apply Znth_eq_ext; rewrite Zlength_upd_Znth zseq_Zlength; try lia.
      rewrite mkseqZ_Zlength; lia. move => j Hj.
      rewrite mkseqZ_Znth // (upd_Znth_lookup' (fd_k h + fd_h h)) //; last first.
        rewrite zseq_Zlength; lia.
      case (Z.eq_dec j (Int.unsigned (fd_blockIndex h))) => Hjh//=.
      rewrite zseq_Znth; try lia.
      (*contradiction: we know no packets can exist in tail, so pickSeq must be None*)
      have Hpick:= 
        (pickSeqP (fun p' : fec_packet_act => (fd_blockId p' == i) && Z.eq_dec j (Int.unsigned (fd_blockIndex p'))) t).
      case: Hpick => [x Hinx /andP[/eqP Hxid Hjx] |//]. rewrite in_mem_In in Hinx.
      apply get_blocks_list_allin in Hinx. case : Hinx => [pkts' Hpkts']. exfalso.
      apply (Hnotin pkts'). by rewrite -Hxid.
  - move => Hin. apply update_or_add_diff in Hin. apply IH in Hin.
    + rewrite Hin. rewrite mkseqZ_Zlength; [|list_solve]. 
      have->//=: (fd_blockId h == i) = false. apply /eqP. auto.
    + by apply (wf_packet_stream_tl Hwf).
    + apply /eqP. auto.
Qed.

(*Prop4: The output list is unique by blockId*)
Lemma get_blocks_list_uniq: forall (l: list fec_packet_act),
  uniq (map fst (get_block_lists l)).
Proof.
  move => l. elim : l => [//= | h t /= IH].
  rewrite /update_block_list. apply al_uniq.
Qed.

(*We bundle these into a single relation*)
Definition get_block_lists_prop (l: list fec_packet_act) (blks: block_list) : Prop :=
  (forall (p: fec_packet_act), In p l -> exists pkts, In (fd_blockId p, pkts) blks) /\
  (forall (i: int) (pkts: list (option (fec_packet_act))),
    In (i, pkts) blks -> exists (p: fec_packet_act), In (Some p) pkts) /\
  (forall (i: int) (pkts: list (option (fec_packet_act))) (p: fec_packet_act),
    In (i, pkts) blks -> In (Some p) pkts -> Zlength pkts = (fd_k p + fd_h p)) /\
  (forall (i: int) (pkts: list (option (fec_packet_act))),
    In (i, pkts) blks -> pkts = mkseqZ (fun j => 
    pickSeq (fun (p': fec_packet_act) => (fd_blockId p' == i) &&
      Z.eq_dec j (Int.unsigned (fd_blockIndex p'))) l) (Zlength pkts)) /\
  uniq (map fst blks).

Lemma get_block_lists_spec: forall (l: list fec_packet_act),
  wf_packet_stream l ->
  get_block_lists_prop l (get_block_lists l).
Proof.
  move => l Hwf. repeat split.
  - apply get_blocks_list_allin.
  - move => i pkts Hin. apply get_blocks_list_nonempty in Hin => //. case : Hin => [p [Hinp _]].
    by exists p.
  - move => i pkts p. by apply get_blocks_lists_lens.
  - move => i pkts. by apply get_block_lists_in.
  - apply get_blocks_list_uniq.
Qed.

(*Now we want to show that if we have any two lists satisfying [get_block_lists_prop], then they are
  unique up to permutation*)

(*Do all the hard work here, so we don't have to repeat twice*)
Lemma get_block_lists_prop_in: forall (l: list fec_packet_act) (blks1 blks2 : block_list) b,
  wf_packet_stream l ->
  get_block_lists_prop l blks1 ->
  get_block_lists_prop l blks2 ->
  b \in (al blks1) ->
  b \in (al blks2).
Proof.
  move => l b1 b2 b Hwf [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]] [Hallin2 [Hnonemp2 [Hlen2 [Heq2 Huniq2]]]] Hin1.
  move: Hin1. rewrite in_mem_In. case: b => [i1 pkts1] Hin1.
  have Hpkts1:=Hin1. apply Heq1 in Hpkts1. 
  (*Idea: get packet from pkts1, it must have id i and it must be in l, so there must be some pkts2
    such that (i, pkts2) is in b2. But by the equality lemma, pkts2 = pkts1*)
  have Hin1':=Hin1. apply Hnonemp1 in Hin1'. case: Hin1' => [p Hinp].
  have [Hidp Hinlp]: fd_blockId p = i1 /\ In p l. {
    move: Hinp. rewrite Hpkts1. rewrite In_Znth_iff mkseqZ_Zlength; [|list_solve].
    move => [i [Hi Hith]]. move: Hith. rewrite mkseqZ_Znth //.
    have Hpick:= 
        (pickSeqP (fun p' : fec_packet_act => (fd_blockId p' == i1) && 
            Z.eq_dec i (Int.unsigned (fd_blockIndex p'))) l).
    case: Hpick => [x Hinx /andP[/eqP Hxid _] [Hxp] | //].
    rewrite -Hxp. split => //. by rewrite -in_mem_In. }
  have Hinlp':=Hinlp. apply Hallin2 in Hinlp'.
  case Hinlp' => [pkts2 Hin2].
  rewrite Hidp in Hin2. have Hpkts2:=Hin2.
  apply Heq2 in Hpkts2. rewrite in_mem_In.
  (*only thing left- show lengths are same*) 
  have->//: pkts1 = pkts2. rewrite Hpkts1 Hpkts2. f_equal.
  rewrite (Hlen1 _ _ _ Hin1 Hinp). 
  have Hin2' := Hin2. apply Hnonemp2 in Hin2'. case : Hin2' => [p2 Hinp2].
  (*Now we have to know that id is same again - TODO: can we reduce duplication?*)
  have [Hidp2 Hinlp2]: fd_blockId p2 = i1 /\ In p2 l. {
    move: Hinp2. rewrite Hpkts2. rewrite In_Znth_iff mkseqZ_Zlength; [|list_solve].
    move => [i [Hi Hith]]. move: Hith. rewrite mkseqZ_Znth //.
    have Hpick:= 
        (pickSeqP (fun p' : fec_packet_act => (fd_blockId p' == i1) && 
            Z.eq_dec i (Int.unsigned (fd_blockIndex p'))) l).
    case: Hpick => [x Hinx /andP[/eqP Hxid _] [Hxp] | //].
    rewrite -Hxp. split => //. by rewrite -in_mem_In. }
  rewrite (Hlen2 _ _ _ Hin2 Hinp2).
  have [Hk Hh]: fd_k p = fd_k p2 /\ fd_h p = fd_h p2. {
    move: Hwf => [Hkh _]. apply Hkh. by apply in_mem_In. by apply in_mem_In.
    by rewrite Hidp Hidp2. }
  by rewrite Hk Hh.
Qed.

Lemma get_block_lists_prop_perm: forall (l: list fec_packet_act) (blks1 blks2 : block_list),
  wf_packet_stream l ->
  get_block_lists_prop l blks1 ->
  get_block_lists_prop l blks2 ->
  perm_eq blks1 blks2.
Proof.
  move => l b1 b2 Hwf [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]] [Hallin2 [Hnonemp2 [Hlen2 [Heq2 Huniq2]]]].
  apply uniq_perm. apply (map_uniq Huniq1). apply (map_uniq Huniq2).
  move => b. 
  case Hin1: (b \in (al b1)); symmetry.
  - move: Hin1. rewrite -!is_true_true. by apply (get_block_lists_prop_in Hwf).
  - case Hin2: (b \in (al b2)) => //. move: Hin2. rewrite -is_true_true => Hin2.
    apply (@get_block_lists_prop_in l b2 b1 b Hwf) in Hin2 => //. by rewrite Hin1 in Hin2.
Qed.

End BlockList.

