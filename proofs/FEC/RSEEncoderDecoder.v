(*Implement the abstract encoder/decoder relations from AbstractEncoderDecoder with RSE algorithm *)
Require Import VST.floyd.functional_base.
Require Import EquivClasses.
Require Import AbstractEncoderDecoder.
Require Import ReedSolomonList.
Require Import ZSeq.
From mathcomp Require Import all_ssreflect.

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

Definition fec_packet_act_eq_axiom  := (fec_packet_eq_axiom fec_data_eq_dec).

Definition fec_packet_act_eqMixin := EqMixin fec_packet_act_eq_axiom.
Canonical fec_packet_act_eqType := EqType fec_packet_act fec_packet_act_eqMixin.

#[export]Instance packet_act_inhab : Inhabitant fec_packet_act := 
  mk_fecpkt packet_inhab fec_data_inhab.

(* Representing Blocks *)

Record block := mk_blk { blk_id: int;
  data_packets: list (option fec_packet_act); parity_packets: list (option fec_packet_act); blk_k : Z; blk_h : Z}.

(*Well-formed block *)
Definition block_wf (b: block) : Prop :=
  (*All packets store correct values of k and h*)
  (forall p, In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) -> 
    (fd_k (p_fec_data p)) = blk_k b /\ (fd_h (p_fec_data p)) = blk_h b) /\
  (*All packets have same blockId (TODO: is this needed?*)
  (forall p, In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) ->
    fd_blockId (p_fec_data p) = blk_id b) /\
  (*Packet sequence numbers are correct*)
  (forall p, In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) ->
    Znth (Int.unsigned (fd_blockIndex (p_fec_data p))) (data_packets b ++ parity_packets b) = Some p) /\
  (*Lengths are correct*)
  Zlength (data_packets b) = blk_k b /\
  Zlength (parity_packets b) = blk_h b.

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
                end) ((data_packets b) ++ (parity_packets b)).

Definition lengths (b: block) : list Z :=
  map (@Zlength byte) (packet_mx b) ++ 
  map (fun x => match x with | None => 0 | Some l => Zlength l end) (parity_mx b).

Definition num_receieved (b: block) : Z :=
  Zlength (filter isSome (data_packets b)) + Zlength (filter isSome (parity_packets b)).

(*Max of list of nonnegative integers*)
Definition list_max_nonneg {A: Type} (f: A -> Z) (l: list A) : Z :=
  fold_right (fun x y => Z.max (f x) y) (-1) l.


(*Get current value of c for the block. If block is not complete, this will be -1.
  It is OK to take max of only packet_contents because parities have Zlength (contents) = c
  and we only care about the value once a block is complete*)
Definition blk_c (b: block) : Z :=
  list_max_nonneg (fun o => match o with
                            | None => -1
                            | Some p => Zlength (p_contents (f_packet p))
                            end) (parity_packets b).

(*A block is complete (these imply that parities are nonempty if data is*)
(*TODO: could make bool, have to make bool (decidable) version of parities_valid*)
Definition block_complete (b: block) : Prop :=
  (*All parities have length c*)
  (forall p, In (Some p) (parity_packets b) -> Zlength (p_contents p) = blk_c b) /\
  (*All data packets (including headers) have length <= c*)
  (forall p, In (Some p) (data_packets b) -> Zlength (packet_bytes p) <= blk_c b) /\
  parities_valid (blk_k b) (blk_c b) (parity_mx b) (packet_mx b).

Definition isNone {A: Type} (o: option A) :=
  negb (isSome o).

Definition block_in_progress (b: block) : bool :=
  forallb isNone (parity_packets b).

(* Getting blocks from stream (encoded/received)*)

(*This is a bit complicated, since we want to filter by blockIndex, then build the block from this list.*)

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
  let k := get_val l (fun p => fd_k (p_fec_data p)) 0 in
  let h := get_val l (fun p => fd_h (p_fec_data p)) 0 in
  let id := list_int_min (fun p => p_seqNum (f_packet p)) l in
  let data := foldr 
    (fun p acc => upd_Znth (Int.unsigned (fd_blockIndex (p_fec_data p))) acc (Some p)) (zseq k None) l in
  let parities := foldr
    (fun p acc => upd_Znth (Int.unsigned (fd_blockIndex (p_fec_data p)) - k) acc (Some p)) (zseq h None) l in
  mk_blk id data parities k h.

(*Get the blocks from the stream *)
Definition get_blocks (l: list fec_packet_act) : list block :=
  let classes := equiv_classes (fun p => fd_blockIndex (p_fec_data p)) Int.eq_dec l in
  map build_block classes.

(*TODO: prove that get_blocks is invariant under permutation assuming that
  1. All packets with same blockIndex have same k
  2. All packets with same blockIndex have same h
  Then we can reason about permutation, not subseq*)

(*Finally, we can define the encoder predicate*)
Definition enc : (encoder fec_data) :=
  fun (orig : list packet) (encoded: list fec_packet_act) =>
    let blocks := (get_blocks encoded) in
    (*all blocks are valid*)
    Forall block_wf blocks /\
    (*all but the last are complete, the last may be in progress or complete*)
    match blocks with
    | nil => True
    | x :: t => Forall block_complete (belast x t) /\ 
      (block_complete (last x blocks) \/ block_in_progress (last x blocks))
    end /\
    (*If we concat all data packets, we get the original stream*)
    orig = concat (map (fun b => fold_right (fun x acc => match x with
                                                          | None => acc
                                                          | Some p => f_packet p :: acc
                                                          end) nil (data_packets b) ) blocks).

(*TODO: handle (i:Z) by finding value*)
Definition decoder_list_block (b: block) : list (list byte) :=
  (*blk_h is just a placeholder*)
  decoder_list (blk_k b) (blk_c b) (packet_mx b) (parity_mx b) (stats b) (lengths b) (blk_h b).

(*TODO: need to transform packet bytes back to packet (with IP fields, etc) - this will be annoying
  also may not need IP/UDP stuff here: see*)
Definition packet_from_bytes (l: list byte) : option (packet).
  (*assume this is IP packet: get header length from IP, know UDP header length, split into
    header and contents, put in packet
    return None if list empty or not long enough
    this isn't great because of bitwise ops but not much else we can do - need headers because
    difference between parity/data packets*)
Admitted.


(*Similarly, we can define the decoder predicate*)
Definition dec : (decoder fec_data) :=
  fun (received : list fec_packet_act) (decoded: list packet) =>
  let blocks := (get_blocks received) in
  (*Because of timeouts, some ill-formed blocks, etc, we give a weak spec: only that
    everything in decoded is either (a) from a data packet in receieved or (b)
    from the decoder_list of some block that is completed. We note that NOT every completed
    block is required or guaranteed to appear*)
  forall (p: packet), In p decoded ->
    (exists (fp: fec_packet_act), In fp received /\ (fd_isParity (p_fec_data fp)) /\
      f_packet fp = p) \/
    (exists (b: block) (i: Z), 0 <= i < (blk_k b) /\ In b blocks /\ 
      Some p = packet_from_bytes (Znth i (decoder_list_block b))). 