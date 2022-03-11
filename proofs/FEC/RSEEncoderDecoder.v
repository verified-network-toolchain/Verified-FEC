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

(** IP/UDP Packets *)
(*Here, we require our packets to be valid IP/UDP packets*)

Definition valid_fec_packet (header: list byte) (contents: list byte) :=
  valid_packet header contents.

(*Packet is defined to be valid according to IP/UDP*)
Definition packet_act := packet valid_packet.

(*An encodable packet has its length <= fec_max_c*)

Definition encodable (p: packet_act) : bool :=
  Z_le_lt_dec (Zlength ((p_header p) ++ (p_contents p))) fec_max_cols.

Definition enc_packet := encodable_packet encodable.

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

Definition fec_packet_act := fec_packet valid_packet fec_data.

Definition f_packet : fec_packet_act -> packet_act := (@p_packet valid_packet fec_data).

Coercion f_packet : fec_packet_act >-> packet_act.

Definition fec_packet_act_eq_axiom  := (@fec_packet_eq_axiom valid_packet _ fec_data_eq_dec).

Definition fec_packet_act_eqMixin := EqMixin fec_packet_act_eq_axiom.
Canonical fec_packet_act_eqType := EqType fec_packet_act fec_packet_act_eqMixin.
(*TODO: this if needed*)
(*
#[export]Instance packet_act_inhab : Inhabitant fec_packet_act := 
  mk_fecpkt packet_inhab fec_data_inhab.
*)
(** Representing Blocks *)

Record block := mk_blk { blk_id: int;
  data_packets: list (option fec_packet_act); parity_packets: list (option fec_packet_act); blk_k : Z; blk_h : Z;
  complete: bool}.

#[export]Instance eta_block: Settable _ := 
  settable! mk_blk <blk_id; data_packets; parity_packets; blk_k; blk_h; complete>.

(*Well-formed block *)
Definition block_wf (b: block) : Prop :=
  (*k and h are within the required bounds*)
  0 < blk_k b <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
  0 < blk_h b <= ByteFacts.fec_max_h /\
  (*All packets store correct values of k and h*)
  (forall p, In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) -> 
    (fd_k (p_fec_data p)) = blk_k b /\ (fd_h (p_fec_data p)) = blk_h b) /\
  (*All packets have same blockId (TODO: is this needed?*)
  (forall p, In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) ->
    fd_blockId (p_fec_data p) = blk_id b) /\
  (*Packet sequence numbers are correct*)
  (forall p (i: Z), 
    In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) ->
    Znth i (data_packets b ++ parity_packets b) = Some p <-> i = Int.unsigned (fd_blockIndex (p_fec_data p))) /\
  (*Lengths are correct*)
  Zlength (data_packets b) = blk_k b /\
  Zlength (parity_packets b) = blk_h b /\
  (*All data packets are encodable*)
  (forall p, In (Some p) (data_packets b) -> encodable p).

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
  forallb (fun o =>
    match o with
    | None => true
    | Some p => Z.eq_dec (fd_k (p_fec_data p)) (blk_k b) &&
                Z.eq_dec (fd_h (p_fec_data p)) (blk_h b) &&
                Int.eq_dec (fd_blockId (p_fec_data p)) (blk_id b) &&
                (Znth (Int.unsigned (fd_blockIndex (p_fec_data p))) (data_packets b ++ parity_packets b) == Some p) &&
                [ forall (x : 'I_(Z.to_nat (Zlength (data_packets b ++ parity_packets b))) |
                            nat_of_ord x != Z.to_nat (Int.unsigned (fd_blockIndex (p_fec_data p))) ),
                    Znth (Z.of_nat x) (data_packets b ++ parity_packets b) != Some p ]
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
  - move => [Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh Henc]]]]]]]. repeat (apply /andP; split); try solve_sumbool.
    + rewrite is_true_true forallb_forall => o. case: o => [p |//]. rewrite in_app_iff => Hin.
      repeat(apply /andP; split).
      * apply Hkh in Hin. solve_sumbool.
      * apply Hkh in Hin. solve_sumbool.
      * apply Hid in Hin. solve_sumbool.
      * apply (Hidx _ (Int.unsigned (fd_blockIndex (p_fec_data p)))) in Hin. apply /eqP. by apply Hin.
      * apply /forallP => x. apply /implyP => Hx.
        case: (Znth (Z.of_nat x) (data_packets b ++ parity_packets b) == Some p) /eqP => [Hnth|//].
        apply Hidx in Hnth. apply (f_equal Z.to_nat) in Hnth. rewrite Nat2Z.id in Hnth.
        move: Hx. by rewrite Hnth eq_refl. by [].
    + rewrite is_true_true forallb_forall => o. case: o => [p |//]. apply Henc.
  - move => /andP [/andP[/andP[/andP[/andP[Hhbound Hkbound] Hall] Hk] Hh] Henc].
    solve_sumbool. move: Hall. rewrite is_true_true forallb_forall => Hall.
    repeat split; try lia.
    + rewrite -in_app_iff in H. apply Hall in H. move: H => /andP[/andP[/andP[/andP [H _] _] _] _].
      by solve_sumbool.
    + rewrite -in_app_iff in H. apply Hall in H. move: H => /andP[/andP[/andP[/andP [_ H] _] _] _].
      by solve_sumbool.
    + move => p. rewrite -in_app_iff => Hin. apply Hall in Hin. move: Hin => /andP[/andP[/andP[_ H] _] _].
      by solve_sumbool.
    + rewrite -in_app_iff in H. apply Hall in H. move: H => /andP[_ Hp2].
      move => Hith.
      have Hi: 0 <= i < Zlength (data_packets b ++ parity_packets b). { apply Znth_inbounds.
        by rewrite Hith. }
      move: Hp2 => /forallP Hp2.
      case: (Z.eq_dec i (Int.unsigned (fd_blockIndex (p_fec_data p)))) => [//|Hneq].
      (*Now need to construct ordinal*)
      have Hibound: (Z.to_nat i < (Z.to_nat (Zlength (data_packets b ++ parity_packets b))))%N. {
        apply /ltP. lia. }
      move: Hp2 => /(_ (Ordinal Hibound))/= => /implyP Hp2. move: Hp2. rewrite Z2Nat.id; try lia. 
      rewrite Hith eq_refl /=. move => Hp2. have: false. apply Hp2.
        case : (Z.to_nat i == Z.to_nat (Int.unsigned (fd_blockIndex (p_fec_data p)))) /eqP => [Heq|//].
        apply Z2Nat.inj in Heq; try rep_lia. by [].
    + move->. rewrite -in_app_iff in H. apply Hall in H. by move: H => /andP[/andP[_ /eqP Hp1] _].
    + move: Henc. rewrite is_true_true forallb_forall => Henc p Hp. by apply Henc in Hp.
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
  mk_blk id data parities k h false.

(*Get the blocks from the stream *)
Definition get_blocks (l: list fec_packet_act) : list block :=
  let classes := equiv_classes (fun p => fd_blockIndex (p_fec_data p)) Int.eq_dec l in
  map build_block classes.

(*TODO: prove that get_blocks is invariant under permutation assuming that
  1. All packets with same blockIndex have same k
  2. All packets with same blockIndex have same h
  Then we can reason about permutation, not subseq*)

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
(*This bool is meant to represent if the fec parameters have changed*)

(*TODO: do with options instead and defer proofs until later? Then don't need messy dependent type?
  Would that make VST proofs harder?*)

(*To construct the packets for a block, we need a proof that each are valid. It would
  be extremely difficult to do this with just a generic map, so we give a custom, dependently-typed function*)
Definition populate_packets (id: int) (model : packet_act) (contents: list (list byte)) 
  (Hcon: forall l, In l contents -> Zlength l <= Short.max_unsigned - 68) : list packet_act.
induction contents as [| h t IH].
- apply nil.
- apply cons.
  + assert (Zlength (p_header model) + Zlength h <= Short.max_unsigned). {
      (*wont use lia because we dont want huge proof term - TODO: see*)
      replace (Short.max_unsigned) with (68 + (Short.max_unsigned - 68)) by reflexivity.
      apply Z.add_le_mono. destruct model. simpl.
      apply (header_bound _ _ p_valid).
      apply Hcon. left. reflexivity. }
    apply (mk_pkt id (@copy_fix_header_valid _ _ h H (p_valid model))).
  + apply IH. intros l Hinl. apply Hcon. right. apply Hinl.
Defined.

Lemma red_block_bound: forall (b: block),
  block_in_progress b = true ->
  block_wf b ->
  blk_c b <= fec_max_cols.
Proof.
  move => b. 
  rewrite /block_in_progress /block_wf => [Hprog [Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh Henc]]]]]]]].
  rewrite /blk_c.
  case Hpars: [seq x <- parity_packets b | isSome x] => [/= | h t /=]; last first.
    have: h \in [seq x <- parity_packets b | isSome x] by rewrite Hpars in_cons eq_refl orTb.
    rewrite mem_filter => /andP[Hhsome Hinpar].
    have: isNone h. { have Hall: forallb isNone (parity_packets b) = true by rewrite Hprog. 
      rewrite forallb_forall in Hall. by rewrite Hall // -in_mem_In. } by rewrite /isNone Hhsome.
  apply list_max_nonneg_ub. rep_lia.
  move => y. case: y => [p Hinp | //]; [|rep_lia].
  apply Henc in Hinp. move: Hinp. rewrite /encodable.
  by case: (Z_le_lt_dec (Zlength (p_header (f_packet p) ++ p_contents (f_packet p))) fec_max_cols).
Qed.

Lemma red_block_bound': forall (b: block),
  block_in_progress b = true ->
  block_wf_bool b = true ->
  blk_c b <= fec_max_cols.
Proof.
  move => b Hprog /block_wf_bool_reflect Hb. by apply red_block_bound.
Qed.

(*TODO: move this section*)
Require Import mathcomp.algebra.ssralg.
Section ToMove.

(*TODO: move to ListMatrix*)
Lemma mk_lmatrix_In: forall {F: fieldType} (m n : Z) (f: Z -> Z -> F) (l: seq F),
  0 <= n -> 0 <= m ->
  In l (ListMatrix.mk_lmatrix m n f) -> Zlength l = n.
Proof.
  move => F m n f l Hn Hm. rewrite /ListMatrix.mk_lmatrix In_Znth_iff => [[i [Hi Hith]]].
  rewrite -Hith mkseqZ_Znth. rewrite mkseqZ_Zlength; lia. move: Hi. rewrite mkseqZ_Zlength; lia.
Qed.

(*Now we can give the proof that we need*)
Lemma parities_bound: forall (b: block) (Hp: block_in_progress b = true) (Hwf: block_wf_bool b = true),
  forall (l: seq byte), In l (encoder_list (blk_h b) (blk_k b) (blk_c b) (packet_mx b)) -> 
    Zlength l <= Short.max_unsigned - 68.
Proof.
  move => b Hprog Hwf l. rewrite /encoder_list /ListMatrix.lmatrix_multiply => Hin.
  apply (@mk_lmatrix_In ByteField.byte_fieldType) in Hin.
  - rewrite Hin. eapply Z.le_trans. apply red_block_bound'; by []. rep_lia'.
  - apply blk_c_nonneg.
  - move: Hwf => /block_wf_bool_reflect Hwf.
    move: Hwf. rewrite /block_wf. lia.
Qed.

(*Finally, we can define what it means to encode a block with a model*)
Definition encode_block_aux (b: block) (model: packet_act) :=
  let packetsNoFec :=
    (match (block_in_progress b) as b1 return (block_in_progress b = b1 -> list packet_act) with
    | false => fun _ => nil
    | true => fun H1 =>
        (match (block_wf_bool b) as b2 return (block_wf_bool b = b2 -> list packet_act) with
        | false => fun _ => nil
        | true => fun H2 => populate_packets (blk_id b) model (parities_bound H1 H2)
        end) (erefl)
    end) (erefl) in
  (*make the FEC packets*)
  map_with_idx packetsNoFec (fun p i => 
    mk_fecpkt p (mk_data (blk_k b) (blk_h b) true (blk_id b) (Int.repr ((blk_k b) + i)))).

(*Encoding a block chooses an appropriate model packet - either the inputted packet
  or the last packet in the block*)
Definition encode_block (b: block) (o: option packet_act) : list fec_packet_act :=
  match (pmap id (data_packets b)), o with
  | nil, None => nil (*can't happen*)
  | _, Some p => encode_block_aux b p
  | h :: t, _ => encode_block_aux b (f_packet (last h (h :: t)))
  end.

(*From here, we need a few utility functions for block so we can create the encoder predicate*)
Definition get_fec_packet (p: packet_act) (b: block) : fec_packet_act :=
   mk_fecpkt p (mk_data (blk_k b) (blk_h b) false (blk_id b) (Int.sub (p_seqNum p) (blk_id b))).

Definition new_fec_packet (p: packet_act) (k: Z) (h: Z) : fec_packet_act :=
  mk_fecpkt p (mk_data k h false (p_seqNum p) Int.zero).

Definition add_packet_to_block_red (p: packet_act) (b: block) : block :=
  let f := get_fec_packet p b in
  b <| data_packets := upd_Znth (Int.unsigned (fd_blockIndex (p_fec_data f))) (data_packets b) (Some f) |>.

Definition new_block_packet (p: packet_act) (k: Z) (h: Z) : block :=
  let f := new_fec_packet p k h in
  mk_blk (p_seqNum p) (upd_Znth 0 (zseq k None) (Some f)) (zseq h None) k h false.

(** Encoder predicate*)

(*We will write our encoder first as a function (with inputted k and h), then write the predicate, where
  we quantify over k and h*)
Definition rse_encode_func (orig: list enc_packet) (encoded: list fec_packet_act) (curr: enc_packet)
  (k h: Z) : list fec_packet_act :=

  (*For the situations when we start a new block*)
  let encode_new (e: enc_packet) (k' h': Z) :=
    new_fec_packet (e_packet e) k' h' ::
    if Z.eq_dec k' 1 then (encode_block (new_block_packet (e_packet e) k' h') (Some (e_packet e))) else nil
  in

  (*For the situation when we add to an existing block*)
  let encode_exist (e: enc_packet) (b: block) :=
    let newBlock := add_packet_to_block_red (e_packet e) b in
    get_fec_packet (e_packet e) b ::
    if Z.eq_dec (Zlength (filter isSome (data_packets newBlock))) (blk_k newBlock) then
      encode_block newBlock (Some (e_packet e)) else nil
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
          [get_fec_packet (e_packet curr) b]
      in
    init ++ newPackets
    end.

(*The final predicate is simple*)

Definition rse_encoder : (@encoder valid_packet encodable fec_data) :=
  fun (orig: list enc_packet) (encoded: list fec_packet_act) (curr: enc_packet) (new: list fec_packet_act) =>
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

(*TODO: NOTE: in black actuator, does NOT regenerate sequence number, but we know what it should be
  based on blockIndex and blockSeq*)
Definition packet_from_bytes (l: list byte) (i: int) : option(packet_act) :=
  let (header, contents) := recover_packet l in
  (match (valid_packet header contents) as v 
    return (valid_packet header contents) = v -> option (packet valid_packet) with
  | true => fun H => Some (mk_pkt i H)
  | false => fun _ => None
  end) Logic.eq_refl.

(*If the block is well-formed, all the packets will be valid. But we prove this later*)
Definition decode_block (b: block) : list packet_act :=
  (*Only add missing packets*)
  foldl (fun acc i => if isNone (Znth i (data_packets b)) then 
                      match (packet_from_bytes (Znth i (decoder_list_block b)) Int.zero) with
                      | Some p => acc ++ [p]
                      | None => acc
                      end else acc) nil (Ziota 0 (blk_c b)).

(*TODO: have to deal with deduce headers once I hear back from Peraton people*)

(*Now we define the different parts, we want several functions that update state (blocks) and give packets to return*)

(*TODO: need to deal with isParity/ordering issue - here we assume that issue doesnt exist*)

(*1. create block with packet*)
Definition create_block_with_packet (p: fec_packet_act) : block * list packet_act :=
  let k := fd_k (p_fec_data p) in
  let h := fd_h (p_fec_data p) in
  let allPackets := upd_Znth (Int.unsigned (fd_blockIndex (p_fec_data p))) (zseq (k + h) None) (Some p) in
  let new_block := mk_blk (fd_blockId (p_fec_data p)) (sublist 0 k allPackets) (sublist k (k+h) allPackets) k h false in
  let packets := (if (fd_isParity (p_fec_data p)) then nil else [p_packet p]) ++
    (if Z.eq_dec k 1 then (decode_block new_block) else nil) in
  let marked_block := if Z.eq_dec k 1 then new_block <| complete := true |> else new_block in
  (marked_block, packets).

(*2. add packet to block*)
Definition add_packet_to_block_black (p: fec_packet_act) (b: block) : block * list packet_act :=
  if complete b then (b, nil) else (*TODO: if this is a data packet, should it still be released?*)
    let new_packets := upd_Znth (Int.unsigned (fd_blockIndex (p_fec_data p))) (data_packets b ++ parity_packets b) (Some p) in
    let new_block := b <| data_packets := sublist 0 (blk_k b) new_packets |> 
      <| parity_packets := sublist (blk_k b) (blk_k b + blk_h b) new_packets |> in
    let packets := (if (fd_isParity (p_fec_data p)) then nil else [p_packet p]) ++
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
  (list block * list packet_act) :=
  match blocks, state with
  | bl :: tl, s :: stl =>
    if s && int_le (fd_blockIndex (p_fec_data curr)) (blk_id bl) then
      (tl, if fd_isParity (p_fec_data curr) then nil else [p_packet curr])
    else if Int.lt (fd_blockIndex (p_fec_data curr)) (blk_id bl) then
      let (b, l) := create_block_with_packet curr in
      (b :: blocks, l)
    else if Int.eq (fd_blockIndex (p_fec_data curr)) (blk_id bl) then
      let (b, l) := add_packet_to_block_black curr bl in
      (b :: tl, l)
    else
      let (bs, l) := update_past_blocks tl curr stl in
      (bl :: bs, l)
  | _ :: _, _ => (nil, nil) (*should never reach here*)
  | _, _ => (*not sure we can reach here - should prove*)
      (nil,  if fd_isParity (p_fec_data curr) then nil else [p_packet curr])
  end. 
  
(*TODO: move*)
Instance block_inhab: Inhabitant block :=
  mk_blk Int.zero nil nil 0 0 false.


(*We cannot build the blocks in 1 go since we must take into account timeouts. Instead, we build it up
  incrementally*)
Definition update_dec_state (blocks: list block) (curr: fec_packet_act) (state: list bool) : 
  (list block * list packet_act) :=
  match blocks with
  | nil => let (b, l) := create_block_with_packet curr in ([b], l)
  | bl :: tl => 
    let currBlock := Znth (Zlength blocks - 1) blocks in
    let currSeq := fd_blockIndex (p_fec_data curr) in
    if Int.eq currSeq (blk_id currBlock) then
      let (b, l) := add_packet_to_block_black curr currBlock in
      (upd_Znth (Zlength blocks - 1) blocks b, l)
    else if Int.lt (blk_id currBlock) currSeq then 
      let (b, l) := create_block_with_packet curr in (blocks ++ [b], l)
    else
      (*here we have to deal with timeouts*)
      update_past_blocks (sublist 0 (Zlength blocks - 1) blocks) curr state
  end.

(*The decoder simply repeatedly applies the above function, generating output packets and updating the state*)
Definition decoder_all_steps (received: list fec_packet_act) (states: list (list bool)) : (list block * list packet_act) :=
  foldl (fun (acc: list block * list packet_act) (x: fec_packet_act * list bool) =>
    let (blks, pkts) := update_dec_state acc.1 x.1 x.2 in
    (blks, acc.2 ++ pkts)) (nil, nil) (combine received states).

(*Now we can define the decoder function and predicate*)
Definition rse_decode_func (received: list fec_packet_act) (curr: fec_packet_act) 
  (states: list (list bool)) (state: list bool) : list packet_act :=
  let (blocks, _) := decoder_all_steps received states in
  let (_, pkts) := update_dec_state blocks curr state in
  pkts.

Definition rse_decoder : (@decoder valid_packet encodable fec_data) :=
  fun (received: list fec_packet_act) (decoded: list enc_packet) (curr: fec_packet_act) (new: list enc_packet) =>
    exists (states: list (list bool)) (state: list bool),
      map (@e_packet _ _) new = rse_decode_func received curr states state.

(** Correctness Theorems*)

(*It is difficult to say much about the correctness of the decoder, since because of timeouts we cannot be
  sure of much. However, we can prove 2 basic theorems:
  1. The decoder does not produce any bad packets - ie: all returned packets were originally sent.
  2. Subject to (TODO) some conditions on h and k, each original packet is returned at most twice
*)



(** Encoder/Decoder correctness (old)*)
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
  f None < 0 ->
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
  rewrite /block_wf /subblock => [[Hkbound [Hhbound [Hkh [Hid [Hidx [Hk Hh]]]]]]] [Hsubid [Hsubdata [Hsubpar [Hsubk Hsubh]]]].
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
       | None => -1
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
                                    | None => -1
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
  block_complete b ->
  0 < blk_c b.
Proof.
  move => b. rewrite /block_complete => [[[p [Hinp Hlenp]] _]].
  rewrite -Hlenp. rewrite {Hlenp Hinp}. case : p => [p fec]/=.
  case: p => h c num valid /=. move: valid. rewrite /valid_packet => /andP[ /boolP Hle _ ].
  move: Hle.
  case : (Z_le_lt_dec 8 (Zlength h)) => [Hle _|//]. rewrite Zlength_app. list_solve.
Qed.

(* A nontrivial theorem to prove that uses [decode_list_correct_full] to show that for ANY
  subblock of a well formed, complete block that has recieved at least k packets, we get 
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
    + rewrite -Hs. have Hc':=(blk_c_pos Hcomp). list_solve.
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

(*Show that if received is a subseq of encoded, then the blocks of received are each
  subblocks of blocks in encoded*)

(*Compose these to get the final theorem*)