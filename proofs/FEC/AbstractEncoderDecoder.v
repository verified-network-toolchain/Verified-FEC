Require Import VST.floyd.functional_base.
Require Import ZSeq.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.

(*Need an eqType*)
Lemma reflect_proj_sumbool: forall (P: Prop) (H: {P} + {~P}),
  reflect P H.
Proof.
  move => P H. case : H => [Hy | Hn].
  by apply ReflectT. by apply ReflectF.
Qed.

(*First, show byte has an eqType - TODO move this so we dont
have 2 - other in ByteField*)
Definition byte_eqMixin := EqMixin 
  (fun i1 i2 => reflect_proj_sumbool (Byte.eq_dec i1 i2)).
Canonical byte_eqType := EqType byte byte_eqMixin.

(*Abstract notions of packets, transcript, encoder, decoder*) 
Section AbstractSpecs.

(*Definition of packet with some sort of header*)

(*Abstract notion that a packet is valid according to its header (to allow multiple protocols)*)
(*It is more convenient for this proposition to be decidable*)
Variable packet_valid : list byte -> list byte -> bool.

Record packet := mk_pkt 
  { p_header : list byte; p_contents: list byte; p_seqNum: nat }.

#[export]Instance eta_packet: Settable _ := 
  settable! mk_pkt <p_header; p_contents; p_seqNum>. 

Definition remove_seqNum (p: packet) : list byte * list byte :=
  (p_header p, p_contents p).

(*Additionally, we may require some more properties of the packet in order for FEC to work correctly.
  This could be combined into [packet_valid], but that is meant to be a more universal validity condition*)
Variable encodable_pred : packet -> bool.

(*Then, when encoding, we add some fec data to the packet*)
Variable fec_data : Type.
Variable fec_data_eq_dec: forall (f1 f2: fec_data), {f1 = f2 } + {f1 <> f2}.

(*An [fec_packet] includes the original packet along with some FEC metadata.*)
Record fec_packet := mk_fecpkt { p_packet : packet; p_fec_data : fec_data}.

(*Actual bytes in packet*)
Definition packet_bytes (p: packet): list byte :=
  p_header p ++ p_contents p.

(*Equality on packets*)

(*Definition byte_list_eq_dec : forall (l1 l2: list byte), {l1 = l2} + {l1 <> l2} :=
  fun l1 l2 => list_eq_dec Byte.eq_dec l1 l2.*)

Definition packet_eqb (p1 p2: packet) : bool :=
  (p_header p1 == p_header p2) &&
  (p_contents p1 == p_contents p2) &&
  (p_seqNum p1 == p_seqNum p2).

Lemma packet_eqP: forall (p1 p2: packet),
  reflect (p1 = p2) (packet_eqb p1 p2).
Proof.
  rewrite /packet_eqb.
  move => p1 p2.
  case: (p_header p1 == p_header p2) /eqP =>/= Hhead; 
    last by (apply ReflectF; intro; subst).
  case: (p_contents p1 == p_contents p2) /eqP => /= Hcons;
    last by (apply ReflectF; intro; subst).
  case: (p_seqNum p1 == p_seqNum p2) /eqP => /= Hseq;
    last by (apply ReflectF; intro; subst).
  apply ReflectT. by move: Hhead Hcons Hseq; case: p1; case p2 => /=
  h1 c1 a1 h2 c2 s2 Hh Hc Hs; subst.
Qed.

Definition packet_eqMixin := EqMixin packet_eqP.
Canonical packet_eqType := EqType packet packet_eqMixin.

Definition fec_packet_eqb (p1 p2: fec_packet) : bool :=
  fec_data_eq_dec (p_fec_data p1) (p_fec_data p2) && ((p_packet p1) == (p_packet p2)).

Lemma fec_packet_eqP: forall (p1 p2: fec_packet),
  reflect (p1 = p2) (fec_packet_eqb p1 p2).
Proof.
  move => p1 p2. rewrite /fec_packet_eqb. 
  case : (fec_data_eq_dec (p_fec_data p1) (p_fec_data p2)) => Heq/=; last first.
    apply ReflectF. move => Hc. by rewrite Hc in Heq.
  case : (p_packet p1 == p_packet p2) /eqP => Hpeq.
  - apply ReflectT. move: Heq Hpeq. by case : p1; case: p2 => /= p1 f1 p2 f2 ->->.
  - apply ReflectF. move => Hc. by rewrite Hc in Hpeq.
Qed.

Definition fec_packet_eqMixin := EqMixin fec_packet_eqP.
Canonical fec_packet_eqType := EqType fec_packet fec_packet_eqMixin.

#[export] Instance packet_inhab: Inhabitant packet.
apply (mk_pkt nil nil 0).
Defined.

Variable fec_packet_inhab: Inhabitant fec_packet.

(** Abstract state *)

Record transcript := mk_tran
  { orig : list packet; (*packets received by sender from origin*)
    encoded : list (list fec_packet); (*encoded by sender*)
    received: list fec_packet; (*subset of encoded packets received by receiver*)
    decoded: list (list packet) (*packets sent by receiver*)
  }.

(*An encoder is a 4 place relation taking in the previously-receieved packets, the previously-encoded
  packets, the current packet, and the currently-encoded packet(s). It need not be determinstic, but
  this allows us to "fix" our choices at each step*)
Definition encoder := list packet -> list (list fec_packet) -> packet -> list fec_packet -> Prop.

(*Decoder is similar*)
Definition decoder := list fec_packet -> list (list packet) -> fec_packet -> list packet -> Prop.

(*We want to say that the whole encoded list is valid for this predicate*)
Definition encoder_list (enc: encoder) (orig: list packet) (encoded: list (list fec_packet)) : Prop :=
  Zlength orig = Zlength encoded /\
  forall(i: Z), 0 <= i < Zlength orig ->
    enc (sublist 0 i orig) (sublist 0 i encoded) (Znth i orig) (Znth i encoded).

Definition decoder_list (dec: decoder) (received: list fec_packet) (decoded: list (list packet)) : Prop :=
  Zlength received = Zlength decoded /\
  forall (i:Z), 0 <= i < Zlength received ->
    dec (sublist 0 i received) (sublist 0 i decoded) (Znth i received) (Znth i decoded).

(*We will say that a transcript is valid if the streams were produced
  by an encoder-decoder pair*)
Variable enc: encoder.
Variable dec: decoder.
Definition valid_transcript (t: transcript) :=
  encoder_list enc (orig t) (encoded t) /\
  decoder_list dec (received t) (decoded t).

(*We can state generic properties of an encoder/decoder pair, but
  not those which rely on specific aspects of the state or the
  packet stream. We give one example: all packets
  outputted by the decoder were given as input to the encoder:*)

(*First, we need a loss relation that drops and/or reorders some packets over the channel*)
(*loss_r l1 l2 means that we dropped/reordered l1 to get l2*)
Definition loss_r := list fec_packet -> list fec_packet -> Prop.

(*A general loss relation does not add packets (though it could duplicate some)*)
(*TODO: should we just make this the definition of loss or do we want to say anything about more specific kinds of loss?*)
Definition valid_loss (r: loss_r) : Prop :=
  forall (l1 l2: list fec_packet),
    r l1 l2 ->
    (forall x, x \in l1 -> x \in l2).

Definition loss := {r: loss_r | valid_loss r }.

Definition loss_rel : loss -> loss_r := (fun r => proj1_sig r).
Coercion loss_rel : loss >-> loss_r.

(*Some loss relations may not reorder (or duplicate) packets*)
(*
Definition no_reorder (l: loss) : Prop :=
  forall (l1 l2: list fec_packet),
    (loss_rel l) l1 l2 ->
    subseq l2 l1.*)

(*Correctness properties we may want:*)

(*All encoder/decoder pairs should satisfy: decoder produces only packets originally received by encoder*)
Definition no_bad_packets (enc: encoder) (dec: decoder) : Prop :=
  forall orig received encoded decoded (l: loss),
    (*If all incoming packets are valid and encodable*)
    (forall p, p \in orig -> packet_valid (p_header p) (p_contents p)) ->
    (forall p, p \in orig -> encodable_pred p) ->
    (*sequence numbers must be unique - this is NOT true of the C code,
      but we will prove that under certain conditions, the machine-length
      integer operations we perform are equivalent to their
      infinite precision counterparts*)
    uniq (map p_seqNum orig) ->
    encoder_list enc orig encoded ->
    decoder_list dec received decoded ->
    (loss_rel l) received (concat encoded) ->
    forall (x: packet), x \in (concat decoded) -> exists y, (y \in orig) /\ (remove_seqNum x = remove_seqNum y).
(*
(*The C implementations will produce transcripts that are consistent with
  some encoder and decoder. We will say that a transcript is valid if this is the case*)

Variable l: loss. (*TODO: how to handle loss relation, which we don't know, maybe just assume*)

(*Then, we have the results about the decoded packets:*)
Lemma valid_transcript_enc_dec: forall (t: transcript),
  valid_encoder_decoder enc dec ->
  valid_transcript t ->
  (forall p, p \in concat (decoded t) -> exists p', p' \in (orig t) /\ remove_seqNum p = remove_seqNum p').
Proof.
  rewrite /valid_encoder_decoder /valid_transcript => t Hval [Hvalid [Hencode [Huniq [Henc [Hdec Hloss]]]]]. eauto.
Qed.*)

End AbstractSpecs.
