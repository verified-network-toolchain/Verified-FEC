Require Import EquivClasses.
Require Import VST.floyd.functional_base.
Require Import ZSeq.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

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

(*Abstract notions of packets, transcript, encoder, decoder*) 
Section AbstractSpecs.

(*Definition of packet with some sort of header*)

(*Abstract notion that a packet is valid according to its header (to allow multiple protocols)*)
(*For decidable equality, we want this proposition to be decidable*)
Variable packet_valid : list byte -> list byte -> bool.

Record packet := mk_pkt 
  { p_header : list byte; p_contents: list byte; p_seqNum: int ; p_valid: packet_valid p_header p_contents }.

(*Additionally, we may require some more properties of the packet in order for FEC to work correctly.
  But these properties need not hold of the encoded packets, so we do not include this in
  the p_valid above*)
Variable encodable_pred : packet -> bool.
(*TODO: sigma type instead?*)
Record encodable_packet := mk_enc { e_packet : packet; e_enc : encodable_pred e_packet }.

(*Then, when encoding, we add some fec data to the packet*)
Variable fec_data : Type.
Variable fec_data_eq_dec: forall (f1 f2: fec_data), {f1 = f2 } + {f1 <> f2}.
(*Variable fec_data_inhab: Inhabitant fec_data.*)

(*An [fec_packet] includes the original packet along with some FEC metadata. We no longer care 
  whether the packet is encodable*)
Record fec_packet := mk_fecpkt { p_packet : packet; p_fec_data : fec_data}.

(*Actual bytes in packet*)
Definition packet_bytes (p: packet): list byte :=
  p_header p ++ p_contents p.

(*Decidable equality on packets (why we need [packet_valid] to be a bool *)
Lemma packet_eq: forall (p1 p2: packet), 
  p_header p1 = p_header p2 ->
  p_contents p1 = p_contents p2 ->
  p_seqNum p1 = p_seqNum p2 ->
  p1 = p2.
Proof.
  move => [h1 c1 s1 v1] [h2 c2 s2 v2]/= => Hh Hc Hs. move: v1 v2. rewrite Hh Hc Hs => v1 v2.
  by have->: v1 = v2 by apply bool_irrelevance.
Qed.

Definition byte_list_eq_dec : forall (l1 l2: list byte), {l1 = l2} + {l1 <> l2} :=
  fun l1 l2 => list_eq_dec Byte.eq_dec l1 l2.

Lemma packet_eq_bool: forall (p1 p2: packet),
  reflect (p1 = p2) (proj_sumbool (byte_list_eq_dec (p_header p1) (p_header p2)) && 
                     proj_sumbool (byte_list_eq_dec (p_contents p1) (p_contents p2)) && 
                     proj_sumbool (Int.eq_dec (p_seqNum p1) (p_seqNum p2))).
Proof.
  move => p1 p2. destruct (byte_list_eq_dec (p_header p1) (p_header p2)) as [Hh | Hh] => /=; last first.
    apply ReflectF. move => Hc. by rewrite Hc in Hh.
  destruct (byte_list_eq_dec (p_contents p1) (p_contents p2)) as [Hp|Hp]=>/=; last first.
    apply ReflectF. move => Hc. by rewrite Hc in Hp.
  destruct (Int.eq_dec (p_seqNum p1) (p_seqNum p2)) as [Hi|Hi]=>/=; last first.
    apply ReflectF. move => Hc. by rewrite Hc in Hi.
  apply ReflectT. by apply packet_eq.
Qed.

Definition packet_eq_dec: forall (p1 p2: packet), {p1 = p2} + {p1 <> p2}.
Proof.
  move => p1 p2. eapply reflect_dec. apply packet_eq_bool.
Qed.

Definition packet_eqMixin := EqMixin packet_eq_bool.
Canonical packet_eqType := EqType packet packet_eqMixin.

(*Similarly, decidable equality on encodable packets*)
Lemma enc_packet_eq: forall (e1 e2 : encodable_packet),
  e_packet e1 = e_packet e2 ->
  e1 = e2.
Proof.
  move => [ep1 ev1] [ep2 ev2]/= => Hep. move: ev1 ev2. rewrite Hep => ev1 ev2.
  by have->: ev1=ev2 by apply bool_irrelevance.
Qed.

Lemma enc_packet_eqP: forall (e1 e2: encodable_packet),
  reflect (e1 = e2) ((e_packet e1) == (e_packet e2)).
Proof.
  move => e1 e2. case He: (e_packet e1 == e_packet e2); move : He => /eqP He.
  - apply ReflectT. by apply enc_packet_eq.
  - apply ReflectF. move => Hc. by rewrite Hc in He.
Qed.

Definition enc_packet_eqMixin := EqMixin enc_packet_eqP.
Canonical enc_packet_eqType := EqType encodable_packet enc_packet_eqMixin.

Definition fec_packet_eq_dec: forall (p1 p2: fec_packet), {p1 = p2} + {p1 <> p2}.
Proof.
  eq_dec_tac.
  apply packet_eq_dec.
Defined.

Lemma fec_packet_eq_axiom: Equality.axiom (fun p1 p2 => proj_sumbool (fec_packet_eq_dec p1 p2)).
Proof.
  move => p1 p2. case : (fec_packet_eq_dec p1 p2) => [/= -> | Hneq /=].
  by apply ReflectT. by apply ReflectF.
Qed.

Definition fec_packet_eqMixin := EqMixin fec_packet_eq_axiom.
Canonical fec_packet_eqType := EqType fec_packet fec_packet_eqMixin.

(*TODO: really shouldn't be quite necessary, but simpler*)
Variable enc_packet_inhab: Inhabitant encodable_packet.
Variable fec_packet_inhab: Inhabitant fec_packet.

(** Abstract state *)

(*The encoder and decoder might depend on some current state*)
(*Variable enc_state : Type.
Variable dec_state : Type.

Variable enc_inhab: Inhabitant enc_state.
Variable dec_inhab: Inhabitant dec_state.*)

Record transcript := mk_tran
  { orig : list encodable_packet; (*packets received by sender from origin*)
    encoded : list fec_packet; (*encoded by sender*)
    received: list fec_packet; (*subset of encoded packets received by receiver*)
    decoded: list encodable_packet (*packets sent by receiver*)
  }.

(*An encoder is a 4 place relation taking in the previously-receieved packets, the previously-encoded
  packets, the current packet, and the currently-encoded packet(s). It need not be determinstic, but
  this allows us to "fix" our choices at each step*)
Definition encoder := list encodable_packet -> list fec_packet -> encodable_packet -> list fec_packet -> Prop.

(*Decoder is similar*)
Definition decoder := list fec_packet -> list encodable_packet -> fec_packet -> list encodable_packet -> Prop.

(*We want to say that the whole encoded list is valid for this predicate*)
Definition encoder_list (enc: encoder) (orig: list encodable_packet) (encoded: list fec_packet) : Prop :=
  exists (l: list (list fec_packet)), concat l = encoded /\
  forall(i: Z), 0 <= i < Zlength orig ->
    enc (sublist 0 i orig) (concat (sublist 0 i l)) (Znth i orig) (Znth i l).

Definition decoder_list (dec: decoder) (received: list fec_packet) (decoded: list encodable_packet) : Prop :=
  exists (l: list (list encodable_packet)), concat l = decoded /\
  forall(i: Z), 0 <= i < Zlength received ->
    dec (sublist 0 i received) (concat (sublist 0 i l)) (Znth i received) (Znth i l).

(*Finally, we need a loss relation that drops and/or reorders some packets over the channel*)
(*loss_r l1 l2 means that we dropped/reordered l1 to get l2*)
Definition loss_r := list fec_packet -> list fec_packet -> Prop.

(*A general loss relation does not add packets*)
Definition valid_loss (r: loss_r) : Prop :=
  forall (l1 l2: list fec_packet),
    r l1 l2 ->
    forall x, x \in l2 -> x \in l1.

Definition loss := {r: loss_r | valid_loss r }.

Definition loss_rel : loss -> loss_r := (fun r => proj1_sig r).
Coercion loss_rel : loss >-> loss_r.

(*Some loss relations may not reorder packets*)
Definition no_reorder (l: loss) : Prop :=
  forall (l1 l2: list fec_packet),
    (loss_rel l) l1 l2 ->
    subseq l2 l1.

(*Correctness properties we may want:*)

(*All encoder/decoder pairs should satisfy: decoder produces only valid packets*)
Definition valid_encoder_decoder (enc: encoder) (dec: decoder) : Prop :=
  forall orig received encoded decoded (l: loss),
    encoder_list enc orig encoded ->
    decoder_list dec received decoded ->
    (loss_rel l) encoded received ->
    forall (x: encodable_packet), x \in decoded -> x \in orig.
(*
TODO: do this
(*Additionally, there should be some loss relation that results in all packets being recovered*)
Variable bounded_loss : loss -> Prop.

Definition enc_dec_bounded_loss (l: loss) (enc: encoder) (dec: decoder) : Prop :=
  forall orig received encoded decoded ,
    encoder_list enc orig encoded ->
    decoder_list dec received decoded ->
    bounded_loss l ->
    (loss_rel l) encoded received ->
    perm_eq orig decoded.
*)

(*The C implementations will produce transcripts that are consistent with
  some encoder and decoder. We will say that a transcript is valid if this is the case*)

Variable enc: encoder.
Variable dec: decoder.
Variable l: loss. (*TODO: how to handle loss relation, which we don't know, maybe just assume*)

Definition valid_transcript (t: transcript) :=
  encoder_list enc (orig t) (encoded t) /\
  decoder_list dec (received t) (decoded t) /\
  (loss_rel l) (encoded t) (received t).

(*Then, we have the results about the decoded packets:*)
Lemma valid_transcript_enc_dec: forall (t: transcript),
  valid_encoder_decoder enc dec ->
  valid_transcript t ->
  (forall p, p \in (decoded t) -> p \in (orig t)).
Proof.
  rewrite /valid_encoder_decoder /valid_transcript => t Hval [Henc [Hdec Hloss]]. eauto.
Qed.
(*
Lemma valid_transcript_all_recovered: forall (t: transcript),
  enc_dec_bounded_loss l enc dec ->
  valid_transcript t ->
  bounded_loss l ->
  perm_eq (orig t) (decoded t).
Proof.
  rewrite /enc_dec_bounded_loss /valid_transcript => t Hbound [Henc [Hdec Hloss]] Hbl. eauto.
Qed.*)

End AbstractSpecs.
