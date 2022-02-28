Require Import EquivClasses.
Require Import VST.floyd.functional_base.
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

Record packet := mk_ptk 
  { p_header : list byte; p_contents: list byte; p_seqNum: int ; p_valid: packet_valid p_header p_contents }.

(* We need some sort of fec data associated with a packet*)
Variable fec_data : Type.
Variable fec_data_eq_dec: forall (f1 f2: fec_data), {f1 = f2 } + {f1 <> f2}.
(*Variable fec_data_inhab: Inhabitant fec_data.*)

(*We separate fec fields because the original and decoded packets should have no (relevant) fec metadata.
  The packet contents should not change; the fec data might*)
Record fec_packet := mk_fecpkt { p_packet : packet; p_fec_data : fec_data }.

(*Actual bytes in packet*)
Definition packet_bytes (p: packet): list byte :=
  p_header p ++ p_contents p.

(*Decidable equality on packets (why we need [pavket_valid] to be a bool *)
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

(** Abstract state *)

Record transcript := mk_tran
  { orig : list packet; (*packets received by sender from origin*)
    encoded : list fec_packet; (*encoded by sender*)
    received: list fec_packet; (*subset of encoded packets received by receiver*)
    decoded: list packet}. (*packets send by receiver*)

Definition encoder := list packet -> list fec_packet -> Prop. 

Definition decoder := list fec_packet -> list packet -> Prop.

(*Encoder is monotonic - cannot change previously encoded data*)
Definition enc_mono (e: encoder) : Prop :=
  forall (orig: list packet) (extra: list packet) (encoded encoded': list fec_packet),
    e orig encoded ->
    e (orig ++ extra) encoded' ->
    exists suffix, encoded' = encoded ++ suffix.

(*Same for decoder*)
Definition dec_mono (d: decoder) : Prop :=
  forall (received: list fec_packet) (extra: list fec_packet) (decoded decoded': list packet),
    d received decoded ->
    d (received ++ extra) decoded' ->
    exists suffix, decoded' = decoded ++ suffix.

(*An encoder-decoder pair is valid if encoding data, losing some of it, and decoding the receieved subset
  gives packets that were present in the original stream*)
Definition encode_decode_pair (e: encoder) (d: decoder) : Prop :=
  forall (orig: list packet) (encoded: list fec_packet) (received: list fec_packet) (decoded: list packet),
    e orig encoded ->
    subseq received encoded -> (*TODO: weaken to subset instead of subseq?*)
    d received decoded ->
    (forall p, p \in decoded -> p \in orig).

Definition valid_encoder_decoder (e: encoder) (d: decoder) : Prop :=
  enc_mono e /\ dec_mono d /\ encode_decode_pair e d.

(*The C implementations will produce transcripts that are consistent with
  some encoder and decoder. We will say that a transcript is valid if this is the case*)

Variable enc: encoder.
Variable dec: decoder.

Definition valid_transcript (t : transcript) :=
  enc (orig t) (encoded t) /\
  subseq (received t) (encoded t) /\
  dec (received t) (decoded t).

(*If we have consistent transcripts and a valid encoder/decoder pair, then the decoded packets
  are a subset of the original ones*)
Lemma encode_decode_pair_transcript: forall (t: transcript),
  encode_decode_pair enc dec ->
  valid_transcript t ->
  (forall p, p \in (decoded t) -> p \in (orig t)).
Proof.
  unfold encode_decode_pair. unfold valid_transcript. intros t Hval [Hoe [Hre Hrd]].
  eauto.
Qed.

End AbstractSpecs.
