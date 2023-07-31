Require Import VST.floyd.functional_base.
Require Import ZSeq.
Require Export ByteFacts.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
From RecordUpdate Require Export RecordSet. (*for updating records easily*)
Export RecordSetNotations.

(*Abstract notions of packets*) 
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

End AbstractSpecs.
