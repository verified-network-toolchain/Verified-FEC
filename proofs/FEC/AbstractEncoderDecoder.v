Require Import EquivClasses.
Require Import VST.floyd.functional_base.
Require Import ZSeq.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.

(*Abstract notions of packets, transcript, encoder, decoder*) 
Section AbstractSpecs.

(*Definition of packet with some sort of header*)

(*Abstract notion that a packet is valid according to its header (to allow multiple protocols)*)
(*It is more convenient for this proposition to be decidable*)
Variable packet_valid : list byte -> list byte -> bool.

Record packet := mk_pkt 
  { p_header : list byte; p_contents: list byte; p_seqNum: int }.

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

Definition byte_list_eq_dec : forall (l1 l2: list byte), {l1 = l2} + {l1 <> l2} :=
  fun l1 l2 => list_eq_dec Byte.eq_dec l1 l2.

Definition packet_eqb (p1 p2: packet) : bool :=
  (proj_sumbool (byte_list_eq_dec (p_header p1) (p_header p2)) && 
   proj_sumbool (byte_list_eq_dec (p_contents p1) (p_contents p2)) && 
   proj_sumbool (Int.eq_dec (p_seqNum p1) (p_seqNum p2))).

Lemma packet_eqP: forall (p1 p2: packet),
  reflect (p1 = p2) (packet_eqb p1 p2).
Proof.
  rewrite /packet_eqb.
  move => p1 p2. destruct (byte_list_eq_dec (p_header p1) (p_header p2)) as [Hh | Hh] => /=; last first.
    apply ReflectF. move => Hc. by rewrite Hc in Hh.
  destruct (byte_list_eq_dec (p_contents p1) (p_contents p2)) as [Hp|Hp]=>/=; last first.
    apply ReflectF. move => Hc. by rewrite Hc in Hp.
  destruct (Int.eq_dec (p_seqNum p1) (p_seqNum p2)) as [Hi|Hi]=>/=; last first.
    apply ReflectF. move => Hc. by rewrite Hc in Hi.
  apply ReflectT. move: Hh Hp Hi. by case : p1; case : p2 => /= h1 c1 s1 h2 c2 s2 ->->->.
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
apply (mk_pkt nil nil Int.zero).
Defined.

Variable fec_packet_inhab: Inhabitant fec_packet.

(** Abstract state *)

Record transcript := mk_tran
  { orig : list packet; (*packets received by sender from origin*)
    encoded : list fec_packet; (*encoded by sender*)
    received: list fec_packet; (*subset of encoded packets received by receiver*)
    decoded: list packet (*packets sent by receiver*)
  }.

(*An encoder is a 4 place relation taking in the previously-receieved packets, the previously-encoded
  packets, the current packet, and the currently-encoded packet(s). It need not be determinstic, but
  this allows us to "fix" our choices at each step*)
Definition encoder := list packet -> list fec_packet -> packet -> list fec_packet -> Prop.

(*Decoder is similar*)
Definition decoder := list fec_packet -> list packet -> fec_packet -> list packet -> Prop.

(*We want to say that the whole encoded list is valid for this predicate*)
Definition encoder_list (enc: encoder) (orig: list packet) (encoded: list fec_packet) : Prop :=
  exists (l: list (list fec_packet)), concat l = encoded /\
  forall(i: Z), 0 <= i < Zlength orig ->
    enc (sublist 0 i orig) (concat (sublist 0 i l)) (Znth i orig) (Znth i l).

Definition decoder_list (dec: decoder) (received: list fec_packet) (decoded: list packet) : Prop :=
  exists (l: list (list packet)), concat l = decoded /\
  forall(i: Z), 0 <= i < Zlength received ->
    dec (sublist 0 i received) (concat (sublist 0 i l)) (Znth i received) (Znth i l).

(*Finally, we need a loss relation that drops and/or reorders some packets over the channel*)
(*loss_r l1 l2 means that we dropped/reordered l1 to get l2*)
Definition loss_r := list fec_packet -> list fec_packet -> Prop.

(*A more generic notion of a subsequence - we do not require the same order*)
(*TODO: move this*)
Definition subseq_gen {A: eqType} (l1 l2: seq A) : bool :=
  all (fun x => (count_mem x l1 <= count_mem x l2)%N) l1.

(*TODO: this has to be somehwere*)
Lemma is_true_eq: forall (b: bool),
  is_true b <-> b = true.
Proof.
  move => b. by case : b.
Qed.

Lemma subseq_genP: forall {A: eqType} (l1 l2: seq A),
  reflect (forall x, (count_mem x l1 <= count_mem x l2)%N) (subseq_gen l1 l2).
Proof.
  move => A l1 l2. apply iff_reflect. rewrite /subseq_gen -is_true_eq CommonSSR.all_in. split => Hmem x.
  - move => _. apply Hmem.
  - case Hin: (x \in l1).
    + by apply Hmem.
    + have /count_memPn Hc: x \notin l1 by rewrite Hin. by rewrite Hc.
Qed. 

Lemma subseq_gen_subseq: forall {A: eqType} (l1 l2: seq A),
  subseq l1 l2 ->
  subseq_gen l1 l2.
Proof.
  move => A l1 l2. move: l1. elim : l2 => [//=l1 /eqP Hl1| h1 t1 /= IH l1].
    by rewrite Hl1.
  case : l1 => [//= | h t /=].
  rewrite /subseq_gen /= eq_refl /=.
  case Hh: (h == h1); move: Hh => /eqP Hh Hsub.
  - rewrite Hh eq_refl /= leq_add2l leq_count_subseq //=.
    move: IH => /(_ t Hsub). rewrite /subseq_gen => Hall.
    erewrite eq_in_all. apply Hall. move => y. by rewrite leq_add2l.
  - move: IH => /(_ _ Hsub) => /subseq_genP Hcount.
    have->/=: (h1 == h) = false by rewrite eq_sym; apply /eqP.
    rewrite add0n.
    have->/=: (1 + count_mem h t <= count_mem h t1)%N = true.
      move: Hcount => /(_ h)/=. by rewrite eq_refl.
    rewrite CommonSSR.all_in => x Hinx. 
    case: (h == x) /eqP => Hhx /=.
    + have->/=:(h1 == x) = false by rewrite -Hhx eq_sym; apply /eqP.
      rewrite add0n. move: Hcount => /(_ h)/=. by rewrite eq_refl Hhx.
    + rewrite add0n. move: Hcount => /(_ x)/=.
      have->/=:(h==x)=false by apply /eqP. rewrite add0n => Hle.
      apply (leq_trans Hle). by rewrite leq_addl.
Qed. 

(*A general loss relation does not add packets*)
(*TODO: should we just make this the definition of loss (subseq_gen) or do we want to say anything about more specific kinds of loss?*)
Definition valid_loss (r: loss_r) : Prop :=
  forall (l1 l2: list fec_packet),
    r l1 l2 ->
    subseq_gen l1 l2.

Definition loss := {r: loss_r | valid_loss r }.

Definition loss_rel : loss -> loss_r := (fun r => proj1_sig r).
Coercion loss_rel : loss >-> loss_r.

(*Some loss relations may not reorder packets*)
Definition no_reorder (l: loss) : Prop :=
  forall (l1 l2: list fec_packet),
    (loss_rel l) l1 l2 ->
    subseq l2 l1.

(*Correctness properties we may want:*)

(*All encoder/decoder pairs should satisfy: decoder produces only packets originally recieved by encoder*)
Definition valid_encoder_decoder (enc: encoder) (dec: decoder) : Prop :=
  forall orig received encoded decoded (l: loss),
    (*If all incoming packets are valid and encodable*)
    (forall p, p \in orig -> packet_valid (p_header p) (p_contents p)) ->
    (forall p, p \in orig -> encodable_pred p) ->
    encoder_list enc orig encoded ->
    decoder_list dec received decoded ->
    (loss_rel l) encoded received ->
    forall (x: packet), x \in decoded -> exists y, (y \in orig) /\ (remove_seqNum x = remove_seqNum y).

(*The C implementations will produce transcripts that are consistent with
  some encoder and decoder. We will say that a transcript is valid if this is the case*)

Variable enc: encoder.
Variable dec: decoder.
Variable l: loss. (*TODO: how to handle loss relation, which we don't know, maybe just assume*)

Definition valid_transcript (t: transcript) :=
  (forall p, p \in (orig t) -> packet_valid (p_header p) (p_contents p)) /\
  (forall p, p \in (orig t) -> encodable_pred p) /\
  encoder_list enc (orig t) (encoded t) /\
  decoder_list dec (received t) (decoded t) /\
  (loss_rel l) (encoded t) (received t).

(*Then, we have the results about the decoded packets:*)
Lemma valid_transcript_enc_dec: forall (t: transcript),
  valid_encoder_decoder enc dec ->
  valid_transcript t ->
  (forall p, p \in (decoded t) -> exists p', p' \in (orig t) /\ remove_seqNum p = remove_seqNum p').
Proof.
  rewrite /valid_encoder_decoder /valid_transcript => t Hval [Hvalid [Hencode [Henc [Hdec Hloss]]]]. eauto.
Qed.

End AbstractSpecs.
