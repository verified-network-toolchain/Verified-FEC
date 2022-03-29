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
  exists (l: list (list fec_packet)), concat l = encoded /\ Zlength l = Zlength orig /\
  forall(i: Z), 0 <= i < Zlength orig ->
    enc (sublist 0 i orig) (concat (sublist 0 i l)) (Znth i orig) (Znth i l).

Definition decoder_list (dec: decoder) (received: list fec_packet) (decoded: list packet) : Prop :=
  exists (l: list (list packet)), concat l = decoded /\ Zlength l = Zlength received /\
  forall(i: Z), 0 <= i < Zlength received ->
    dec (sublist 0 i received) (concat (sublist 0 i l)) (Znth i received) (Znth i l).

(*An alternate approach - let's see*)
Section Alt.

Variable enc_param: Type.
Variable enc_state : Type.
Variable dec_param: Type.
Variable dec_state : Type.

Variable init_enc_state : enc_state.
Variable init_dec_state: dec_state.

(*NOTE: special case where we don't need to look at past info bc we are mantaining (implicitly) some state*)
Definition encoder' := packet -> enc_state -> enc_param -> list fec_packet * enc_state.
Definition decoder' := fec_packet -> dec_state -> dec_param -> list packet * dec_state.

Definition encoder_all (enc: encoder') (orig: list packet) (states: list enc_param) : list fec_packet * enc_state :=
  foldl (fun (acc : list fec_packet * enc_state) (x: packet * enc_param) => 
    (acc.1 ++ (enc x.1 acc.2 x.2).1, (enc x.1 acc.2 x.2).2)) (nil, init_enc_state) (zip orig states).

Definition encoder_func (enc: encoder') (orig: list packet) (curr: packet) (states: list enc_param) (state: enc_param)
 : list fec_packet :=
 (enc curr (encoder_all enc orig states).2 state).1.

(*Now we relate this to the more general formulation above*)

Definition encoder_from_encoder' (enc: encoder') : encoder :=
 fun orig encoded curr additional =>
 exists (states : list enc_param) (state: enc_param),
  Zlength states = Zlength orig /\
  additional = encoder_func enc orig curr states state.

Definition encoder_list' (enc: encoder') (orig: list packet) (encoded: list fec_packet) : Prop :=
  exists states : list enc_param,
  Zlength states = Zlength orig /\
  encoded = (encoder_all enc orig states).1.

Lemma zip_nil: forall {A B: Type} (l: list B),
  zip (@nil A) l = nil.
Proof.
  move => A B l. by case: l.
Qed.

Ltac split_all :=
  repeat match goal with
  | |- ?P /\ ?Q => split; try by []; try lia; auto
  end.

Lemma get_ex: forall {A: Type} (P: A -> Prop) (Q: Prop) (a: A),
  ((exists a, P a) -> Q) ->
  P a ->
  Q.
Proof.
  eauto.
Qed.

Context `{Hinhab: Inhabitant enc_param}.

(*TODO: move*)
Require Import ZSeq.

(*TODO: prove in Zseq*)
Lemma mkseqZ_1_plus: forall {A: Type} `{H: Inhabitant A} (f: Z -> A) (z: Z), 0 <= z ->
  mkseqZ f (z+1) = (f 0) :: mkseqZ (fun i => f (i+1)) z.
Proof.
  move => A Hinh f z Hz. apply Znth_eq_ext; rewrite !mkseqZ_Zlength; try lia. 
  - rewrite Zlength_cons mkseqZ_Zlength; lia.
  - move => i Hi. have [Hi0 | Hibig]: i = 0 \/ 1 <= i < z + 1 by lia.
    + rewrite Hi0 Znth_0_cons mkseqZ_Znth //. lia.
    + rewrite Znth_pos_cons; [|lia]. rewrite !mkseqZ_Znth; try lia. f_equal. lia.
Qed.

(*This is the key theorem that relates stepwise encoding with the whole thing. We can do this
  without existentials*)
Lemma encoder_all_steps_concat: forall (e: encoder') (states: list enc_param) (orig: list packet),
  Zlength states = Zlength orig ->
  (encoder_all e orig states).1 = concat (mkseqZ 
    (fun i => encoder_func e (sublist 0 i orig) (Znth i orig) (sublist 0 i states) (Znth i states)) (Zlength orig)).
Proof.
  move => e states orig. rewrite /encoder_func /encoder_all.
  remember (@nil fec_packet) as base. rewrite -(cat0s (concat _)) -Heqbase. rewrite {Heqbase}.
  move: states base init_enc_state. elim: orig => [//= states b1 b2 Hlen | h t /= IH states b1 b2].
  - by rewrite zip_nil /= cats0.
  - case : states => [|st1 st2 Hlen/=]. list_solve.
    rewrite IH;[|list_solve]. have->: Zlength (h::t) = Zlength t + 1 by list_solve.
    rewrite mkseqZ_1_plus/=; [|list_solve]. rewrite !Znth_0_cons catA. f_equal.
    f_equal. have Hpos: 0 <= Zlength t by list_solve. apply Znth_eq_ext; rewrite !mkseqZ_Zlength //. 
    move => i Hi. rewrite !mkseqZ_Znth// !Znth_pos_cons; try lia. rewrite !sublist_0_cons; try lia.
    by rewrite !Z.add_simpl_r.
Qed.

(*NOTE: the theorem we would want to prove is NOT true. We cannot go from encoder_list -> encoder_list',
  at least not without some uniqueness properties about states that we don't want to have to deal with.
  This suggests that encoder_list is actually TOO general to the point where it is extremely difficult
  to say anything useful about it. It seems to me that the "right" predicate is encoder_list', since
  we have a single state list existentially quanitified, and then we can work with a function
  with a nice compositional structure like the above lemma*)

(*Theorem we wanted to prove:
Lemma encoder_list_equiv: forall (e: encoder') (orig: list packet) (encoded: list fec_packet),
  encoder_list' e orig encoded <->
  encoder_list (encoder_from_encoder' e) orig encoded.*)

(*wrong (old) proof:
Proof.
  move => e orig encoded. rewrite /encoder_list' /encoder_list /encoder_from_encoder'.
  (*generalize IH enough for foldl - this is kind of annoying*)
  remember (@nil fec_packet) as b1. have Hcon: (forall l, concat l = b1 ++ concat l) by move => l; rewrite Heqb1.
  setoid_rewrite Hcon.
  (*have Hbound: forall i: Z, 0 <= i < Zlength orig <-> Zlength b1 <= i < Zlength b1 + Zlength orig by list_solve.
  setoid_rewrite Hbound.
  have Hisub: forall i : Z, sublist 0 i orig = sublist 0 (i - Zlength b1) orig by (f_equal; list_solve).
  have Hith: forall {A: Type} {H: Inhabitant A} (i : Z) (l: seq A), Znth i l = Znth (i - Zlength b1) l by intros; f_equal; list_solve.
  setoid_rewrite Hith. setoid_rewrite Hisub.
  rewrite {Hcon Heqb1 Hbound Hisub Hith}.*) rewrite {Hcon Heqb1}. move: b1 init_enc_state encoded.
  elim: orig => [b1 b2 encoded /= | h t /= IH b1 b2 encoded]; try setoid_rewrite zip_nil; split.
  - move => /=[states [Hlen Henc]]. rewrite Henc. exists nil. split_all. list_solve. list_solve.
  - move => [l [Hl [Hlen Hall]]]/=. rewrite -Hl {Hl}. exists nil. split_all.
    have->//: l = [::] by list_solve. list_solve.
  - move => [states H]. move: H. case : states => [|st1 st2]; [list_solve|]. move => /=[Hlen Henc].
    have Hlen': Zlength st2 = Zlength t by list_solve.
    have Hih:= conj Hlen' Henc. 
    apply (get_ex (proj1 (IH _ _ _))) in Hih. case : Hih => [l [Hencl [Hlenl Hnthl]]].
    exists ((e h b2 st1).1 :: l). split_all. by rewrite /= catA. list_solve.
    move => i Hi.
    have [Hi0 | Hibig]: (i = 0 \/ 1 <= i < Zlength t + 1) by list_solve.
    + (*case for added element*) 
      rewrite Hi0. exists nil. exists st1. split_all.
    + (*case by IH*) have Hi1: 0 <= i-1 < Zlength t by lia. 
      move: Hnthl => /(_ (i-1) Hi1) => [[states [state [Hsatelen Hith]]]].
      exists (st1 :: states). exists state. split_all. list_solve.
      rewrite !Znth_pos_cons; try lia. rewrite sublist_0_cons; [|lia].
      by rewrite /= Hith.
  - (*other direction*)
    move => [l [Henc [Hlenl Hil]]]. 
    (*First, we need the first state in the context*)
    have Hi0:=Hil. have H0: 0 <= 0 < Zlength (h :: t) by list_solve.
    move: Hi0 => /(_ _ H0). rewrite !Znth_0_cons !sublist_nil/=.
    move => [st2 [st1 [Hlen H0th]]]. move: H0th. have->/=:st2 = nil by list_solve.
    move => H0th.
    (*potential problem: I don't think this is true. If we have a sequence of states that each work,
      doesnt mean that the entire works
      Maybe not: we are saying that for each i, for all possible states, it must work
      so in particular, it must work for the sequence of steps we chose for the whole thing
      problem: in IH - states such that it works for tail, but what about head
*)
    (*Not the most elegant but oh well - just assert IH*)
    have [states [Hstatelen Henc']]: (exists states : seq enc_param,
       Zlength states = Zlength t /\
      encoded =
      (foldl
         (fun (acc : seq fec_packet * enc_state) (x : packet * enc_param) =>
          (acc.1 ++ (e x.1 acc.2 x.2).1, (e x.1 acc.2 x.2).2)) (b1 ++ (e h b2 st1).1, (e h b2 st1).2)
         (zip t states)).1). {
      apply IH. have Hl: exists tl, l = (e h b2 st1).1 :: tl. { rewrite {Henc Hil}.
        move: Hlenl H0th. case : l => [|h' t']. list_solve. move => _. rewrite Znth_0_cons. move->.
        by exists t'. } case : Hl => [tl Hl].
      exists tl. split_all. by rewrite -Henc -catA Hl. list_solve. move => i Hi.
      have Hi1: 0 <= i + 1 < Zlength (h :: t) by list_solve. 
      move: Hil => /(_ _ Hi1) [states [state [Hstatelen Hith]]].
      move: Hith. rewrite Hl !Znth_pos_cons; [|lia|lia]. rewrite !Z.add_simpl_r.
      move: Hstatelen. case: states => [|st1' st2']. list_solve.
      rewrite !sublist_0_cons; [|lia]. rewrite /= Z.add_simpl_r. move => Hlen' Hith.
      exists st2'. exists state. split_all. list_solve.
      rewrite Hith. f_equal. f_equal. f_equal. f_equal.*)
End Alt.

(*Finally, we need a loss relation that drops and/or reorders some packets over the channel*)
(*loss_r l1 l2 means that we dropped/reordered l1 to get l2*)
Definition loss_r := list fec_packet -> list fec_packet -> Prop.

(*A more generic notion of a subsequence - we do not require the same order*)
(*TODO: move this*)
(*Definition subseq_gen {A: eqType} (l1 l2: seq A) : bool :=
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
Qed. *)

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
Definition no_reorder (l: loss) : Prop :=
  forall (l1 l2: list fec_packet),
    (loss_rel l) l1 l2 ->
    subseq l2 l1.

(*Correctness properties we may want:*)

(*All encoder/decoder pairs should satisfy: decoder produces only packets originally received by encoder*)
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
