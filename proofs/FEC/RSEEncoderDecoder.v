(*Implement the abstract encoder/decoder relations from AbstractEncoderDecoder with RSE algorithm *)
Require Import VST.floyd.functional_base.
Require Import AssocList.
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

Ltac split_all := repeat match goal with | |- ?p /\ ?q => split end.

Ltac solve_sumbool :=
  repeat match goal with
  | [ H: is_true (proj_sumbool ?x) |- _] => destruct x; [clear H | solve [inversion H]]
  | [ |- is_true (proj_sumbool ?x)] => destruct x; auto; try lia
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

Section Block.

Record block := mk_blk { blk_id: int;
  data_packets: list (option fec_packet_act); parity_packets: list (option fec_packet_act); blk_k : Z; blk_h : Z;
  complete: bool}.

#[export]Instance block_inhab: Inhabitant block :=
  mk_blk Int.zero nil nil 0 0 false.

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

Lemma block_wf_bool_reflect: forall b,
  reflect (block_wf b) (block_wf_bool b).
Proof.
  move => b. apply iff_reflect. rewrite /block_wf /block_wf_bool. split.
  - move => [Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh Henc]]]]]]]. 
    do 5 (try(apply /andP; split)); try solve_sumbool.
    + rewrite is_true_true_eq forallb_forall => o. case: o => [p |//]. rewrite in_app_iff => Hin.
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
    + rewrite is_true_true_eq forallb_forall => o. case: o => [p |//]. apply Henc.
  - move => /andP [/andP[/andP[/andP[/andP[Hhbound Hkbound] Hall] Hk] Hh] Henc].
    solve_sumbool. move: Hall. rewrite is_true_true_eq forallb_forall => Hall.
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
    + move: Henc. rewrite is_true_true_eq forallb_forall => Henc p Hp. by apply Henc in Hp.
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

End Block.

(** Getting blocks from a stream *)
(*This is surprisingly complex, particularly because we want to reason about streams in which the order
  of the packets changes. The full block structure includes some uneccesary (but helpful) metadata, so
  we first simply find the list (option fec_packet) for each block, then build the full structure later.*)

Section WfStream.

(*A valid stream of packets that will eventually produce well-formed blocks*)
Definition wf_packet_stream (l: list fec_packet_act) :=
  (forall (p1 p2 : fec_packet_act), p1 \in l -> p2 \in l -> 
    fd_blockId p1 = fd_blockId p2 -> fd_k p1 = fd_k p2 /\ fd_h p1 = fd_h p2) /\
  (forall (p1 p2: fec_packet_act), p1 \in l -> p2 \in l -> 
    fd_blockId p1 = fd_blockId p2 -> fd_blockIndex p1 = fd_blockIndex p2 -> p1 = p2) /\
  (forall (p: fec_packet_act), p \in l -> 0 <= Int.unsigned (fd_blockIndex p) < fd_k p + fd_h p).

Lemma wf_substream: forall l1 l2,
  wf_packet_stream l1 ->
  (forall x, x \in l2 -> x \in l1) ->
  wf_packet_stream l2.
Proof.
  move => l1 l2 [Hkh [Hinj Hbounds]] Hsub. split; [|split].
  - move => p1 p2 Hp1 Hp2. apply Hkh; by apply Hsub.
  - move => p1 p2 Hp1 Hp2. apply Hinj; by apply Hsub.
  - move => p Hp. by apply Hbounds; apply Hsub.
Qed.

Lemma wf_perm: forall l1 l2,
  wf_packet_stream l1 ->
  perm_eq l1 l2 ->
  wf_packet_stream l2.
Proof.
  move => l1 l2 Hwf Hperm. apply (wf_substream Hwf).
  move => x Hinx. by rewrite (perm_mem Hperm).
Qed.

Lemma wf_packet_stream_tl: forall h t,
  wf_packet_stream (h :: t) ->
  wf_packet_stream t.
Proof.
  move => h t Hwf. apply (wf_substream Hwf). move => x Hx. by rewrite in_cons Hx orbT.
Qed.

(*This implies the following useful condition*)
Lemma wf_all_nonneg: forall (l: list fec_packet_act),
  wf_packet_stream l ->
  (forall (x: fec_packet_act), x \in l -> 0 <= fd_k x + fd_h x).
Proof.
  move => l [_ [_ Hbounds]] x Hinx. move: Hbounds => /(_ x Hinx). lia.
Qed.

End WfStream. 

(*Helps with using this specific pickSeq instance*)
(*TODO: put in section so it doesn't ruin global?*)
Ltac case_pickSeq l ::=
  match goal with
  | |- context [ pickSeq ?p l ] => let H := fresh "Hpick" in
                                          let x := fresh "x" in
                                          let Hinx := fresh "Hinx" in
                                          let Hxid := fresh "Hxid" in
                                          let Hidx := fresh "Hidx" in
    have H:= (pickSeqP p l); case : H => [ x Hinx /andP[/eqP Hxid Hidx] |]
  end.

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

(*The above function is unwieldy to use directly for all the theorems we need. Instead, we give 5 
  conditions that (get_blocks l) satisfies. Then we prove that any 2 lists that satisfy these 5
  conditions are equal up to permutation. With only 1 exception (TODO: ensure), we will only need
  these 5 conditions for all subsequent proofs; it is much nicer than needing induction and direct
  reasoning about association lists for everything*)

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

(*Prop2: All lists are nonempty (each contains at least 1 packet). We just proved a stronger version of this*)

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

(*Prop3: For every entry in the block list, we give the list explicitly. This is the most important
  property; it says that each list contains all packets in the input with that blockId, in their
  correct (blockIndex) places*) 
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
      case_pickSeq t => [|//]. rewrite in_mem_In in Hinx.
      apply get_blocks_list_allin in Hinx. case : Hinx => [pkts' Hpkts']. exfalso.
      apply (Hnotin pkts'). by rewrite -Hxid.
  - move => Hin. apply update_or_add_diff in Hin. apply IH in Hin.
    + rewrite Hin. rewrite mkseqZ_Zlength; [|list_solve]. 
      have->//=: (fd_blockId h == i) = false. apply /eqP. auto.
    + by apply (wf_packet_stream_tl Hwf).
    + apply /eqP. auto.
Qed.

Opaque update_or_add.

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

(*Additional properties we can derive from this relation:*)

(*All packets in a list have the same id as the list and are in the original stream*)
Lemma get_block_lists_prop_packets: forall (l: list fec_packet_act) (blks: block_list) (i: int)
  (pkts: list (option fec_packet_act)) (p: fec_packet_act),
  get_block_lists_prop l blks ->
  In (i, pkts) blks ->
  In (Some p) pkts ->
  fd_blockId p = i /\ In p l.
Proof.
  move => l blks i pkts p [Hallin [Hnonemp [Hlen [Heq Huniq]]]] Hin.
  apply Heq in Hin. rewrite Hin In_Znth_iff mkseqZ_Zlength; [|list_solve].
  move => [j [Hj Hjth]]. move: Hjth. rewrite mkseqZ_Znth //.
  case_pickSeq l => [[Hxp]|//].
  rewrite -Hxp. split => //. by rewrite -in_mem_In.
Qed.

(*We prove that this relation is preserved through lists with the same elements*)
Lemma get_block_lists_prop_perm_equiv: forall (l1 l2: list fec_packet_act) (blks: block_list),
  wf_packet_stream l1 ->
  l1 =i l2 ->
  get_block_lists_prop l1 blks ->
  get_block_lists_prop l2 blks.
Proof.
  move => l1 l2 blks Hwf Hperm [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]].
  rewrite /get_block_lists_prop. split_all => //.
  - move => p Hinp. apply Hallin1. move: Hinp. by rewrite -!in_mem_In Hperm.
  - move => i pkts Hin. apply Heq1 in Hin. rewrite {1}Hin {Hin}.
    apply Znth_eq_ext; rewrite !mkseqZ_Zlength //; try apply Zlength_nonneg.
    move => j Hj. rewrite !mkseqZ_Znth //; try lia.
    case_pickSeq l1; case_pickSeq l2 => [|//].
    + (*rely on uniqueness of (id, idx) pairs*)
      f_equal. apply (proj1 (proj2 Hwf)) => //. by rewrite Hperm.
      congruence. solve_sumbool. apply (f_equal Int.repr) in e, e0.
      move: e e0. by rewrite !Int.repr_unsigned=><-<-.
    + move => /(_ x). rewrite Hxid eq_refl Hidx /= => Hc.
      have//:true = false by (apply Hc; rewrite -Hperm).
    + move => /(_ x). rewrite Hxid eq_refl Hidx /= => Hc.
      have//: true = false by (apply Hc; rewrite Hperm).
Qed.  

(*Any 2 block_lists from the same source have the same elements*)
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
  have [Hidp Hinlp]: fd_blockId p = i1 /\ In p l
    by apply (@get_block_lists_prop_packets _ b1 _ pkts1).
  have Hinlp':=Hinlp. apply Hallin2 in Hinlp'.
  case Hinlp' => [pkts2 Hin2].
  rewrite Hidp in Hin2. have Hpkts2:=Hin2.
  apply Heq2 in Hpkts2. rewrite in_mem_In.
  (*only thing left- show lengths are same*) 
  have->//: pkts1 = pkts2. rewrite Hpkts1 Hpkts2. f_equal.
  rewrite (Hlen1 _ _ _ Hin1 Hinp). 
  have Hin2' := Hin2. apply Hnonemp2 in Hin2'. case : Hin2' => [p2 Hinp2].
  (*Now we have to know that id is same again*)
  have [Hidp2 Hinlp2]: fd_blockId p2 = i1 /\ In p2 l by
    apply (@get_block_lists_prop_packets _ b2 _ pkts2). 
  rewrite (Hlen2 _ _ _ Hin2 Hinp2).
  have [Hk Hh]: fd_k p = fd_k p2 /\ fd_h p = fd_h p2. {
    move: Hwf => [Hkh _]. apply Hkh. by apply in_mem_In. by apply in_mem_In.
    by rewrite Hidp Hidp2. }
  by rewrite Hk Hh.
Qed.

(*Therefore, any 2 block_lists satisfying the relation are equal up to permutation*)
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
  - move: Hin1. rewrite -!is_true_true_eq. by apply (get_block_lists_prop_in Hwf).
  - case Hin2: (b \in (al b2)) => //. move: Hin2. rewrite -is_true_true_eq => Hin2.
    apply (@get_block_lists_prop_in l b2 b1 b Hwf) in Hin2 => //. by rewrite Hin1 in Hin2.
Qed.

(*One more result: if we get_blocks for any 2 lists which are permutations, then the two get_blocks
  are permutations*)
Lemma get_blocks_lists_perm: forall (l1 l2: list fec_packet_act),
  wf_packet_stream l1 ->
  perm_eq l1 l2 ->
  perm_eq (get_block_lists l1) (get_block_lists l2).
Proof.
  move => l1 l2 Hwf Hperm. apply (get_block_lists_prop_perm Hwf).
  - by apply get_block_lists_spec.
  - apply (get_block_lists_prop_perm_equiv (wf_perm Hwf Hperm)).
    by apply perm_mem; rewrite perm_sym.
    apply get_block_lists_spec. by apply (wf_perm Hwf).
Qed.

(*Another small result that is quite helpful - all packets from with the same id as a block_list are in that list*)
Lemma get_blocks_list_all_id: forall (l: list fec_packet_act) (i: int) (pkts: list (option fec_packet_act))
  (p: fec_packet_act),
  wf_packet_stream l ->
  In (i, pkts) (get_block_lists l) ->
  In p l ->
  fd_blockId p = i ->
  In (Some p) pkts.
Proof.
  move => l i pkts p Hwf Hinb Hinp Hid.
  have [Hallin [Hnonemp [Hlen [Heq Huniq]]]] := (get_block_lists_spec Hwf).
  case: Hwf => [Hkh [Hinj Hbounds]].
  (*get p' that is actually there, show k and h equal, so use definition of mkSeq and length*)
  have Hex:=Hinb. apply Hnonemp in Hex. case: Hex => [p' Hinp'].
  have [Hidp' Hinpl']: fd_blockId p' = i /\ In p' l by apply (@get_block_lists_prop_packets _ (get_block_lists l) _ pkts).
  have [Hk Hh]: fd_k p = fd_k p' /\ fd_h p = fd_h p'. apply Hkh. by rewrite in_mem_In. by rewrite in_mem_In.
    by rewrite Hidp'.
  have Hpkts:=Hinb. apply Heq in Hpkts. rewrite Hpkts In_Znth_iff mkseqZ_Zlength;[|list_solve].
  rewrite (Hlen _ _ _ Hinb Hinp') -Hk -Hh.
  have Hbound: 0 <= Int.unsigned (fd_blockIndex p) < fd_k p + fd_h p by apply Hbounds; rewrite in_mem_In.
  exists (Int.unsigned (fd_blockIndex p)). split => //.
  rewrite mkseqZ_Znth //.
  case_pickSeq l. 
  (*here, we rely on uniqueness of (id, idx) pairs*)
  - solve_sumbool. apply int_unsigned_inj in e. f_equal. apply Hinj => //.
    by rewrite in_mem_In. by rewrite Hxid.
  - move => /(_ p). rewrite Hid eq_refl /=.
    case : (Z.eq_dec (Int.unsigned (fd_blockIndex p)) (Int.unsigned (fd_blockIndex p))) => //= _ => Hcon.
    have//: true = false by apply Hcon; rewrite in_mem_In.
Qed.

(*Now we will convert between (int, list (option fec_packet_act)) and blocks. A block is useful because
  it has lots of extra metadata which makes things easier, but it is more annoying to work with directly*)

Definition btuple := (int * list (option fec_packet_act))%type.

Definition btuple_to_block (x: btuple) : block :=
  (*find a packet that exists*)
  match (pmap id x.2) with
  | p :: _ => let k := fd_k p in
              let h := fd_h p in
              mk_blk x.1 (sublist 0 k x.2) (sublist k (k+h) x.2) k h false
  | nil => (*this case will not occur with badly-formed lists*)
            block_inhab
  end.

(*The above definition is not very usable, since we don't know which packet (pmap id x.2) will give.
  The following lemma allows us to express the block's contents in terms of ANY packet in it*)
Lemma btuple_to_block_eq: forall (l: list fec_packet_act) (i: int) (pkts: list (option fec_packet_act))
  (p: fec_packet_act),
  wf_packet_stream l ->
  In (i, pkts) (get_block_lists l) ->
  In p l ->
  fd_blockId p = i ->
  btuple_to_block (i, pkts) = mk_blk i (sublist 0 (fd_k p) pkts) (sublist (fd_k p) (fd_k p + fd_h p) pkts) 
    (fd_k p) (fd_h p) false.
Proof.
  move => l i pkts p Hwf Hint Hinp Hid. rewrite /btuple_to_block.
  rewrite /=.
  have Hhin: In (Some p) pkts by apply (get_blocks_list_all_id Hwf Hint).
  have: p \in (pmap id pkts) by rewrite -pmap_id_some in_mem_In.
  case Hp': (pmap id pkts) => [// |p' t].
  move => _. have Hinp': In (Some p') pkts by rewrite -in_mem_In pmap_id_some Hp' in_cons eq_refl.
  (*now just show these 2 packets have same id, k, and h*)
  have [Hidp' Hinpl']: fd_blockId p' = i /\ In p' l
    by apply (@get_block_lists_prop_packets _ (get_block_lists l) _ pkts) => //; apply get_block_lists_spec.
  case : Hwf => [Hkh _].
  have [Hk Hh]: fd_k p = fd_k p' /\ fd_h p = fd_h p'. apply Hkh. by rewrite in_mem_In. by rewrite in_mem_In.
    by rewrite Hidp'.
  by rewrite Hk Hh.
Qed.

(*TODO: will we need this?*)
Definition block_to_btuple (b: block) : btuple :=
  (blk_id b, data_packets b ++ parity_packets b).

(*Finally, we can get all the blocks from a list*)
Definition get_blocks (l: list fec_packet_act) := map btuple_to_block (get_block_lists l).

End BlockList.

(** Encoder **)

Section Encoder.

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

(*TODO: write version updating state, have it take in previous state, produce new state + packets
  can feed it (get_blocks encoded) once we prove correctness*)

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
    (*TODO: conditions on k and h*)
    new = rse_encode_func orig encoded curr k h.

End Encoder.

(** The Decoder *)

Section Decoder.

(*First major step: what does it mean to decode a block?*)
(*[decoder_list] takes in a value i, representing the sublist of parities that we will look at
  to find xh parity packets. We will write a function to find that value so the user doesn't need
  to know it. TODO: maybe move to ReedSolomonList.v*)

(*TODO: take away block stuff, move to ReedSolomonList.v*)

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

(*TODO: CommonSSR?*)
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

(*TODO: deduce headers?*)

(*TODO: parity/ordering issue - for now assume it is correct*)

(*1. create block with packet*)
Definition create_block_with_fec_packet (p: fec_packet_act) : block :=
  let k := fd_k p in
  let h := fd_h p in
  let allPackets := upd_Znth (Int.unsigned (fd_blockIndex p)) (zseq (k + h) None) (Some p) in
  mk_blk (fd_blockId p) (sublist 0 k allPackets) (sublist k (k+h) allPackets) k h false.

Definition create_block_with_packet_black (p: fec_packet_act) : block * list packet :=
  let new_block := create_block_with_fec_packet p in
  let packets := (if (fd_isParity p) then nil else [p_packet p]) ++
    (if Z.eq_dec (fd_k p) 1 then (decode_block new_block) else nil) in
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
    if s && int_le (fd_blockId curr) (blk_id bl) then
      (tl, if fd_isParity curr then nil else [p_packet curr])
    else if Int.lt (fd_blockId curr) (blk_id bl) then
      let t := create_block_with_packet_black curr in
      (t.1 :: blocks, t.2)
    else if Int.eq (fd_blockId curr) (blk_id bl) then
      let t := add_packet_to_block_black curr bl in
      (t.1 :: tl, t.2)
    else
      let t := update_past_blocks tl curr stl in
      (bl :: t.1, t.2)
  | _ :: _, _ => (nil, nil) (*should never reach here*)
  | _, _ => (*not sure we can reach here - should prove*)
      (nil,  if fd_isParity curr then nil else [p_packet curr])
  end. 

(*We cannot build the blocks in 1 go since we must take into account timeouts. Instead, we build it up
  incrementally*)
Definition update_dec_state (blocks: list block) (curr: fec_packet_act) (state: list bool) : 
  (list block * list packet) :=
  match blocks with
  | nil => let t := create_block_with_packet_black curr in ([t.1], t.2)
  | bl :: tl => 
    let currBlock := Znth (Zlength blocks - 1) blocks in
    let currSeq := fd_blockId curr in
    if Int.eq currSeq (blk_id currBlock) then
      let t := add_packet_to_block_black curr currBlock in
      (upd_Znth (Zlength blocks - 1) blocks t.1, t.2)
    else if Int.lt (blk_id currBlock) currSeq then 
      let t := create_block_with_packet_black curr in (blocks ++ [t.1], t.2)
    else
      (*here we have to deal with timeouts*)
      update_past_blocks (sublist 0 (Zlength blocks - 1) blocks) curr state
  end.

(*The decoder simply repeatedly applies the above function, generating output packets and updating the state*)
Definition decoder_all_steps (received: list fec_packet_act) (states: list (list bool)) : (list block * list packet) :=
  foldl (fun (acc: list block * list packet) (x: fec_packet_act * list bool) =>
    let t := update_dec_state acc.1 x.1 x.2 in
    (t.1, acc.2 ++ t.2)) (nil, nil) (combine received states).

Definition decoder_block_state (received: list fec_packet_act) (states: list (list bool)) :=
  (decoder_all_steps received states).1.

(*Now we can define the decoder function and predicate*)
Definition rse_decode_func (received: list fec_packet_act) (curr: fec_packet_act) 
  (states: list (list bool)) (state: list bool) : list packet :=
  (update_dec_state (decoder_all_steps received states).1 curr state).2.

Definition rse_decoder : (@decoder fec_data) :=
  fun (received: list fec_packet_act) (decoded: list packet) (curr: fec_packet_act) (new: list packet) =>
    exists (states: list (list bool)) (state: list bool),
      new = rse_decode_func received curr states state.

End Decoder.

(*TODO: figure out what to do with this*)
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

(** Correctness Theorem **)

Section Correctness.

(*We can only give a weak correctness theorem: all packets produced by the decoder were in the original list.
  We would like to be able to say more, but timeouts ensure that there is little that can be guaranteed (unless
  we reason about specific sequences of timeouts)

  To prove the theorem, we need to show 3 main results
  1. Suppose we have a recoverable subblock of a well-formed, complete block. Then, decode_block gives back
     all the data packets that are missing from the subblock but found in the original block.
  2. Every block in the decoder's state is a subblock of a block that was produced by the encoder.
  3. Every block produced by the encoder is well formed, and is recoverable if it is complete.

  Together, these imply the result that we want. We start with Part 1:*)

Section SubblockDecode.

(*1. Define a subblock of a block*)

(*Special sublist for list of options - TODO separate file?*)
Definition subseq_option {A: Type} (l1 l2: list (option A)) : Prop :=
  Zlength l1 = Zlength l2 /\
  forall (i: Z), 0 <= i < Zlength l1 ->
  Znth i l1 = Znth i l2 \/ Znth i l1 = None.

Lemma subseq_option_refl: forall {A: Type} (s: list (option A)),
  subseq_option s s.
Proof.
  move => A s. rewrite /subseq_option. split. list_solve. move => i Hi. by left.
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

Lemma subseq_option_upd_Znth: forall {A: Type} (s1 s2: list (option A)) (i: Z) (a: option A),
  subseq_option s1 s2 ->
  subseq_option (upd_Znth i s1 a) (upd_Znth i s2 a).
Proof.
  move => A s1 s2 i a. rewrite /subseq_option !Zlength_upd_Znth => [[Hlen Hall]]. split => //.
  move => j Hj. have [Hiin | Hiout]: (0 <= i < Zlength s1) \/ ((0 > i) \/ i >= Zlength s1) by lia.
  - rewrite !(upd_Znth_lookup' (Zlength s1)); try lia. 
    case : (Z.eq_dec j i) => //. by left. move => Hji. by apply Hall.
  - rewrite !upd_Znth_out_of_range; try lia. by apply Hall.
Qed.

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

Lemma nth_firstn_hi: forall {A: Type} (contents: seq A) (n m: nat) (d: A),
  (n >= m)%coq_nat -> List.nth n (firstn m contents) d = d.
Proof.
  move => A contents m n d Hmn.
  apply nth_overflow. have Hlen:= (firstn_le_length n contents). lia.
Qed.

(*We prove this in full generality, so we don't have to carry hypotheses about positive numbers,
  which compond*)
Lemma subseq_option_sublist: forall {A: Type} (s1 s2: seq (option A)) (lo hi: Z),
  subseq_option s1 s2 ->
  subseq_option (sublist lo hi s1) (sublist lo hi s2).
Proof.
  move => A s1 s2 lo hi. rewrite /subseq_option => [[Hlen Hall]].
  rewrite /sublist. move: Hlen Hall. rewrite !Zlength_correct !skipn_length !firstn_length. move => Hlen. split. lia.
  move => i Hi. move: Hall. rewrite /Znth. case : (Z_lt_dec i 0); try lia.
  rewrite !nth_skipn.
  have [Hin | Hhi]: ((Z.to_nat i + Z.to_nat lo)%coq_nat < Z.to_nat hi)%coq_nat \/
    ((Z.to_nat i + Z.to_nat lo)%coq_nat >= Z.to_nat hi)%coq_nat by lia.
  - rewrite !nth_firstn; try lia. move => Hipos Hall.
    have [Hins | Houts]: ((Z.to_nat i + Z.to_nat lo)%coq_nat < Datatypes.length s1)%coq_nat \/
      ((Z.to_nat i + Z.to_nat lo)%coq_nat >= Datatypes.length s1)%coq_nat by lia.
    + move: Hall => /( _ (Z.of_nat (Z.to_nat i + Z.to_nat lo))). 
      case : (Z_lt_dec (Z.of_nat (Z.to_nat i + Z.to_nat lo)) 0); try lia. move => _.
      rewrite !Nat2Z.id. move => Hall. apply Hall. split; try lia. by apply inj_lt.
    + rewrite !nth_overflow; lia.
  - move => _ _. rewrite !nth_overflow; lia.
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

(*Now we can define a subblock*)
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

Lemma subblock_add: forall h b1 b2,
  subblock b1 b2 ->
  subblock (add_fec_packet_to_block h b1) (add_fec_packet_to_block h b2).
Proof.
  move => h b1 b2. rewrite /subblock /add_fec_packet_to_block/= => [[Hid [Hopt1 [Hopt2 [Hk Hh]]]]].
  split_all => //; rewrite Hk ?Hh; apply subseq_option_sublist; apply subseq_option_upd_Znth; by apply subseq_option_app.
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
      move: Hall => /allP Hall.
      have Hn: None \in data_packets b1. rewrite in_mem_In In_Znth_iff. exists i. split.
        by rewrite Hlendata. by []. by move: Hall => /(_ _ Hn). }
    have Hfp': 0 <= f (Some def) by rewrite Hf; list_solve.
    have Hinp: In (Some def) (data_packets b1) by apply Hallin.
    have Hlb:=(list_max_nonneg_in Hfp' Hinp).
    have: f(Some def) = list_max_nonneg f (data_packets b2)
      by rewrite Hf Hlendef Hf -/(blk_c b2) blk_c_complete.
    lia.
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
  move => /andP[ Hle _]. move: Hle. 
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

End SubblockDecode.

(*Now we prove part 2: every block in the decoder is a subblock of a block produced by the encoder.
  We need 2 parts: first, that the blocks in received are subblocks of those of encoded, second, that
  the blocks in the decoder state are subblocks of those in received (because of timeouts). Then, we
  can use the transitivity of the subblock relation.
  
  Proving these is the main benefit of the [get_block_lists] approach; it would be very difficult to
  prove these by induction directly*)

Section DecoderSubblocks.

(*A key result: if we have some stream of packets, then we take some (generalized) substream of these packets
  (such that duplicates are allowed), then every block formed by get_block_lists of the substream is
  a subseq_option of a block from the original stream. This allows us to relate the "encoded" and "received" blocks*)
Lemma get_blocks_lists_substream: forall (l1 l2: list fec_packet_act),
  wf_packet_stream l1 ->
  (forall x, x \in l2 -> x \in l1) ->
  forall i pkts, (i, pkts) \in (al (get_block_lists l2)) -> 
    exists pkts', (i, pkts') \in (al (get_block_lists l1)) /\ subseq_option pkts pkts'.
Proof.
  move => l1 l2 Hwf Hallin i pkts. rewrite !in_mem_In => Hin. have Hpkts:=Hin.
  have [Hallin2 [Hnonemp2 [Hlen2 [Heq2 Huniq2]]]] := (get_block_lists_spec (wf_substream Hwf Hallin)).
  apply Heq2 in Hpkts. rewrite Hpkts {Hpkts}.
  (*we know that there is some p in pkts and p is in l2, so p is in l1, so there
    is some pkts' with the same id, we use the mkseqZ definition to prove subseq option*)
  have Hex:=Hin. apply Hnonemp2 in Hex. case: Hex => [p Hinp].
  have [Hidp Hinpl2]: fd_blockId p = i /\ In p l2 by
    apply (@get_block_lists_prop_packets _ (get_block_lists l2) _ pkts).
  have Hinpl1: In p l1. { move: Hinpl2. rewrite -!in_mem_In. apply Hallin. }
  have Hex:=Hinpl1.
  have [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]] := (get_block_lists_spec Hwf).
  apply Hallin1 in Hinpl1. case : Hinpl1 => [pkts' Hin'].
  exists pkts'. split. by rewrite in_mem_In -Hidp. 
  have Hlenp : Zlength pkts' = fd_k p + fd_h p. {
    have Hex':=Hin'. apply Hnonemp1 in Hex'. case: Hex' => [p' Hinp']. rewrite Hidp in Hin'.
    have [Hidp' Hinpl1]: fd_blockId p' = i /\ In p' l1 by
      apply (@get_block_lists_prop_packets _ (get_block_lists l1) _ pkts').
    rewrite (Hlen1 _ _ _ Hin' Hinp').
    have [Hk Hh]: fd_k p' = fd_k p /\ fd_h p' = fd_h p. apply Hwf => //.
    by rewrite in_mem_In. by rewrite in_mem_In. by rewrite Hidp'. by rewrite Hk Hh. }
  have Hpkts':=Hin'. apply Heq1 in Hpkts'. rewrite Hpkts' {Hpkts'} Hlenp (Hlen2 _ _ _ Hin Hinp).
  move: Hwf => [_ [Hinj /(_ p)]] Htemp.
  have Hidx : 0 <= Int.unsigned (fd_blockIndex p) < fd_k p + fd_h p by apply Htemp; rewrite in_mem_In.
  rewrite {Htemp}.
  split; rewrite !mkseqZ_Zlength; try lia. move => j Hj. rewrite !mkseqZ_Znth; try lia.
  case_pickSeq l2; last first. by right. rewrite Hidp.
  case_pickSeq l1.
  - (*use uniqueness of (id, idx) pairs*)
    left. f_equal. apply Hinj => //. by apply Hallin. congruence.
    solve_sumbool. apply (f_equal Int.repr) in e0. apply (f_equal Int.repr) in e.
    move: e0 e. by rewrite !Int.repr_unsigned => <-<-.
  - move => /(_ x). rewrite Hxid eq_refl Hidx0 /=. have->//:x \in l1 by apply Hallin.
    (*should be automatic*) move => Hc. have//:true = false by apply Hc.
Qed.

(*NOTE: we will need this later too. This is the block version of [get_blocks_lists_substream]*)
Theorem get_blocks_sublist: forall (l1 l2: seq fec_packet_act),
  wf_packet_stream l1 ->
  (forall x, x \in l2 -> x \in l1) ->
  forall b, In b (get_blocks l2) ->
  exists b', In b' (get_blocks l1) /\ subblock b b'.
Proof.
  move => l1 l2 Hwf Hsub b. rewrite /get_blocks !in_map_iff => [[t [Ht Hint]]]. rewrite -Ht.
  move: Ht Hint. case : t => [i pkts] Hb Hint. have Hint':= Hint. rewrite -in_mem_In in Hint'.
  have [pkts' [Hinpkts Hopt]]:= (get_blocks_lists_substream Hwf Hsub Hint').
  exists (btuple_to_block (i, pkts')). split. rewrite in_map_iff. exists (i, pkts'). split => //.
    by rewrite -in_mem_In.
  (*Now, we just need an element that is in pkts (and we prove, also in pkts')*)
  have [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]] := (get_block_lists_spec Hwf).
  have [Hallin2 [Hnonemp2 [Hlen2 [Heq2 Huniq2]]]] := (get_block_lists_spec (wf_substream Hwf Hsub)).
  have Hex:=Hint. apply Hnonemp2 in Hex. case : Hex => [p Hinp].
  have [Hidp Hinpl2]: fd_blockId p = i /\ In p l2 by 
    apply (@get_block_lists_prop_packets _ (get_block_lists l2) _ pkts).
  have Hinpl1: In p l1. move: Hinpl2. rewrite -!in_mem_In. apply Hsub.
  rewrite in_mem_In in Hinpkts.
  (*now we can use btuple_to_block_eq lemma*)
  rewrite (btuple_to_block_eq Hwf Hinpkts Hinpl1 Hidp).
  rewrite (btuple_to_block_eq (wf_substream Hwf Hsub) Hint Hinpl2 Hidp).
  rewrite /subblock/=. split_all => //.
  by apply subseq_option_sublist.
  by apply subseq_option_sublist.
Qed.

(*The decoder has several intermediate functions we need to handle first*)

(*TODO: move these?*)
Lemma perm_rev': forall {T: eqType} (s: seq T),
  perm_eq s (rev s).
Proof.
  move => T s. have /(_ s):=(perm_rev s). by rewrite perm_refl perm_sym.
Qed.
Lemma zip_nil_r: forall {A B: Type} (s: seq A),
  zip s (@nil B) = [::].
Proof.
  move => A B s. by case: s.
Qed. 

(*Intermediate case 1: create a new block*)
Lemma create_block_subblock: forall (l: list fec_packet_act) (h: fec_packet_act),
  wf_packet_stream l ->
  In h l ->
  exists b': block, In b' (get_blocks l) /\ subblock (create_block_with_packet_black h).1 b'.
Proof.
  move => l h Hwf Hinhl.
  (*the real result*)
  have [b' [Hinb' Hsubb']]: exists b' : block, In b' (get_blocks l) /\ subblock (create_block_with_fec_packet h) b'; last first.
    exists b'. rewrite /create_block_with_packet_black; split => //=. by case: (Z.eq_dec (fd_k h) 1).
  rewrite /subblock/= /get_blocks/=.
  have [Hallin [Hnonemp [Hlen [Heq Huniq]]]] := (get_block_lists_spec Hwf).
  have Hex := Hinhl. apply Hallin in Hex. case: Hex => [pkts Hinpkts].
  exists (btuple_to_block (fd_blockId h, pkts)).
  split.
    rewrite in_map_iff. by exists (fd_blockId h, pkts).
  rewrite (btuple_to_block_eq Hwf Hinpkts Hinhl erefl)/=.
  (*most are trivial, only 2 are interesting. We prove the stronger claim:*)
  have Hsub: subseq_option (upd_Znth (Int.unsigned (fd_blockIndex h)) (zseq (fd_k h + fd_h h) None) (Some h))
    pkts. {
    rewrite (Heq _ _ Hinpkts).
    have Hbound: 0 <= Int.unsigned (fd_blockIndex h) < fd_k h + fd_h h. apply (proj2 (proj2 Hwf)).
      by rewrite in_mem_In.
    rewrite /subseq_option upd_Znth_Zlength !zseq_Zlength; try lia.
    rewrite !mkseqZ_Zlength;[|list_solve].
    have Hinh:= (get_blocks_list_all_id Hwf Hinpkts Hinhl erefl).
    rewrite (Hlen _  _ _ Hinpkts Hinh).
    split => //. move => i Hi.
    rewrite !(upd_Znth_lookup'(fd_k h + fd_h h)); try lia; last first.
      rewrite zseq_Zlength; lia.
    rewrite mkseqZ_Znth //.
    case: (Z.eq_dec i (Int.unsigned (fd_blockIndex h))) => [Hih | Hneqih]; last first.
      right. rewrite zseq_Znth //. lia.
    left. case_pickSeq l. 
    (*here, we rely on uniqueness of (id, idx) pairs*)
    - solve_sumbool. f_equal. apply (proj1 (proj2 Hwf)) => //. by rewrite in_mem_In.
      rewrite e in Hih. by apply int_unsigned_inj in Hih.
    - move => /(_ h); rewrite eq_refl -Hih/=. case: (Z.eq_dec i i) => //= _ Hcon.
      have//:true = false by apply Hcon; rewrite in_mem_In.
  }
  split_all => //; by apply subseq_option_sublist.
Qed. 


(*Intermediate case 2: add packet to existing block. This one is quite complicated because if the block
  is complete, we don't add anything at all, so must show b1 is a subblock*)
Lemma add_to_block_subblock: forall (l: list fec_packet_act) (h: fec_packet_act)  (b1 b2: block),
 (forall p, In p (h :: l) -> 0 <= fd_k p /\ 0 <= fd_h p) -> (*TODO: should this be in wf?*)
  wf_packet_stream (h :: l) ->
  fd_blockId h = blk_id b1 ->
  In b2 (get_blocks l) ->
  subblock b1 b2 ->
  In (add_fec_packet_to_block h b2) (get_blocks (h :: l)) /\
  subblock (add_packet_to_block_black h b1).1 (add_fec_packet_to_block h b2).
Proof.
  move => l h b1 b2 Hpos Hwf Hidh Hinb2 Hsub.
  move: Hinb2. rewrite /get_blocks !in_map_iff => [[t [Hb2 Hint]]]. rewrite -Hb2.
  have [Hallin [Hnonemp [Hlen [Heq Huniq]]]] := (get_block_lists_spec (wf_packet_stream_tl Hwf)).
  move: Hb2 Hint. case : t => [i pkts] Hb2 Hint.
  have Hex:=Hint. apply Hnonemp in Hex. case: Hex => [p Hinp].
  have [Hidp Hinpl]: fd_blockId p = i /\ In p l by apply (@get_block_lists_prop_packets _ (get_block_lists l) i pkts p).
  have Hidi: fd_blockId h = i. { have->:i = blk_id b2
    by rewrite -Hb2 (btuple_to_block_eq (wf_packet_stream_tl Hwf) Hint Hinpl Hidp).
    move: Hsub => [Hsub _]. by rewrite -Hsub. }
  (*some results will be useful in multiple parts*)
  split.
  - (*TODO: separate lemmas? maybe*)
    exists (i, upd_Znth (Int.unsigned (fd_blockIndex h)) pkts (Some h)).
    (*second part is useful for both*)
    have Hnewin: In (i, upd_Znth (Int.unsigned (fd_blockIndex h)) pkts (Some h)) (get_block_lists (h :: l)). {
      have [Hallin2 [Hnonemp2 [Hlen2 [Heq2 Huniq2]]]] := (get_block_lists_spec Hwf).
      have Hex: In h (h :: l) by left. apply Hallin2 in Hex. case: Hex => [pkts' Hin'].
      rewrite -Hidi. have->//: upd_Znth (Int.unsigned (fd_blockIndex h)) pkts (Some h) = pkts'.
      have Hpkts' := Hin'. apply Heq2 in Hpkts'. rewrite Hpkts' {Hpkts'}.
      have Hpkts := Hint. apply Heq in Hpkts. rewrite Hpkts {Hpkts}.
      (*first, need to deal with lengths*)
      rewrite (Hlen _ _ _ Hint Hinp).
      have Hinh:=(get_blocks_list_all_id Hwf Hin' (in_eq _ _) erefl).
      rewrite (Hlen2 _ _ _ Hin' Hinh).
      have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. { apply Hwf.
        rewrite in_cons. have ->/=:p \in l by rewrite in_mem_In. by rewrite orbT. by rewrite in_cons eq_refl.
        by rewrite Hidp. }
      rewrite Hk Hh. have Hinht: h \in h :: l  by rewrite in_cons eq_refl.
      case : Hwf => [_ [Hinj /(_ h Hinht)]] Hbound.
      apply Znth_eq_ext; rewrite Zlength_upd_Znth !mkseqZ_Zlength; try lia. move => j Hj.
        rewrite mkseqZ_Znth // (upd_Znth_lookup' (fd_k h + fd_h h)); try lia; last first.
          by rewrite mkseqZ_Zlength; lia.
        case : (Z.eq_dec j (Int.unsigned (fd_blockIndex h))) => [Hjh | Hjh].
        - case_pickSeq (h :: l).
          (*here, we rely on uniqueness of (id, idx) pairs*)
          + f_equal. apply Hinj => //. solve_sumbool.
            rewrite e in Hjh. apply (f_equal Int.repr) in Hjh. by rewrite !Int.repr_unsigned in Hjh.
          + move => /(_  h Hinht). rewrite eq_refl/= -Hjh. by case : (Z.eq_dec j j).
        - rewrite mkseqZ_Znth //. case_pickSeq (h :: l); case_pickSeq l => [|//].
          + f_equal. apply Hinj => //. by rewrite in_cons Hinx0 orbT. by rewrite Hxid0 Hxid.
            solve_sumbool. rewrite e in e0. apply (f_equal Int.repr) in e0. by rewrite !Int.repr_unsigned in e0.
          + have Hinxl: x \in l. move: Hinx; rewrite in_cons => /orP[/eqP Hxh | //]. solve_sumbool.
            by subst. move => /(_ x Hinxl). by rewrite Hxid Hidi eq_refl/= Hidx.
          + have Hinxl: x \in h :: l by rewrite in_cons Hinx orbT. move => /(_ x Hinxl).
            by rewrite Hxid Hidi eq_refl/= Hidx. }
    split => [|//]. 
    rewrite (btuple_to_block_eq (wf_packet_stream_tl Hwf) Hint Hinpl Hidp)/=.
    rewrite (btuple_to_block_eq Hwf Hnewin (in_eq _ _)) //. 
    rewrite /add_fec_packet_to_block /=.
    have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. { apply Hwf.
      rewrite in_cons. have ->/=:p \in l by rewrite in_mem_In. by rewrite orbT. by rewrite in_cons eq_refl.
      by rewrite Hidp. }
    rewrite Hk Hh.
    have Hlenpkts: Zlength pkts = fd_k h + fd_h h. { rewrite -Hk -Hh. apply (Hlen _ _ _ Hint Hinp). }
    have->: (forall (A: Type) (a1 a2: seq A), a1 ++ a2 = (a1 ++ a2)%list) by [].
    move: Hpos => /( _ h (in_eq _ _ )) => Hpos.
    rewrite -!sublist_split; try lia. by rewrite (sublist_same 0 (fd_k h + fd_h h)).
  - rewrite /add_packet_to_block_black. case Hcomp: (complete b1); last first.
      case Hrec: (recoverable (add_fec_packet_to_block h b1)).
      apply subblock_add. by rewrite Hb2. apply subblock_add. by rewrite Hb2.
    (*If it was complete, we don't change anything. Proving the subblock relation is a bit harder*)
    (*TODO: separate lemma?*) move: Hb2.
    rewrite !(btuple_to_block_eq (wf_packet_stream_tl Hwf) Hint Hinpl Hidp)/= => Hb2.
    have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. { apply Hwf.
      rewrite in_cons. have ->/=:p \in l by rewrite in_mem_In. by rewrite orbT. by rewrite in_cons eq_refl.
      by rewrite Hidp. } rewrite Hk Hh.
    have Hlenpkts: Zlength pkts = fd_k h + fd_h h. rewrite -Hk -Hh. apply (Hlen _ _ _ Hint Hinp).
    rewrite /subblock/=. split.
      move: Hsub. by rewrite /subblock -Hb2 //= => [[H _]].
    move: Hpos => /( _ h (in_eq _ _)) => Hbounds.
    rewrite !cat_app -sublist_split; try lia.
    rewrite !(sublist_same 0 (fd_k h + fd_h h)) //.
    move: Hsub. rewrite /subblock => [[Hid [Hdat [Hpars [Hks Hhs]]]]].
    have Hbounds': 0 <= Int.unsigned (fd_blockIndex h) < fd_k h + fd_h h. apply Hwf. by rewrite in_cons eq_refl.
    (*we need to know the relationship between data_packets, parity_packets, etc*)
    subst; simpl in *.
    (*Do this so we don't need to prove same things twice:*)
    have Hsubupd: forall lo hi l, 0 <= Int.unsigned (fd_blockIndex h) < Zlength pkts -> 0 <= lo <= hi ->
        hi <= Zlength pkts ->
        subseq_option l (sublist lo hi pkts) ->
        subseq_option l (sublist lo hi (upd_Znth (Int.unsigned (fd_blockIndex h)) pkts (Some h))). {
      move => lo hi l1 Hhhi Hlohi Hhilen. 
      rewrite /subseq_option !Zlength_sublist; try lia; [|list_solve] => [[Hlens Hith]]. split. lia.
      move => j Hj.
      have [Hin | [Hout1 | Hout2]]: lo <= Int.unsigned (fd_blockIndex h) < hi \/
        0 <= Int.unsigned (fd_blockIndex h) < lo \/ hi <= Int.unsigned (fd_blockIndex h) < Zlength pkts by lia.
      * rewrite sublist_upd_Znth_lr; try lia.
        rewrite (upd_Znth_lookup' (hi - lo)); try lia; [|list_solve].
        case : (Z.eq_dec j (Int.unsigned (fd_blockIndex h) - lo)) => Hjh.
        -- (*the key part: Znth j (data_packets b1) MUST be None or Some h, since if it is anything else,
             pkts will not a well-formeed packet list -conradicts uniquenss*)
          case Hjth: (Znth j l1) => [p' |//]; last first. by right.
          left. f_equal.
          move : Hith => /(_ j Hj). rewrite Znth_sublist; try lia.
          have->: j + lo = Int.unsigned (fd_blockIndex h) by lia.
          rewrite Hjth => [[Hjth' | //]]. apply esym in Hjth'.
          have Hinj: In (Some p') pkts. rewrite -Hjth'. apply Znth_In. lia.
          have [Hidp' Hinlp']: fd_blockId p' = fd_blockId p /\ In p' l by 
            apply (@get_block_lists_prop_packets l (get_block_lists l) (fd_blockId p) pkts).
          apply Hwf.
          ++ rewrite in_cons. have->//: p' \in l by rewrite in_mem_In. by rewrite orbT.
          ++ by rewrite in_cons eq_refl.
          ++ by rewrite Hidp'.
          ++ move: Hjth'. rewrite (Heq _ _ Hint). rewrite mkseqZ_Znth; try lia.
             case_pickSeq l => [[Hxp]|//]. rewrite -Hxp. solve_sumbool. 
             by apply int_unsigned_inj in e.
        -- by apply Hith.
      * rewrite sublist_upd_Znth_r; try lia. by apply Hith.
      * rewrite sublist_upd_Znth_l; try lia. by apply Hith.
    } 
    split_all.
    + apply Hsubupd; try lia. by rewrite -Hk.
    + apply Hsubupd; try lia. by rewrite -Hh -Hk.
    + lia.
    + lia.
Qed.

Lemma int_eqP: forall (i1 i2: int),
  reflect (i1 = i2) (Int.eq i1 i2).
Proof.
  move => i1 i2. case Hint: (Int.eq i1 i2).
  - apply ReflectT. by apply Int.same_if_eq.
  - apply ReflectF. by apply forward_lemmas.int_eq_false_e.
Qed.

Opaque create_block_with_packet_black.

(*Intermediate case 3: we need a separate inductive lemma for [update_past_blocks]*)
Lemma update_past_blocks_subblocks: forall l blks curr state,
  wf_packet_stream (curr:: l) ->
  (forall p : fec_packet_act, In p (curr :: l) -> 0 <= fd_k p /\ 0 <= fd_h p) ->
  (forall b, In b blks -> exists b', In b' (get_blocks l) /\ subblock b b') ->
  forall b, In b (update_past_blocks blks curr state).1 ->
    exists b', In b' (get_blocks (curr :: l)) /\ subblock b b'.
Proof.
  move => l blks curr. elim: blks => [//= | h t /= IH st Hwf Hpos Hsubs b].
  case : st => [//| s stl].
  have Hht: (forall x, x \in l -> x \in curr :: l) by move => x Hx; rewrite in_cons Hx orbT.
  case Hc1: (s && int_le (fd_blockId curr) (blk_id h)) => [/= | //=].
  - move => Hin. (*use [get_blocks_sublist] here*)
    have [b1 [Hinb1 Hsub1]]: exists b' : block, In b' (get_blocks l) /\ subblock b b' by apply Hsubs; right.
    have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1).
    exists b2. split => //. by apply (subblock_trans Hsub1).
  - case Hc2: (Int.lt (fd_blockId curr) (blk_id h)) => /=.
    + move => [Hnew | Hold]; last first.
      * move : Hsubs => /( _ _ Hold) [b1 [Hinb1 Hsub1]].
        have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1).
        exists b2. split => //. by apply (subblock_trans Hsub1).
      * move: Hnew. case: (Z.eq_dec (fd_k curr) 1) => /= _ <-; apply create_block_subblock => //;by left.
    + case : (Int.eq (fd_blockId curr) (blk_id h)) /int_eqP => Hcurrh/= => [[Hb | Hin] |[Hhb | Hin]].
      * rewrite -Hb. move: Hsubs => /( _ h (in_eq _ _)) [b1 [Hinb1 Hsub1]].
        exists (add_fec_packet_to_block curr b1). by apply add_to_block_subblock.
      * move: Hsubs => /(_ b (or_intror Hin)) [b1 [Hinb1 Hsub1]].
        have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1).
        exists b2. split => //. by apply (subblock_trans Hsub1).
      * move: Hsubs => /(_ b (or_introl Hhb)) [b1 [Hinb1 Hsub1]].
        have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1).
        exists b2. split => //. by apply (subblock_trans Hsub1).
      * apply (IH stl) => //. move => b' Hinb'. apply Hsubs. by right.
Qed.

(*Now, finally we can show that every block in the decoder state is a subblock of some
  block from the received stream.*)
Theorem decoder_all_steps_state_subblocks: forall (received: seq fec_packet_act) (states: seq (seq bool)) (b: block),
  wf_packet_stream received ->
  (forall p, In p received -> 0 <= fd_k p /\ 0 <= fd_h p) -> (*TODO: should this be in wf?*)
  size received = size states ->
  In b (decoder_block_state received states) ->
  exists b', In b' (get_blocks received) /\ subblock b b'.
Proof.
  move => r sts b Hwf Hpos Hsz. rewrite /decoder_block_state /decoder_all_steps -(revK (combine _ _)) 
    foldl_rev -zip_combine rev_zip // {Hsz}. forget (rev sts) as s. rewrite {sts}.
  (*want to use (rev r) everywhere to simplify induction. Luckily rev is a permutation, so we can safely
    switch get_blocks'*)
  move => Hin.
  have: exists b', In b' (get_blocks (rev r)) /\ subblock b b'; last first.
    move => [b' [Hinb Hsub]]. exists b'. split => //. move: Hinb. rewrite -!in_mem_In.
    rewrite /get_blocks => /mapP [ t Hint Htup]. rewrite Htup. apply map_f.
    by rewrite (perm_mem (get_blocks_lists_perm Hwf (perm_rev' r))).
  move: Hin.
  have: wf_packet_stream (rev r) by apply (wf_perm Hwf); apply perm_rev'.
  rewrite {Hwf}.
  have: forall p, In p (rev r) -> 0 <= fd_k p /\ 0 <= fd_h p. { move => p Hp. apply Hpos.
    move: Hp. by rewrite -!in_mem_In mem_rev. } rewrite {Hpos}. 
  forget (rev r) as r'. rewrite {r}. rename r' into r.
  move: s b.
  elim : r => [//= s b Hpos Hwf | h t /= IH s b Hpos Hwf].
  - by rewrite zip_nil.
  - case : s => [| sh st].
    + by rewrite zip_nil_r.
    + rewrite /=. move: IH => /(_ st). set blks := (foldr
      (fun (x0 : fec_packet_act * seq bool) (z : seq block * seq packet) =>
       ((update_dec_state z.1 x0.1 x0.2).1, z.2 ++ (update_dec_state z.1 x0.1 x0.2).2)) 
      ([::], [::]) (zip t st)). move => IH.
      rewrite /update_dec_state. (*we don't actually care what blks is anymore; only that the IH applies*)
      move: IH.
      case : blks => [blks pkts]/=.
      have [Hallin [Hnonemp [Hlen [Heq Huniq]]]] := (get_block_lists_spec Hwf).
      (*Some additional results we need multiple times*)
      have Hpos': forall p : fec_packet_act, In p (h :: t) -> 0 <= fd_k p /\ 0 <= fd_h p by apply Hpos.
      have Hpos'': forall p, In p t -> 0 <= fd_k p /\ 0 <= fd_h p. move => p Hin. apply Hpos. by right.
      have Hwft: wf_packet_stream t by apply (wf_packet_stream_tl Hwf). 
      case: blks => [| blkh blkt]/=.
      * move => IH/=. move: Hallin => /( _ h (in_eq _ _)) => [[ps Hinps]].
        move => [Hb | Hf//]. rewrite -Hb. apply create_block_subblock => //=. by left.
      * move => IH/=. set lastblk := (Znth (Zlength (blkh :: blkt) - 1) (blkh :: blkt)).
        have Hlastin: In lastblk (blkh :: blkt). { subst lastblk. rewrite In_Znth_iff. 
          exists (Zlength (blkh :: blkt) - 1). list_solve. }
        (*case 1: we are in the last block*)
        case: (Int.eq (fd_blockId h) (blk_id lastblk)) /int_eqP => Hhlast.
        -- move =>/= Hin. apply In_upd_Znth in Hin. case: Hin => [Hb | Hin].
          ++ rewrite Hb. move: IH => /(_ lastblk Hpos'' Hwft Hlastin) [b' [Hinb' Hsub]].
             exists (add_fec_packet_to_block h b').
             by apply add_to_block_subblock.
          ++ (*for IH, we use [get_blocks_sublist] and transitivity*)
            move: IH => /(_ b Hpos'' Hwft Hin) [b1 [Hinb1 Hsub1]].
            have Hht: forall x, x \in t -> x \in h :: t. { move => x Hx. by rewrite in_cons Hx orbT. }
            have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1). exists b2. split => //.
            by apply (subblock_trans Hsub1).
        -- (*case 2: we are in a future block*)
          case Hfut: (Int.lt (blk_id lastblk) (fd_blockId h)).
          ++ rewrite -cat_cons cat_app in_app_iff => [[Hold | Hnew]].
            ** (*IH case again - TODO: less copy and paste*)
               move: IH => /(_ b Hpos'' Hwft Hold) [b1 [Hinb1 Hsub1]].
               have Hht: forall x, x \in t -> x \in h :: t. { move => x Hx. by rewrite in_cons Hx orbT. }
               have [b2 [Hinb2 Hsub2]]:=(get_blocks_sublist Hwf Hht Hinb1). exists b2. split => //.
               by apply (subblock_trans Hsub1).
            ** move : Hnew => /= [Hb |//]. rewrite -Hb. apply create_block_subblock => //=. by left.
          ++ (*Now, need result for update_past_blocks*)
            move => Hinpast.
            apply (update_past_blocks_subblocks Hwf) in Hinpast => //. move => b' Hinsub.
            apply sublist_In in Hinsub. by apply IH.
Qed. 

End DecoderSubblocks.

(*Part 3: All blocks from the encoder are well formed and are complete if they are recoverable*)
Section EncoderBlocks.

(*TODO:*)

End EncoderBlocks.

End Correctness.
