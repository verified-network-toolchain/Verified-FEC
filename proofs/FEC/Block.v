(*Definitions and proofs about RSE blocks, independent of the specific encoder/decoder *)
Require Import VST.floyd.functional_base.
Require Import AssocList.
Require Import IP.
Require Import AbstractEncoderDecoder.
Require Import CommonSSR.
Require Import ReedSolomonList.
Require Import ZSeq.
Require Import Endian.
Require Import ByteFacts.
(*Require Import ByteField.*) (*For byte equality - TODO: move to ByteFacts*)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.

(*Construct Inhabitant instance automatically*)
Ltac solve_inhab :=
  repeat match goal with
  | |- Z => exact 0%Z
  | |- nat => exact 0%N
  | |- int => exact Int.zero
  | |- byte => exact Byte.zero
  | |- ?A list => exact nil
  | |- seq ?A => exact nil
  | |- ?A option => exact None
  | |- bool => exact false
  end.

(*Decide equality for types and records made of primitives and machine sized ints*)
Ltac eq_dec_tac :=
  decide equality;
  repeat match goal with
  | [a : Z, b : Z |- {?a = ?b} + {?a <> ?b} ] => apply Z.eq_dec
  | [a : byte, b : byte |- {?a = ?b} + {?a <> ?b} ] => apply Byte.eq_dec
  | [a : list ?t, b : list ?t |- {?a = ?b} + {?a <> ?b} ] => apply list_eq_dec
  | [ |- forall x y : ?t, {x = y} + {x <> y}] => intros x y
  end.

Ltac split_all := repeat match goal with | |- ?p /\ ?q => split end.

Ltac solve_sumbool :=
  try match goal with
  | [ H: is_true (proj_sumbool ?x) |- _] => destruct x; [clear H | solve [inversion H]]; solve_sumbool
  | [ |- is_true (proj_sumbool ?x)] => destruct x; auto; try lia
  end.

(*Two results about [filter] Zlength we will need. TODO: where to put these?*)

Lemma Zlength_filter: forall {A: Type} (p: pred A) (l: list A),
  Zlength (filter p l) <= Zlength l.
Proof.
  move => A p l. rewrite Zlength_correct -size_length size_filter.
  rewrite -(Z2Nat.id (Zlength l)); [| list_solve]. apply inj_le. apply /leP.
  by rewrite ZtoNat_Zlength -size_length count_size.
Qed.

Lemma filter_all_Zlength: forall {A: eqType} (p: pred A) (s: seq A),
  Zlength (filter p s) = Zlength s <-> all p s.
Proof.
  move => A p s. rewrite !Zlength_correct -!size_length. split.
  - move => Hsz. rewrite -filter_all_size. apply /eqP. lia.
  - rewrite -filter_all_size => /eqP Hsz. by rewrite Hsz.
Qed.

(*TODO: should we replace in CommonSSR?*)
Lemma inP: forall {A: eqType} (x: A) (l: seq A),
  reflect (In x l) (x \in l).
Proof.
  move=> A x l. elim: l => [//= | h t /= IH].
  - by apply ReflectF.
  - rewrite in_cons. apply orPP => //.
    rewrite eq_sym. apply eqP.
Qed.

(*TODO: where to put?*)
Lemma zip_nil: forall {A B: Type} (l: list B),
  zip (@nil A) l = nil.
Proof.
  move => A B l. by case: l.
Qed.

(** IP/UDP Packets *)
(*Here, we require our packets to be valid IP/UDP packets*)

Definition valid_fec_packet (header: list byte) (contents: list byte) :=
  valid_packet header contents.

Definition packet_valid (p:packet) := valid_fec_packet (p_header p) (p_contents p).

Definition encodable (p: packet) : bool :=
  Z_le_lt_dec (Zlength ((p_header p) ++ (p_contents p))) fec_max_cols.

(*(k, isParity, block id, blockIndex*)
Record fec_data : Type := mk_data { fd_k : Z; fd_h : Z; fd_isParity : bool; fd_blockId: nat; fd_blockIndex : nat }.

Lemma fec_data_eq_dec: forall (f1 f2: fec_data), {f1 = f2} + {f1 <> f2}.
Proof.
  repeat eq_dec_tac.
Qed.

#[export]Instance fec_data_inhab: Inhabitant fec_data.
Proof.
constructor; solve_inhab.
Defined.

Definition fpacket := fec_packet fec_data.

Definition f_packet : fpacket -> packet := (@p_packet fec_data).

Coercion f_packet : fpacket >-> packet.

Definition fpacket_eq_axiom  := (@fec_packet_eqP _ fec_data_eq_dec).

Definition fpacket_eqMixin := EqMixin fpacket_eq_axiom.
Canonical fpacket_eqType := EqType fpacket fpacket_eqMixin.

#[export]Instance fpacket_inhab : Inhabitant fpacket := 
  @mk_fecpkt fec_data packet_inhab fec_data_inhab.

Definition p_fec_data' : fpacket -> fec_data := @p_fec_data fec_data.
Coercion p_fec_data' : fpacket >-> fec_data.

(** Representing Blocks *)

(*Timeout is 10 seconds. We give this in microseconds. TODO: is Z ok?*)
(*
Definition fec_timeout : Z := proj1_sig (opaque_constant 10000000).
Definition fec_timeout_eq : fec_timeout = 10000000%Z := proj2_sig (opaque_constant _).
*)
Section Block.

Record block := mk_blk { blk_id: nat;
  data_packets: list (option fpacket); 
  parity_packets: list (option fpacket);
  blk_k : Z; blk_h : Z;
  black_complete: bool; black_time : Z}.

#[export]Instance block_inhab: Inhabitant block :=
  mk_blk 0 nil nil 0 0 false 0.

#[export]Instance eta_block: Settable _ := 
  settable! mk_blk <blk_id; data_packets; parity_packets; blk_k; blk_h; black_complete; black_time>.

Definition block_to_tuple (b: block) : (nat * seq (option fpacket) * seq (option fpacket) * 
  Z * Z * bool * Z) :=
  (blk_id b, data_packets b, parity_packets b, blk_k b, blk_h b, black_complete b, black_time b).

Definition tuple_to_block (t: (nat * seq (option fpacket) * seq (option fpacket) * Z * Z * bool * Z)) :
  block :=
  mk_blk (t.1.1.1.1.1.1) (t.1.1.1.1.1.2) (t.1.1.1.1.2) (t.1.1.1.2) (t.1.1.2) (t.1.2) (t.2).

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

(*Nicer definitions for packets in a block*)
Definition packet_in_data (p: fpacket) (b: block) : bool :=
  (Some p) \in (data_packets b).
Definition packet_in_parity (p: fpacket) (b: block) : bool :=
  (Some p) \in (parity_packets b).
Definition packet_in_block (p: fpacket) (b: block) : bool :=
  packet_in_data p b || packet_in_parity p b.

Lemma data_in_block p b :
  packet_in_data p b ->
  packet_in_block p b.
Proof.
  by rewrite /packet_in_block => ->.
Qed.

Lemma parity_in_block p b:
  packet_in_parity p b ->
  packet_in_block p b.
Proof.
  by rewrite /packet_in_block => ->; rewrite orbT.
Qed.

Lemma packet_in_block_eq p b:
  packet_in_block p b =
  ((Some p) \in data_packets b) ||
  ((Some p) \in parity_packets b).
Proof.
  by [].
Qed. 
(*Well-formed block *)
Definition block_wf (b: block) : Prop :=
  (*k and h are within the required bounds*)
  0 < blk_k b <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
  0 < blk_h b <= ByteFacts.fec_max_h /\
  (*All packets store correct values of k and h*)
  (forall p, packet_in_block p b -> 
    (fd_k p) = blk_k b /\ (fd_h p) = blk_h b) /\
  (*All packets have same blockId *)
  (forall p, packet_in_block p b ->
    fd_blockId (p_fec_data p) = blk_id b) /\
  (*Packet sequence numbers are correct*)
  (forall p (i: Z), packet_in_block p b ->
    Znth i (data_packets b ++ parity_packets b) = Some p <-> 
    i = Z.of_nat (fd_blockIndex p)) /\
  (*Lengths are correct*)
  Zlength (data_packets b) = blk_k b /\
  Zlength (parity_packets b) = blk_h b /\
  (*All data packets are encodable*)
  (forall p, packet_in_data p b -> encodable p) /\
  (*All packets are valid packets*)
  (forall p, packet_in_block p b -> packet_valid p) /\
  (*Parity packets are marked correctly*)
  (forall p, packet_in_data p b -> fd_isParity p = false) /\
  (forall p, packet_in_parity p b -> fd_isParity p).

(*Definition range_lt_le_dec: forall (x y z: Z),
  { x < y <= z} + {~(x < y <= z)}.
Proof.
  intros. destruct (Z_lt_ge_dec x y).
  - destruct (Z_le_gt_dec y z).
    + left. auto.
    + right. lia.
  - right. lia.
Defined.*)
(*
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
*)
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
Section ListMax.
Definition list_max_nonneg {A: Type} (f: A -> Z) (l: list A) : Z :=
  fold_right (fun x y => Z.max (f x) y) 0 l.

Lemma list_max_nonneg_in: forall {A: eqType} (f: A -> Z) (l: list A) (x: A),
  0 <= f x ->
  x \in l ->
  0 <= f x <= (list_max_nonneg f l).
Proof.
  move => A f l x. rewrite /list_max_nonneg. 
  elim : l => [//= | h t /= IH Hfx].
  rewrite in_cons => /orP[/eqP Hhx | Hin].
  - rewrite Hhx. split. by subst. apply Z.le_max_l.
  - split. by []. eapply Z.le_trans. apply IH => //. 
    apply Z.le_max_r.
Qed.

Lemma list_max_nonneg_lb: forall {A: Type} (f: A -> Z) (l: list A),
  0 <= list_max_nonneg f l.
Proof.
  move => A f l. elim: l => [// | h t /= IH]. lia.
Qed.

Lemma list_max_nonneg_ub: forall {A: eqType} (f: A -> Z) (l: list A) n,
  0 <= n ->
  (forall y, y \in l -> f y <= n) ->
  list_max_nonneg f l <= n.
Proof.
  move => A f l n Hn. elim : l => [/= Hall | h t /= IH Hall]. lia.
  apply Z.max_lub. apply Hall. by rewrite in_cons eq_refl. 
  apply IH. move => y Hy. apply Hall. by rewrite in_cons Hy orbT.
Qed.

Lemma list_max_nonneg_eq: forall {A: eqType} (f: A -> Z) (l: list A) (x: A) n,
  x \in l ->
  0 <= f x ->
  f x = n ->
  (forall y, y \in l -> f y <= n) ->
  list_max_nonneg f l = n.
Proof.
  move => A f l x n Hin Hfx Hn Hall.
  have Hlb:= (list_max_nonneg_in Hfx Hin). rewrite Hn in Hfx.
  have Hub:=(list_max_nonneg_ub Hfx Hall). lia.
Qed. 

Lemma list_max_nonneg_exists: forall {A: eqType} (f: A -> Z) (l: seq A) (x: A),
  x \in l ->
  0 <= f x ->
  exists y, y \in l /\ list_max_nonneg f l = f y.
Proof.
  move => A f l. elim : l => [//= | h t /= IH x].
  rewrite in_cons => /orP[/eqP Hx | Hint] => Hfx.
  - subst. (*this is annoying, need to see if any element in tail with >= 0*)
    case: (all (fun y => Z_gt_le_dec 0 (f y)) t) /allP => Hall.
    + exists h. split. by rewrite in_cons eq_refl. 
      apply Z.max_l. apply list_max_nonneg_ub => //. move => y Hy.
      move: Hall => /(_ _ Hy) Hlt. solve_sumbool. lia.
    + move: Hall => /allP /allPn [y Hyin Hylt]. have Hfy: 0 <= f y. move: Hylt.
        by case: (Z_gt_le_dec 0 (f y)).
      move: IH => /(_ _ Hyin Hfy) [z [Hinz Hmax]].
      have [Hx | Hz]: f z <= f h \/ f h <= f z by lia.
      * exists h. split. by rewrite in_cons eq_refl. lia.
      * exists z. split. by rewrite in_cons Hinz orbT. lia.
  - move: IH => /(_ _ Hint Hfx) [y [Hiny Hfy]].
    have [Hx | Hy]: f y <= f h \/ f h <= f y by lia.
      * exists h. split. by rewrite in_cons eq_refl. lia.
      * exists y. split. by rewrite in_cons Hiny orbT. lia.
Qed.

End ListMax.

  
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

(* Some results about [blk_c]*)

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
Definition block_encoded (b: block) : Prop :=
  (*The block has a data packet that has length c (so c is actually the max, not just an upper bound)*)
  (exists p, packet_in_data p b /\ 
    Zlength (p_header (f_packet p) ++ p_contents (f_packet p)) = blk_c b) /\
  (*All parities have length c*)
  (forall p, packet_in_parity p b -> 
    Zlength (p_contents (f_packet p)) = blk_c b) /\
  (*All data packets (including headers) have length <= c*)
  (forall p, packet_in_data p b -> 
    Zlength (packet_bytes (f_packet p)) <= blk_c b) /\
  parities_valid (blk_k b) (blk_c b) (parity_mx b) (packet_mx b).

Definition isNone {A: Type} (o: option A) :=
  negb (isSome o).

Definition block_in_progress (b: block) : bool :=
  all isNone (parity_packets b).

(*A block is "recoverable" if we have at least k total packets*)
Definition recoverable (b: block) : bool :=
  Z_ge_lt_dec (Zlength (filter isSome (data_packets b)) + Zlength (filter isSome (parity_packets b))) 
    (Zlength (data_packets b)) .

End Block.

(*Some additional results about [blk_c] that will be useful*)
Section C.

(*For complete blocks, we can calculate blk_c just by taking max length of data packets*)
Lemma blk_c_encoded: forall b,
  block_encoded b ->
  blk_c b = list_max_nonneg
      (fun o : option fpacket =>
       match o with
       | Some p => Zlength (p_header (f_packet p) ++ p_contents (f_packet p))
       | None => 0
       end) (data_packets b).
Proof.
  move => b. rewrite /block_encoded => [[[p [Hinp Hlenp]] [Hparc [Hdatac _]]]].
  symmetry. eapply list_max_nonneg_eq. apply Hinp. list_solve.
  - by [].
  - move => y. case : y => [y /= Hiny | _].
    + by apply Hdatac.
    + rewrite /blk_c. case : [seq x <- parity_packets b | isSome x] => [|/= h t].
      apply list_max_nonneg_lb. case : h.
      move => ?. list_solve. apply list_max_nonneg_lb.
Qed.

(*We need to know that c is positive - ie: some packet has nonzero length. This is a weak bound;
  we know that each packet really has length at least 28 for IP/UDP header*)
Lemma blk_c_pos: forall (b: block),
  block_wf b ->
  block_encoded b ->
  0 < blk_c b.
Proof.
  move => b. rewrite /block_wf /block_encoded => 
    [[Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc Hvalid]]]]]]]]] [[p [Hinp Hlenp]] _].
  rewrite -Hlenp. have: packet_valid p. apply Hvalid. by apply data_in_block. 
  rewrite /packet_valid /valid_fec_packet.
  move => /andP[ Hle _]. move: Hle. 
  case : (Z_le_lt_dec 8 (Zlength (p_header p))) => Hle//=. 
  rewrite Zlength_app. list_solve.
Qed.

Lemma blk_c_bound: forall b,
  block_in_progress b ->
  block_wf b ->
  blk_c b <= fec_max_cols.
Proof.
  move => b. rewrite /block_in_progress /block_wf => Hprog [Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc Hval]]]]]]]].
  rewrite /blk_c.
  have->: [seq x <- parity_packets b | isSome x] = [seq x <- parity_packets b | pred0 x]. {
    apply eq_in_filter. move => y/=. case: y => [x Hinx |//]. by move: Hprog => /allP /(_ _ Hinx). }
  rewrite filter_pred0. apply list_max_nonneg_ub. rep_lia. move => o. case: o => [p Hinp|]; [|rep_lia].
  move: Henc => /( _ _ Hinp). rewrite /encodable => Hlt. by solve_sumbool.
Qed.

Lemma pars_in_progress: forall b,
  block_in_progress b ->
  [seq x <- parity_packets b | isSome x] = nil.
Proof.
  move => b Hprog.
  rewrite -(filter_pred0 (parity_packets b)). apply eq_in_filter. move: Hprog.
  rewrite /block_in_progress => /allP Hprog x Hinx. move: Hprog => /(_ x Hinx)/=.
  move: Hinx. by case : x.
Qed.

Lemma blk_c_in_progress: forall b,
  block_in_progress b ->
  blk_c b =
  list_max_nonneg
    (fun o : option fpacket =>
     match o with
     | Some p => Zlength (p_header p ++ p_contents p)
     | None => 0
     end) (data_packets b).
Proof.
  move => b Hprog. rewrite /blk_c.
  by rewrite pars_in_progress.
Qed.

End C.

(*Nonempty blocks*)
Section Nonempty.

(*Testing if a block is nonempty*)
Definition block_elt (b: block) : option fpacket :=
  match (pmap id (data_packets b ++ parity_packets b)) with
  | nil => None
  | h :: _ => Some h
  end.

(*Testing if the block has at least one data packet*)
Definition data_elt (b: block): option fpacket :=
  match (pmap id (data_packets b)) with
  | nil => None
  | h :: _ => Some h
  end.

Lemma data_block_elt: forall b,
  data_elt b ->
  block_elt b.
Proof.
  move => b. rewrite /data_elt /block_elt. case Hp: (pmap id (data_packets b)) => [//| h t].
  move => _. case Hp2: (pmap id (data_packets b ++ parity_packets b)) => [|//].
  have: h \in pmap id (data_packets b ++ parity_packets b). by rewrite pmap_cat mem_cat Hp in_cons eq_refl.
  by rewrite Hp2.
Qed.

End Nonempty.

(* Other useful results about wf blocks, makes using the definition a bit easier*)
Section WFFacts.

(*An easier way to use the [Znth] condition in many cases*)
Lemma block_wf_znth: forall p b,
  block_wf b ->
  packet_in_block p b ->
  Znth (Z.of_nat (fd_blockIndex p)) 
    (data_packets b ++ parity_packets b) = Some p.
Proof.
  move=> p b [Hkbound [Hhbound [Hkh [Hid [Hidx _]]]]] Hin.
  move: Hidx => /(_ _ (Z.of_nat (fd_blockIndex p)) Hin) Hnth.
  by apply Hnth.
Qed.


(*Useful for proving [wf_packet_stream] (below)*)
Lemma in_wf_blockIndex_inj: forall b p1 p2,
  block_wf b ->
  packet_in_block p1 b ->
  packet_in_block p2 b ->
  (*In (Some p1) (data_packets b ++ parity_packets b) ->
  In (Some p2) (data_packets b ++ parity_packets b) ->*)
  fd_blockIndex p1 = fd_blockIndex p2 ->
  p1 = p2.
Proof.
  move => b p1 p2 Hwf Hin1 Hin2 Heq.
  have Hnth1:=(block_wf_znth Hwf Hin1).
  have Hnth2:=(block_wf_znth Hwf Hin2).
  rewrite Heq in Hnth1. rewrite Hnth2 in Hnth1.
  by case: Hnth1.
Qed.

Lemma in_data_idx_bound: forall (b: block) (p: fpacket),
  block_wf b ->
  packet_in_data p b ->
  Z.of_nat (fd_blockIndex p) < blk_k b.
Proof.
  move => b p [Hkbound [Hhound [_ [_ [Hnth [Hlen1 [Hlen2 _]]]]]]] Hin.
  have Hin':=Hin. move: Hin' => /inP.
  rewrite In_Znth_iff Hlen1 => [[i [Hi]]].
  rewrite -(Znth_app1 _ _ (data_packets b) (parity_packets b)); [|lia].
  rewrite Hnth; try lia. by apply data_in_block.
Qed.

Lemma in_parity_idx_bound: forall (b: block) (p: fpacket),
  block_wf b ->
  packet_in_parity p b ->
  blk_k b <= Z.of_nat (fd_blockIndex p) < blk_k b + blk_h b.
Proof.
  move => b p [Hkbound [Hhound [_ [_ [Hnth [Hlen1 [Hlen2 _]]]]]]] Hin.
  have Hin':=Hin. move: Hin' => /inP.
  rewrite In_Znth_iff Hlen2 => [[i [Hi]]].
  have->: i = (blk_k b + i) - (Zlength (data_packets b)) by lia.
  rewrite -(Znth_app2 _ _ (data_packets b) (parity_packets b)); try lia.
  rewrite Hnth; try lia. by apply parity_in_block.
Qed.

Lemma in_block_idx_bound: forall b p,
  block_wf b ->
  packet_in_block p b ->
  0 <= Z.of_nat (fd_blockIndex p) < fd_k p + fd_h p.
Proof.
  move => b p Hwf Hin.
  have [Hk Hh]: fd_k p = blk_k b /\ fd_h p = blk_h b  by apply Hwf.
  case Hwf => [Hhbound [Hkbound _]].
  move: Hin => /orP[Hin | Hin].
  - apply in_data_idx_bound in Hin => //. lia.
  - apply in_parity_idx_bound in Hin => //. lia.
Qed. 

(*For proving the hard condition (the index iff) in [block_wf]: the following 2 lemmas make it a bit easier
  in some situations*)

Lemma block_wf_list_equiv: forall (l: list (option fpacket)),
  (forall p i, (Some p) \in l -> Znth i l = Some p <-> i = Z.of_nat (fd_blockIndex (p_fec_data' p))) <->
  (forall p i, 0 <= i < Zlength l ->
    (Some p) \in l -> Znth i l = Some p <-> i = Z.of_nat (fd_blockIndex (p_fec_data' p))).
Proof.
  move => l. split.
  - move => Hcon p i Hi. by apply Hcon.
  - move => Hcon p i Hi. split.
    + move => Hith. have Hib: 0 <= i < Zlength l. apply Znth_inbounds. by rewrite Hith.
      by apply Hcon.
    + move => Hidx.
      have [j [Hj Hjth]]: exists j, 0 <= j < Zlength l /\ Znth j l = Some p.
        rewrite -In_Znth_iff. by apply /inP.
      have: j = Z.of_nat (fd_blockIndex (p_fec_data' p)) by apply Hcon. 
      by move => Hj'; subst.
Qed.

(*A generic way to handle the iff condition in block_wf when adding a new element*)
Lemma block_wf_list_upd_Znth: forall (l: list (option fpacket)) (p: fpacket) j,
  (forall (p: fpacket) i, (Some p) \in l -> Znth i l = Some p <-> 
    i = Z.of_nat (fd_blockIndex p)) ->
  0 <= j < Zlength l ->
  Znth j l = None ->
  j = Z.of_nat (fd_blockIndex p) ->
  (forall (p': fpacket) i, (Some p') \in (upd_Znth j l (Some p)) -> 
    Znth i (upd_Znth j l (Some p)) = Some p' <-> i = Z.of_nat (fd_blockIndex p')).
Proof.
  move => l p j Hall Hj Hjidx Hjth. rewrite block_wf_list_equiv.
  move => p' i. zlist_simpl. move => Hi /inP Hin.
  apply In_upd_Znth in Hin. case: Hin => [[Hp''] | Hin].
  - subst. split.
    + rewrite (upd_Znth_lookup' (Zlength l)); try lia.
      case : (Z.eq_dec i (Z.of_nat (fd_blockIndex p))) => //= Hij Hith.
      apply Hall => //. apply /inP. rewrite In_Znth_iff. by exists i.
    + move ->. by rewrite upd_Znth_same.
  - subst. split.
    + rewrite (upd_Znth_lookup' (Zlength l)); try lia.
      case : (Z.eq_dec i (Z.of_nat (fd_blockIndex p))) => //=.
      * move => Hi' [Hp]. by subst.
      * move => Hi' Hith. apply Hall => //. by apply /inP.
    + move ->. have Hnth: Znth (Z.of_nat (fd_blockIndex (p_fec_data' p'))) l 
      = Some p'. apply Hall => //. by apply /inP.
      have Hbound: 0 <= (Z.of_nat (fd_blockIndex (p_fec_data' p'))) < Zlength l by apply Znth_inbounds; rewrite Hnth.
      rewrite upd_Znth_diff //; try lia. move => Heq.
      rewrite Heq in Hnth. by rewrite Hjidx in Hnth.
Qed.

(*This is convenient to have*)
Lemma blockIndex_Znth_data: forall (b: block) (p: fpacket),
  block_wf b ->
  packet_in_data p b ->
  Znth (Z.of_nat (fd_blockIndex p)) (data_packets b) = Some p.
Proof.
  move => b p Hwf.
  case Hwf => [_ [_ [_ [_ [Hidx _]]]]] Hin.
  have Hin':= Hin. apply data_in_block in Hin'. 
  apply block_wf_znth in Hin' => //.
  rewrite Znth_app1 in Hin' => //.
  have->:Zlength (data_packets b) = blk_k b by apply Hwf.
  by apply in_data_idx_bound.
Qed.

End WFFacts.

(** Getting blocks from a stream *)
(*This is surprisingly complex, particularly because we want to reason about streams in which the order
  of the packets changes. The full block structure includes some uneccesary (but helpful) metadata, so
  we first simply find the list (option fec_packet) for each block, then build the full structure later.*)

Section WfStream.

(*A valid stream of packets that will eventually produce well-formed blocks*)
Definition wf_packet_stream (l: list fpacket) :=
  (forall (p1 p2 : fpacket), p1 \in l -> p2 \in l -> 
    fd_blockId p1 = fd_blockId p2 -> fd_k p1 = fd_k p2 /\ fd_h p1 = fd_h p2) /\
  (forall (p1 p2: fpacket), p1 \in l -> p2 \in l -> 
    fd_blockId p1 = fd_blockId p2 -> fd_blockIndex p1 = fd_blockIndex p2 -> p1 = p2) /\
  (forall (p: fpacket), p \in l -> Z.of_nat (fd_blockIndex p) < fd_k p + fd_h p) /\
  (forall (p: fpacket), p \in l -> 0 <= fd_k p /\ 0 <= fd_h p).

Lemma wf_substream: forall l1 l2,
  wf_packet_stream l1 ->
  (forall x, x \in l2 -> x \in l1) ->
  wf_packet_stream l2.
Proof.
  move => l1 l2 [Hkh [Hinj [Hbounds Hpos]]] Hsub. rewrite /wf_packet_stream. split_all.
  - move => p1 p2 Hp1 Hp2. apply Hkh; by apply Hsub.
  - move => p1 p2 Hp1 Hp2. apply Hinj; by apply Hsub.
  - move => p Hp. by apply Hbounds; apply Hsub.
  - move => p Hp. apply Hpos. by apply Hsub.
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
Lemma wf_all_nonneg: forall (l: list fpacket),
  wf_packet_stream l ->
  (forall (x: fpacket), x \in l -> 0 <= fd_k x + fd_h x).
Proof.
  move => l [_ [_ [Hbounds _]]] x Hinx. move: Hbounds => /(_ x Hinx). lia.
Qed.

End WfStream. 

(*Helps with using this specific pickSeq instance*)
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

Definition block_list := alist nat_eqType (seq_eqType (option_eqType fpacket_eqType)).
(*Canonical block_list_eqType : eqType := 
  EqType block_list (alist_eqMixin nat_eqType 
    (seq_eqType (option_eqType fpacket_eqType))).
*)
(*Packet should have same blockId*)
Definition update_packet_list (p: fpacket) (l: list (option fpacket)) :=
  upd_Znth (Z.of_nat (fd_blockIndex p)) l (Some p).

Definition new_packet_list (p: fpacket) : list (option fpacket) :=
  upd_Znth (Z.of_nat  (fd_blockIndex p)) (zseq (fd_k p + fd_h p) None) (Some p).

Definition update_block_list (idx: nat) (p: fpacket) (b: block_list) :=
  update_or_add idx (new_packet_list p) (update_packet_list p) b.

(*Use this to get lists for each block*)
Definition get_block_lists (l: list fpacket) : block_list :=
  foldr (fun (p: fpacket) acc => update_block_list (fd_blockId p) p acc) (@empty _ _) l.

(*Theorems about this*)

(*The above function is unwieldy to use directly for all the theorems we need. Instead, we give 5 
  conditions that (get_blocks l) satisfies. Then we prove that any 2 lists that satisfy these 5
  conditions are equal up to permutation. With only 1 exception, we will only need
  these 5 conditions for all subsequent proofs; it is much nicer than needing induction and direct
  reasoning about association lists for everything*)

(*Prop1: Every packet in the input belongs to some (unique, as we will show) list in the output. We need this
  first to prove the second property*)
Lemma get_blocks_list_allin: forall (l: list fpacket) (p: fpacket),
  p \in l ->
  exists pkts, (fd_blockId p, pkts) \in al (get_block_lists l).
Proof.
  move => l p. rewrite /get_block_lists. elim : l => [//= | h t /=].
  rewrite /update_block_list => IH. move => Hor.
  case Hhp: (fd_blockId h == fd_blockId p).
  - move: Hhp => /eqP Hhp. rewrite Hhp. apply update_or_add_exists.
  - move: Hhp => /eqP Hhp. move: Hor; rewrite in_cons => /orP[/eqP Heq // | Hin].
    by rewrite Heq in Hhp.
    setoid_rewrite update_or_add_diff; last first. by apply /eqP.
    by apply IH.
Qed.

(*We need a few auxilliary lemmas to prove the rest*)

(*This will follow from later propositions, but we need it now first*)
Lemma get_blocks_list_from_src: forall (l: list fpacket) (i: nat) (pkts: list (option (fpacket)))
  (p: fpacket),
  (forall (x: fpacket), x \in l -> 0 <= fd_k x + fd_h x) ->
  (i, pkts) \in al (get_block_lists l) ->
  (Some p) \in pkts ->
  p \in l.
Proof.
  move => l i pkts p. move: pkts. elim : l => [//= | h t /=].
  rewrite /update_block_list. move => IH pkts Hbound.
  case: (i == (fd_blockId h)) /eqP => Hih.
  - rewrite -Hih/=. move => Hin. apply update_or_add_same in Hin.
    case : Hin => [[oldV [Hin Hpkts]] | [Hpkts Hnotin]].
    + rewrite Hpkts. rewrite /update_packet_list. move => /inP Hinp.
      apply In_upd_Znth in Hinp. rewrite in_cons. 
      case : Hinp => [[Hhp] // | Hinp]. by subst; rewrite eq_refl.
      rewrite (IH oldV) //. by rewrite orbT.
      move => x Hinx. apply Hbound. by rewrite in_cons Hinx orbT.
      by apply /inP.
    + rewrite Hpkts /new_packet_list => /inP Hin. apply In_upd_Znth in Hin.
      rewrite in_cons.
      case : Hin => [[Hinp] // | Hinp]. by subst; rewrite eq_refl.
      move: Hinp.
      have H0kh: 0 <= fd_k h + fd_h h. apply Hbound. by rewrite in_cons eq_refl.
      rewrite In_Znth_iff zseq_Zlength // => [[j [Hj Hnth]]]. 
      by rewrite zseq_Znth in Hnth.
  - move => Hin. rewrite update_or_add_diff in Hin; last first.
      rewrite eq_sym. by apply /eqP. 
    move => Hinp. rewrite in_cons. rewrite (IH pkts) => //.
    by rewrite orbT. move => x Hinx. apply Hbound.
    by rewrite in_cons Hinx orbT.
Qed.

(*1.5: all lists are nonempty; this element also has the same blockId and can be used to calculate the length*)
Lemma get_blocks_list_nonempty: forall (l: list fpacket) (i: nat) (pkts: list (option (fpacket))),
  wf_packet_stream l ->
  (i, pkts) \in al (get_block_lists l) ->
  exists (p: fpacket), (Some p) \in pkts /\ fd_blockId p = i /\ Zlength pkts = fd_k p + fd_h p.
Proof.
  move => l i. elim : l => [//= | h t /=].
  rewrite /update_block_list. move => IH pkts Hwf. 
  case: (i == (fd_blockId h)) /eqP => Hih.
  - rewrite -Hih/=. move => Hin. apply update_or_add_same in Hin.
    case : Hin => [[oldV [Hin Hpkts]] | [Hpkts Hnotin]].
    + have Hin':=Hin. apply IH in Hin => //; last first. by apply (wf_packet_stream_tl Hwf).
      case : Hin => [p [Hinp [Hidp Hlenp]]]. rewrite Hpkts /update_packet_list Zlength_upd_Znth.
      have Hinpt: p \in t. { apply (@get_blocks_list_from_src t i oldV) => //.
        apply wf_all_nonneg. apply (wf_packet_stream_tl Hwf). } 
      exists h. have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. {
        move: Hwf; rewrite /wf_packet_stream => [[Hkh _]].
        apply Hkh. by rewrite in_cons Hinpt orbT. by rewrite in_cons eq_refl.
        by rewrite -Hih Hidp. }
      repeat split => //; try lia. apply /inP. apply upd_Znth_In. move: Hwf.
      rewrite /wf_packet_stream => [[_ [_[ /(_ h)]]]]. rewrite in_cons eq_refl/= => Hb _.
      rewrite Hlenp Hk Hh. split; try lia. by apply Hb.
    + rewrite Hpkts /new_packet_list. exists h.
      have Hbound: 0 <= Z.of_nat (fd_blockIndex h) < fd_k h + fd_h h. {
        move: Hwf; rewrite /wf_packet_stream => [[_ [_ [/(_ h) ]]]]. rewrite in_cons eq_refl/= => Hb _.
        split; try lia. by apply Hb. }
      repeat split => //. 2: rewrite upd_Znth_Zlength zseq_Zlength.
      apply /inP.
      apply upd_Znth_In. rewrite zseq_Zlength. all: lia.
  - move => Hin. rewrite update_or_add_diff in Hin; last first. by rewrite eq_sym; apply /eqP.
    apply IH => //. by apply (wf_packet_stream_tl Hwf).
Qed.

(*Prop2: All lists are nonempty (each contains at least 1 packet). We just proved a stronger version of this*)

(*Prop3: for every entry in the block list, its length is k+h for ANY packet in it*)
Lemma get_blocks_lists_lens: forall (l: list fpacket) (i: nat) (pkts: list (option (fpacket)))
  (p: fpacket),
  wf_packet_stream l ->
  (i, pkts) \in al (get_block_lists l) ->
  (Some p) \in pkts ->
  Zlength pkts = (fd_k p + fd_h p).
Proof.
  move => l i pkts p. move: pkts p. elim : l => [//= | h t /=].
  rewrite /update_block_list. move => IH pkts p Hwf.
  case: (i == (fd_blockId h)) /eqP => Hih.
  - rewrite -Hih/=. move => Hin. apply update_or_add_same in Hin.
    case : Hin => [[oldV [Hin Hpkts]] | [Hpkts Hnotin]].
    + rewrite Hpkts /update_packet_list Zlength_upd_Znth => /inP Hinp.
      apply In_upd_Znth in Hinp. case : Hinp => [[Hhp] | Hinp].
      * rewrite Hhp.
        have Hin':=Hin.
        apply get_blocks_list_nonempty in Hin; last first. by apply (wf_packet_stream_tl Hwf).
        case : Hin => [p' [Hinp' [Hidp' Hlenold]]]. rewrite Hlenold.
        have [Hk Hh]: fd_k p' = fd_k h /\ fd_h p' = fd_h h. { have Hwf':=Hwf.
          move: Hwf' => [Hkh [_ Hbounds]]. apply Hkh.
          - rewrite in_cons. have->: p' \in t; last first. by rewrite orbT.
            eapply (get_blocks_list_from_src).
            apply wf_all_nonneg. apply (wf_packet_stream_tl Hwf).
            apply Hin'. by [].
          - by rewrite in_cons eq_refl.
          - by rewrite Hidp'. }
        by rewrite Hk Hh.
      * apply IH => //. by apply (wf_packet_stream_tl Hwf). by apply /inP.
    + have H0kh: 0 <= fd_k h + fd_h h. move: Hwf => [_[_ Hbound]].
        have: 0 <= Z.of_nat (fd_blockIndex h) < fd_k h + fd_h h.
        split; try lia. apply Hbound. by rewrite in_cons eq_refl. lia.
      rewrite Hpkts /new_packet_list Zlength_upd_Znth zseq_Zlength // => /inP Hin.
      apply In_upd_Znth in Hin. move: Hin => [[Hph] |]. by rewrite Hph.
      rewrite In_Znth_iff zseq_Zlength //. move => [j [Hj Hnth]].
      by rewrite zseq_Znth in Hnth.
  - move => Hin. rewrite update_or_add_diff in Hin; last first. rewrite eq_sym. by apply /eqP.
    apply IH => //. apply (wf_packet_stream_tl Hwf).
Qed.

(*Prop3: For every entry in the block list, we give the list explicitly. This is the most important
  property; it says that each list contains all packets in the input with that blockId, in their
  correct (blockIndex) places*) 
Lemma get_block_lists_in: forall (l: list fpacket) (i: nat) (pkts: list (option (fpacket))),
  wf_packet_stream l ->
  (i, pkts) \in al (get_block_lists l) ->
  pkts = mkseqZ (fun j => 
    pickSeq (fun (p': fpacket) => (fd_blockId p' == i) &&
      Z.eq_dec j (Z.of_nat (fd_blockIndex p'))) l) (Zlength pkts).
Proof.
  move => l i pkts. move: pkts. elim : l => [//=| h t /=].
  rewrite /update_block_list. move => IH pkts Hwf. 
  case: (i == (fd_blockId h)) /eqP => Hih.
  - rewrite -Hih eq_refl /=. move => Hin. apply update_or_add_same in Hin.
    case : Hin => [[oldV [Holdv Hpkts]] | Hnew].
    + have Holdv':=Holdv. apply IH in Holdv.
      * rewrite {1}Hpkts Holdv /update_packet_list. 
        (*To show these are equal, we will compare element-wise*)
        have Hnonneg: 0 <= Zlength oldV by list_solve.
        have Hlens: Zlength oldV = Zlength pkts. { rewrite Hpkts. rewrite /update_packet_list. list_solve. }
        apply Znth_eq_ext; rewrite Zlength_upd_Znth !mkseqZ_Zlength //. list_solve.
        move => j Hj. simpl in *. rewrite mkseqZ_Znth; [|lia]. 
        rewrite (upd_Znth_lookup' (Zlength oldV)); try lia. 
        rewrite mkseqZ_Znth; try lia.
        by case : (Z.eq_dec j (Z.of_nat (fd_blockIndex h))). rewrite mkseqZ_Zlength. lia. list_solve.
        (*to prove length, we use fact that there is some element there*)
        have Holdv'':=Holdv'.
        apply get_blocks_list_nonempty in Holdv'; last first.
          apply (wf_packet_stream_tl Hwf).
        case : Holdv' => [p [Hinp [Hpid Holdlen]]].
        rewrite Holdlen. have Hwf':=Hwf. move: Hwf' => [Hkh [_ Hbounds]].
        have [Hk Hh]: fd_k p = fd_k h /\ fd_h p = fd_h h. { apply Hkh.
          rewrite in_cons. have->: p \in t; last first. by apply orbT.
          eapply get_blocks_list_from_src. apply wf_all_nonneg.
          apply (wf_packet_stream_tl Hwf). apply Holdv''. by []. by rewrite in_cons eq_refl.
          by rewrite Hpid. }
        rewrite Hk Hh. split; try lia. apply Hbounds. by rewrite in_cons eq_refl.
      * apply (wf_packet_stream_tl Hwf).
    + case : Hnew => [Hpkts Hnotin].
      have Hidxb: 0 <= Z.of_nat (fd_blockIndex h) < fd_k h + fd_h h. {
        move: Hwf => [_ [_ Hbounds]]. split; try lia. apply Hbounds. by rewrite in_cons eq_refl. }
      rewrite Hpkts /new_packet_list Zlength_upd_Znth zseq_Zlength; try lia.
      (*once again, compare elementwise*)
      apply Znth_eq_ext; rewrite Zlength_upd_Znth zseq_Zlength; try lia.
      rewrite mkseqZ_Zlength; lia. move => j Hj.
      rewrite mkseqZ_Znth // (upd_Znth_lookup' (fd_k h + fd_h h)) //; last first.
        rewrite zseq_Zlength; lia.
      case (Z.eq_dec j (Z.of_nat (fd_blockIndex h))) => Hjh//=.
      rewrite zseq_Znth; try lia.
      (*contradiction: we know no packets can exist in tail, so pickSeq must be None*)
      case_pickSeq t => [|//].
      apply get_blocks_list_allin in Hinx. case : Hinx => [pkts' Hpkts'].
      by move: Hnotin => /( _ pkts'); rewrite -Hxid Hpkts'.
  - move => Hin. rewrite update_or_add_diff in Hin. apply IH in Hin.
    + rewrite Hin. rewrite mkseqZ_Zlength; [|list_solve]. 
      have->//=: (fd_blockId h == i) = false. apply /eqP. auto.
    + by apply (wf_packet_stream_tl Hwf).
    + apply /eqP. auto.
Qed.

Opaque update_or_add.

(*Prop4: The output list is unique by blockId*)
Lemma get_blocks_list_uniq: forall (l: list fpacket),
  uniq (map fst (get_block_lists l)).
Proof.
  move => l. elim : l => [//= | h t /= IH].
  rewrite /update_block_list. apply al_uniq.
Qed.

Definition btuple := (nat * list (option fpacket))%type.

(*We bundle these into a single relation*)
Definition get_block_lists_prop (l: list fpacket) (blks: list btuple) : Prop :=
  (forall (p: fpacket), p \in l -> exists pkts, (fd_blockId p, pkts) \in blks) /\
  (forall (i: nat) (pkts: list (option (fpacket))),
    (i, pkts) \in blks -> exists (p: fpacket), (Some p) \in pkts) /\
  (forall (i: nat) (pkts: list (option (fpacket))) (p: fpacket),
    (i, pkts) \in blks -> (Some p) \in pkts -> Zlength pkts = (fd_k p + fd_h p)) /\
  (forall (i: nat) (pkts: list (option (fpacket))),
    (i, pkts) \in blks -> pkts = mkseqZ (fun j => 
    pickSeq (fun (p': fpacket) => (fd_blockId p' == i) &&
      Z.eq_dec j (Z.of_nat (fd_blockIndex p'))) l) (Zlength pkts)) /\
  uniq (map fst blks).

Lemma get_block_lists_spec: forall (l: list fpacket),
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
Lemma get_block_lists_prop_packets: forall (l: list fpacket) (blks: list btuple) (i: nat)
  (pkts: list (option fpacket)) (p: fpacket),
  get_block_lists_prop l blks ->
  (i, pkts) \in blks ->
  (Some p) \in pkts ->
  fd_blockId p = i /\ p \in l.
Proof.
  move => l blks i pkts p [Hallin [Hnonemp [Hlen [Heq Huniq]]]] Hin.
  apply Heq in Hin. rewrite Hin => /inP; rewrite In_Znth_iff mkseqZ_Zlength; [|list_solve].
  move => [j [Hj Hjth]]. move: Hjth. rewrite mkseqZ_Znth //.
  case_pickSeq l => [[Hxp]|//].
  by rewrite -Hxp. 
Qed.

(*We prove that this relation is preserved through lists with the same elements*)
Lemma get_block_lists_prop_perm_equiv: forall (l1 l2: list fpacket) (blks: list btuple),
  wf_packet_stream l1 ->
  l1 =i l2 ->
  get_block_lists_prop l1 blks ->
  get_block_lists_prop l2 blks.
Proof.
  move => l1 l2 blks Hwf Hperm [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]].
  rewrite /get_block_lists_prop. split_all => //.
  - move => p Hinp. apply Hallin1. move: Hinp. by rewrite Hperm.
  - move => i pkts Hin. apply Heq1 in Hin. rewrite {1}Hin {Hin}.
    apply Znth_eq_ext; rewrite !mkseqZ_Zlength //; try apply Zlength_nonneg.
    move => j Hj. rewrite !mkseqZ_Znth //; try lia.
    case_pickSeq l1; case_pickSeq l2 => [|//].
    + (*rely on uniqueness of (id, idx) pairs*)
      f_equal. apply (proj1 (proj2 Hwf)) => //. by rewrite Hperm.
      congruence. solve_sumbool. subst. by apply Nat2Z.inj in e.
    + move => /(_ x). rewrite Hxid eq_refl Hidx /= => Hc.
      have//:true = false by (apply Hc; rewrite -Hperm).
    + move => /(_ x). rewrite Hxid eq_refl Hidx /= => Hc.
      have//: true = false by (apply Hc; rewrite Hperm).
Qed.  

(*Any 2 block_lists from the same source have the same elements*)
Lemma get_block_lists_prop_in: forall (l: list fpacket) (blks1 blks2 : list btuple) b,
  wf_packet_stream l ->
  get_block_lists_prop l blks1 ->
  get_block_lists_prop l blks2 ->
  b \in blks1 ->
  b \in blks2.
Proof.
  move => l b1 b2 b Hwf [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]] [Hallin2 [Hnonemp2 [Hlen2 [Heq2 Huniq2]]]] Hin1.
  move: Hin1. case: b => [i1 pkts1] Hin1.
  have Hpkts1:=Hin1. apply Heq1 in Hpkts1. 
  (*Idea: get packet from pkts1, it must have id i and it must be in l, so there must be some pkts2
    such that (i, pkts2) is in b2. But by the equality lemma, pkts2 = pkts1*)
  have Hin1':=Hin1. apply Hnonemp1 in Hin1'. case: Hin1' => [p Hinp].
  have [Hidp Hinlp]: fd_blockId p = i1 /\ p \in l
    by apply (@get_block_lists_prop_packets _ b1 _ pkts1).
  have Hinlp':=Hinlp. apply Hallin2 in Hinlp'.
  case Hinlp' => [pkts2 Hin2].
  rewrite Hidp in Hin2. have Hpkts2:=Hin2.
  apply Heq2 in Hpkts2.
  (*only thing left- show lengths are same*) 
  have->//: pkts1 = pkts2. rewrite Hpkts1 Hpkts2. f_equal.
  rewrite (Hlen1 _ _ _ Hin1 Hinp). 
  have Hin2' := Hin2. apply Hnonemp2 in Hin2'. case : Hin2' => [p2 Hinp2].
  (*Now we have to know that id is same again*)
  have [Hidp2 Hinlp2]: fd_blockId p2 = i1 /\ p2 \in l by
    apply (@get_block_lists_prop_packets _ b2 _ pkts2). 
  rewrite (Hlen2 _ _ _ Hin2 Hinp2).
  have [Hk Hh]: fd_k p = fd_k p2 /\ fd_h p = fd_h p2. {
    move: Hwf => [Hkh _]. apply Hkh => //. 
    by rewrite Hidp Hidp2. }
  by rewrite Hk Hh.
Qed.

(*Therefore, any 2 block_lists satisfying the relation are equal up to permutation*)
Lemma get_block_lists_prop_perm: forall (l: list fpacket) (blks1 blks2 : list btuple),
  wf_packet_stream l ->
  get_block_lists_prop l blks1 ->
  get_block_lists_prop l blks2 ->
  perm_eq blks1 blks2.
Proof.
  move => l b1 b2 Hwf [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]] [Hallin2 [Hnonemp2 [Hlen2 [Heq2 Huniq2]]]].
  apply uniq_perm. apply (map_uniq Huniq1). apply (map_uniq Huniq2).
  move => b. 
  case Hin1: (b \in b1); symmetry.
  - move: Hin1. rewrite -!is_true_true_eq. by apply (get_block_lists_prop_in Hwf).
  - case Hin2: (b \in b2) => //. move: Hin2. rewrite -is_true_true_eq => Hin2.
    apply (@get_block_lists_prop_in l b2 b1 b Hwf) in Hin2 => //. by rewrite Hin1 in Hin2.
Qed.

(*Similarly, these properties are not affected by permuting the block list*)
Lemma perm_get_block_lists_prop: forall (l: list fpacket) (blks1 blks2 : list btuple),
  get_block_lists_prop l blks1 ->
  perm_eq blks1 blks2 ->
  get_block_lists_prop l blks2.
Proof.
  move => l blks1 blks2 [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]] Hperm.
  rewrite /get_block_lists_prop. split_all.
  - move => p Hp. apply Hallin1 in Hp. case : Hp => [pkts Hinp]. exists pkts.
    move: Hinp. by rewrite (perm_mem Hperm).
  - move => i pkts Hin. apply (Hnonemp1 i). move: Hin. by rewrite (perm_mem Hperm).
  - move => i pkts p Hinb Hinp. apply (Hlen1 i) => //. move: Hinb. by rewrite (perm_mem Hperm).
  - move => i pkts Hb. apply Heq1. move: Hb. by rewrite (perm_mem Hperm).
  - by rewrite -(perm_uniq (perm_map fst Hperm)).
Qed. 

(*One more result: if we get_blocks for any 2 lists which are permutations, then the two get_blocks
  are permutations*)
Lemma get_blocks_lists_perm: forall (l1 l2: list fpacket),
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
Lemma get_block_lists_prop_all_id: forall (l: list fpacket) blks (i: nat) 
  (pkts: list (option fpacket)) (p: fpacket),
  wf_packet_stream l ->
  get_block_lists_prop l blks ->
  (i, pkts) \in blks ->
  p \in l ->
  fd_blockId p = i ->
  (Some p) \in pkts.
Proof.
  move => l blks i pkts p Hwf [Hallin [Hnonemp [Hlen [Heq Huniq]]]] Hinb Hinp Hid.
  case: Hwf => [Hkh [Hinj Hbounds]].
  (*get p' that is actually there, show k and h equal, so use definition of mkSeq and length*)
  have Hex:=Hinb. apply Hnonemp in Hex. case: Hex => [p' Hinp'].
  have [Hidp' Hinpl']: fd_blockId p' = i /\ p' \in l by apply (@get_block_lists_prop_packets _ blks _ pkts).
  have [Hk Hh]: fd_k p = fd_k p' /\ fd_h p = fd_h p'. apply Hkh => //. by subst.
  have Hpkts:=Hinb. apply Heq in Hpkts. rewrite Hpkts; apply /inP; 
    rewrite In_Znth_iff mkseqZ_Zlength;[|list_solve].
  rewrite (Hlen _ _ _ Hinb Hinp') -Hk -Hh.
  have Hbound: 0 <= Z.of_nat (fd_blockIndex p) < fd_k p + fd_h p by 
    (split; try lia; apply Hbounds).
  exists (Z.of_nat (fd_blockIndex p)). split => //.
  rewrite mkseqZ_Znth //.
  case_pickSeq l. 
  (*here, we rely on uniqueness of (id, idx) pairs*)
  - solve_sumbool. apply Nat2Z.inj in e. f_equal. apply Hinj => //.
    by rewrite Hxid.
  - move => /(_ p). rewrite Hid eq_refl /=.
    case : (Z.eq_dec (Z.of_nat (fd_blockIndex p)) (Z.of_nat (fd_blockIndex p))) => //= _ => Hcon.
    have//: true = false by apply Hcon.
Qed.

(*Version specialized to [get_block_lists] TODO: remove? this is legacy*)
Lemma get_blocks_list_all_id: forall (l: list fpacket) (i: nat) (pkts: list (option fpacket))
  (p: fpacket),
  wf_packet_stream l ->
  (i, pkts) \in al (get_block_lists l) ->
  p \in l ->
  fd_blockId p = i ->
  (Some p) \in pkts.
Proof.
  move => l i pkts p Hwf Hinb Hinp Hid.
  by apply (get_block_lists_prop_all_id Hwf (get_block_lists_spec Hwf) Hinb).
Qed.

(*Furthermore, every packet in the list is in some block and has the correct id*)
Lemma get_block_lists_allin_in: forall (l: list fpacket) blks (p: fpacket),
  wf_packet_stream l ->
  get_block_lists_prop l blks ->
  p \in l ->
  exists pkts, (fd_blockId p, pkts) \in blks /\ (Some p) \in pkts.
Proof.
  move => l blks p Hwf [Hallin [Hnonemp [Hlen [Heq Huniq]]]] Hin. have Hallin':=Hallin.
  move: Hallin => /(_ _ Hin) [pkts Hinpkts].
  exists pkts. split => //. by apply (@get_block_lists_prop_all_id l blks (fd_blockId p)).
Qed.

Section App.

Transparent update_or_add.
(*The only place we need to use the definition of [get_blocks] directly rather than just the relation*)
Lemma get_block_lists_app: forall (l1 l2: list fpacket),
  (forall (p1 p2 : fpacket), p1 \in l1 -> p2 \in l2 -> fd_blockId p1 != fd_blockId p2) ->
  wf_packet_stream (l1 ++ l2) ->
  al (get_block_lists (l1 ++ l2)) = (get_block_lists l1) ++ (get_block_lists l2).
Proof.
  move => l1. elim : l1 => [//= | h t /= IH l2 Hdisj Hwf]. rewrite IH; last first.
    apply (wf_packet_stream_tl Hwf).
    move => p1 p2 Hp1. apply Hdisj. by rewrite in_cons Hp1 orbT.
  rewrite update_or_add_app' //. apply /mapP =>[[ x]]. 
  case : x => [i pkts]/= => [Hin Hi]. subst.
  (*need to get packet in pkts*)
  have Hwfl2: wf_packet_stream l2. apply (wf_substream Hwf). move => x Hinx. by rewrite in_cons mem_cat Hinx !orbT.
  have [p [Hinp _]]:= get_blocks_list_nonempty Hwfl2 Hin.
  have [Hid Hinpl2]:=get_block_lists_prop_packets (get_block_lists_spec Hwfl2) Hin Hinp.
  have Hinh: h \in h :: t by rewrite in_cons eq_refl.
  move: Hdisj => /(_  h p Hinh Hinpl2). by rewrite Hid eq_refl.
Qed.

End App.

(*Now we will convert between (int, list (option fpacket)) and blocks. A block is useful because
  it has lots of extra metadata which makes things easier, but it is more annoying to work with directly*)

Definition btuple_to_block (x: btuple) : block :=
  (*find a packet that exists*)
  match (pmap id x.2) with
  | p :: _ => let k := fd_k p in
              let h := fd_h p in
              mk_blk x.1 (sublist 0 k x.2) (sublist k (k+h) x.2) k h false 0
  | nil => (*this case will not occur with badly-formed lists*)
            block_inhab
  end.

(*The above definition is not very usable, since we don't know which packet (pmap id x.2) will give.
  The following lemma allows us to express the block's contents in terms of ANY packet in it*)
Lemma btuple_to_block_eq: forall (l: list fpacket) (i: nat) (pkts: list (option fpacket))
  (p: fpacket),
  wf_packet_stream l ->
  (i, pkts) \in al (get_block_lists l) ->
  p \in l ->
  fd_blockId p = i ->
  btuple_to_block (i, pkts) = mk_blk i (sublist 0 (fd_k p) pkts) (sublist (fd_k p) (fd_k p + fd_h p) pkts) 
    (fd_k p) (fd_h p) false 0.
Proof.
  move => l i pkts p Hwf Hint Hinp Hid. rewrite /btuple_to_block.
  rewrite /=.
  have Hhin: (Some p) \in pkts by apply (get_blocks_list_all_id Hwf Hint).
  have: p \in (pmap id pkts) by rewrite -pmap_id_some.
  case Hp': (pmap id pkts) => [// |p' t].
  move => _. have Hinp': (Some p') \in pkts by rewrite pmap_id_some Hp' in_cons eq_refl.
  (*now just show these 2 packets have same id, k, and h*)
  have [Hidp' Hinpl']: fd_blockId p' = i /\ p' \in l
    by apply (@get_block_lists_prop_packets _ (get_block_lists l) _ pkts) => //; apply get_block_lists_spec.
  case : Hwf => [Hkh _].
  have [Hk Hh]: fd_k p = fd_k p' /\ fd_h p = fd_h p'. apply Hkh => //.
    by rewrite Hidp'.
  by rewrite Hk Hh.
Qed.

Definition block_to_btuple (b: block) : btuple :=
  (blk_id b, data_packets b ++ parity_packets b).

(*Results about btuples and blocks*)
Lemma btuple_block_inv: forall b,
  block_wf b ->
  black_complete b = false ->
  black_time b = 0 ->
  (*block must be nonempty*)
  isSome (block_elt b) ->
  btuple_to_block (block_to_btuple b) = b.
Proof.
  move => b [Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc Hvalid]]]]]]]] Hcomp Htime.
  rewrite /block_to_btuple /btuple_to_block/block_elt/=.
  case Hpkts: (pmap id (data_packets b ++ parity_packets b)) => [//|h t /=].
  move => _.
  have Hin: packet_in_block h b
    (*TODO: lemma? See after changing if*)
    by rewrite /packet_in_block/packet_in_data/packet_in_parity -mem_cat
    pmap_id_some Hpkts in_cons eq_refl.
  have [Hkeq  Hheq]: fd_k h = blk_k b /\ fd_h h = blk_h b by apply (Hkh _ Hin).
  rewrite Hkeq Hheq sublist_app1; try lia.
  rewrite sublist_app2; try lia.
  have->: (blk_k b - Zlength (data_packets b)) = 0 by lia.
  have->: (blk_k b + blk_h b - Zlength (data_packets b)) = blk_h b by lia.
  rewrite !sublist_same; try lia. rewrite -Hcomp -Htime. clear -b. by case: b.
Qed.

Lemma block_btuple_inv: forall i pkts p,
  (Some p) \in pkts ->
  (forall (p': fpacket), (Some p') \in pkts -> 0 <= fd_k p' /\ 0 <= fd_h p') ->
  (forall (p' : fpacket), (Some p') \in pkts -> Zlength pkts = fd_k p' + fd_h p') ->
  block_to_btuple (btuple_to_block (i, pkts)) = (i, pkts).
Proof.
  move => i pkts p Hinp Hpos Hlen. rewrite /btuple_to_block/=/block_to_btuple/=.
  case Hpmap: (pmap id pkts) => [//= | p' tl /=].
  - move: Hinp. by rewrite pmap_id_some Hpmap.
  - have Hinp': (Some p') \in pkts by rewrite pmap_id_some Hpmap in_cons eq_refl.
    move: Hpos => /( _ _ Hinp') [Hk Hh].
    move: Hlen => /(_ _ Hinp') Hlen.  
    rewrite cat_app -sublist_split; simpl in *; try lia.
    by rewrite sublist_same.
Qed.

(*Similar versions for mapping over a list*)
Lemma btuple_block_inv_list_aux: forall (s: seq btuple),
  (forall i pkts, (i, pkts) \in s -> exists p, (Some p) \in pkts) ->
  (forall i pkts (p: fpacket), (i, pkts) \in s -> (Some p) \in pkts -> 0 <= fd_k p /\ 0 <= fd_h p) ->
  (forall i pkts (p: fpacket), (i, pkts) \in s -> (Some p) \in pkts -> Zlength pkts = fd_k p + fd_h p) ->
  [seq (block_to_btuple \o btuple_to_block) i | i <- s] = s.
Proof.
  move => s. elim : s => [//= | [i' pkts'] t /= IH Hnonemp Hpos Hlens].
  rewrite IH //. 
  - f_equal. 
    have [p Hinp]: exists p, (Some p) \in pkts' by 
      apply (Hnonemp i' pkts'); rewrite in_cons eq_refl.
    eapply block_btuple_inv. apply Hinp. move => p' Hinp'. apply (@Hpos i' pkts') => //.
    by rewrite in_cons eq_refl.
    move => p' Hinp'. apply (@Hlens i' pkts') => //.
    by rewrite in_cons eq_refl.
  - move => i pkts Hint. apply (Hnonemp i).
    by rewrite in_cons Hint orbT.
  - move => i pkts p Hint. apply (Hpos i).
    by rewrite in_cons Hint orbT.
  - move => i pkts p Hint. apply (Hlens i).
    by rewrite in_cons Hint orbT.
Qed.

Lemma btuple_block_inv_list: forall (l: seq fpacket) (s: seq btuple),
  wf_packet_stream l ->
  get_block_lists_prop l s ->
  [seq (block_to_btuple \o btuple_to_block) i | i <- s] = s.
Proof.
  move => l s [Hkh [Hinj [Hbounds Hpos]]] [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]].
  apply btuple_block_inv_list_aux.
  - apply Hnonemp1.
  - move => i pkts p Hins Hinp. apply Hpos.
    by apply (@get_block_lists_prop_packets l s i pkts p).
  - apply Hlen1.
Qed.

Lemma block_btuple_inv_list: forall (l: seq block),
  (forall b, b \in l -> block_wf b) ->
  (forall b, b \in l -> black_complete b = false) ->
  (forall b, b \in l -> black_time b = 0) ->
  (forall b, b \in l -> block_elt b) ->
  [ seq (btuple_to_block \o block_to_btuple) i | i <- l] = l.
Proof.
  move => l. elim : l => [//= | h t /= IH Hwf Hblack Htimes Hnonemp].
  rewrite btuple_block_inv; [rewrite IH //| | | |];
  try(move=> b Hinb); [apply Hwf | apply Hblack | apply Htimes |
    apply Hnonemp | apply Hwf | apply Hblack | apply Htimes |
    apply Hnonemp ]; rewrite in_cons; try (by rewrite Hinb orbT); 
    by rewrite eq_refl.
Qed.

(*Finally, we can get all the blocks from a list*)
Definition get_blocks (l: list fpacket) := map btuple_to_block (get_block_lists l).

Lemma get_blocks_app: forall (l1 l2: list fpacket),
  (forall (p1 p2 : fpacket), p1 \in l1 -> p2 \in l2 -> fd_blockId p1 != fd_blockId p2) ->
  wf_packet_stream (l1 ++ l2) ->
  get_blocks (l1 ++ l2) = get_blocks l1 ++ get_blocks l2.
Proof.
  move => l1 l2 Hdisj Hwf. by rewrite /get_blocks get_block_lists_app // map_cat.
Qed. 

(*When we are given a single, nonempty block and a list containing only all of the elements of the block,
  get_block_lists equals the block itself*)
Lemma get_block_lists_single: forall (b: block) (s: seq fpacket),
  block_wf b ->
  block_elt b ->
  (forall p, p \in s <-> packet_in_block p b) ->
  al (get_block_lists s) = [:: block_to_btuple b].
Proof.
  move => b s [Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc Hvalid]]]]]]]] Hnonemp Hs.
  apply perm_small_eq => //.
  have Hwf: wf_packet_stream s. {
    rewrite /wf_packet_stream; split_all.
    - move => p1 p2 Hp1 Hp2 Hid'.
      apply Hs in Hp1. apply Hkh in Hp1. case: Hp1 => [Hk1 Hh1]. rewrite Hk1 Hh1.
      apply Hs in Hp2. apply Hkh in Hp2. case: Hp2 => [Hk2 Hh2]. by rewrite Hk2 Hh2.
    - move => p1 p2 Hp1 Hp2 Hids Hidxeq.
      apply Hs in Hp1. apply (Hidx _ (Z.of_nat (fd_blockIndex p1))) in Hp1.
      apply Hs in Hp2. apply (Hidx _ (Z.of_nat (fd_blockIndex p1))) in Hp2.
      rewrite -Hidxeq in Hp2.
      have: Znth (Z.of_nat (fd_blockIndex p1)) (data_packets b ++ parity_packets b) = Some p1 by apply Hp1.
      have: Znth (Z.of_nat (fd_blockIndex p1)) (data_packets b ++ parity_packets b) = Some p2 by apply Hp2.
      by move -> => [[Hp]].
    - move => p Hp. have Hp':=Hp. apply Hs in Hp'. apply Hkh in Hp'. case: Hp' => [Hkp Hhp].
      apply Hs in Hp. apply (Hidx _ (Z.of_nat (fd_blockIndex p))) in Hp.
      have: Znth (Z.of_nat (fd_blockIndex p)) (data_packets b ++ parity_packets b) = Some p by apply Hp.
      move : Hp => _ Hp. (*list_solve should really be able to do this without Zlength_app*)
      have->: fd_k p + fd_h p = Zlength (data_packets b ++ parity_packets b) by rewrite Zlength_app; list_solve.
      apply Znth_inbounds. by rewrite Hp.
    - move => p Hp. apply Hs in Hp. apply Hkh in Hp. lia.
  } 
  apply (@get_block_lists_prop_perm s) => //; [ apply get_block_lists_spec => // |].
  rewrite /get_block_lists_prop /block_to_btuple/=.
  split_all => //.
  - move => p Hp. exists (data_packets b ++ parity_packets b).
    rewrite Hid //. by rewrite in_cons eq_refl. by apply Hs.
  - move => i pkts; rewrite in_cons => /orP [/eqP[Hi Hpkts] | Hf //]. subst. 
    move: Hnonemp. rewrite /block_elt.
    case Hpmap: (pmap id (data_packets b ++ parity_packets b)) => [//|p tl].
    move => _.
    exists p. by rewrite pmap_id_some Hpmap in_cons eq_refl.
  - move => i pkts p; rewrite in_cons => /orP[/eqP[Hi Hpkts] | Hf //]. subst. 
    move => Hinp. 
    have Hs': packet_in_block p b by rewrite /packet_in_block -mem_cat.
    apply Hkh in Hs'. rewrite Zlength_app. lia.
  - move => i pkts; rewrite in_cons => /orP[/eqP[Hi Hpkts] | Hf //]. subst.
    apply Znth_eq_ext; zlist_simpl.
    move => i Hi. zlist_simpl.
    case_pickSeq s.
    + solve_sumbool. subst. apply Hidx => //. by apply Hs.
    + move => Hc. case Hcon: (Znth i (data_packets b ++ parity_packets b)) => [p' |//].
      have /inP Hinp': In (Some p') (data_packets b ++ parity_packets b). { rewrite -Hcon.
        apply Znth_In. zlist_simpl. }
        have Hinp'': packet_in_block p' b by rewrite /packet_in_block -mem_cat.
      apply Hidx in Hcon => //. subst.
      have Hps: p' \in s by apply Hs.
      move: Hc => /( _ p' Hps)/=.
      apply Hid in Hinp''. rewrite Hinp'' eq_refl/=. 
      by case: (Z.eq_dec (Z.of_nat (fd_blockIndex p')) (Z.of_nat (fd_blockIndex p'))).
Qed. 

Lemma get_blocks_allin: forall (s: seq fpacket) (p: fpacket),
  wf_packet_stream s ->
  p \in s ->
  exists b, (b \in (get_blocks s)) && (packet_in_block p b).
Proof.
  move => s p Hwf Hp. rewrite /get_blocks. 
  have [pkts [Hinb Hinp]]:=(get_block_lists_allin_in Hwf (get_block_lists_spec Hwf) Hp).
  exists (btuple_to_block (fd_blockId p, pkts)). apply /andP. split.
  - apply /mapP. by exists (fd_blockId p, pkts).
  - rewrite /btuple_to_block/=. case Hmap: (pmap id pkts) => [|p' tl/=].
    + have: p \in (pmap id pkts) by rewrite -pmap_id_some.
      by rewrite Hmap.
    + have [_ [_ [Hlen _]]] := (get_block_lists_spec Hwf). 
      have [Hpid' Hinp']: fd_blockId (p_fec_data' p') = fd_blockId p /\ p' \in s. {
        apply (get_block_lists_prop_packets (get_block_lists_spec Hwf) Hinb).
        by rewrite pmap_id_some Hmap in_cons eq_refl. }
      (*Why is the coercion not working? TODO*)
      have [Hk' Hh']: fd_k p = fd_k (p_fec_data' p') /\ 
        fd_h p = fd_h (p_fec_data' p') by apply Hwf.
      case Hwf => [Hkh [_ [_  /( _ p Hp)]]] [Hk Hh].
      rewrite packet_in_block_eq/=
        -Hk' -Hh' -mem_cat cat_app -sublist_split; try lia. 
      rewrite sublist_same //; try lia.
      by rewrite (Hlen _ _ _ Hinb Hinp). rewrite (Hlen _ _ _ Hinb Hinp).
      lia.
Qed.

(*Basically the reverse of the above: Everything in [get_blocks] is in the original list*)
Lemma get_blocks_in_orig: forall (s: seq fpacket) (b: block) (p: fpacket),
  wf_packet_stream s ->
  b \in (get_blocks s) ->
  packet_in_block p b ->
  p \in s.
Proof.
  move => s b p Hwf. rewrite /get_blocks => /mapP [[i pkts] Hinpkts Hb]. subst.
  rewrite /btuple_to_block/=.
  case Hmap: (pmap id pkts) => [// | p' t' /=].
  have [_ [_ [Hlen _]]] := (get_block_lists_spec Hwf).
  have Hinp'': (Some p') \in pkts by rewrite pmap_id_some Hmap in_cons eq_refl.
  have Hallsum: forall x : fpacket, x \in s -> 0 <= fd_k x + fd_h x. {
    move => x Hinx.
    have [Hkx Hhx]: 0 <= fd_k x /\ 0 <= fd_h x by apply Hwf. lia. }
  have Hinp': p' \in s by apply (get_blocks_list_from_src Hallsum Hinpkts). 
  have [Hk0 Hh0]: 0 <= fd_k (p_fec_data' p') /\ 0 <= fd_h (p_fec_data' p')
    by apply Hwf.
  rewrite packet_in_block_eq -mem_cat cat_app -sublist_split; try lia. rewrite sublist_same; try lia.
    2: by rewrite (Hlen _ _ _ Hinpkts Hinp'').
    2: rewrite (Hlen _ _ _ Hinpkts Hinp''); lia.
  move=> Hinp.
  by apply (get_blocks_list_from_src Hallsum Hinpkts).
Qed.

(*TODO: see what I need exactly, may not need all this*)
(*TODO: have I proved this or part of this before?*)
(*
Lemma get_blocks_wf: forall (s: seq fpacket) (b: block),
  wf_packet_stream s ->
  (forall (p: fpacket), p \in s -> 0 < fd_k p <= fec_n - 1 - fec_max_h /\
    0 < fd_h p <= fec_max_h) ->
  b \in (get_blocks s) ->
  block_wf b.
Proof.
  move=> s b Hwf. rewrite /get_blocks => /mapP [[i pkts] Hin Hb]. subst.
  have [Hallin [Hnonemp [Hlen [Heq Huniq]]]] := 
    (get_block_lists_spec Hwf).
  have [p Hinp]: exists (p: fpacket), Some p \in pkts by apply (Hnonemp _ _ Hin).
  have [Hpid Hpinl]:=
    (get_block_lists_prop_packets (get_block_lists_spec Hwf) Hin Hinp).
  rewrite (btuple_to_block_eq Hwf Hin Hpinl Hpid).
  rewrite /block_wf/=.
  Print wf_packet_stream.
  
  Lemma get_block_lists_prop_packets: forall (l: list fpacket) (blks: list btuple) (i: nat)
  (pkts: list (option fpacket)) (p: fpacket),
  get_block_lists_prop l blks ->
  (i, pkts) \in blks ->
  (Some p) \in pkts ->
  fd_blockId p = i /\ p \in l.
  
  Search get_bl

  Search btuple_to_block.
  rewrite Hb.
*)
End BlockList.

(* For the decoder, we need to reason about subblocks)*)

Section Subblock.

(*1. Define a subblock of a block*)

(*Special sublist for list of options*)
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

Lemma subseq_option_in: forall {A: eqType} (l1 l2: list (option A)) (x: A),
  subseq_option l1 l2 ->
  (Some x) \in l1 ->
  (Some x) \in l2.
Proof.
  move => A l1 l2 x. rewrite /subseq_option => [[Hlens Hsub]] /inP Hin1.
  apply /inP. move: Hin1.
  rewrite !In_Znth_iff => [[i [Hi Hnth]]]. exists i. split; simpl in *; try lia.
  move: Hsub => /(_ i Hi). by rewrite Hnth => [[H|H]].
Qed.

(*This particular form will be more helpful*)
Lemma subseq_option_in': forall {A: eqType} (l1 l2 l3 l4: list(option A)) (x: A),
  subseq_option l1 l2 ->
  subseq_option l3 l4 ->
  ((Some x) \in l1) || ((Some x) \in l3) ->
  ((Some x) \in l2) || ((Some x) \in l4).
Proof.
  move => A l1 l2 l3 l4 x Ho1 Ho2 /orP[Hin1 | Hin2].
  - by rewrite (subseq_option_in Ho1 Hin1).
  - by rewrite (subseq_option_in Ho2 Hin2) orbT.
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

Lemma subseq_option_filter: forall {A: Type} (l1 l2: list (option A)),
  subseq_option l1 l2 ->
  Zlength (filter isSome l1) <= Zlength (filter isSome l2).
Proof.
  move => A l1. elim : l1 => [//= l2 | h t /= IH].
  - rewrite /subseq_option => [[Hlens _]]. have->//: l2 = nil by list_solve.
  - move => l2. case : l2 => [/= | h1 t1 /=].
    + rewrite /subseq_option => [[Hlens _]]. list_solve.
    + move => Hopt. have Hoptt: subseq_option t t1 by apply subseq_option_tl in Hopt.
      move: Hopt. rewrite /subseq_option => [[Hlens Hith]].
      have H0: 0 <= 0 < Zlength (h :: t) by list_solve.
      move: Hith => /(_ _ H0). rewrite !Znth_0_cons; move => [Hh | HH]/=; subst; rewrite {H0 Hlens}.
      * apply IH in Hoptt. case: h1 => [a |]/=; list_solve.
      * apply IH in Hoptt. rewrite /=. case: h1 => [a|]/=; list_solve.
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
  rewrite /block_wf /subblock => [[Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc [Hvalid [Hdats Hpars]]]]]]]]]]] 
    [Hsubid [Hsubdata [Hsubpar [Hsubk Hsubh]]]].
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
      have Hinb2: packet_in_block p b2 by
      apply (subseq_option_in' Hsubdata Hsubpar). move: Hin.
      (*TODO: these are very similar*)
      rewrite packet_in_block_eq -mem_cat => /inP Hin.
      apply in_app_or in Hin. move: Hin. rewrite !In_Znth_iff => [[[j [Hj Hnth]] | [j [Hj Hnth]]]].
      * move: Hsubdata. rewrite /subseq_option => [[Hlen Hall]]. move: Hall => /(_ j Hj).
        rewrite !Hnth => [[Hjb2 | //]]. symmetry in Hjb2.
        have<-: j = i. { rewrite Hi. apply Hidx. by []. rewrite Znth_app1 //.
          simpl in *. lia. }
        rewrite Znth_app1 //. simpl in *. lia.
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
  - move => p Hp. apply Hdats. by apply (subseq_option_in Hsubdata).
  - move => p Hp. apply Hpars. by apply (subseq_option_in Hsubpar).
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


(*First, we need to know that blk_c of a recoverable subblock of a complete block is the same as the
  superblock. This is surprisingly nontrivial to prove*)
Lemma blk_c_recoverable: forall (b1 b2: block),
  block_encoded b2 ->
  subblock b1 b2 ->
  recoverable b1 ->
  blk_c b1 = blk_c b2.
Proof.
  move => b1 b2 Hc. have Hcomp:=Hc. move: Hc. 
  rewrite /block_encoded /subblock /blk_c => [[[def [Hindef Hlendef] [Hparc [Hdatac _]]]]].
  remember (fun o : option fpacket => match o with
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
        by apply subseq_option_in. }
      have: (Some pa) \in [seq x <- parity_packets b2 | isSome x] by rewrite mem_filter.
      case Hpar': [seq x <- parity_packets b2 | isSome x] => [//|h t]. move => _.
      move: Hpar'. case: h => [a /= Hfilt' | // Hcon]; last first.
        have: None \in [seq x <- parity_packets b2 | isSome x] by rewrite Hcon in_cons orTb.
        by rewrite mem_filter.
      move: Hparc => /(_ _ Hinpa'). by rewrite Hfilt'.
    + have: None \in [seq x <- parity_packets b1 | isSome x] by rewrite Hfilt in_cons orTb.
      by rewrite mem_filter.
  - (*In the other case, we need to show list_max of (packets b1) and (packets b2) are equal*)
    have->//: list_max_nonneg f (data_packets b1) = blk_c b2; last first.
      by rewrite /blk_c Hf.
    rewrite (blk_c_encoded Hcomp) -Hf.
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
    have Hallin: forall o, o \in (data_packets b2) -> o \in (data_packets b1). {
      move=> o /inP Hin. apply /inP; move: Hin.  
      rewrite !In_Znth_iff. move: Hsubdata. rewrite /subseq_option => [[Hlendata Hnth] [i [Hi Hith]]].
      have Hi':=Hi. rewrite -Hlendata in Hi. apply Hnth in Hi. case : Hi => [Hi | Hi].
        exists i. split. by rewrite Hlendata. by rewrite Hi Hith.
      move: Hall => /allP Hall.
      have Hn: None \in data_packets b1. rewrite in_mem_In In_Znth_iff. exists i. split.
        by rewrite Hlendata. by []. by move: Hall => /(_ _ Hn). }
    have Hfp': 0 <= f (Some def) by rewrite Hf; list_solve.
    have Hinp: (Some def) \in (data_packets b1) by apply Hallin.
    have Hlb:=(list_max_nonneg_in Hfp' Hinp).
    have: f(Some def) = list_max_nonneg f (data_packets b2)
      by rewrite Hf Hlendef Hf -/(blk_c b2) blk_c_encoded.
    simpl in *.
    lia.
Qed.

(*If a subblock is recoverable, so is its parent*)
Lemma subblock_recoverable: forall (b1 b2 : block),
  subblock b1 b2 ->
  recoverable b1 ->
  recoverable b2.
Proof.
  move => b1 b2. rewrite /subblock /recoverable => [[_ [Hsubdat [Hsubpar _]]]] Hrec.
  have<-: Zlength (data_packets b1) = Zlength (data_packets b2) by apply Hsubdat.
  solve_sumbool => /=. apply subseq_option_filter in Hsubdat. apply subseq_option_filter in Hsubpar. lia.
Qed. 

End Subblock.

Section Substream.

(*A key result: if we have some stream of packets, then we take some (generalized) substream of these packets
  (such that duplicates are allowed), then every block formed by get_block_lists of the substream is
  a subseq_option of a block from the original stream. This allows us to relate the "encoded" and "received" blocks*)
Lemma get_blocks_lists_substream: forall (l1 l2: list fpacket),
  wf_packet_stream l1 ->
  (forall x, x \in l2 -> x \in l1) ->
  forall i pkts, (i, pkts) \in (al (get_block_lists l2)) -> 
    exists pkts', (i, pkts') \in (al (get_block_lists l1)) /\ subseq_option pkts pkts'.
Proof.
  move => l1 l2 Hwf Hallin i pkts Hin. have Hpkts:=Hin.
  have [Hallin2 [Hnonemp2 [Hlen2 [Heq2 Huniq2]]]] := (get_block_lists_spec (wf_substream Hwf Hallin)).
  apply Heq2 in Hpkts. rewrite Hpkts {Hpkts}.
  (*we know that there is some p in pkts and p is in l2, so p is in l1, so there
    is some pkts' with the same id, we use the mkseqZ definition to prove subseq option*)
  have Hex:=Hin. apply Hnonemp2 in Hex. case: Hex => [p Hinp].
  have [Hidp Hinpl2]: fd_blockId p = i /\ p \in l2 by
    apply (@get_block_lists_prop_packets _ (get_block_lists l2) _ pkts).
  have Hinpl1: p \in l1. { move: Hinpl2. apply Hallin. }
  have Hex:=Hinpl1.
  have [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]] := (get_block_lists_spec Hwf).
  apply Hallin1 in Hinpl1. case : Hinpl1 => [pkts' Hin'].
  exists pkts'. split. by rewrite -Hidp. 
  have Hlenp : Zlength pkts' = fd_k p + fd_h p. {
    have Hex':=Hin'. apply Hnonemp1 in Hex'. case: Hex' => [p' Hinp']. rewrite Hidp in Hin'.
    have [Hidp' Hinpl1]: fd_blockId p' = i /\ p' \in l1 by
      apply (@get_block_lists_prop_packets _ (get_block_lists l1) _ pkts').
    rewrite (Hlen1 _ _ _ Hin' Hinp').
    have [Hk Hh]: fd_k p' = fd_k p /\ fd_h p' = fd_h p. apply Hwf => //.
    by rewrite Hidp'. by rewrite Hk Hh. }
  have Hpkts':=Hin'. apply Heq1 in Hpkts'. rewrite Hpkts' {Hpkts'} Hlenp (Hlen2 _ _ _ Hin Hinp).
  move: Hwf => [_ [Hinj [/(_ p) ]]] Htemp _.
  have Hidx : 0 <= Z.of_nat (fd_blockIndex p) < fd_k p + fd_h p by 
    (split; try lia; apply Htemp).
  rewrite {Htemp}.
  split; rewrite !mkseqZ_Zlength; try lia. move => j Hj. rewrite !mkseqZ_Znth; try lia.
  case_pickSeq l2; last first. by right. rewrite Hidp.
  case_pickSeq l1.
  - (*use uniqueness of (id, idx) pairs*)
    left. f_equal. apply Hinj => //. by apply Hallin. congruence.
    solve_sumbool. subst. by apply Nat2Z.inj in e.
  - move => /(_ x). rewrite Hxid eq_refl Hidx0 /=. have->//:x \in l1 by apply Hallin.
    (*should be automatic*) move => Hc. have//:true = false by apply Hc.
Qed.

(*NOTE: we will need this later too. This is the block version of [get_blocks_lists_substream]*)
Theorem get_blocks_sublist: forall (l1 l2: seq fpacket),
  wf_packet_stream l1 ->
  (forall x, x \in l2 -> x \in l1) ->
  forall b, b \in (get_blocks l2) ->
  exists b', b' \in (get_blocks l1) /\ subblock b b'.
Proof.
  move => l1 l2 Hwf Hsub b. rewrite /get_blocks => /mapP[t Hint Ht]. rewrite Ht.
  move: Ht Hint. case : t => [i pkts] Hb Hint. have Hint':= Hint.
  have [pkts' [Hinpkts Hopt]]:= (get_blocks_lists_substream Hwf Hsub Hint').
  exists (btuple_to_block (i, pkts')). split. apply /mapP. by exists (i, pkts').
  (*Now, we just need an element that is in pkts (and we prove, also in pkts')*)
  have [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]] := (get_block_lists_spec Hwf).
  have [Hallin2 [Hnonemp2 [Hlen2 [Heq2 Huniq2]]]] := (get_block_lists_spec (wf_substream Hwf Hsub)).
  have Hex:=Hint. apply Hnonemp2 in Hex. case : Hex => [p Hinp].
  have [Hidp Hinpl2]: fd_blockId p = i /\ p \in l2 by 
    apply (@get_block_lists_prop_packets _ (get_block_lists l2) _ pkts).
  have Hinpl1: p \in l1. move: Hinpl2. apply Hsub.
  (*now we can use btuple_to_block_eq lemma*)
  rewrite (btuple_to_block_eq Hwf Hinpkts Hinpl1 Hidp).
  rewrite (btuple_to_block_eq (wf_substream Hwf Hsub) Hint Hinpl2 Hidp).
  rewrite /subblock/=. split_all => //.
  by apply subseq_option_sublist.
  by apply subseq_option_sublist.
Qed.

End Substream.
