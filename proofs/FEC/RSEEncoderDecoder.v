(*Implement the abstract encoder/decoder relations from AbstractEncoderDecoder with RSE algorithm *)
Require Import VST.floyd.functional_base.
Require Import EquivClasses.
Require Import IP.
Require Import AbstractEncoderDecoder.
Require Import CommonSSR.
Require Import ReedSolomonList.
Require Import ZSeq.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

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

(*Packet is defined to be valid according to IP/UDP*)
Definition packet_act := packet valid_packet.

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
  data_packets: list (option fec_packet_act); parity_packets: list (option fec_packet_act); blk_k : Z; blk_h : Z}.

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
                end) (data_packets b).

Definition num_receieved (b: block) : Z :=
  Zlength (filter isSome (data_packets b)) + Zlength (filter isSome (parity_packets b)).

(*Max of list of nonnegative integers*)
Definition list_max_nonneg {A: Type} (f: A -> Z) (l: list A) : Z :=
  fold_right (fun x y => Z.max (f x) y) (-1) l.

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
  -1 <= list_max_nonneg f l.
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
                            | None => -1
                            | Some p => Zlength (p_header(f_packet p) ++ p_contents (f_packet p))
                            end) (data_packets b)
  end.

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
  mk_blk id data parities k h.

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
Definition enc_state := bool.
Print packet_act.
Print packet.

(*TODO: need to have length hypotheses involved because of validity constraints - how to best pass
  these around? More complicated because of map*)

(*Quick attempt: map with some function that requires a hypothesis*)
Definition in_map_hyp {A B C: Type} (P: A -> Prop) (f: forall a : A, P a -> B) (l: list A) 
  (H: forall x, In x l -> P x) : list B.
Proof.
induction l as [| h t IH].
- apply nil.
- apply cons. apply (f h). apply H. left. reflexivity.
apply IH. intros x Hinx. apply H. right. apply Hinx.
Defined.

(*TODO: version with indices I think, look at below, see what I need exactly*)
Print fec_data.

Print packet.
Search filter.

Definition get_somes {A: Type} (s: seq (option A)) : seq A :=
  foldr (fun x acc => match x with
                      | None => acc
                      | Some y => y :: acc
                      end) nil s.

(*TODO: fix packet to mk_pkt*)
(*TODO: figure out a way to get that proof in the context, then we should be good for
  this part at least*)
Definition encode_block (b: block) (o: option packet_act) : list fec_packet_act :=
  let parities := encoder_list (blk_h b) (blk_k b) (blk_c b) (packet_mx b) in
  (*these are the contents of the parities - put each in a packet with correct values - values from
    either p if passed in or last packet in block if not*)
  let populate_packets (model: packet_act) : list fec_packet_act :=
    map_with_idx parities (fun (par: list byte) (i: Z) =>
      let new_packet := mk_ptk (blk_id b) 
        (@copy_fix_header_valid _ _ par _ (p_valid model)) in
      mk_fecpkt new_packet (mk_data (blk_k b) (blk_h b) true (blk_id b) (Int.repr i))) in
    



  match (get_somes (data_packets b)), o with
  | nil, None => nil (*can't happen*)
  | _, Some p => populate_packets p
  | h :: t, _ => populate_packets (f_packet (last h (h :: t)))
  end.

    

Definition enc : encoder valid_packet fec_data enc_state :=
  fun (orig: list packet_act) (s: enc_state) =>
    let curr = Znth (Zlength orig - 1) orig in
    let blocks := get_blocks (sublist 0 (Zlength orig - 1) orig) in
    let lastBlock := last 



    let curr = Znth (Zlength orig - 1)


(** Encoder predicate *)

(*Finally, we can define the encoder predicate*)
Definition enc : (encoder valid_packet fec_data) :=
  fun (orig : list packet_act) (encoded: list fec_packet_act) =>
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

(** Decoder predicate *)

(*A block is "recoverable" if we have at least k total packets*)
Definition recoverable (b: block) : bool :=
  Z_ge_lt_dec (Zlength (filter isSome (data_packets b)) + Zlength (filter isSome (parity_packets b))) 
    (Zlength (data_packets b)) .

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
Definition packet_from_bytes (l: list byte) (i: int) : option(packet valid_packet) :=
  let (header, contents) := recover_packet l in
  (match (valid_packet header contents) as v 
    return (valid_packet header contents) = v -> option (packet valid_packet) with
  | true => fun H => Some (mk_ptk i H)
  | false => fun _ => None
  end) Logic.eq_refl.

(*Similarly, we can define the decoder predicate*)
(*TODO: adding correct sequence number, but wont be in memory except sort of via FEC params
  need to figure out good way to handle VST preds*)
Definition dec : (decoder valid_packet fec_data) :=
  fun (received : list fec_packet_act) (decoded: list packet_act) =>
  let blocks := (get_blocks received) in
  (*Because of timeouts, some ill-formed blocks, etc, we give a weak spec: only that
    everything in decoded is either (a) from a data packet in receieved or (b)
    from the decoder_list of some block that is completed. We note that NOT every completed
    block is required or guaranteed to appear*)
  forall (p: packet_act), In p decoded ->
    (exists (fp: fec_packet_act), In fp received /\ (fd_isParity (p_fec_data fp)) /\
      f_packet fp = p) \/
    (exists (b: block) (i: Z), 0 <= i < (blk_k b) /\ In b blocks /\ 
      Some p = packet_from_bytes (Znth i (decoder_list_block b)) (Int.repr (i + Int.unsigned (blk_id b)))). 

(** Encoder/Decoder correctness*)
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