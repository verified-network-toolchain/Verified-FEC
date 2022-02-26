(*Implement the abstract encoder/decoder relations from AbstractEncoderDecoder with RSE algorithm *)
Require Import VST.floyd.functional_base.
Require Import EquivClasses.
Require Import AbstractEncoderDecoder.
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

Definition fec_packet_act_eq_axiom  := (fec_packet_eq_axiom fec_data_eq_dec).

Definition fec_packet_act_eqMixin := EqMixin fec_packet_act_eq_axiom.
Canonical fec_packet_act_eqType := EqType fec_packet_act fec_packet_act_eqMixin.

#[export]Instance packet_act_inhab : Inhabitant fec_packet_act := 
  mk_fecpkt packet_inhab fec_data_inhab.

(** Representing Blocks *)

Record block := mk_blk { blk_id: int;
  data_packets: list (option fec_packet_act); parity_packets: list (option fec_packet_act); blk_k : Z; blk_h : Z}.

(*Well-formed block *)
Definition block_wf (b: block) : Prop :=
  (*All packets store correct values of k and h*)
  (forall p, In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) -> 
    (fd_k (p_fec_data p)) = blk_k b /\ (fd_h (p_fec_data p)) = blk_h b) /\
  (*All packets have same blockId (TODO: is this needed?*)
  (forall p, In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) ->
    fd_blockId (p_fec_data p) = blk_id b) /\
  (*Packet sequence numbers are correct*)
  (forall p, In (Some p) (data_packets b) \/ In (Some p) (parity_packets b) ->
    Znth (Int.unsigned (fd_blockIndex (p_fec_data p))) (data_packets b ++ parity_packets b) = Some p) /\
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

Definition lengths (b: block) : list Z :=
  map (@Zlength byte) (packet_mx b) ++ 
  map (fun x => match x with | None => 0 | Some l => Zlength l end) (parity_mx b).

Definition num_receieved (b: block) : Z :=
  Zlength (filter isSome (data_packets b)) + Zlength (filter isSome (parity_packets b)).

(*Max of list of nonnegative integers*)
Definition list_max_nonneg {A: Type} (f: A -> Z) (l: list A) : Z :=
  fold_right (fun x y => Z.max (f x) y) (-1) l.

(*Get current value of c for the block. If block is not complete, this will be -1.
  It is OK to take max of only packet_contents because parities have Zlength (contents) = c
  and we only care about the value once a block is complete*)
Definition blk_c (b: block) : Z :=
  list_max_nonneg (fun o => match o with
                            | None => -1
                            | Some p => Zlength (p_contents (f_packet p))
                            end) (parity_packets b).

(*A block is complete (these imply that parities are nonempty if data is*)
(*TODO: could make bool, have to make bool (decidable) version of parities_valid*)
Definition block_complete (b: block) : Prop :=
  (*All parities have length c*)
  (forall p, In (Some p) (parity_packets b) -> Zlength (p_contents p) = blk_c b) /\
  (*All data packets (including headers) have length <= c*)
  (forall p, In (Some p) (data_packets b) -> Zlength (packet_bytes p) <= blk_c b) /\
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

(** Encoder predicate *)

(*Finally, we can define the encoder predicate*)
Definition enc : (encoder fec_data) :=
  fun (orig : list packet) (encoded: list fec_packet_act) =>
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
Lemma parity_mx_sublist_length: forall (i: nat) (s: seq (option fec_packet_act)) (*(b: block)*),
Zlength [seq x <- sublist 0 (Z.of_nat i) (* (Z.of_nat (nat_of_ord i))*) s (*(parity_packets b)*) | isSome x] =
Zlength
  [seq x <- sublist 0 (Z.of_nat i) (* (Z.of_nat (nat_of_ord i))*)
              [seq match x with
                   | Some p => Some (p_contents (f_packet p))
                   | None => None
                   end
                 | x <- s (*parity_packets b *)]
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
Lemma find_decoder_list_param_correct: forall (b: block),
  recoverable b ->
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
    + rewrite -Hpick /parity_mx.
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

(*Now we use [find_decoder_list_param] to find the appropriate sublist of parities*)
Definition decoder_list_block (b: block) : list (list byte) :=
  decoder_list (blk_k b) (blk_c b) (packet_mx b) (parity_mx b) (stats b) (lengths b) (find_decoder_list_param b).

(*TODO: need to transform packet bytes back to packet (with IP fields, etc) - this will be annoying
  also may not need IP/UDP stuff here: see*)
Definition packet_from_bytes (l: list byte) : option (packet).
  (*assume this is IP packet: get header length from IP, know UDP header length, split into
    header and contents, put in packet
    return None if list empty or not long enough
    this isn't great because of bitwise ops but not much else we can do - need headers because
    difference between parity/data packets*)
Admitted.


(*Similarly, we can define the decoder predicate*)
Definition dec : (decoder fec_data) :=
  fun (received : list fec_packet_act) (decoded: list packet) =>
  let blocks := (get_blocks received) in
  (*Because of timeouts, some ill-formed blocks, etc, we give a weak spec: only that
    everything in decoded is either (a) from a data packet in receieved or (b)
    from the decoder_list of some block that is completed. We note that NOT every completed
    block is required or guaranteed to appear*)
  forall (p: packet), In p decoded ->
    (exists (fp: fec_packet_act), In fp received /\ (fd_isParity (p_fec_data fp)) /\
      f_packet fp = p) \/
    (exists (b: block) (i: Z), 0 <= i < (blk_k b) /\ In b blocks /\ 
      Some p = packet_from_bytes (Znth i (decoder_list_block b))). 

(** Encoder/Decoder correctness*)