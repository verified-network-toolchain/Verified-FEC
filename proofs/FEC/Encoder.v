Require Import VST.floyd.functional_base.
Require Import AssocList.
Require Import IP.
Require Import AbstractEncoderDecoder.
Require Import CommonSSR.
Require Import ReedSolomonList.
Require Import ZSeq.
Require Import ByteFacts.
(*Require Import ByteField.*) (*For byte equality - TODO: move to ByteFacts*)
Require Import Block.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.
(** Encoder **)

Section Encoder.

Definition populate_packets (id: nat) (model : packet) (contents: list (list byte)) : list packet :=
  map (fun l => let newHeader := copy_fix_header (p_header model) l in mk_pkt newHeader l id) contents.

(*Finally, we can define what it means to encode a block with a model*)
Definition encode_block_aux (b: block) (model: packet) : block * seq fpacket :=
  let packetsNoFec := populate_packets (blk_id b) model 
     (encoder_list (blk_h b) (blk_k b) (blk_c b) (packet_mx b))  in
  let packetsWithFec := map_with_idx packetsNoFec (fun p i => 
    mk_fecpkt p (mk_data (blk_k b) (blk_h b) true (blk_id b) (Z.to_nat((blk_k b) + i)))) in
  (b <| parity_packets := map Some packetsWithFec |>, packetsWithFec).

(*Encoding a block chooses an appropriate model packet - either the inputted packet
  or the last packet in the block*)
Definition encode_block (b: block) (o: option packet) : block * list fpacket :=
  match (pmap id (data_packets b)), o with
  | nil, None => (b, nil) (*can't happen*)
  | _, Some p => encode_block_aux b p
  | h :: t, _ => encode_block_aux b (f_packet (last h (h :: t)))
  end.

(*From here, we need a few utility functions for block so we can create the encoder predicate*)

Definition get_fec_packet (p: packet) (b: block) : fpacket :=
   mk_fecpkt p (mk_data (blk_k b) (blk_h b) false (blk_id b) (Z.to_nat (Zindex None (data_packets b)))).

Definition new_fec_packet (p: packet) (k: Z) (h: Z) : fpacket :=
  mk_fecpkt p (mk_data k h false (p_seqNum p) 0).

Definition add_packet_to_block_red (p: packet) (b: block) : block :=
  let idx := Zindex None (data_packets b) in
  b <| data_packets := upd_Znth idx (data_packets b) (Some (get_fec_packet p b)) |>.

Definition create_block_with_packet_red (p: packet) (k: Z) (h: Z) : block :=
  let f := new_fec_packet p k h in
  mk_blk (p_seqNum p) (upd_Znth 0 (zseq k None) (Some f)) (zseq h None) k h false 0.

(** Encoder predicate*)

(*TODO: change name state*)

(*We will write our encoder first as a function (with inputted k and h), then write the predicate, where
  we quantify over k and h*)
(*We include 2 pieces of state: the list of blocks include all previous blocks, and the current block is
  represented separately as a block option*)

(*For the situations when we start a new block*)
Definition encode_new (p: packet) (k' h': Z) : list block * option block * list fpacket :=
    let blk := create_block_with_packet_red p k' h' in
    let t := encode_block blk (Some p) in
    if Z.eq_dec k' 1 then ([:: t.1], None, new_fec_packet p k' h' :: t.2) else (nil, Some blk, [ :: new_fec_packet p k' h']).

(*For the situation when we add to an existing block*)
Definition encode_exist (p :packet) (b: block) : list block * option block * list fpacket :=
    let newBlock := add_packet_to_block_red p b in
    let t := encode_block newBlock (Some p) in
    if Z.eq_dec (Zlength (filter isSome (data_packets newBlock))) (blk_k newBlock) then
      ([:: t.1], None, get_fec_packet p b :: t.2) else (nil, Some newBlock, [ :: get_fec_packet p b]).

Definition encoder_one_step (blocks: list block) (currBlock : option block) (curr: packet)
  (k h: Z) : list block * option block * list fpacket :=
  match currBlock with
  | None => (*last block finished, need to create a new one*)
    let t := encode_new curr k h in
    (t.1.1 ++ blocks, t.1.2, t.2)
  | Some b =>
      if ~~(Z.eq_dec (blk_k b) k) || ~~(Z.eq_dec (blk_h b) h)
      then let t1 := encode_block b None in
           let t2 := encode_new curr k h in
           (t2.1.1 ++ [:: t1.1] ++ blocks, t2.1.2, t1.2 ++ t2.2)
      else
        let t := encode_exist curr b in
        (t.1.1 ++ blocks, t.1.2, t.2)
  end.

(*TODO: just use all steps version below*)

(*For proofs, a version which concatenates all of the results of encoder_one_step*)
Definition encoder_all_steps (orig: list packet) (params: list (Z * Z)) : list block * option block * list fpacket :=
  foldl (fun (acc: list block * option block * list fpacket) (x : packet * (Z * Z)) =>
   let t := encoder_one_step acc.1.1 acc.1.2 x.1 x.2.1 x.2.2 in
    (t.1.1, t.1.2, acc.2 ++ t.2)) (nil, None, nil) (combine orig params).

Definition rse_encode_func orig params curr k h :=
  (encoder_one_step (encoder_all_steps orig params).1.1 (encoder_all_steps orig params).1.2 curr k h).2.

(*For the final predicate, we need to find the past parameters that were used. We can do so with
  the following:*)

Definition get_encode_params (l: list fpacket) : option (Z * Z) :=
  match filter (fun (x: fpacket) => ~~ (fd_isParity x)) l with
  | [ :: p] => Some (fd_k p, fd_h p)
  | _ => None
  end.

Lemma encode_block_aux_filter: forall b p,
  [seq x <- (encode_block_aux b p).2 | ~~ fd_isParity (p_fec_data' x)] = [::].
Proof.
  move => b p. erewrite eq_in_filter. apply filter_pred0.
  move => x. rewrite in_mem_In /= In_Znth_iff; zlist_simpl. move => [i] [Hi]. zlist_simpl.
  by move <-.
Qed.

Lemma encode_block_filter : forall b o,
  [seq x <- (encode_block b o).2 | ~~ fd_isParity (p_fec_data' x)] = nil.
Proof.
  move => b o. rewrite /encode_block/=.
  case Hmap: (pmap id (data_packets b)) => [// | h t ]; case : o => [p |//]; apply encode_block_aux_filter.
Qed.

Lemma encode_func_get_params: forall l orig params curr k h,
  l = rse_encode_func orig params curr k h ->
  get_encode_params l = Some (k, h).
Proof.
  move => l orig params curr k h. rewrite /rse_encode_func /encoder_one_step/encode_new/encode_exist/=/get_encode_params.
  case : (encoder_all_steps orig params).1.2 => [b | ].
  - case Hneq: (~~ Z.eq_dec (blk_k b) k || ~~ Z.eq_dec (blk_h b) h).
    + case : (Z.eq_dec k 1) => Hk1 //=.
      * move ->. rewrite filter_cat/=.
        by rewrite encode_block_filter /= encode_block_filter.
      * move ->. rewrite filter_cat/=. by rewrite encode_block_filter.
    + apply orb_false_elim in Hneq.
        case : Hneq => [Hkeq Hneq]. apply negbFE in Hkeq. apply negbFE in Hneq. solve_sumbool.
      case: (Z.eq_dec
        (Zlength
           [seq x <- upd_Znth (Zindex None (data_packets b)) (data_packets b)
                       (Some (get_fec_packet curr b))
              | isSome x]) (blk_k b)) => /= Hk ->/=.
      * rewrite encode_block_filter. by subst. 
      * by subst.
  - case: (Z.eq_dec k 1) => Hk/= -> //=.
    by rewrite encode_block_filter.
Qed.

Corollary encode_func_get_params': forall orig params curr k h,
  get_encode_params (rse_encode_func orig params curr k h) = Some (k, h).
Proof.
  move => orig params curr k h. by eapply encode_func_get_params.
Qed. 

(*Then, we have our final function and predicate*)

Definition rse_encode_func' (orig: list packet) (encoded: list (list fpacket)) (curr: packet) (param: Z * Z) :
  list fpacket :=
  let prevStates := pmap id (map get_encode_params encoded) in
  rse_encode_func orig prevStates curr param.1 param.2.

Definition rse_encoder: (@encoder fec_data) :=
  fun orig encoded curr new =>
    exists (k h: Z),
    0 < k <= fec_n - 1 - fec_max_h /\ 0 < h <= fec_max_h /\
    new = rse_encode_func' orig encoded curr (k, h).

End Encoder.

(*We want to prove the properties we will need of our encoder.
  We express this (eventually) through a large invariant. Unlike the
  decoder, we only need to consider 1 version, and we prove all
  the properties we may need in 1 go.
  The main result: all blocks from the encoder are well formed
  (as is the resulting packet stream) and they are complete if
  they are recoverable.*)

  Section EncoderBlocks.

(*The following tactic will be helpful. First, we have a few lemmas to avoid unfolding*)
Lemma populate_packets_Zlength: forall i model s,
  Zlength (populate_packets i model s) = Zlength s.
Proof.
  move => i model s. by rewrite Zlength_map.
Qed.

Lemma encoder_list_Zlength: forall h k c packets,
  0 <= h ->
  0 <= c ->
  Zlength (encoder_list h k c packets) = h.
Proof.
  move => h k c pkts Hh Hc. 
  by rewrite /encoder_list (proj1 (ListMatrix.lmatrix_multiply_wf _ _ _ _ _)); rep_lia.
Qed.

Lemma encoder_list_Znth_Zlength: forall h k c packets i,
  0 <= c ->
  0 <= i < h ->
  Zlength (Znth i (encoder_list h k c packets)) = c.
Proof.
  move => h k c pkts i Hc Hi. 
  have: ListMatrix.wf_lmatrix (encoder_list h k c pkts) h c. {
    apply encoder_wf; lia. }
  rewrite /ListMatrix.wf_lmatrix/ListMatrix.rect => [[Hlen [_ Hnth]]].
  move: Hnth. by rewrite Forall_Znth Hlen => /(_ _ Hi).
Qed. 

Ltac len_encode :=
  zlist_simpl;
  repeat match goal with
  | [H: context [Zlength (populate_packets _ _ _) ] |- _] => move: H
  | |- context [Zlength (populate_packets ?i ?p ?s) ]  => rewrite populate_packets_Zlength
  | |- context [Zlength (encoder_list _ _ _ _) ] => rewrite encoder_list_Zlength
  | |- context [Zlength (Znth ?x (encoder_list _ _ _ _)) ] => rewrite encoder_list_Znth_Zlength
  | |- 0 <= blk_c ?b => apply blk_c_nonneg
  end; try rep_lia.

(** Lemmas about [encode_block]*)

(*If we give a valid packet as a template and start with a well-formed, in-progress block,
  encoding this block with p as the template gives a well-formed block*)
Lemma encode_block_aux_wf: forall b p,
  packet_valid p ->
  block_in_progress b ->
  block_wf b ->
  block_wf (encode_block_aux b p).1.
Proof.
  move => b p Hpval Hprog. rewrite /block_wf/encode_block_aux/= => 
    [[Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc [Hvalid [Hdats Hpars]]]]]]]]]]].
  split_all => //; try lia.
  - move => p'; rewrite packet_in_block_eq => /orP/=[Hdat | Hpar].
    + apply Hkh. by apply data_in_block.
    + move: Hpar. rewrite mem_map; last first. apply some_inj.
      by move => /mapWithIdxP[ j [y [Hj [Hjth Hp']]]]; subst.
  - move => p'; rewrite packet_in_block_eq => /orP/=[Hdat | Hpar].
    + apply Hid. by rewrite data_in_block.
    + move: Hpar. rewrite mem_map; last first. apply some_inj.
      by move => /mapWithIdxP[ j [y [Hj [Hjth Hp']]]]; subst.
  - (*the hard step*)
    move => p' i; rewrite packet_in_block_eq => /orP/= [Hdat | Hpar].
    + have Hin:=Hdat. move: Hin => /inP. rewrite In_Znth_iff => [[j [Hj Hjth]]].
      split.
      * have [Hi | [Hi | Hout]]: 0 <= i < blk_k b \/ blk_k b <= i < blk_k b + blk_h b \/
          (0 > i \/ i >= blk_k b + blk_h b) by lia.
        -- rewrite Znth_app1; try lia. 
           move: Hidx => /(_ p' i). rewrite data_in_block // Znth_app1; try lia.
           move => H.
           by apply H.
        -- rewrite Znth_app2; try lia. len_encode. 
           move => [Hp']. subst => //=. lia.
        -- rewrite Znth_outofbounds // Zlength_app. len_encode.
      * move ->. have Hj': j = Z.of_nat (fd_blockIndex p'). apply Hidx.
        by apply data_in_block. 
        by rewrite Znth_app1 //; simpl in *; lia.
        rewrite Znth_app1; simpl in *; try lia. by subst.
    + move: Hpar => /mapP => /(_ fec_data_eq_dec) [x Hinx [Hxp]]. 
      subst. move: Hinx => /mapWithIdxP[ j [y [Hj [Hjth Hp']]]]; subst => //=.
      have Hj': 0 <= j < blk_h b by len_encode.
      rewrite {Hj}. split.
      * have [Hi | [Hi | Hout]]: 0 <= i < blk_k b \/ blk_k b <= i < blk_k b + blk_h b \/
          (0 > i \/ i >= blk_k b + blk_h b) by lia.
        -- rewrite Znth_app1; try lia. set p':= {|
            p_packet :=
              Znth j (populate_packets (blk_id b) p (encoder_list (blk_h b) (blk_k b) (blk_c b) (packet_mx b)));
            p_fec_data :=
              {|
                fd_k := blk_k b;
                fd_h := blk_h b;
                fd_isParity := true;
                fd_blockId := blk_id b;
                fd_blockIndex := Z.to_nat (blk_k b + j)
              |}
            |}. move => Hith. have /inP Hin: In (Some p') (data_packets b).
             rewrite In_Znth_iff. exists i. split => //.
            by rewrite Hk. (*why doesnt lia work*)
            move: Hith. subst p'.
            rewrite -((Znth_app1 _ _ _ (parity_packets b))); try lia.
            rewrite Hidx/=. simpl in *. rep_lia. by apply data_in_block.
        -- rewrite Znth_app2; try lia. len_encode.
           move => [Heq]. rep_lia.
        -- rewrite Znth_outofbounds // Zlength_app. len_encode.
      * move ->. rewrite Znth_app2; rewrite Z2Nat.id; try rep_lia.
        have->:(blk_k b + j - Zlength (data_packets b)) = j by lia. by len_encode.
  - len_encode.
  - move => p'; rewrite packet_in_block_eq => /orP /= [Hdat | Hpar].
    + apply Hvalid. by apply data_in_block.
    + move: Hpar. rewrite mem_map; last first. apply some_inj.
      move => /mapWithIdxP[ j [y [Hj [Hjth Hp']]]]; subst.
      rewrite Znth_map;[|len_encode] => /=.
      rewrite /packet_valid/=. apply copy_fix_header_valid with(con1:=(p_contents p)).
      * have: 0 <= j < blk_h b by len_encode. move: Hj => _ Hj. len_encode.
        (*need in_progress for bound here*)
        have Hc: blk_c b <= fec_max_cols by apply blk_c_bound.
        move: Hpval. rewrite /packet_valid /valid_fec_packet => Hval. apply header_bound in Hval.
        rewrite /Endian.Short.max_unsigned/=. rep_lia.
      * apply Hpval.
  - move => p'. by rewrite /packet_in_parity/= => /mapP => /(_ fec_data_eq_dec)
    [x /mapWithIdxP [i [x' [_ [_ Hxeq]]]] [Hx]]; subst.
Qed.

Lemma encode_block_some_wf: forall b p,
  packet_valid p ->
  block_in_progress b ->
  block_wf b ->
  block_wf (encode_block b (Some p)).1.
Proof.
  move => b p Hval Hprog Hwf. rewrite /encode_block.
  case Hdat: (pmap id (data_packets b)) => [|h t];
  by apply encode_block_aux_wf.
Qed.

Lemma encode_block_aux_comp: forall b p,
  black_complete (encode_block_aux b p).1 = black_complete b.
Proof.
  move => b p. by [].
Qed.

Lemma encode_block_black_comp: forall b o,
  black_complete (encode_block b o).1 = black_complete b.
Proof.
  move => b o. rewrite /encode_block/=. case : (pmap id(data_packets b)) => [/= | h t]; case : o => [x|//];
  apply encode_block_aux_comp.
Qed.

Lemma encode_block_time: forall b o,
  black_time (encode_block b o).1 = black_time b.
Proof.
  move => b o. rewrite /encode_block/=. by case : (pmap id(data_packets b)) => [/= | h t]; case : o => [x|//].
Qed.

Lemma data_packets_encode: forall b o,
  data_packets (encode_block b o).1 = data_packets b.
Proof.
  move => b o. rewrite /encode_block/=.
  by case Hmpap: (pmap id (data_packets b)) => [/=|h t /=]; case : o.
Qed.

Lemma encode_block_nonempty: forall b o,
  data_elt b ->
  data_elt (encode_block b o).1.
Proof.
  move => b o. by rewrite /data_elt data_packets_encode.
Qed.

Lemma encode_some: forall b p,
  encode_block b (Some p) = encode_block_aux b p.
Proof.
  move => b p. rewrite /encode_block. by case: (pmap id (data_packets b)).
Qed.

Lemma c_encode_aux: forall (b: block) (p: packet),
  0 <= blk_h b ->
  block_in_progress b ->
  blk_c (encode_block_aux b p).1 = blk_c b.
Proof.
  move => b p Hh Hprog. rewrite /encode_block_aux/= {1}/blk_c/= {2}/blk_c/=.
  rewrite pars_in_progress //.
  case Hpars:   [seq x <- [seq Some i
               | i <- map_with_idx
                        (populate_packets (blk_id b) p
                           (encoder_list (blk_h b) (blk_k b) (blk_c b) (packet_mx b)))
                        (fun (p0 : packet) (i : Z) =>
                         {|
                           p_packet := p0;
                           p_fec_data :=
                             {|
                               fd_k := blk_k b;
                               fd_h := blk_h b;
                               fd_isParity := true;
                               fd_blockId := blk_id b;
                               fd_blockIndex := Z.to_nat (blk_k b + i)
                             |}
                         |})]
     | isSome x] => [//| h t /=]. move: Hpars.
  case : h => [p' /= | //]. move => Hpars'.
  have: (Some p') \in   [seq x <- [seq Some i
             | i <- map_with_idx
                      (populate_packets (blk_id b) p
                         (encoder_list (blk_h b) (blk_k b) (blk_c b) (packet_mx b)))
                      (fun (p0 : packet) (i : Z) =>
                       {|
                         p_packet := p0;
                         p_fec_data :=
                           {|
                             fd_k := blk_k b;
                             fd_h := blk_h b;
                             fd_isParity := true;
                             fd_blockId := blk_id b;
                             fd_blockIndex := Z.to_nat (blk_k b + i)
                           |}
                       |})]
   | isSome x].
  move => Heq. rewrite Hpars'. by rewrite in_cons eq_refl.
  move => /(_ fec_data_eq_dec). (*why do i get these weird goals?*)
  rewrite mem_filter/=. rewrite (@mem_map fpacket_eqType); last first.
    by apply some_inj.
  rewrite in_mem_In In_Znth_iff. len_encode. move => [i [Hi Hith]]. subst.
  len_encode => /=. rewrite Znth_map; len_encode => /=. len_encode.
  by rewrite /blk_c pars_in_progress.
Qed.

Lemma encode_block_aux_encoded: forall b p,
  0 <= blk_h b ->
  block_in_progress b ->
  data_elt b ->
  block_encoded (encode_block_aux b p).1.
Proof.
  move => b p Hh Hprog Helt. rewrite /block_encoded c_encode_aux //.
  split_all.
  - rewrite /= blk_c_in_progress //.
    move: Helt. rewrite /data_elt.
    case Hpmap: (pmap id (data_packets b)) => [// | hd tl /=].
    have Hhd: (Some hd) \in (data_packets b) by rewrite pmap_id_some Hpmap in_cons eq_refl.
    (*have Hhd: In (Some hd) (data_packets b) by rewrite -in_mem_In.*)
    have Hfhd: 0 <= Zlength (p_header hd ++ p_contents hd)  by list_solve.
    have [o ] := (@list_max_nonneg_exists _ (fun o : option fpacket =>
     match o with
     | Some p1 => Zlength (p_header p1 ++ p_contents p1)
     | None => 0
     end) _ _ Hhd Hfhd).
    case : o => [y |//=].
    + (*normal case*)
      move => [Hiny Hymax] _. by exists y.
    + (*weird case where all packets empty*)
      move => [Hin Hmax] _. exists hd. split => //.
      have [H0 | Hgt]: 0 = Zlength (p_header hd ++ p_contents hd) \/
        0 < Zlength (p_header hd ++ p_contents hd) by lia.
      * lia.
      * have//: 0 < 0. have: Zlength (p_header hd ++ p_contents hd) <= 0; last first. lia.
        rewrite -Hmax.
        have Hmax' := (@list_max_nonneg_in _(fun o : option fpacket =>
         match o with
         | Some p1 => Zlength (p_header p1 ++ p_contents p1)
         | None => 0
         end) (data_packets b) (Some hd) Hfhd Hhd). simpl in *; lia.
  - move => p'/=; rewrite /packet_in_parity/= => /inP. 
    rewrite In_Znth_iff; len_encode. move => [i [Hi]]. len_encode. 
    move => [Hp']. subst => /=.
    by rewrite Znth_map/=; len_encode.
  - move => p'/=. rewrite blk_c_in_progress //. move => Hin. rewrite /packet_bytes.
    have Hnonneg: 0 <= Zlength (p_header p' ++ p_contents p') by list_solve.
    have Hb:= (@list_max_nonneg_in _ (fun o : option fpacket =>
     match o with
     | Some p1 => Zlength (p_header p1 ++ p_contents p1)
     | None => 0
     end) (data_packets b) (Some p') Hnonneg Hin). simpl in *; lia.
  - (*the key one: parities are valid*)
    rewrite /= /packet_mx/= -/(packet_mx b) /parity_mx/=/parities_valid; len_encode.
    move => i j Hi Hj.
    len_encode. f_equal. by rewrite Znth_map/=; len_encode.
Qed.

Lemma encode_block_encoded: forall b o,
  0 <= blk_h b ->
  block_in_progress b ->
  data_elt b ->
  block_encoded (encode_block b o).1.
Proof.
  move => b o Hh Hprog Helt. rewrite /encode_block. have Helt':=Helt.
  move: Helt. rewrite /data_elt.
  case Hpmap: (pmap id (data_packets b)) => [//|hd tl/=].
  move => _.
  case : o => [p|]; by apply encode_block_aux_encoded.
Qed.

Lemma encode_block_id: forall (b: block) o,
  blk_id (encode_block b o).1 = blk_id b.
Proof.
  move => b o. rewrite /encode_block. by case : o => /=[p|]; case: (pmap id (data_packets b)).
Qed.

Lemma encode_in_aux: forall b m (p: fpacket),
  (p \in (encode_block_aux b m).2) =
  ((Some p) \in (parity_packets (encode_block_aux b m).1)).
Proof.
  move => b m p. rewrite /= mem_map //. apply some_inj.
Qed.

Lemma encode_in: forall b o (p: fpacket),
  p \in (encode_block b o).2 ->
  (Some p) \in (parity_packets (encode_block b o).1).
Proof.
  move => b o p. rewrite /encode_block.
  by case Hpmap:(pmap id (data_packets b)) => [//= | hd tl /=]; case o => [p' | //]; rewrite encode_in_aux.
Qed.

Lemma in_encode: forall b o (p: fpacket),
  data_elt b ->
  (Some p) \in (parity_packets (encode_block b o).1) ->
  p \in (encode_block b o).2.
Proof.
  move => b o p. rewrite /data_elt /encode_block.
  by case Hmap: (pmap id (data_packets b)) => [//= | hd tl /=] _; case o => [p' |//]; rewrite encode_in_aux.
Qed.

Lemma encode_block_k: forall (b: block) (o: option packet),
  blk_k (encode_block b o).1 = blk_k b.
Proof.
  move => b o. rewrite /encode_block. case : (pmap id (data_packets b)) => [/=| Hd tl /=]; by case : o.
Qed.

Lemma encode_block_h: forall (b: block) (o: option packet),
  blk_h (encode_block b o).1 = blk_h b.
Proof.
  move => b o. rewrite /encode_block. case : (pmap id (data_packets b)) => [/=| Hd tl /=]; by case : o.
Qed.

Lemma encode_parities_Zlength_aux: forall (b: block) p,
  block_wf b ->
  Zlength (parity_packets (encode_block_aux b p).1) = blk_h b.
Proof.
  move => b p Hwf/=. len_encode. case : Hwf. lia.
Qed.

Lemma encode_parities_Zlength: forall (b: block) o,
  block_wf b ->
  Zlength (parity_packets (encode_block b o).1) = blk_h b.
Proof.
  move => b o Hwf. rewrite /encode_block.
  case : (pmap id (data_packets b)) => [//= | h t /=]; case : o => [p|]//; try by apply encode_parities_Zlength_aux.
  rewrite /=. apply Hwf.
Qed.

(*We can switch between None and Some for encode_block*)
Lemma encode_block_none_some: forall (b: block),
  data_elt b ->
  exists model, (Some model) \in (map (omap (@p_packet _)) (data_packets b)) /\
  encode_block b None = encode_block b (Some model).
Proof.
  move => b. rewrite /data_elt /encode_block.
  case Hmap: (pmap id (data_packets b)) => [// | h t /=] _.
  exists (last h t). split => //.
  apply /mapP. exists (Some (last h t)) => //.
  by rewrite pmap_id_some Hmap mem_last.
Qed.

(** Lemmas about [create_block_with_packet_red]*)

Lemma create_block_red_wf: forall p k h,
  packet_valid p ->
  encodable p ->
  0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h ->
  0 < h <= ByteFacts.fec_max_h ->
  block_wf (create_block_with_packet_red p k h).
Proof.
  move => p k h Hval Henc Hk Hh. rewrite /create_block_with_packet_red/block_wf/=.
  (*These will help with a bunch:*)
  have Hin1: forall p',
    (Some p') \in (upd_Znth 0 (zseq k None) (Some (new_fec_packet p k h))) -> p' = (new_fec_packet p k h). {
    move => p' /inP Hin. apply In_upd_Znth in Hin. case : Hin => [[Hp']// | Hin].
    move: Hin. rewrite In_Znth_iff => [[i]]. rewrite zseq_Zlength; try lia; move => [Hi]. by zlist_simpl. }
  have Hin2: forall p', 
    ((Some p') \in (upd_Znth 0 (zseq k None) (Some (new_fec_packet p k h)))) || ((Some p') \in (zseq h None)) ->
    p' = (new_fec_packet p k h). {
    move => p' /orP[ Hinp' | /inP]. by apply Hin1.
    rewrite In_Znth_iff => [[i]]. 
    rewrite zseq_Zlength; try lia; move => [Hi]. by zlist_simpl. }
  split_all => //; try lia.
  - move => p'; rewrite packet_in_block_eq/= => Hinp'. apply Hin2 in Hinp'. by subst.
  - move => p'; rewrite packet_in_block_eq/==> Hinp'. apply Hin2 in Hinp'. by subst.
  - move => p' i; rewrite packet_in_block_eq/==> Hinp'. apply Hin2 in Hinp'. subst => /=.
    split.
    + have [Hi1 | [Hi2 | Hiout]]: (0 <= i < k \/ k <= i < k + h \/ (i < 0 \/ i >= k + h)) by lia.
      * rewrite Znth_app1; zlist_simpl.
        rewrite (upd_Znth_lookup' k); zlist_simpl.
        by case : (Z.eq_dec i 0).
      * by rewrite Znth_app2; zlist_simpl. 
      * rewrite Znth_outofbounds // Zlength_app. by zlist_simpl.
    + move ->. rewrite Znth_app1; zlist_simpl.
      rewrite upd_Znth_same //. by zlist_simpl. 
  - by zlist_simpl.
  - by zlist_simpl.
  - move => p' Hinp'. apply Hin1 in Hinp'. by subst.
  - move => p' Hinp'. apply Hin2 in Hinp'. by subst.
  - move => p' Hinp'. apply Hin1 in Hinp'. by subst.
  - move => p'. rewrite /packet_in_parity/= => /inP. 
    rewrite In_Znth_iff => [[i] [Hi]]. 
    have Hi': 0 <= i < h by move: Hi; zlist_simpl.
    by zlist_simpl.
Qed.

Lemma create_red_nonempty: forall p h k,
  0 < h ->
  data_elt (create_block_with_packet_red p h k).
Proof.
  move => p h k Hh. rewrite /data_elt/=.
  have Hin: (new_fec_packet p h k) \in pmap id (upd_Znth 0 (zseq h None) (Some (new_fec_packet p h k))). {
    rewrite -pmap_id_some in_mem_In In_Znth_iff. exists 0. zlist_simpl. split; try lia.
    rewrite (upd_Znth_lookup' h); zlist_simpl. by case (Z.eq_dec 0 0).
  }
  move: Hin. by case : ( pmap id (upd_Znth 0 (zseq h None) (Some (new_fec_packet p h k)))).
Qed.

Lemma create_red_in_progress: forall p k h,
  0 <= h ->
  block_in_progress (create_block_with_packet_red p k h).
Proof.
  move => p k h Hh. rewrite /block_in_progress/=. apply /allP => x.
  rewrite in_mem_In In_Znth_iff => [[i [Hi]]]. zlist_simpl. by move <-. move: Hi; zlist_simpl.
Qed.

Lemma create_red_Zindex: forall p k h,
  1 <= k ->
  Zindex None (data_packets (create_block_with_packet_red p k h)) = 1.
Proof.
  move => p k h Hk. rewrite /Zindex /index/=.
  rewrite zseq_hd; try lia. rewrite upd_Znth0.
  simpl find.
  have [Hk1 | Hk1]: k = 1 \/ k > 1 by lia.
  - subst. by have->:1-1 = 0 by [].
  - by rewrite zseq_hd; try lia.
Qed.

Lemma create_block_in: forall p k h,
  0 < k ->
  (Some p) \in (map (omap (@p_packet _)) (data_packets (create_block_with_packet_red p k h))).
Proof.
  move => p k h Hk. rewrite /create_block_with_packet_red/=.
  apply /mapP. exists (Some (new_fec_packet p k h)) =>//.
  apply/inP. apply upd_Znth_In. zlist_simpl.
Qed.


(** Lemmas about [add_packet_to_block_red]*)

Lemma add_red_k: forall p b,
  blk_k (add_packet_to_block_red p b) = blk_k b.
Proof.
  by [].
Qed.

Lemma add_red_h: forall p b,
  blk_h (add_packet_to_block_red p b) = blk_h b.
Proof.
  by [].
Qed.

Lemma add_red_id: forall p b,
  blk_id (add_packet_to_block_red p b) = blk_id b.
Proof.
  by [].
Qed.

Lemma add_red_parity: forall p b,
  parity_packets (add_packet_to_block_red p b) = parity_packets b.
Proof.
  by [].
Qed.

Lemma add_black_comp: forall b p,
  black_complete (add_packet_to_block_red p b) = black_complete b.
Proof.
  by [].
Qed.

Lemma add_red_wf: forall p b,
  block_wf b ->
  packet_valid p ->
  encodable p ->
  Zindex None (data_packets b) < blk_k b ->
  block_wf (add_packet_to_block_red p b).
Proof.
  move => p b Hwf Hval Henc Hzidx. rewrite /block_wf add_red_k add_red_h add_red_parity/=.
  case : Hwf => [Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc' [Hvalid [Hdats Hpars]]]]]]]]]].
  have Hnonneg:=(@Zindex_nonneg _ None (data_packets b)).
  split_all => //; try lia.
  - move => p'; rewrite packet_in_block_eq => /orP[/inP Hinp | Hinp]; last first.
    by apply Hkh; apply parity_in_block.
    apply In_upd_Znth in Hinp. case: Hinp => [[Hp'] | Hinp']; subst => //. 
    apply Hkh. apply data_in_block. by apply /inP.
  - move => p'; rewrite packet_in_block_eq => /orP[/inP Hinp | Hinp]; last first. 
    by apply Hid; apply parity_in_block.
    apply In_upd_Znth in Hinp. case: Hinp => [[Hp'] | Hinp']; subst => //.
    by apply Hid; apply data_in_block; apply /inP.
  - simpl in *. move => p' i.
    rewrite cat_app -upd_Znth_app1; try lia.
    rewrite packet_in_block_eq -mem_cat cat_app /= -upd_Znth_app1; try lia.
    move: p' i.
    apply block_wf_list_upd_Znth.
    move => p' i Hin. apply Hidx. by rewrite packet_in_block_eq -mem_cat.
    list_solve.
    rewrite Znth_app1; try lia. apply Znth_Zindex. apply Zindex_In. simpl in *; lia.
    rewrite /= Z2Nat.id; lia.
  - rewrite upd_Znth_Zlength; simpl in *; try lia.
  - move => p' /inP Hinp. 
    apply In_upd_Znth in Hinp. case: Hinp => [[Hp'] | Hinp']; subst => //.
    by apply Henc'; apply /inP.
  - move => p'; rewrite packet_in_block_eq => /orP[/inP Hinp | Hinp]; last first. 
    by apply Hvalid; apply parity_in_block.
    apply In_upd_Znth in Hinp. case: Hinp => [[Hp'] | Hinp']; subst => //. 
    by apply Hvalid; apply data_in_block; apply /inP.
  - move => p' /inP Hinp. apply In_upd_Znth in Hinp. case: Hinp => [[Hp'] | Hinp']; subst => //.
    by apply Hdats; apply /inP.
Qed.

(*not the strongest spec, but OK for us*)
Lemma add_red_nonempty: forall (b: block) p,
  data_elt b ->
  data_elt (add_packet_to_block_red p b).
Proof.
  move => b p. rewrite /data_elt.
  case Hpmap: (pmap id (data_packets b)) => [// | h t /=] _.
  have Hin: In (Some h) (data_packets b) by rewrite -in_mem_In pmap_id_some Hpmap in_cons eq_refl.
  have Hidxlen:=(@Zindex_leq_Zlength _  (data_packets b) None). apply Zle_lt_or_eq in Hidxlen.
  have: h \in pmap id (upd_Znth (Zindex None (data_packets b)) (data_packets b) (Some (get_fec_packet p b))). {
    rewrite -pmap_id_some in_mem_In. case: Hidxlen => [Hlt | Heq].
    - apply In_upd_Znth_old => //. rewrite Znth_Zindex //. by apply Zindex_In.
      have H:=(@Zindex_nonneg _ None (data_packets b)). lia.
    - rewrite upd_Znth_out_of_range //=. right. rewrite Heq/=. lia.
  }
  by case: (pmap id (upd_Znth (Zindex None (data_packets b)) (data_packets b) (Some (get_fec_packet p b)))).
Qed. 

(*When we add a packet to a red block, it gets 1 packet bigger*)
Lemma add_red_size: forall b p,
  Zindex None (data_packets b) < Zlength (data_packets b) ->
  Zlength [seq x <- data_packets b | isSome x] + 1  = 
  Zlength [seq x <- (data_packets (add_packet_to_block_red p b)) | isSome x ].
Proof.
  move => b p Hidx. rewrite /= upd_Znth_Zindex_Zlength //. apply Z.add_comm.
Qed.

Lemma add_block_in: forall (p: packet) (b: block),
  Zindex None (data_packets b) < Zlength (data_packets b) ->
  (Some p) \in [seq omap (p_packet (fec_data:=fec_data)) i | i <- data_packets (add_packet_to_block_red p b)].
Proof.
  move => p b Hidx /=. apply /mapP. exists (Some (get_fec_packet p b)).
  apply /inP. 
  apply upd_Znth_In. split => //. apply Zindex_nonneg. by [].
Qed.

(*Results about uniqeness of packet outputs (and packet outputs
  more generally)*)
Section Uniq.

(*TODO: move next few*)
Lemma mem_zip: forall {A B: eqType} (s1: seq A) (s2: seq B) x y,
  (x, y) \in (zip s1 s2) ->
  (x \in s1) && (y \in s2).
Proof.
  move=> A B s1 s2 x y. move: s2. elim: s1 => 
    [[]// | h1 t1 /= IH [// | h2 t2 /=]].
  rewrite in_cons => /orP[/eqP []->-> | Hinxy].
  - by rewrite mem_head eq_refl.
  - by rewrite andb_orl in_cons (orbC (y == h2)) 
      !andb_orr (IH t2) // !orbT.
Qed. 

Lemma uniq_zip: forall {A B: eqType} (s1: seq A) (s2: seq B),
  uniq s1 || uniq s2 ->
  uniq (zip s1 s2).
Proof.
  move=> A B s1. elim: s1 => [//= [// | //] | h1 t1 /= IH [// | h2 t2 /=]].
  move => /orP[/andP[Hnotin Huniq] | /andP[Hnotin Huniq]].
  - rewrite IH; last by rewrite Huniq.
    case Hin: ((h1, h2) \in (zip t1 t2))=>//.
    apply mem_zip in Hin.
    move: Hin. by rewrite (negbTE Hnotin).
  - rewrite IH; last by rewrite Huniq orbT.
    case Hin: ((h1, h2) \in (zip t1 t2))=>//.
    apply mem_zip in Hin.
    move: Hin. by rewrite (negbTE Hnotin) andbF.
Qed.
  
Lemma map_with_idx_uniq: forall {A: eqType} {B: eqType} (l: seq A) (f: A -> Z -> B),
  (forall z1 z2 a1 a2, 0 <= z1 < Zlength l -> 0 <= z2 < Zlength l ->
    z1 <> z2 -> f a1 z1 <> f a2 z2) ->
  uniq (map_with_idx l f).
Proof.
  move=> A B l f Hinj. rewrite /map_with_idx.
  (*Can't use library functions, f not necessarily injective, but changes
    for each integer, which can only appear once*)
  rewrite -zip_combine. 
  remember (Ziota 0 (Zlength l)) as ints.
  have: uniq ints by rewrite Heqints uniq_NoDup; apply Ziota_NoDup.
  have: size l = size ints by
    rewrite Heqints /Ziota size_map size_iota ZtoNat_Zlength size_length.
  have: (forall z1 z2 a1 a2,
    z1 \in ints -> z2 \in ints -> f a1 z1 = f a2 z2 -> z1 = z2). {
    move=> z1 z2 a1 a2 Hz1 Hz2 Hfeq.
    apply /eqP. apply negbFE. apply /negP =>  /negP /eqP C.
    apply (Hinj z1 z2 a1 a2) =>//.
    move: Hz1. rewrite Heqints => /inP; rewrite Ziota_In; try lia.
    list_solve.
    move: Hz2. rewrite Heqints => /inP; rewrite Ziota_In; try lia.
    list_solve.
}
  rewrite {Heqints Hinj}.
  (*Now, our lemma is sufficiently general (TODO; maybe should just
    prove general lemma separately)*)
  move: ints. elim: l => [// []// | h1 t1 /= IH [//| h2 t2/=]] 
    Hinj [Hsz] /andP[Hnotin Huniq].
  apply /andP; split.
  - apply /negP => /mapP [[x y]] Hin Hfeq.
    apply mem_zip in Hin; move: Hin => /andP[Hinx Hiny].
    have Hy: h2 = y. { 
      apply (Hinj h2 y h1 x)=>//. by rewrite mem_head.
      by rewrite in_cons Hiny orbT.
    }
    subst. by rewrite Hiny in Hnotin.
  - apply IH=>//. move=> z1 z2 a1 a2 Hinz1 Hinz2. 
    by apply Hinj; rewrite in_cons; 
      [rewrite Hinz1 | rewrite Hinz2]; rewrite orbT.
Qed.

(*End move*)

Lemma encode_block_aux_uniq: forall b p,
  0 <= blk_k b ->
  uniq (encode_block_aux b p).2.
Proof.
  move=> b p Hk. rewrite /encode_block_aux/=.
  apply map_with_idx_uniq => z1 z2 a1 a2 Hz1 Hz2 Hneq C.
  inversion C. lia.
Qed.

Lemma encode_block_uniq: forall b o,
  0 <= blk_k b ->
  uniq (encode_block b o).2.
Proof.
  move=> b o Hk.
  rewrite /encode_block. by case: (pmap id (data_packets b)) =>// [| a l];
  case: o=>//; try move=>x; apply encode_block_aux_uniq.
Qed.

Lemma encode_new_uniq: forall p k h,
  uniq (encode_new p k h).2.
Proof.
  move=> p k h. rewrite /encode_new.
  case: (Z.eq_dec k 1)=>//= ->. 
  rewrite encode_block_aux_uniq; last by simpl; lia.
  rewrite andbT. apply /negP => /mapP [[p' z]]/=.
  rewrite -zip_combine => Hin.
  apply mem_zip in Hin.
  rewrite /new_fec_packet => Heq. inversion Heq.
Qed.

Lemma in_encode_new_kh: forall p k h (p': fpacket),
  p' \in (encode_new p k h).2 ->
  fd_k p' = k /\ fd_h p' = h.
Proof.
  move=> p k h p'. rewrite /encode_new.
  case: (Z.eq_dec k 1)=>//= Hk1.
  - rewrite in_cons => /orP[/eqP -> // |]. by
    rewrite encode_some/= => /mapWithIdxP [x] [p''] [] _ [] _ ->.
  - by rewrite in_cons orbF => /eqP ->.
Qed.

Lemma in_encode_block_aux_kh: forall (p: fpacket) b (m: packet),
  p \in (encode_block_aux b m).2 ->
  fd_k p = blk_k b /\ fd_h p = blk_h b.
Proof.
  move=> p b m.
  by rewrite /encode_block_aux/= => /mapWithIdxP [i [x [] _ [] _ ->]].
Qed.

Lemma in_encode_block_kh: forall (p: fpacket) b o,
  p \in (encode_block b o).2 ->
  fd_k p = blk_k b /\ fd_h p = blk_h b.
Proof.
  move=> p b o. rewrite /encode_block.
  case: (pmap id (data_packets b)) => //= [| h t ]; case: o=>//.
  - move=> a. by apply in_encode_block_aux_kh.
  - move=> a. by apply in_encode_block_aux_kh.
  - by apply in_encode_block_aux_kh.
Qed.

Lemma in_encode_block_aux_parity: forall (p: fpacket) b (m: packet),
  p \in (encode_block_aux b m).2 ->
  fd_isParity p = true.
Proof.
  move=> p b m.
  by rewrite /encode_block_aux/= => /mapWithIdxP [i [x [] _ [] _ ->]].
Qed.

Lemma in_encode_block_parity: forall (p: fpacket) b o,
  p \in (encode_block b o).2 ->
  fd_isParity p = true.
Proof.
  move=> p b o. rewrite /encode_block.
  case: (pmap id (data_packets b)) => //= [| h t ]; case: o=>//.
  - move=> a. by apply in_encode_block_aux_parity.
  - move=> a. by apply in_encode_block_aux_parity.
  - by apply in_encode_block_aux_parity.
Qed.

Lemma encode_exist_uniq: forall p b,
  uniq (encode_exist p b).2.
Proof.
  move=> p b. rewrite /encode_exist.
  case: (Z.eq_dec
  (Zlength [seq x <- data_packets (add_packet_to_block_red p b) | isSome x])
  (blk_k (add_packet_to_block_red p b)))=>//= Hkeq.
  rewrite encode_block_uniq; last by
    rewrite add_red_k; list_solve.
  rewrite andbT. apply /negP => C. 
  by apply in_encode_block_parity in C.
Qed.

Lemma in_encode_block_aux_id: forall (p: fpacket) b (m: packet),
  p \in (encode_block_aux b m).2 ->
  fd_blockId p = blk_id b.
Proof.
  move=> p b m.
  by rewrite /encode_block_aux/= => /mapWithIdxP [i [x [] _ [] _ ->]].
Qed.

Lemma in_encode_block_id: forall (p: fpacket) b o,
  p \in (encode_block b o).2 ->
  fd_blockId p = blk_id b.
Proof.
  move=> p b o. rewrite /encode_block.
  case: (pmap id (data_packets b)) => //= [| h t ]; case: o=>//.
  - move=> a. by apply in_encode_block_aux_id.
  - move=> a. by apply in_encode_block_aux_id.
  - by apply in_encode_block_aux_id.
Qed.

(*TODO: maybe put in Block?*)
Lemma wf_in_data: forall b (p: fpacket),
  block_wf b ->
  packet_in_block p b ->
  fd_isParity p = false ->
  packet_in_data p b.
Proof.
  move=> b p. rewrite packet_in_block_eq 
    /packet_in_data => Hwf /orP[Hindat //| Hinpar] Hnopar.
  have: fd_isParity p by apply Hwf. by rewrite Hnopar.
Qed.

End Uniq.

(*Some small results we need, not sure where to put them*)

(*deal with generic preds of the form: forall x, x \in l -> p x*)
Lemma in_pred_rev: forall {A: eqType} (s: seq A) (p: pred A),
  (forall x, x \in s -> p x) ->
  (forall x, x \in (rev s) -> p x).
Proof.
  move => A s p Hall x Hinx. apply Hall. move: Hinx. by rewrite mem_rev.
Qed.

Lemma in_pred_tl: forall {A: eqType} (h: A) (s: seq A)  (p: pred A),
  (forall x, x \in (h :: s) -> p x) ->
  (forall x, x \in s -> p x).
Proof.
  move => A s h p Hall x Hxin. apply Hall. by rewrite in_cons Hxin orbT.
Qed.

Lemma cons_app: forall {A: Type} (x : A) (l: seq A),
  x :: l = [:: x] ++ l.
Proof.
  by [].
Qed.

(** Encoder properties *)

(*To prove the main theorem about the encoder, we need to show that a number of properties are preserved in
  each run of encoder_one_step. To reduce repetition and make things
  cleaner, we group the properties together and prove the 3 different cases we need before proving the full theorem*)

Definition block_option_list (x: list block * option block) : list block :=
  match x.2 with
  | None => x.1
  | Some b => b :: x.1
  end.

Definition encoder_props (orig: list packet) (blks: list block) (currBlock: option block) 
  (pkts: seq fpacket) : Prop :=
  perm_eq (get_blocks pkts) (block_option_list (blks, currBlock)) /\
  (forall b, b \in (block_option_list (blks, currBlock)) -> block_wf b) /\
  (forall b, b \in (block_option_list (blks, currBlock)) -> black_complete b = false) /\
  (forall b, b \in (block_option_list (blks, currBlock)) -> black_time b = 0) /\
  (forall b, b \in (block_option_list (blks, currBlock)) -> data_elt b) /\
  (forall b p, b \in (block_option_list (blks, currBlock)) -> 
    packet_in_data p b ->
    (p_packet p) \in orig) /\
  (forall b, b \in (block_option_list (blks, currBlock)) -> exists p,
      packet_in_data p b /\ blk_id b = p_seqNum p) /\
  (*All previous blocks are done; the current is either done (with k packets) or has no parities*)
  (forall b, b \in blks -> block_encoded b) /\
  (forall b, currBlock = Some b -> block_in_progress b) /\
  wf_packet_stream pkts /\
  uniq pkts /\
  (*The underlying packets of the data packets are unique*)
  uniq (map (@p_packet _) (filter (fun (f: fpacket) => ~~ fd_isParity f) pkts)).

Lemma encoder_props_orig_rev: forall orig blks currBlock pkts,
  encoder_props orig blks currBlock pkts ->
  encoder_props (rev orig) blks currBlock pkts.
Proof.
  move => orig blks currBlock pkts. rewrite /encoder_props => Henc; split_all; try apply Henc.
  move => b p Hinp Hin. rewrite mem_rev. move: Hinp Hin. by apply Henc.
Qed.

Lemma encoder_props_orig_rev_iff: forall orig blks currBlock pkts,
  encoder_props orig blks currBlock pkts <->
  encoder_props (rev orig) blks currBlock pkts.
Proof.
  move => orig blks currBlock pkts. split; move => Henc.
  - by apply encoder_props_orig_rev.
  - rewrite -(revK orig). by apply encoder_props_orig_rev.
Qed.


(** Lemmas for main theorem *)

(* Overall, we need 3 cases to prove the theorem:
  1. the properties are preserved when we start a new block
  2. the properties are preserved when we encode the current block
  3. the properties are preserved when we add a packet to the current block

  We prove these properties after several helper lemmas below:*)

Lemma create_red_encode_block_lists: forall (p: packet) h k,
  0 < h <= fec_max_h ->
  0 < k <= fec_n - 1 - fec_max_h ->
  packet_valid p ->
  encodable p ->
  al (get_block_lists (new_fec_packet p k h :: (encode_block (create_block_with_packet_red p k h) (Some p)).2)) =
  [:: block_to_btuple (encode_block (create_block_with_packet_red p k h) (Some p)).1 ].
Proof.
  move => p h k Hh0 Hk0 Hval Henc.
  apply get_block_lists_single.
  - apply encode_block_some_wf => //.
    apply create_red_in_progress; lia.
    by apply create_block_red_wf.
  - apply data_block_elt. apply encode_block_nonempty.
    apply create_red_nonempty; lia.
  - move => p'. rewrite encode_some/= in_cons/=.
    split.
    + move => /orP[/eqP Hp' | Hin].
      * subst. apply /orP. left. apply /inP. apply upd_Znth_In. by zlist_simpl.
      * apply /orP. right. by apply map_f.
    + move => /orP[ Hinp | Hinp].
      * apply /orP. left. apply /eqP. move: Hinp => /inP Hinp.
        apply In_upd_Znth in Hinp. case: Hinp => [[Hp']// | Hinp'].
        move: Hinp'. rewrite In_Znth_iff => [[i [Hlen]]]. zlist_simpl => //.
        move: Hlen; zlist_simpl.
      * apply /orP. right. move: Hinp => /inP /inP; rewrite mem_map //.
        by apply some_inj.
Qed.

(*Extend this easily*)
Lemma create_red_encode_blocks: forall (p: packet) h k,
  0 < h <= fec_max_h ->
  0 < k <= fec_n - 1 - fec_max_h ->
  packet_valid p ->
  encodable p ->
  get_blocks (new_fec_packet p k h :: (encode_block (create_block_with_packet_red p k h) (Some p)).2) =
  [:: (encode_block (create_block_with_packet_red p k h) (Some p)).1 ].
Proof.
  move => p h k Hh Hk Hvalid Henc. rewrite /get_blocks create_red_encode_block_lists //= btuple_block_inv //=.
  - apply encode_block_some_wf => //. apply create_red_in_progress; lia.
    by apply create_block_red_wf.
  - by rewrite encode_block_black_comp.
  - by rewrite encode_block_time.
  - apply data_block_elt. apply encode_block_nonempty. apply create_red_nonempty; lia.
Qed. 

(*An easier case*)
Lemma create_red_block: forall (p: packet) h k,
  0 < k ->
  0 <= h ->
  get_blocks [:: new_fec_packet p k h] = [:: create_block_with_packet_red p k h].
Proof.
  move => b h k Hk Hh. rewrite /get_blocks/=/create_block_with_packet_red/new_packet_list/new_fec_packet/=.
  set p:= {|
               p_packet := b;
               p_fec_data :=
                 {|
                   fd_k := k;
                   fd_h := h;
                   fd_isParity := false;
                   fd_blockId := p_seqNum b;
                   fd_blockIndex := 0
                 |}
             |}.
  rewrite /btuple_to_block/={1}zseq_hd; try lia. rewrite upd_Znth0/=.
  f_equal. f_equal.
  - rewrite sublist_upd_Znth_lr; zlist_simpl => //=. f_equal.
    rewrite zseq_sublist; try lia. f_equal. lia.
  - rewrite sublist_upd_Znth_r; zlist_simpl.
    rewrite zseq_sublist; try lia. f_equal. lia.
Qed.


(*If there is no block in progress, we can get useful information about the sequence numbers of all
  packets in pkts*)
Lemma in_pkts_id_new_block: forall orig blks pkts h,
  encoder_props orig blks None pkts ->
  p_seqNum h \notin (map p_seqNum orig) ->
  forall (p: fpacket),
  p \in pkts ->
  fd_blockId p != p_seqNum h.
Proof.
  move => orig blks pkts h [IHperm [IHallwf [IHblackcomp [IHtime 
    [IHdata [IHinorig [IHids [IHencoded [IHprog [IHwfpkts IHuniqpkts]]]]]]]]]] 
  Hht p Hpin.
  (*have Hpin': In p pkts by rewrite -in_mem_In.*)
  have Hprop: get_block_lists_prop pkts (map block_to_btuple blks). {
    eapply perm_get_block_lists_prop. by apply get_block_lists_spec. have Hperm':=IHperm.
    move: Hperm'. rewrite /get_blocks => Hperm'. apply (perm_map (block_to_btuple)) in Hperm'.
    rewrite -map_comp in Hperm'. rewrite (btuple_block_inv_list IHwfpkts) in Hperm' => //.
    by apply get_block_lists_spec.
  }
  have [pkts' [Hinpkts Hinp]] :=(get_block_lists_allin_in IHwfpkts Hprop Hpin).
  move: Hinpkts => /mapP.
  (*idea: p is in a block b which is in blks. We know by IH that blk_id b = seqNum of some
    packet (which must be in pkts). Thus, by uniqueness of sequence numbers, different than h's*)
  rewrite /block_to_btuple/= => [[b] Hinb [Hid Hpkts']]. rewrite Hid.
  move: IHids => /(_ _ Hinb) [p'] [Hinp' Hidp']. rewrite Hidp'.
  move: IHinorig => /(_ _ _ Hinb Hinp') Hint.
  case: (p_seqNum p' == p_seqNum h) /eqP => Heq //. move: Hht.
  have->//: p_seqNum h \in [seq p_seqNum i | i <- orig]. rewrite -Heq.
  by apply map_f.
Qed.

(*Case 1: If there is no block in progress, we can add a new block and packet, preserving the invariant*)
Lemma encoder_props_new_block: forall p orig blks pkts k h,
  0 < k <= fec_n - 1 - fec_max_h ->
  0 < h <= fec_max_h ->
  packet_valid p ->
  encodable p ->
  p_seqNum p \notin (map p_seqNum orig) ->
  encoder_props orig blks None pkts ->
  encoder_props (p :: orig) blks (Some (create_block_with_packet_red p k h))
    (pkts ++ [:: new_fec_packet p k h]).
Proof.
  move => p orig blks pkts k h Hk Hh Hval Henc Hhnum Hprops.
  have Hpktsid:=(in_pkts_id_new_block Hprops Hhnum).
  case: Hprops => [IHperm [IHallwf [IHblackcomp [IHtime [IHdata [IHinorig [IHids [IHencoded [IHprog [IHwfpkts [IHwfuniq IHuniqdat]]]]]]]]]]].
  (*We need to prove wf_packet_stream first*)
  have Hwf: wf_packet_stream (pkts ++ [:: new_fec_packet p k h]). {
    rewrite /wf_packet_stream; split_all.
    - move => p1 p2. rewrite !mem_cat !in_cons/= => /orP[Hp1 | /orP[/eqP Hp1 |//]] 
        /orP[Hp2 | /orP[/eqP Hp2|//]]; subst => //=.
      + by apply IHwfpkts.
      + move => Heq. apply Hpktsid in Hp1. move: Hp1. by rewrite Heq eq_refl.
      + move => Heq. apply Hpktsid in Hp2. move: Hp2. by rewrite Heq eq_refl.
    - move => p1 p2. rewrite !mem_cat !in_cons/= => /orP[Hp1 | /orP[/eqP Hp1 |//]] 
        /orP[Hp2 | /orP[/eqP Hp2|//]]; subst => //=.
      + by apply IHwfpkts.
      + move => Heq. apply Hpktsid in Hp1. move: Hp1. by rewrite Heq eq_refl.
      + move => Heq. apply Hpktsid in Hp2. move: Hp2. by rewrite Heq eq_refl.
      (*literally same proof*)
    - move => p'. rewrite !mem_cat !in_cons/= => /orP[Hp1 | /orP[/eqP Hp1 |//]]; subst => //=.
      + by apply IHwfpkts.
      + lia.
    - move => p'. rewrite !mem_cat !in_cons/= => /orP[Hp1 | /orP[/eqP Hp1 |//]]; subst => //=.
      + by apply IHwfpkts.
      + lia.
  }
  (*For uniq goals*)
  have Hpnotin: forall (x: fpacket), fd_isParity x = false -> 
    p_packet x = p -> x \notin pkts. {
    move=> x Hpar Hp. apply /negP => Hin.
    (*this packet is in a block*)
    have [b /andP[Hinb Hinpb]]:=(get_blocks_allin IHwfpkts Hin).
    have Hinb': b \in (block_option_list (blks, None)) by 
      rewrite -(perm_mem IHperm).
    have Hindat: packet_in_data x b by
      apply wf_in_data=>//; apply IHallwf.
    move: IHinorig => /(_ _ _ Hinb' Hindat)/= => Hinorig.
    move: Hhnum => /negP => C; apply C.
    apply /mapP. exists (p_packet x)=>//. by rewrite Hp. 
  }
  (*Now we can complete this case*)
  rewrite /encoder_props /block_option_list/=; split_all =>//.
  { rewrite get_blocks_app //. eapply perm_trans. rewrite perm_catC. apply perm_refl.
    rewrite (cons_app _ blks). apply perm_cat => //. by rewrite create_red_block //; lia.
    move => p1 p2 Hp1. apply Hpktsid in Hp1. rewrite in_cons => /orP[/eqP Hp2 | //]. by subst. 
  }
  { move => b; rewrite in_cons => /orP[/eqP Hb | Hinb//]; last first. by apply IHallwf. subst.
    by apply create_block_red_wf.
  }
  { move => b; rewrite in_cons => /orP[/eqP Hb | Hinb]; last first. by apply IHblackcomp. by subst. }
  { move => b; rewrite in_cons => /orP[/eqP Hb | Hinb]; last first. by apply IHtime. by subst. }
  { move => b; rewrite in_cons => /orP[/eqP Hb | Hinb]; last first. by apply IHdata. subst.
    apply create_red_nonempty; lia. }
  { move => b p'; rewrite in_cons => /orP[/eqP Hb /inP Hinp | Hinb Hinp]; last first; rewrite in_cons. 
    by rewrite (IHinorig _ _ Hinb) // orbT.
    subst. apply In_upd_Znth in Hinp.
    case : Hinp => [[Hpnew] | Hin].
    - subst. by rewrite eq_refl.
    - move: Hin. rewrite In_Znth_iff; zlist_simpl. move => [i [Hi]]. 
      by zlist_simpl.
  }
  { move => b; rewrite in_cons => /orP[/eqP Hb | Hinb]; last first. 
    by apply IHids. subst => /=.
    exists (new_fec_packet p k h).
    split => //. apply /inP. apply upd_Znth_In. zlist_simpl.
  }
  { move => b [Hb]. rewrite -Hb/=. apply create_red_in_progress. lia. }
  { rewrite cat_uniq/= orbF andbT IHwfuniq/=.
    by apply Hpnotin.
  }
  { rewrite filter_cat/= map_cat/= cat_uniq/= orbF andbT IHuniqdat/=.
    apply /mapP => [[f]]. rewrite mem_filter => /andP[Hnotpar Hinf] Hp.
    have: f \notin pkts by apply Hpnotin=>//; rewrite (negbTE Hnotpar).
    by rewrite Hinf.
  }
Qed.

(*This is needed in several cases*)
Lemma in_old_block: forall pkts blks b,
  wf_packet_stream pkts ->
  perm_eq (get_blocks pkts) (b :: blks) ->
  block_in_progress b ->
  block_wf b ->
  forall (x: fpacket), x \in pkts -> fd_blockId x = blk_id b ->
    packet_in_data x b.
Proof.
  move => pkts blks b Hwf Hperm Hprog Hwfb x Hinx Hidx.
  apply (perm_map block_to_btuple) in Hperm. move: Hperm. rewrite -map_comp.
  rewrite (btuple_block_inv_list Hwf) //; last first.
    by apply get_block_lists_spec.
  move => Hperm.
  (*have Hinx1: In x pkts by rewrite -in_mem_In.*)
  have Hprop:=(perm_get_block_lists_prop (get_block_lists_spec Hwf) Hperm).
  have [pkts' [Hinpkts' Hinxp]]: 
    exists pkts', (fd_blockId (p_fec_data' x), pkts') \in
    (block_to_btuple b :: [seq block_to_btuple i | i <- blks]) /\ (Some x) \in pkts' by
    apply (get_block_lists_allin_in Hwf).
  move: Hinpkts'; rewrite in_cons /= => /orP[Hinpkts' | Hinpkts'].
  - move: Hinpkts'. rewrite /block_to_btuple/= => /eqP [Hid] Hpkts'; subst.
    (*has to be in data packets because block is in progress*)
    move: Hinxp; rewrite mem_cat => /orP[/inP Hindat // | Hinpar].
    move: Hprog. rewrite /block_in_progress => /allP Hprog.
    by move: Hprog => /(_ _ Hinpar).
  - (*problem - ids are unique*)
    case Hprop => [_ [_ [_ [_ Huniq]]]].
    move: Huniq. rewrite /=.
    have->//:(blk_id b \in [seq i.1 | i <- [seq block_to_btuple i | i <- blks]]).
    apply /mapP. by exists (fd_blockId x, pkts').
Qed.

(*The most difficult part of Cases 2 and 3 is dealing with the [get_blocks]. Both cases are broadly similar,
  so we generalize with the following lemma and prove each case as a corollary. This is quite a long, ugly proof*)
Lemma get_blocks_expand: forall pkts p1 blks b b1,
  wf_packet_stream (pkts ++ p1) ->
  (forall b', (b == b') || (b' \in blks) -> block_wf b') ->
  (forall b', (b == b') || (b' \in blks) -> black_complete b' = false) ->
  (forall b', (b == b') || (b' \in blks) -> black_time b' = 0) ->
  (forall b', (b == b') || (b' \in blks) -> data_elt b') ->
  block_in_progress b ->
  (*If b1 and p1 satisfy some reasonable properties with b and each other:*)
  block_wf b1 ->  
  blk_id b1 = blk_id b ->
  blk_k b1 = blk_k b ->
  blk_h b1 = blk_h b ->
  black_complete b1 = false ->
  black_time b1 = 0 ->
  (forall p, packet_in_data p b -> packet_in_data p b1)  ->
  (forall p, p \in p1 -> packet_in_block p b1) ->
  (forall p, packet_in_block p b1 -> packet_in_data p b \/ p \in p1) ->
  (forall (p p': fpacket), packet_in_data p b -> p' \in p1 -> 
    fd_blockIndex p != fd_blockIndex p') ->
  perm_eq (get_blocks pkts) (b :: blks) ->
  perm_eq (get_blocks (pkts ++ p1)) (b1 :: blks).
Proof.
  move => pkts p1 blks b b1 Hwf Hallwf Hallblack Htimes Hnonemp Hprog Hwfb1 Hidb1 Hkb1 Hhb1 Hblackb1 Htimeb1 Hinb Hinp1 
    Hiniff Hdisj Hperm.
  have Hwfb : block_wf b by apply Hallwf; rewrite eq_refl.
  have Hwfp: wf_packet_stream pkts. apply (wf_substream Hwf). move => x Hinx. by rewrite mem_cat Hinx.
  have Hinpkts: forall (x: fpacket), x \in pkts -> fd_blockId x = blk_id b ->
    packet_in_data x b. {
    move => x Hpkts Hid. by apply (in_old_block Hwfp Hperm). }
  have Hinp1': forall (x: fpacket), x \in p1 -> fd_blockId x = blk_id b /\
    fd_k x = blk_k b /\ fd_h x = blk_h b. {
    move => x Hin. apply Hinp1 in Hin. rewrite -Hidb1 -Hkb1 -Hhb1.
    by split; apply Hwfb1. }
  have Hdatab1: data_elt b1. { have: data_elt b by apply Hnonemp; rewrite eq_refl.
    rewrite /data_elt.
    case Hmap: (pmap id (data_packets b)) => [// | h t /=] _.
    have: h \in pmap id (data_packets b1). rewrite -pmap_id_some.
    apply Hinb. by rewrite /packet_in_data pmap_id_some Hmap in_cons eq_refl.
    by case: (pmap id (data_packets b1)).
  }
  move: Hperm. rewrite /get_blocks. move => Hperm.
  apply (perm_map block_to_btuple) in Hperm. move: Hperm. rewrite -map_comp.
  rewrite (btuple_block_inv_list Hwfp) //; last first.
    by apply get_block_lists_spec. (*NOTE: Hwfb1 <-> Hwfenc*)
  rewrite -(@block_btuple_inv_list (b1 :: blks)).
  2 : { move => b' /=; rewrite in_cons => /orP[/eqP Hb |Hin// ]; 
        subst => //. by apply Hallwf; rewrite Hin orbT. }
  2 : { move => b' /=; rewrite in_cons => /orP[/eqP Hb |Hin// ];
        subst => //. by apply Hallblack; rewrite Hin orbT. }
  2 : { move => b' /=; rewrite in_cons => /orP[/eqP Hb |Hin// ]; 
        subst => //. by apply Htimes; rewrite Hin orbT. }
  2 : { move => b' /=; rewrite in_cons => /orP[/eqP Hb |Hin// ]; 
        subst => //; apply data_block_elt => //.
        by apply Hnonemp; rewrite Hin orbT.  }
  move => Hperm. rewrite (map_comp btuple_to_block). apply perm_map.
  (*Now we finally have things just in terms of block lists*)
  move: Hperm => /=Hperm.
  apply (get_block_lists_prop_perm Hwf). by apply get_block_lists_spec.
  apply (perm_get_block_lists_prop (get_block_lists_spec Hwfp)) in Hperm.
  (*We have now reduced this to a problem just about [get_block_lists_prop], which is tedious
    but possible to work with*)
  case Hperm => [Hallin1 [Hnonemp1 [Hlen1 [Heq1 Huniq1]]]].
  (*One more lemma before continuing case-by-case*)
  have Hinborig: forall (x: fpacket), packet_in_block x b ->
    x \in pkts. {
    have Hinb': (blk_id b, data_packets b ++ parity_packets b) \in
      (block_to_btuple b :: [seq block_to_btuple i | i <- blks]) by 
      rewrite in_cons eq_refl.
    move => x. rewrite packet_in_block_eq -mem_cat => Hinx.
    by apply (get_block_lists_prop_packets Hperm Hinb' Hinx). }
  rewrite /get_block_lists_prop; split_all.
  - move => p; rewrite mem_cat => /orP[Hinp | Hinp].
    + apply Hallin1 in Hinp. case: Hinp => /= [pkts'].
      rewrite !in_cons => /orP[/eqP Hinb' | Hinb'].
      * exists (block_to_btuple b1).2. rewrite in_cons; apply /orP; left.
        move: Hinb'. rewrite /block_to_btuple/= Hidb1 => [[Hid Hpkts]].
        by rewrite Hid.
      * exists pkts'. by rewrite in_cons Hinb' orbT.
    + exists (block_to_btuple b1).2. rewrite in_cons; apply /orP; left.
      rewrite /block_to_btuple/= Hidb1.
      f_equal. apply Hinp1' in Hinp. case: Hinp => -> _.
      by rewrite eq_refl.
  - move => i' pkts'/=; rewrite in_cons => /orP[/eqP Hin1 | Hin2].
    + move: Hin1. rewrite /block_to_btuple/= Hidb1 => [[Hid Hpkts']].
      subst. move: Hdatab1. rewrite /data_elt.
      case Hmap: (pmap id (data_packets b1)) => [//| h tl /=] _.
      exists h. rewrite mem_cat. 
      by rewrite pmap_id_some Hmap in_cons eq_refl.
    + apply (Hnonemp1 i' pkts'). by rewrite in_cons Hin2 orbT.
  - move => i' pkts' p/=; rewrite in_cons => /orP[/eqP Hin1 | Hin2] Hinp.
    + move: Hin1. rewrite /block_to_btuple/= Hidb1 => [[Hid Hpkts']].
      subst. rewrite mem_cat in Hinp.
      rewrite Zlength_app //.
      have->:Zlength(data_packets b1) = blk_k b1 by apply Hwfb1.
      have->:Zlength(parity_packets b1) = blk_h b1 by apply Hwfb1.
      have [Hkeq Hheq]: fd_k p = blk_k b /\ fd_h p = blk_h b. {
        rewrite -Hkb1 -Hhb1. by apply Hwfb1.  }
      by rewrite Hkeq Hheq Hkb1 Hhb1.
    + apply (Hlen1 i') => //. by rewrite in_cons Hin2 orbT.
  - case Hwfb1 => [Hhbound [Hkbound [_ [_ [_ [Hdat1 [Hpar1 _]]]]]]].
    (*Now we can prove this*)
    move => i' pkts'/=; rewrite in_cons => /orP[/eqP Hin1 | Hin2].
    + move: Hin1. rewrite /block_to_btuple/= Hidb1.
      have Hinb': (blk_id b, data_packets b ++ parity_packets b) \in
        (block_to_btuple b :: [seq block_to_btuple i | i <- blks]) by 
        rewrite in_cons eq_refl.
      apply Heq1 in Hinb'.
      move => [Hid Hpkts']; subst.
      apply Znth_eq_ext; zlist_simpl.
      rewrite Hdat1 Hpar1 => i Hi. zlist_simpl.
      case_pickSeq (pkts ++ p1).
      { move: Hinx. rewrite mem_cat => /orP[Hinx | Hinx].
        { case Hwfb1 => [_ [_ [_ [_ [Hidxb1 _]]]]].
          solve_sumbool. apply Hidxb1 in e => //.
          apply Hinpkts in Hinx =>//. apply data_in_block. 
          by apply Hinb.
        }
        { case Hwfb1 => [_ [_ [_ [_ [Hidxb1 _]]]]].
          solve_sumbool. apply Hidxb1 in e => //.
          by apply Hinp1.
        }
      }
      { move => Hall. case Hith: (Znth i (data_packets b1 ++ parity_packets b1)) => [p' |//].
        have Hinp': packet_in_block p' b1. { 
          rewrite packet_in_block_eq -mem_cat. apply /inP.
          rewrite -Hith. apply Znth_In. rewrite Zlength_app; simpl in *; lia. }
        have Hidp': fd_blockId p' = blk_id b. { rewrite -Hidb1. by apply Hwfb1. } 
        have Hidxp': i = (Z.of_nat (fd_blockIndex p')) by apply Hwfb1.
        have Hincat: p' \in (pkts ++ p1). { (*NOTE: here is where we need iff condition*)
          have [Hinpb | Hinpp1]: packet_in_data p' b \/ p' \in p1 by apply Hiniff => //.
          - rewrite mem_cat. apply /orP. left. apply Hinborig. by apply data_in_block.
          - by rewrite mem_cat Hinpp1 orbT.
        }
        move: Hall => /( _ _ Hincat). rewrite -Hidxp' Hidp' eq_refl. by case: (Z.eq_dec i i).
      }
    +  (*now at the other case, just need to know no tuple has this id*)
      have Hin2': (i', pkts') \in (block_to_btuple b :: [seq block_to_btuple i | i <- blks])
        by rewrite in_cons Hin2 orbT.
      apply Heq1 in Hin2'. rewrite {1}Hin2'. apply Znth_eq_ext; zlist_simpl. move => i Hi.
      zlist_simpl. case_pickSeq pkts.
      * case_pickSeq (pkts ++ p1).
        { move: Hinx0. rewrite mem_cat => /orP[Hinx0 | Hinx0].
          { f_equal. apply Hwfp => //. congruence. solve_sumbool. subst.
            by apply Nat2Z.inj in e.
          }
          { have Hinx0':=Hinx0. apply Hinp1' in Hinx0'. case: Hinx0' => [Hblkidx0 [Hkx0 Hhx0]].
            apply Hinpkts in Hinx => //; [|congruence]. solve_sumbool. subst.
            apply Nat2Z.inj in e.
            move: Hdisj => /( _ _ _ Hinx Hinx0). by rewrite e eq_refl.
          }
        }
        { have Hinxapp: x \in pkts ++ p1 by rewrite mem_cat Hinx.
          move => /(_  _ Hinxapp). by rewrite Hxid Hidx eq_refl.
        }
      * case_pickSeq (pkts ++ p1) => //.
        move: Hinx. rewrite mem_cat => /orP[Hinx0 | Hinx0].
        { move => /( _ _ Hinx0). by rewrite Hxid Hidx eq_refl. }
        { apply Hinp1' in Hinx0. case : Hinx0 => [Hxblkid [Hxk Hxh]].
          (*by uniqueness of idx*)
          move: Huniq1 => /=.
          have->//: (blk_id b \in [seq i.1 | i <- [seq block_to_btuple i | i <- blks]]).
          apply /mapP. exists (i', pkts') => //=. congruence.
        }
  - rewrite /= Hidb1. apply Huniq1.
Qed.

(*The property we need (derived from previous) for case 2*)
Lemma get_blocks_encode: forall pkts blks b model,
  wf_packet_stream (pkts ++ (encode_block b (Some model)).2) ->
  (forall b', (b == b') || (b' \in blks) -> block_wf b') ->
  (forall b', (b == b') || (b' \in blks) -> black_complete b' = false) ->
  (forall b', (b == b') || (b' \in blks) -> black_time b' = 0) ->
  (forall b', (b == b') || (b' \in blks) -> data_elt b') ->
  packet_valid model ->
  block_in_progress b ->
  perm_eq (get_blocks pkts) (b :: blks) ->
  perm_eq (get_blocks (pkts ++ (encode_block b (Some model)).2)) ((encode_block b (Some model)).1 :: blks).
Proof.
  move => pkts blks b model Hwf Hallwf Hallblack Htimes Hnonemp Hvalid Hprog Hperm.
  have Hwfb : block_wf b by apply Hallwf; rewrite eq_refl.
  apply (get_blocks_expand Hwf Hallwf) => //.
  - by apply encode_block_some_wf.
  - by rewrite encode_block_id.
  - by rewrite encode_block_k.
  - by rewrite encode_block_h.
  - rewrite encode_block_black_comp. by apply Hallblack; rewrite eq_refl.
  - rewrite encode_block_time. by apply Htimes; rewrite eq_refl.
  - move => p Hinp. by rewrite /packet_in_data data_packets_encode.
  - move => p Hinp. apply parity_in_block.
    by apply encode_in.
  - move => p'. rewrite packet_in_block_eq data_packets_encode => 
      /orP[Hin // | Hin]. by left.
    right. 
    apply in_encode =>//. by apply Hnonemp; rewrite eq_refl.
  - move => p p' Hinp Hinp'.
    apply in_data_idx_bound in Hinp => //.
    apply encode_in in Hinp'.
    apply in_parity_idx_bound in Hinp'; [| by apply encode_block_some_wf].
    move: Hinp'. rewrite encode_block_k encode_block_h => Hidx.
    apply /eqP => Hc. rewrite Hc in Hinp. lia.
Qed.


(*The property we need (derived from previous) for case 3*)
Lemma get_block_add: forall pkts blks b p,
  wf_packet_stream (pkts ++ [:: get_fec_packet p b]) ->
  (forall b', (b == b') || (b' \in blks) -> block_wf b') ->
  (forall b', (b == b') || (b' \in blks) -> black_complete b' = false) ->
  (forall b', (b == b') || (b' \in blks) -> black_time b' = 0) ->
  (forall b', (b == b') || (b' \in blks) -> data_elt b') ->
  block_in_progress b ->
  packet_valid p ->
  encodable p ->
  Zindex None (data_packets b) < blk_k b ->
  perm_eq (get_blocks pkts) (b :: blks) ->
  perm_eq (get_blocks (pkts ++ [:: get_fec_packet p b])) (add_packet_to_block_red p b :: blks).
Proof.
  move => pkts blks b p Hwf Hallwf Hallblack Htimes Hnonemp Hprog Hvalid Henc Hnotdone Hperm.
  have Hwfb : block_wf b by apply Hallwf; rewrite eq_refl.
  case Hwfb => [Hkbound [Hhbound [ _ [ _ [ _ [Hdatlen [Hparlen _]]]]]]].
  have Hzidxb: 0 <= Zindex None (data_packets b) < Zlength (data_packets b). {
     have Hnonneg:=(@Zindex_nonneg _ None (data_packets b)). lia. }
  apply (get_blocks_expand Hwf Hallwf) => //.
  - by apply add_red_wf.
  - rewrite add_black_comp. by apply Hallblack; rewrite eq_refl.
  - rewrite /=. by apply Htimes; rewrite eq_refl. 
  - move => p' Hinp'. rewrite /packet_in_data /=. apply /inP. 
    apply In_upd_Znth_old => //; simpl in *; try lia. by apply /inP.
    rewrite Znth_Zindex //. apply Zindex_In. simpl in *; lia.
  - move => p'/=; rewrite in_cons =>/orP[/eqP Hp' |//]; subst.
    rewrite packet_in_block_eq/=. apply /orP; left. apply /inP.
    apply upd_Znth_In. apply Hzidxb.
  - move => p'. rewrite packet_in_block_eq add_red_parity => 
      /orP[/= /inP Hdat | Hpar]; last first. 
      move: Hprog. rewrite /block_in_progress => /allP Hall. 
      by move: Hall => /( _ _ Hpar).
    apply In_upd_Znth in Hdat.
    case: Hdat => [[Hp'] | Hin]; subst. rewrite in_cons eq_refl. by right.
    by left; apply /inP.
  - move => p1 p2 Hinp1/=; rewrite in_cons => /orP[/eqP Hp2 /= |//]. subst.
    rewrite /=.
    apply blockIndex_Znth_data in Hinp1 => //.
    apply /eqP => Hidxeq. move: Hinp1.
    rewrite Hidxeq Nat2Z.id; simpl in *; try rep_lia. rewrite Znth_Zindex //.
    apply Zindex_In; simpl in *; lia.
Qed.

(*TODO: move*)
Lemma map_nil {A B: eqType} (f: A -> B) (s: seq A):
  (map f s == [::]) = (s == [::]).
Proof.
  by case: s.
Qed.

(*Case 2: We can encode the current block and add all such packets to the output, preserving the invariant*)
Lemma encoder_props_encode: forall orig b blks pkts model,
  (Some model) \in (map (omap (@p_packet _)) (data_packets b)) ->
  encoder_props orig blks (Some b) pkts ->
  encoder_props orig ((encode_block b (Some model)).1 :: blks) None
    (pkts ++ ((encode_block b (Some model)).2)).
Proof.
  move => orig b blks pkts model Hinmodel.
  rewrite {1}/encoder_props/block_option_list/=.
  setoid_rewrite in_cons =>
  [[IHperm [IHallwf [IHblackcomp [IHtimes [IHdata [IHinorig [IHids [IHencoded [IHprog [IHwfpkts [IHuniq IHuniqdat]]]]]]]]]]]].
  (*First, prove wf*)
  have Hvalmod: (packet_valid model). {
    have Hwfb: block_wf b by apply IHallwf; rewrite eq_refl. 
    case: Hwfb => [_ [_ [_ [_ [_ [_ [_ [_ [Hvalid _]]]]]]]]].
    move: Hinmodel => /mapP [[/=fp Hmodel [Hin] | Hc]] //; subst.
    apply Hvalid. by apply data_in_block.
  }
  (*These are useful to have in context*)
  have Hprog': block_in_progress b by apply IHprog.
  have Hwfb: block_wf b by apply IHallwf; rewrite eq_refl.
  have Hwf: wf_packet_stream (pkts ++ (encode_block b (Some model)).2). {
    rewrite /wf_packet_stream.
    have Hinpkts: forall (p' : fpacket), p' \in pkts -> (fd_blockId p' != blk_id b) \/ 
    ( packet_in_data p' b /\ fd_blockId p' = blk_id b /\ fd_k p' = blk_k b /\
      fd_h p' = blk_h b /\ (Z.of_nat (fd_blockIndex p') < blk_k b)). {
      move => p' Hp'. case: (fd_blockId p' == blk_id b) /eqP => [Hbp | Hbp //]; last by left. 
      right. have Hin: packet_in_data p' b by apply (in_old_block IHwfpkts IHperm).
      split. by []. split. apply Hwfb. by apply data_in_block. 
      rewrite -and_assoc. split.
      apply Hwfb. by apply data_in_block. by apply in_data_idx_bound.
  }
  have Hwfenc: block_wf (encode_block b (Some model)).1 by apply encode_block_some_wf. 
  have Hinenc: forall (p': fpacket), p' \in (encode_block b (Some model)).2 -> 
      fd_blockId p' =  blk_id b /\ fd_k p' = blk_k b /\ fd_h p' = blk_h b /\
      blk_k b <= Z.of_nat (fd_blockIndex p'). {
      move => p' Hinp'. apply encode_in in Hinp'.
      case Hwfenc => [Hkbound [Hhbound [Hkh [Hid [Hidx [Hk [Hh [Henc' Hvalid]]]]]]]].
      split; [|rewrite -and_assoc; split].
      - rewrite Hid. by rewrite encode_block_id. 
        by rewrite packet_in_block_eq Hinp' orbT.
      - rewrite encode_block_k in Hkh. rewrite encode_block_h in Hkh.
        apply Hkh. by rewrite packet_in_block_eq Hinp' orbT.
      - rewrite -(encode_block_k b (Some model)). 
        by apply in_parity_idx_bound.
  }
  (*Ok, now we can prove wf*)
  split_all.
  - move => p1 p2. rewrite !mem_cat => /orP[Hinp1 | Hinp1] /orP[Hinp2 | Hinp2].
    + by apply IHwfpkts.
    + apply Hinpkts in Hinp1. apply Hinenc in Hinp2. case Hinp1 => [Hidp1 | [Hinbp1 [Hidp1 [Hkp1 [Hhp1 _]]]]];
      case Hinp2 => [Hidp2 [Hkp2 [Hhp2 _]]].
      * move => Heq. move: Hidp1. by rewrite Heq Hidp2 eq_refl.
      * lia.
    + (*exact reverse*)
      apply Hinpkts in Hinp2. apply Hinenc in Hinp1. case Hinp2 => [Hidp2 | [Hinbp2 [Hidp2 [Hkp2 [Hhp2 _]]]]];
      case Hinp1 => [Hidp1 [Hkp1 [Hhp1 _]]].
      * move => Heq. move: Hidp2. by rewrite -Heq Hidp1 eq_refl.
      * lia.
    + apply Hinenc in Hinp1. apply Hinenc in Hinp2. lia.
  - move => p1 p2. rewrite !mem_cat => /orP[Hinp1 | Hinp1] /orP[Hinp2 | Hinp2].
    + by apply IHwfpkts.
    + apply Hinpkts in Hinp1. have Hinp2':=Hinp2.
      apply Hinenc in Hinp2'. case Hinp1 => [Hidp1 | [Hin[Hidp1 [Hkp1 [Hhp1 _]]]]];
      case Hinp2' => [Hidp2 [Hkp2 [Hhp2 _]]].
      * move => Heq. move: Hidp1. by rewrite Heq Hidp2 eq_refl.
      * move => Hideq Hidxeq. apply (in_wf_blockIndex_inj Hwfenc) => //;
        rewrite packet_in_block_eq; apply /orP.
        rewrite data_packets_encode. by left. right; by apply encode_in.
    + (*basically same*)
      apply Hinpkts in Hinp2. have Hinp1':=Hinp1.
      apply Hinenc in Hinp1'. case Hinp2 => [Hidp2 | [Hin[Hidp2 [Hkp2 [Hhp2 _]]]]];
      case Hinp1' => [Hidp1 [Hkp1 [Hhp1 _]]].
      * move => Heq. move: Hidp2. by rewrite -Heq Hidp1 eq_refl.
      * move => Hideq Hidxeq. apply (in_wf_blockIndex_inj Hwfenc) => //;
        rewrite packet_in_block_eq; apply /orP.
        right; by apply encode_in.
        rewrite data_packets_encode. by left.
    + move => _ Hidxeq.
      apply (in_wf_blockIndex_inj Hwfenc) => //;
      rewrite packet_in_block_eq //; apply /orP;
      by right; apply encode_in.
  - move => p'. rewrite !mem_cat => /orP[Hinp' | Hinp'].
    + by apply IHwfpkts.
    + apply (in_block_idx_bound Hwfenc). 
      rewrite packet_in_block_eq; apply /orP; right.
      by apply encode_in.
  - move => p'. rewrite !mem_cat => /orP[Hinp' | Hinp'].
    + by apply IHwfpkts.
    + move: Hwfenc. rewrite /block_wf; rewrite encode_block_k encode_block_h => [[Hkbound [Hhbound [Hkh _]]]].
      have Hkh':fd_k p' = blk_k b /\ fd_h p' = blk_h b. apply Hkh.
      rewrite packet_in_block_eq; apply /orP; right. 
      by apply encode_in. lia.
  }
  (*Now we prove the full props*)
  rewrite /encoder_props/block_option_list/=; split_all => //;
  try (move => b'; rewrite in_cons => /orP[/eqP Hb' | Hinb']); subst.
  - (*separate lemma makes things nice*)
    by apply get_blocks_encode => //; setoid_rewrite eq_sym. 
  - by apply encode_block_some_wf.
  - by apply IHallwf; rewrite Hinb' orbT. 
  - rewrite encode_block_black_comp. by apply IHblackcomp; rewrite eq_refl.
  - by apply IHblackcomp; rewrite Hinb' orbT.
  - rewrite encode_block_time. by apply IHtimes; rewrite eq_refl.
  - by apply IHtimes; rewrite Hinb' orbT.
  - apply encode_block_nonempty. by apply IHdata; rewrite eq_refl.
  - by apply IHdata; rewrite Hinb' orbT.
  - move => b' p'; rewrite in_cons => /orP[/eqP Hb' | Hinb'] Hinp'; last first.
    apply (IHinorig b') => //. by rewrite Hinb' orbT.
    subst. move: Hinp'; rewrite /packet_in_data data_packets_encode => Hin.
    apply (IHinorig b) =>//. by rewrite eq_refl.
  - rewrite /packet_in_data data_packets_encode encode_block_id.
    apply IHids. by rewrite eq_refl.
  - by apply IHids; rewrite Hinb' orbT.
  - apply encode_block_encoded =>//. case: Hwfb; lia.
    by apply IHdata; rewrite eq_refl.
  - by apply IHencoded.
  - rewrite cat_uniq IHuniq/= encode_block_uniq; last first.
      move: IHallwf => /(_ b). rewrite eq_refl/= => /(_ isT).
      rewrite /block_wf; lia.
    rewrite andbT.
    (*Idea: no overlap because all packets with this blockIndex
      in pkts must have been data packets (by [block_in_progress])*)
    apply /negP => /hasP/= [p] Hpinenc Hinp.
    have Hidp: fd_blockId p = blk_id b by
      apply (in_encode_block_id Hpinenc).
    have Hindat: packet_in_data p b by apply (in_old_block IHwfpkts IHperm).
    have Hppar: fd_isParity p = false by apply Hwfb.
    apply in_encode_block_parity in Hpinenc. 
    by rewrite Hpinenc in Hppar.
  - rewrite filter_cat map_cat.
    have->:[seq p_packet i | 
      i <- (encode_block b (Some model)).2 & ~~ fd_isParity (p_fec_data' i)] = nil;
    last by rewrite cats0.
    apply /eqP. rewrite map_nil -(negbK (_ == nil)) -has_filter 
      -all_predC/=. 
    apply /allP => p Hinp/=. rewrite negbK.
    by apply (in_encode_block_parity Hinp).
Qed.
 
(*Case 3: Add packet to existing block (that is not yet finished)*)
Lemma encoder_props_add: forall p orig b blks pkts,
  packet_valid p ->
  encodable p ->
  Zindex None (data_packets b) < blk_k b ->
  p_seqNum p \notin (map p_seqNum orig) ->
  encoder_props orig blks (Some b) pkts ->
  encoder_props (p :: orig) blks (Some (add_packet_to_block_red p b)) (pkts ++ [:: get_fec_packet p b]).
Proof.
  move => p orig b blks pkts Hval Henc  Hzidx Hseqnotin.
  rewrite {1}/encoder_props/block_option_list/=.
  setoid_rewrite in_cons =>
  [[IHperm [IHallwf [IHblackcomp [IHtimes [IHdata [IHinorig [IHids [IHencoded [IHprog [IHwfpkts [IHuniq IHuniqdat]]]]]]]]]]]].
  (*Some helpful results*)
  have Hprog: block_in_progress b by apply IHprog.
  have Hwfb: block_wf b by apply IHallwf; rewrite eq_refl.
  have Hinpkts: forall (x: fpacket), x \in pkts -> fd_blockId x = blk_id b ->
    packet_in_data x b by apply (in_old_block IHwfpkts IHperm).
  (*1 similar result*)
  have Hinpktsidx:  forall (x: fpacket), x \in pkts -> fd_blockId x = blk_id b ->
    Z.of_nat (fd_blockIndex x) <> Zindex None (data_packets b). {
    move => x Hinx Hidx. apply (Hinpkts _ Hinx) in Hidx.
    have: Znth (Z.of_nat (fd_blockIndex x)) (data_packets b ++ parity_packets b) = Some x. {
      apply Hwfb => //. by apply data_in_block. }
    rewrite Znth_app1; last first.
      have->: Zlength (data_packets b) = blk_k b by apply Hwfb.
      by apply in_data_idx_bound.
    move => Hznth Hc. rewrite Hc in Hznth. rewrite Znth_Zindex in Hznth => //.
    apply Zindex_In. by have->: Zlength (data_packets b) = blk_k b by apply Hwfb.
  }
  case Hwfb => [Hkbound [Hhbound [_ [_ [_ [Hdatlen [Hparlen _]]]]]]].
  have Hidxb: 0 <= (Zindex None (data_packets b)) <= blk_k b. { split.
      apply Zindex_nonneg. rewrite -Hdatlen. apply Zindex_leq_Zlength. }
  have Hinget: forall (x: fpacket), x \in [:: get_fec_packet p b] ->
    fd_blockId x = blk_id b /\ fd_k x = blk_k b /\ fd_h x = blk_h b /\
    Z.of_nat (fd_blockIndex x) = Zindex None (data_packets b). {
    move => x. rewrite /= in_cons => /orP[/eqP Hx |//]. subst =>//=. split_all => //.
    by rewrite Nat2Z.id.
  }
  (*First, prove wf*)
  have Hwf: wf_packet_stream (pkts ++ [:: get_fec_packet p b]). {
    rewrite /wf_packet_stream; split_all.
  - move => p1 p2. rewrite !mem_cat => /orP[Hp1 | Hp1] /orP[Hp2 | Hp2].
    + by apply IHwfpkts.
    + apply Hinget in Hp2. case : Hp2 => [Hp2id [Hp2k [Hp2h Hp2idx]]].
      move => Heqid. apply Hinpkts in Hp1 => //=. 2: congruence.
      rewrite Hp2k Hp2h. apply Hwfb. by apply data_in_block.
    + apply Hinget in Hp1. case : Hp1 => [Hp1id [Hp1k [Hp1h Hp1idx]]].
      move => Heqid. apply Hinpkts in Hp2 => //=. 2: congruence.
      rewrite Hp1k Hp1h. by split; symmetry; apply Hwfb, data_in_block.
    + move: Hp1 Hp2. rewrite in_cons => /orP[/eqP Hp1 |//] /orP[/eqP Hp2|//].
      by subst.
  - move => p1 p2. rewrite !mem_cat => /orP[Hp1 | Hp1] /orP[Hp2 | Hp2].
    + by apply IHwfpkts.
    + apply Hinget in Hp2. case : Hp2 => [Hp2id [Hp2k [Hp2h Hp2idx]]].
      move => Heqid Heqidx. apply Hinpktsidx in Hp1 => //=; congruence.
    + apply Hinget in Hp1. case : Hp1 => [Hp1id [Hp1k [Hp1h Hp1idx]]].
      move => Heqid Heqidx. apply Hinpktsidx in Hp2 => //=; congruence.
    + move: Hp1 Hp2. rewrite in_cons => /orP[/eqP Hp1 |//] /orP[/eqP Hp2|//]. by subst.
  - move => p'. rewrite mem_cat => /orP[ Hp' | Hp'].
    + by apply IHwfpkts.
    + apply Hinget in Hp'. case : Hp' => [Hpid [Hpk [Hph Hpidx]]].
      rewrite Hpk Hph Hpidx. lia.
  - move => p'. rewrite mem_cat => /orP[ Hp' | Hp'].
    + by apply IHwfpkts.
    + apply Hinget in Hp'. case : Hp' => [Hpid [Hpk [Hph Hpidx]]]. lia.
  }
  (*For uniq goals*)
  have Hpnotin: forall (x: fpacket), fd_isParity x = false -> 
    p_packet x = p -> x \notin pkts. {
    move=> x Hpar Hp. apply /negP => Hin.
    (*this packet is in a block*)
    have [b' /andP[Hinb' Hinpb]]:=(get_blocks_allin IHwfpkts Hin).
    have Hinb'': (b' == b) || (b' \in blks) by
    move: Hinb'; rewrite (perm_mem IHperm) in_cons.
    have Hindat: packet_in_data x b' by
      apply wf_in_data=>//; apply IHallwf.
    move: IHinorig => /(_ _ _ Hinb'' Hindat)/= => Hinorig.
    move: Hseqnotin => /negP => C; apply C.
    apply /mapP.  exists (p_packet x)=>//. by rewrite Hp. 
  }
  (*Now we can prove the rest*)
  rewrite /encoder_props/block_option_list/=. split_all;
  try (move => b'; rewrite in_cons => /orP[/eqP Hb' | Hinb']); subst.
  - by apply get_block_add =>//; setoid_rewrite eq_sym.
  - by apply add_red_wf.
  - by apply IHallwf; rewrite Hinb' orbT.
  - rewrite add_black_comp. by apply IHblackcomp; rewrite eq_refl.
  - by apply IHblackcomp; rewrite Hinb' orbT.
  - rewrite /=. by apply IHtimes; rewrite eq_refl.
  - by apply IHtimes; rewrite Hinb' orbT.
  - apply add_red_nonempty. by apply IHdata; rewrite eq_refl.
  - by apply IHdata; rewrite Hinb' orbT.
  - move => b' p'; rewrite in_cons => /orP[/eqP Hb' | Hinb'] Hinp'; 
    subst; last first; rewrite in_cons; apply /orP. 
    right. apply (IHinorig b') => //. by rewrite Hinb' orbT.
    move: Hinp'; rewrite /packet_in_data/= => /inP Hinp'.
    apply In_upd_Znth in Hinp'.
    case: Hinp' => [[Hp'] | Hinp'].
    + subst. by left.
    + right. apply (IHinorig b) => //. by rewrite eq_refl. by apply /inP.
  - rewrite add_red_id.
    have [p' [Hinp' Hidp']]: exists p : fpacket, packet_in_data p b /\ blk_id b = p_seqNum p
      by apply IHids; rewrite eq_refl.
    exists p'. split => //. rewrite /packet_in_data /=. apply /inP. 
    apply In_upd_Znth_old => //. by apply /inP.
    rewrite Znth_Zindex //. apply Zindex_In. all: simpl in *; lia.
  - by apply IHids; rewrite Hinb' orbT.
  - apply IHencoded. 
  - move => b' [Hb']; subst. rewrite /block_in_progress add_red_parity.
    apply Hprog.
  - by apply Hwf.
  - (*Almost the same as the first case*)
    rewrite cat_uniq/= orbF andbT IHuniq/=.
    by apply Hpnotin.
  - rewrite filter_cat/= map_cat/= cat_uniq/= orbF andbT IHuniqdat/=.
    apply /mapP => [[f]]. rewrite mem_filter => /andP[Hnotpar Hinf] Hp.
    have: f \notin pkts by apply Hpnotin=>//; rewrite (negbTE Hnotpar).
    by rewrite Hinf.
Qed.

(*TODO: put in block or somewhere once done with file*)
Lemma zip_nil_r: forall {A B: Type} (s: seq A),
  zip s (@nil B) = [::].
Proof.
  move => A B s. by case: s.
Qed. 

(*The key theorem about the encoder: encoder_props holds. We need all of these properties for a strong enough
  IH, even though only a few are important in the final theorem we need (TODO: reference*)
(*We have 1 other statement (about Zindex). We don't have this in [encoder_props] because it doesn't hold at
  all the intermediate steps*)
Theorem encoder_all_steps_blocks: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, (k, h) \in params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  encoder_props orig (encoder_all_steps orig params).1.1 (encoder_all_steps orig params).1.2 (encoder_all_steps orig params).2 /\
  (forall b, (encoder_all_steps orig params).1.2 = Some b -> Zindex None (data_packets b) < blk_k b).
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz.
  (*First, switch to foldr*)
  rewrite /encoder_all_steps -(revK (combine _ _)) foldl_rev -zip_combine rev_zip // {Hsz}.
  have Hparam': forall k h, (k, h) \in (rev params) -> 0 < k <= fec_n - 1 - fec_max_h /\ 0 < h <= fec_max_h. {
    move => k h Hin. apply Hparam. by rewrite -mem_rev. }
  move: Hparam Hparam' => _ Hparam. forget (rev params) as p. rewrite {params}.
  have: forall p, p \in rev (orig) -> packet_valid p by apply in_pred_rev.
  have: forall p, p \in rev orig -> encodable p by apply in_pred_rev.
  have: uniq (map p_seqNum (rev orig)) by rewrite map_rev rev_uniq. 
  move: Hvalid Henc Huniq => _ _ _ Huniq Henc Hvalid. rewrite encoder_props_orig_rev_iff.
  forget (rev orig) as o. rewrite {orig}. move: p Hparam Huniq Henc Hvalid.
  elim : o => [//= p Hp Henc Hvalid | h t /= IH p Hp /andP[Hht Huniq] Henc Hvalid].
  - by rewrite zip_nil.
  - move: Hp. case : p => [|ph pt] Hp.
    + by rewrite zip_nil_r.
    + rewrite /=. have Hpt: forall k h : Z, (k, h) \in pt -> 0 < k <= fec_n - 1 - fec_max_h /\ 0 < h <= fec_max_h. {
        move => k' h' Hin. apply Hp. by rewrite in_cons Hin orbT. }
      move: IH => /(_ _ Hpt Huniq (in_pred_tl Henc) (in_pred_tl Hvalid)). rewrite {Hpt}.
      set ind := (foldr
         (fun (x : packet * (Z * Z)) (z : seq block * option block * seq fpacket) =>
          ((encoder_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).1.1,
          (encoder_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).1.2,
          z.2 ++ (encoder_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).2)) ([::], None, [::]) 
         (zip t pt)). (*once again, don't care what ind is, just that we can use IH*)
      rewrite /encoder_one_step/encode_new/encode_exist.
      case : ind => [[blks currBlock] pkts]/=.
      have [Hph1 Hph2]: 0 < ph.1 <= fec_n - 1 - fec_max_h /\ 0 < ph.2 <= fec_max_h. {
        apply Hp. rewrite {Hp}. by case: ph => [a b]/=; rewrite in_cons eq_refl. }
      have Hhval: packet_valid h. { apply Hvalid. by rewrite in_cons eq_refl. }
      have Hhenc: encodable h. { apply Henc. by rewrite in_cons eq_refl. }
      case currBlock => [/= b | /=]; last first.
      * move => [IH Hzindex]. case: (Z.eq_dec ph.1 1) => HHl1/=; last first.
          split. by apply encoder_props_new_block. move => b [Hb]. subst.
          rewrite create_red_Zindex/=; lia.
        apply (@encoder_props_new_block h t _ _ ph.1 ph.2) in IH => //.
        set b := (create_block_with_packet_red h ph.1 ph.2).
        have->:(pkts ++ new_fec_packet h ph.1 ph.2 :: (encode_block b (Some h)).2) =
          (pkts ++ [:: new_fec_packet h ph.1 ph.2]) ++ (encode_block b (Some h)).2 by rewrite -catA.
        split => //. apply encoder_props_encode => //. subst b. 
        apply create_block_in. lia.
      * move => [IH Hzindex].
        case Hchange : (~~ Z.eq_dec (blk_k b) ph.1 || ~~ Z.eq_dec (blk_h b) ph.2) => /=.
        -- have Hdat: data_elt b. apply IH => /=. rewrite /block_option_list/=.
           by rewrite in_cons eq_refl.
           apply encode_block_none_some in Hdat. case : Hdat => [model [Hinmod Hencns]].
           rewrite Hencns. apply (encoder_props_encode Hinmod) in IH.
           (*similar cases as before now*)
           case: (Z.eq_dec ph.1 1) => HHl1/=; last first.
              rewrite catA.  split. by apply encoder_props_new_block. move => b' [Hb']. subst.
              rewrite create_red_Zindex/=; lia.
           apply (@encoder_props_new_block h t _ _ ph.1 ph.2) in IH => //. move: IH.
           set b' := (create_block_with_packet_red h ph.1 ph.2) => IH.
           rewrite (cons_app (new_fec_packet _ _ _)) (catA _ _ (encode_block b' (Some h)).2).
           apply (@encoder_props_encode _ _ _ _ h) in IH.
           rewrite -!catA in IH. rewrite -!catA. split => //.
           subst b'. apply create_block_in. lia.
        -- (*last case - add packet to existing block*)
          have Hidx: Zindex None (data_packets b) < blk_k b by apply Hzindex.
          have->:(Zlength
             [seq x <- upd_Znth (Zindex None (data_packets b)) (data_packets b)
                         (Some (get_fec_packet h b))
                | isSome x]) = Zlength [seq x <- (data_packets b) | isSome x] + 1.
          { rewrite upd_Znth_Zindex_Zlength //. apply Z.add_comm.
            have Hwf: block_wf b. apply IH. rewrite /block_option_list/=.
            by rewrite in_cons eq_refl.
            have->: Zlength (data_packets b) = blk_k b by apply Hwf. by apply Hzindex.
          }
          case: (Z.eq_dec (Zlength [seq x <- data_packets b | isSome x] + 1) (blk_k b)) => /= Hfinish; last first.
          ++ split. apply encoder_props_add => //.
            move => b' [Hb']; subst.
            have Hdatlen: Zlength(data_packets (add_packet_to_block_red h b)) = blk_k (add_packet_to_block_red h b). {
              have Hwfb: block_wf (add_packet_to_block_red h b). apply add_red_wf => //. apply IH.
              by rewrite /block_option_list/=in_cons eq_refl.
              apply Hwfb. } rewrite -Hdatlen.
            have Hleqlt: forall (z1 z2 : Z), z1 <= z2 -> z1 <> z2 -> z1 < z2. lia.
            apply Hleqlt. apply Zindex_leq_Zlength. move => Hlen.
            have: Zlength [seq x <- data_packets (add_packet_to_block_red h b) | isSome x] =
              blk_k b. { rewrite -Hdatlen. apply filter_all_Zlength. apply /allP.
              apply Zindex_notin in Hlen. move => x. case: x => [//|]. by rewrite in_mem_In.
            }
            rewrite -add_red_size //. have->//: Zlength(data_packets b) = blk_k b.
            have Hwfb: block_wf b. apply IH.
            by rewrite /block_option_list/=in_cons eq_refl. apply Hwfb.
          ++ split => //.
            have Hwfb: block_wf b. apply IH.
            by rewrite /block_option_list/=in_cons eq_refl.
            (*Once again, we apply 2 cases*)
            apply (encoder_props_add Hhval) in IH => //.
            apply (encoder_props_encode) with(model:=h) in IH. by rewrite -catA in IH.
            apply add_block_in.  have->//: Zlength(data_packets b) = blk_k b.
            apply Hwfb.
Qed.

(*Corollaries: the specific properties we need*)

(*1. The resulting packet stream is well formed*)
Corollary rse_encode_stream_wf: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, (k, h) \in params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  wf_packet_stream (encoder_all_steps orig params).2.
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz.
  by apply encoder_all_steps_blocks.
Qed.

(*2. Every data packet in the output came from the input*)
Corollary rse_encode_stream_from_orig: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, (k, h) \in params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  (forall (p: fpacket), p \in (encoder_all_steps orig params).2 -> 
    fd_isParity p = false -> 
    p_packet p \in orig).
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz p Hp Hpar.
  (*It's not quite as trivial as the last one*)
  have [Hprops _]:=(encoder_all_steps_blocks Hparam Hvalid Henc Huniq Hsz).
  case Hprops => [Hperm [Hallwf [_ [encoder_all_steps_ [_ [Hinorig [_ [_ [_ [Hwf _]]]]]]]]]].
  have [b /andP[Hb Hpb]]:= get_blocks_allin Hwf Hp.
  apply (Hinorig b).
  - by rewrite -(perm_mem Hperm).
  - have Hwfb: block_wf b. apply Hallwf. by rewrite -(perm_mem Hperm).
    move: Hpb. rewrite packet_in_block_eq => /orP[Hdat // | Hinpar].
    have: fd_isParity p. by apply Hwfb. by rewrite Hpar.
Qed.

(*3. Every block in [get_blocks] of the output is well-formed*)
Corollary rse_encode_stream_blocks_wf: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, (k, h) \in params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  (forall b, b \in (get_blocks (encoder_all_steps orig params).2) -> block_wf b).
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz b Hb.
  have [Hprops _]:=(encoder_all_steps_blocks Hparam Hvalid Henc Huniq Hsz).
  apply Hprops. case Hprops => [Hperm _].
  by rewrite -(perm_mem Hperm).
Qed.

(*4. Every recoverable block in [get_blocks] of the output is encoded. This one does not appear
  directly in [encoded_props] but can be derived without too much trouble*)
Corollary rse_encode_stream_recoverable_encoded: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, (k, h) \in params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  (forall b, b \in (get_blocks (encoder_all_steps orig params).2) -> recoverable b -> block_encoded b).
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz b Hb.
  have [Hprops Hinprog]:=(encoder_all_steps_blocks Hparam Hvalid Henc Huniq Hsz).
  move => Hrec. apply Hprops. move: Hb. case Hprops => [Hperm _].
  rewrite (perm_mem Hperm)/block_option_list/=.
  case Hb: (encoder_all_steps orig params).1.2 => [b' |//].
  rewrite in_cons => /orP[/eqP Hb' | //]. subst. 
  have Hprog: block_in_progress b' by apply Hprops. have Hzidx:=Hb. 
  apply Hinprog in Hzidx.
  move: Hrec. rewrite /recoverable.
  have->: Zlength [seq x <- parity_packets b' | isSome x] = 0. {
    have->//:[seq x <- parity_packets b' | isSome x] = nil. by apply pars_in_progress. }
  rewrite Z.add_0_r. move => Hsum. solve_sumbool.
  have Hgt:=(@Zlength_filter _ isSome (data_packets b')).
  have: Zlength [seq x <- data_packets b' | isSome x] = Zlength (data_packets b'). {
  (*again, why won't lia work?*)
  have Halleq: forall z1 z2, z1 <= z2 -> z1 >= z2 -> z1 = z2 by lia.
  by apply Halleq. }
  rewrite {g Hgt} filter_all_Zlength => /allP Hall.
  have Hwfb': block_wf b'. apply Hprops. rewrite /block_option_list/= Hb.
  by rewrite in_cons eq_refl.
  have Hlen: Zlength (data_packets b') = blk_k b' by apply Hwfb'. move: Hzidx.
  rewrite -Hlen Zindex_In -in_mem_In => Hnone. by move: Hall => /(_ _ Hnone).
Qed.

(*5. The output stream has no duplicates (very easy to prove)*)
Corollary rse_encode_stream_uniq: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, (k, h) \in params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  uniq (encoder_all_steps orig params).2.
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz.
  by apply encoder_all_steps_blocks.
Qed.

End EncoderBlocks.

(*One more theorem: the data packets the encoder outputs are exactly
  the packets in the original list.*)

Lemma encode_new_filter: forall p k h,
  map f_packet (filter (fun (p: fpacket) => ~~ (fd_isParity p))
    (encode_new p k h).2) = [:: p].
Proof.
  move=> p k h. rewrite /encode_new.
  case : (Z.eq_dec k 1) => //= _.
  by rewrite encode_block_filter/=.
Qed.

Lemma encode_exist_filter: forall p b,
  map f_packet (filter (fun (p: fpacket) => ~~ (fd_isParity p))
    (encode_exist p b).2) = [:: p].
Proof.
  move=> p b. rewrite /encode_exist.
  case: (Z.eq_dec
  (Zlength
      [seq x <- data_packets (add_packet_to_block_red p b)
        | isSome x]) (blk_k (add_packet_to_block_red p b))) =>//= _.
  by rewrite encode_block_filter.
Qed.

(*Want to prove one more thing (if it's easy)*)

Theorem encoder_all_steps_sent_data: forall (orig: list packet) 
  (params: list (Z * Z)),
  size orig = size params ->
  map f_packet 
    ((filter (fun b => negb (fd_isParity (p_fec_data' b)))) 
      (encoder_all_steps orig params).2) =
  orig.
Proof.
  move=> orig params Hsz.
  (*switch to foldr*)
  rewrite /encoder_all_steps -(revK (combine _ _)) foldl_rev -zip_combine
    rev_zip //.
  move: Hsz. rewrite -(size_rev params) -(size_rev orig).
  rewrite -{3}(revK orig). forget (rev params) as p.
  forget (rev orig) as o.
  rewrite {params orig}.
  move: p. elim: o => [// p | phd ptl /= IH p].
  - by rewrite /rev/=zip_nil/=.
  - case: p => [//| parh part /=Hsz].
    rewrite rev_cons -(cats0 (rcons _ _)) (cat_rcons _ _ nil).
    move: IH => /(_ part (eq_add_S _ _ Hsz)).
    rewrite !filter_cat !map_cat=>->. f_equal.
    case: (foldr
      (fun (x : packet * (Z * Z))
        (z : seq block * option block * seq fpacket) =>
      ((encoder_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).1.1,
      (encoder_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).1.2,
      z.2 ++ (encoder_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).2))
      ([::], None, [::]) (zip ptl part)) => [[blks inprog] send].
    rewrite /encoder_one_step/=.
    case: inprog => [//= blk | //=]; last by
      rewrite encode_new_filter.
    case: (~~ proj_sumbool (Z.eq_dec (blk_k blk) parh.1)
    || ~~ proj_sumbool (Z.eq_dec (blk_h blk) parh.2)); last by
      rewrite encode_exist_filter.
    by rewrite /= filter_cat map_cat encode_block_filter encode_new_filter.
Qed.

(*Concat version of encoder*)
(*TODO: see if we still need this - for now, just use to prove
  simple encoder equivalent*)
Section Concat.


Definition encoder_concat (orig: seq packet) (params: seq (Z * Z)) :=
  foldl
  (fun (acc : seq block * option block * seq (seq (fpacket))) (x : packet * (Z * Z)) =>
   let t := encoder_one_step acc.1.1 acc.1.2 x.1 x.2.1 x.2.2 in 
    (t.1.1, t.1.2, acc.2 ++ [ :: t.2]))
  ([::], None, [::]) (combine orig params).

Opaque encoder_one_step.

Lemma encoder_all_steps_concat_aux: forall orig params,
  (encoder_all_steps orig params).1 = (encoder_concat orig params).1 /\ 
  (encoder_all_steps orig params).2 = concat (encoder_concat orig params).2.
Proof.
  move => orig params. rewrite /encoder_all_steps/encoder_concat/= -(revK (combine _ _)) !foldl_rev. 
  remember (rev (combine orig params)) as l. rewrite {orig params Heql}. elim : l => [// | h t /= [IH1 IH2]]. 
  by rewrite !IH1 !IH2//= !concat_app/= !cat_app app_nil_r.
Qed.

Lemma encoder_all_steps_concat: forall orig params,
  (encoder_all_steps orig params).2 = concat (encoder_concat orig params).2.
Proof.
  move => orig params. by apply encoder_all_steps_concat_aux.
Qed.

(*This lemma will actually be quite easy with previous result*)
(*From here, we can describe each element of [encoder_concat] purely in terms of [rse_encode_func])*)
Lemma rse_concat_mkseqZ: forall orig params,
  Zlength orig = Zlength params ->
  (encoder_concat orig params).2 = mkseqZ (fun i => rse_encode_func (sublist 0 i orig) (sublist 0 i params)
    (Znth i orig) (Znth i params).1 (Znth i params).2) (Zlength orig).
Proof.
  move => orig params Hlens. rewrite /encoder_concat /rse_encode_func /encoder_all_steps.
  remember (@nil block) as b1. remember (@None block) as b2. remember (@nil fpacket) as b3.
  remember (@nil (seq fpacket)) as b4. rewrite {1}Heqb4. rewrite -(cat0s (mkseqZ _ _)). rewrite -{2}Heqb4.
  rewrite {Heqb1 Heqb2 Heqb3 Heqb4}. move: b1 b2 b3 b4 params Hlens.
  elim : orig => [//= b1 b2 b3 b4 params Hlen | h t /= IH b1 b2 b3 b4 params].
  - have->/=:Zlength [::] = 0 by list_solve. rewrite mkseqZ_0. by rewrite cats0.
  - case: params => [| [k' h'] tl/=]; [list_solve |].
    move => Hlen. erewrite IH. 2: list_solve.
    have->: Zlength (h::t) = Zlength t + 1 by list_solve.
    rewrite mkseqZ_1_plus/=; [|list_solve]. rewrite !Znth_0_cons -catA/=. f_equal. f_equal.
    have Hpos: 0 <= Zlength t by list_solve. apply Znth_eq_ext; rewrite !mkseqZ_Zlength //. 
    move => i Hi. rewrite !mkseqZ_Znth// !Znth_pos_cons; try lia. rewrite !sublist_0_cons; try lia.
    by rewrite !Z.add_simpl_r.
Qed.

Corollary rse_concat_nth: forall orig params i,
  Zlength orig = Zlength params ->
  0 <= i < Zlength orig ->
  Znth i (encoder_concat orig params).2 = 
  rse_encode_func (sublist 0 i orig) (sublist 0 i params) (Znth i orig) (Znth i params).1 (Znth i params).2.
Proof.
  move => orig params i Hi Hlens. by rewrite rse_concat_mkseqZ //; zlist_simpl.
Qed.

Corollary rse_concat_Zlength: forall orig params,
  Zlength orig = Zlength params ->
  Zlength (encoder_concat orig params).2 = Zlength orig.
Proof.
  move => orig params Hlen. by rewrite rse_concat_mkseqZ //; zlist_simpl.
Qed.

End Concat.

(*TODO: separate file?*)

(* Reasoning about block boundaries*)

(*Now we want to say something more so that we can express that
  not too many packets are lost without exposing information about blocks.
  To do this, we first assume that all parameters are equal; we give
  such an encoder and prove it equivalent*)
Section Boundaries.

(*Encoder with only 1 param*)
Section Simple.

Variable k : Z.
Variable h : Z.

Definition encoder_one_step_nochange (blocks: seq block) (currBlock: option block) (curr: packet) :=
  match currBlock with
  | Some b => 
      let t := encode_exist curr b in (t.1.1 ++ blocks, t.1.2, t.2)
  | None => 
      let t := encode_new curr k h in (t.1.1 ++ blocks, t.1.2, t.2)
  end.

Definition encoder_concat_nochange (orig: seq packet) : 
  list block * option block * list (list fpacket) :=
  foldl (fun acc x =>
    let t := encoder_one_step_nochange acc.1.1 acc.1.2 x in
    (t.1.1, t.1.2, acc.2 ++ [:: t.2])) (nil, None, nil) orig.

(*can easily get encoder_all_steps_nochange from this if we need it*)

(*Equality with full encoder*)
(*Coq has trouble if we don't include the return Prop*)
Lemma encoder_one_step_nochange_eq: forall blks (curr: option block) p,
  match curr with
  | Some b => blk_k b = k /\ blk_h b = h
  | None => True
  end ->
  (encoder_one_step_nochange blks curr p) = (encoder_one_step blks curr p k h).
Proof.
  move=> blks curr p.
  rewrite /encoder_one_step_nochange/encoder_one_step.
  case: curr => [curr /= [Hk Hh] | //=].
  rewrite Hk Hh.
  case: (Z.eq_dec k k)=>//.
  by case: (Z.eq_dec h h).
Qed.

(*This is equivalent to the original encoder with all the parameters being (k, h)*)
Lemma encoder_concat_nochange_eq: forall orig,
  encoder_concat_nochange orig = encoder_concat orig (zseq (Zlength orig) (k, h)).
Proof.
  move=> orig. rewrite /encoder_concat/encoder_concat_nochange.
  move: (@nil block) => blks.
  remember (@None block) as curr.
  have: (match curr return Prop with
        | None => True
        | Some b => blk_k b = k /\ blk_h b = h
        end) by rewrite Heqcurr.
  rewrite {Heqcurr}.
  remember (@nil (list fpacket)) as sent. 
  rewrite {1 3}Heqsent {Heqsent}.
  move: blks curr sent.
  elim: orig => [// | p ptl /= IH blks curr sent Hcurr].
  rewrite IH//=.
  - rewrite (@zseq_hd _ (Zlength (p :: ptl)) (k, h))//=; last by list_solve.
    rewrite encoder_one_step_nochange_eq //=. do 3 f_equal. list_solve.
  - (*Invariant preservation*) 
    rewrite /encoder_one_step_nochange/=.
    move: Hcurr. case: curr => [curr /= [Hk Hh] | //= _].
    + rewrite /encode_exist.
      by case: (Z.eq_dec
      (Zlength
         [seq x <- data_packets (add_packet_to_block_red p curr) | isSome x])
      (blk_k (add_packet_to_block_red p curr))).
    + rewrite /encode_new. by case: (Z.eq_dec k 1).
Qed.

End Simple.

(*Here, we use nats instead so that we can use mathcomp's results about
  nat division*)
(*TODO: maybe use nats everywhere*)
Variable k: nat.
Variable h: nat.

Local Open Scope nat_scope.

(*Now we can reason about the block boundaries*)

(*TODO: add this somewhere and use it*)
Lemma Zlength_size: forall {A: Type} (s: seq A),
  Zlength s = Z.of_nat (size s).
Proof.
  move=> A s. by rewrite Zlength_correct size_length.
Qed. 
(*Our invariant is the following*)

(*Hmm, let's think about a better invariant*)
(*Much nicer than working with nat division and multiplication everywhere*)
Definition encode_boundary_invar (blks: seq block) (curr: option block) (sent: seq fpacket) :=
  (exists (l: list (list fpacket)) (last: list fpacket),
  sent = concat l ++ last /\
  map (fun l1 => map Some l1) l = 
  map (fun b => data_packets b ++ parity_packets b) (rev blks) /\
  (forall b, curr = Some b ->
    exists filled,
    data_packets b = map Some filled ++ nseq (k - size filled) None /\
    last = filled) /\
  (curr = None -> last = nil)) /\
   (*Metadata info we need*)
   (forall b, b \in block_option_list (blks, curr) -> 
   blk_k b = Z.of_nat k /\
   size (data_packets b) = k) /\
   (*somewhat redundant with invar - TODO: need to fix*)
   (forall b, curr = Some b -> (Zindex None (data_packets b) < Z.of_nat k)%Z).

Lemma cat_cons: forall {A: Type} (s1 s2: seq A) (x: A),
  s1 ++ x :: s2 = (s1 ++ [:: x]) ++ s2.
Proof.
  move=> A s1 s2 x. by rewrite -catA.
Qed.

Lemma add_red_data_size: forall p curr,
  size (data_packets (add_packet_to_block_red p curr)) = size (data_packets curr).
Proof.
  move=> p curr/=.
  by rewrite size_length -ZtoNat_Zlength 
    Zlength_upd_Znth ZtoNat_Zlength -size_length.
Qed.

(*TODO: did I prove this somewhere*)
Lemma ltn_0: forall n m,
  n < m ->
  0 < m.
Proof.
  move=> n m. case: n=>// n' Hn'.
  by eapply ltn_trans; last by apply Hn'.
Qed. 

(*Need that k is nonzero*)
Variable k_not0: k != 0.

(*Prove that this invariant is preserved. We don't need any other
  assumptions.*)
Lemma encode_boundary_invar_pres: forall blks curr sent p,
  encode_boundary_invar blks curr sent ->
  let t := encoder_one_step_nochange (Z.of_nat k) (Z.of_nat h) blks curr p in
  encode_boundary_invar t.1.1 t.1.2 (sent ++ t.2).
Proof.
  move=> blks curr sent p. 
  rewrite /=/encoder_one_step_nochange/=/encode_boundary_invar =>
    [[[l [ last [ Hsent [Hprevs []]]]]]].
  case: curr => [curr /= Hsome Hnone [Hallk Hindexlt] | /= Hsome Hnone [Hallk Hindexlt]].
  - (*We need to consider if we finish this block or not*)
    rewrite /encode_exist.
    move: Hsome => /(_ curr erefl) [filled [Hdat Hlast]]; subst.
      (*First, prove something about Zindex*)
    have Hidx: Zindex None (data_packets curr) = Z.of_nat (size filled). {
      rewrite /Zindex. f_equal. rewrite Hdat index_cat.
      have->//=: None \in [seq Some i | i <- filled] = false
        by apply /mapP => [[x]]//.
      rewrite size_map.
      have->:(index None (nseq (k - size filled) None)) = 0; last by
        rewrite addn0.
      move=> t. by case: ((k - size filled)).
    }
    case:  (Z.eq_dec
    (Zlength
       [seq x <- data_packets (add_packet_to_block_red p curr) | isSome x])
    (blk_k (add_packet_to_block_red p curr)))=>/= Hlen.
    + (*length goal is easy*) 
      split_all; last by []; last by move=>b;
        rewrite /block_option_list/= in_cons => /orP[/eqP ->/= | Hinb];
        [rewrite encode_block_k add_red_k data_packets_encode add_red_data_size |];
        apply Hallk; rewrite /block_option_list/=;
        [rewrite mem_head | rewrite in_cons Hinb orbT].
      exists (l ++ [:: (filled ++ [:: (get_fec_packet p curr)] ++ 
      (encode_block (add_packet_to_block_red p curr) (Some p)).2)]).
      exists nil. split_all=>//.
      * by rewrite -catA concat_app/= -!cat_app !cats0 !catA.
      * rewrite !map_cat/= !map_cat/= map_rev/= data_packets_encode/= Hprevs.
        rewrite rev_cons -cats1 map_rev. f_equal. rewrite cat_cons. f_equal. 
        f_equal; last by rewrite encode_some.
        (*Now we have to prove equivalence of the new lists*)        
        rewrite Hidx Hdat upd_Znth_app2; last by
          rewrite !Zlength_size !size_map; split; lia.
        rewrite Zlength_size !size_map Z.sub_diag -cat_app. f_equal.
        (*Now, just need to show that k - size filled = 1*)
        (*Idea: know that Zindex None (data_packets curr) < k
          so it is k-1 or < k -1. If < k -1, then multiple None values,
          so contradicts filter assumption*)
        have->//: (k - size filled = 1).
        have<-//: size filled + 1 = k; last by rewrite -addnBAC // subnn.
        move: Hindexlt => /( _ curr erefl) Hlt.
        have Hlt': size filled < k by apply /ltP; apply Nat2Z.inj_lt;
          rewrite -Hidx.
        have->//: size filled = k -1; last by
          rewrite subnK //; apply (ltn_0 Hlt').
        have: size filled <= k - 1 by
          rewrite subn1 -ltn_pred //; apply (ltn_0 Hlt'). 
        rewrite leq_eqVlt => /orP[/eqP ->// | Hsmall].
        (*In this case, get that we have multiple None values*)
        have H2ge: 2 <= k - size filled by rewrite ltn_subCr.
        move: Hallk => /( _ curr); rewrite /block_option_list/= mem_head => 
          /(_ isT) [Hk Hszk].
        have/allP: all isSome (upd_Znth (Zindex None (data_packets curr))
          (data_packets curr) (Some (get_fec_packet p curr))) by
          apply filter_all_Zlength;
          rewrite Zlength_upd_Znth Hlen Zlength_size Hszk.
        rewrite Hidx Hdat upd_Znth_app2; last by
          rewrite !Zlength_size !size_map; split; lia.
        rewrite Zlength_size size_map Z.sub_diag.
        move: H2ge. case: (k - size filled)=>//= n.
        rewrite upd_Znth0.
        case: n =>//= n _.
        move => Hcon. have//: isSome (@None fpacket). apply (Hcon None).
        by rewrite mem_cat !in_cons eq_refl !orbT.
    + (*Case when block not finished*)
      split_all.
      * (*main result*)
        exists l. exists (filled ++ [:: get_fec_packet p curr]).
        split_all.
        -- by rewrite catA.
        -- by rewrite Hprevs.
        -- move => b [Hb]; subst.
          exists (filled ++ [:: get_fec_packet p curr]).
          rewrite /= map_cat/= size_cat/=. split=>//.
          rewrite Hidx Hdat upd_Znth_app2; last by
            rewrite !Zlength_size size_map; split; lia.
          rewrite -cat_app Zlength_size size_map Z.sub_diag -catA.
          f_equal.
          (*Here, just need to show that size filled < k - idea:
            if it equals k, then contradicts Hlen*)
          have: 0 <= k - size filled by [].
          rewrite leq_eqVlt => /orP[Hksz |]; last first.
            rewrite subnDA.
            case: (k - size filled) =>//= n _.
            by rewrite subn1 -pred_Sn upd_Znth0.
          move: Hallk => /(_ curr); 
          rewrite /block_option_list/= mem_head => /(_ isT) [Hk Hszk].
          have Hkeq: k = size filled. {
            move: Hksz. rewrite eq_sym subn_eq0 => Hle.
            apply /eqP. rewrite eqn_leq Hle/=.
            by rewrite -Hszk Hdat size_cat size_map leq_addr.
          }
          exfalso. apply Hlen. rewrite Hidx -Hkeq.
          rewrite upd_Znth_out_of_range; last by right;
            rewrite Hdat Hkeq subnn/= cats0 Zlength_size size_map; lia.
          rewrite Hk -Hszk -Zlength_size filter_all_Zlength.
          apply /allP => x.
          by rewrite Hdat Hkeq subnn cats0 => /mapP [y] _ ->.
        -- by [].
      * (*Prove k invariant (easy)*)
        move=> b. by rewrite /block_option_list/= in_cons => 
          /orP [/eqP -> | Hinb]; [rewrite add_red_k add_red_data_size |];
          apply Hallk; rewrite /block_option_list/=; 
          [rewrite mem_head | rewrite in_cons Hinb orbT].
      * move=> b [] <-/=.
        (*Now, we need to prove that the block is not yet full*)
        move: Hallk => /(_ curr); rewrite /block_option_list/= mem_head 
          => /(_ isT) [Hk Hszk].
        have Hin: In None ((upd_Znth (Zindex None (data_packets curr)) (data_packets curr)
        (Some (get_fec_packet p curr)))). {
          apply /inP.
          have: ~~ all isSome (upd_Znth (Zindex None (data_packets curr))
          (data_packets curr) (Some (get_fec_packet p curr))). {
            apply /negP => C.
            rewrite -filter_all_Zlength in C. move: C.
            by rewrite Zlength_upd_Znth (Zlength_size (data_packets curr)) 
              Hszk -Hk => C.
          }
          rewrite -has_predC. by move => /hasP [[]].
        }
        rewrite -Zindex_In in Hin.
        move: Hin. by rewrite Zlength_upd_Znth 
          (Zlength_size (data_packets curr)) Hszk .
  - (*Case where block is None*)
    rewrite /encode_new.
    (*First case: k =1, so finish block*)
    case: (Z.eq_dec (Z.of_nat k) 1) => /= Hk1.
    + split_all=>//.
      * exists (l ++ [:: ((new_fec_packet p (Z.of_nat k) (Z.of_nat h)
        :: (encode_block (create_block_with_packet_red p (Z.of_nat k) (Z.of_nat h))
            (Some p)).2))]). exists nil.
        split_all=>//.
        -- by rewrite Hsent -!catA concat_app /= -!cat_app !cats0 Hnone.
        -- rewrite !map_cat/= map_rev/= data_packets_encode/= Hprevs
            rev_cons -cats1 map_rev. f_equal. by rewrite Hk1.
      * move=> b. rewrite /block_option_list/= in_cons => 
          /orP[/eqP -> | Hinb].
          rewrite encode_block_k/= data_packets_encode/= Hk1/=.
          split=>//. lia.
        apply Hallk. by rewrite /block_option_list.
    + (*Start new packet but dont finish*) 
      split_all=>//.
      * exists l. exists [:: new_fec_packet p (Z.of_nat k) (Z.of_nat h)].
        split_all=>//.
        -- by rewrite Hsent -catA Hnone.
        -- move=> b [] <-. exists [:: new_fec_packet p (Z.of_nat k) (Z.of_nat h)].
          split=>//=.
          rewrite /zseq Nat2Z.id. 
          move: Hk1 k_not0. case: k =>// n. case: n => // n _ _/=.
          by rewrite upd_Znth0.
      * move=> b. rewrite /block_option_list/= in_cons 
        => /orP[/eqP ->/= | Hinb].
        -- split=>//. apply Nat2Z.inj.
          rewrite -Zlength_size Zlength_upd_Znth zseq_Zlength //. lia.
        -- by apply Hallk.
      * move=> b [] <-/=; rewrite /zseq Nat2Z.id.
        move: k_not0 Hk1. case: k => // n. case: n => // n _ _.
        rewrite /Zindex. apply inj_lt. apply /ltP.
        by rewrite /= upd_Znth0/=.
Qed.

(*Lift to all steps*)
Lemma encode_boundary_invar_all: forall orig,
  let t := encoder_concat_nochange (Z.of_nat k) (Z.of_nat h) orig in
  encode_boundary_invar t.1.1 t.1.2 (concat t.2).
Proof.
  (*Almost trivial, just need to generalize IH appropriately*)
  move=> orig/=.
  rewrite /encoder_concat_nochange.
  remember (@nil block) as blks.
  remember (@None block) as curr.
  remember (@nil (seq fpacket)) as sent.
  rewrite {1 3 5} Heqsent.
  have: encode_boundary_invar blks curr (concat sent). {
    rewrite Heqblks Heqcurr Heqsent /encode_boundary_invar//; split_all=>//.
    exists nil. by exists nil.
  }
  rewrite {Heqblks Heqcurr Heqsent}. move: blks curr sent.
  elim: orig => [// | p otl /= IH blks curr sent Hinvar].
  apply IH.
  rewrite concat_app/= -!cat_app cats0.
  by apply (encode_boundary_invar_pres p).
Qed. 

(*We need one more (small invariant) - we prove separately because
  this is much simpler and doesn't need everything else*)
Definition encode_boundary_h_invar (blks: seq block) (curr: option block) :=
  (forall b, b \in block_option_list (blks, curr) ->
    blk_h b = Z.of_nat h /\
    size (parity_packets b) = h).

Lemma encode_boundary_h_pres: forall blks curr p,
  encode_boundary_h_invar blks curr ->
  let t := encoder_one_step_nochange (Z.of_nat k) (Z.of_nat h) blks curr p in
  encode_boundary_h_invar t.1.1 t.1.2.
Proof.
  move=> blks curr p.
  rewrite /=/encoder_one_step_nochange/=/encode_boundary_h_invar
  /block_option_list.
  case: curr => [curr /= Hinvar | /= Hinvar].
  - rewrite /encode_exist.
    case: (Z.eq_dec
    (Zlength
       [seq x <- data_packets (add_packet_to_block_red p curr)
          | isSome x]) (blk_k (add_packet_to_block_red p curr))) =>/= Hk b.
    + rewrite in_cons => /orP[/eqP -> | Hinb]; last by 
        apply Hinvar; rewrite in_cons Hinb orbT.
      move: Hinvar => /(_ curr (mem_head _ _)) [Hh1 Hh2].
      split_all; first by rewrite encode_block_h add_red_h.     
      rewrite encode_some/= size_map.
      apply Nat2Z.inj. rewrite -!Zlength_size Zlength_map_with_idx
      populate_packets_Zlength.
      rewrite encoder_list_Zlength //; last by apply blk_c_nonneg. lia.
    + rewrite in_cons => /orP[/eqP ->/= | Hinb]; last by
        apply Hinvar; rewrite in_cons Hinb orbT.
      by apply Hinvar; rewrite mem_head.
  - rewrite /encode_new.
    case: (Z.eq_dec (Z.of_nat k) 1)=>/= Hk1 b.
    + (*same proof*) 
      rewrite in_cons => /orP[/eqP -> | Hinb]; last by apply Hinvar.
      rewrite encode_block_h/= encode_some/= size_map. split=>//.
      apply Nat2Z.inj. rewrite -!Zlength_size Zlength_map_with_idx
      populate_packets_Zlength.
      rewrite encoder_list_Zlength //; last by apply blk_c_nonneg. lia.
    + rewrite in_cons => /orP[/eqP -> /= | Hinb]; last by apply Hinvar.
      split=>//. by rewrite /zseq size_nseq Nat2Z.id.
Qed. 

(*All steps version*)
Lemma encode_boundary_h_all: forall orig,
  let t := encoder_concat_nochange (Z.of_nat k) (Z.of_nat h) orig in
  encode_boundary_h_invar t.1.1 t.1.2.
Proof.
  (*Almost trivial, just need to generalize IH appropriately*)
  move=> orig/=.
  rewrite /encoder_concat_nochange.
  remember (@nil block) as blks.
  remember (@None block) as curr.
  remember (@nil (seq fpacket)) as sent.
  rewrite {1 3} Heqsent {Heqsent}.
  have: encode_boundary_h_invar blks curr by
    rewrite Heqblks Heqcurr /encode_boundary_h_invar.
  rewrite {Heqblks Heqcurr}. move: blks curr sent.
  elim: orig => [// | p otl /= IH blks curr sent Hinvar].
  apply IH.
  by apply encode_boundary_h_pres.
Qed. 

End Boundaries.

Local Open Scope nat_scope.

Lemma size_concat: forall {A: Type} (n: nat) (s: seq (seq A)),
  all (fun l => size l == n) s ->
  size (concat s) = size s * n.
Proof.
  move=> A n s. elim: s => [// | h t /= IH /andP[/eqP Hsz Hall]].
  by rewrite size_cat Hsz IH.
Qed.

Lemma in_block_option_list: forall (o: option block) 
  (b: block) (l: seq block),
  b \in l ->
  b \in (block_option_list (l, o)).
Proof.
  move=> [a b l Hbl/= |b l //].
  rewrite /block_option_list/=. by rewrite in_cons Hbl orbT.
Qed.

Lemma skipn_drop: forall {A: Type} (n: nat) (s: seq A),
  skipn n s = drop n s.
Proof.
  move=> A n s. move: n. 
  by elim: s => [//= [| n] //| h t IH /= [//| n' /=]].
Qed.

Lemma firstn_take: forall {A: Type} (n: nat) (s: seq A),
  firstn n s = take n s.
Proof.
  move=> A n s. move: n.
  elim: s => [[|]// | h t /= IH [// | n']/=].
  by rewrite IH.
Qed.

Lemma uniq_sublist: forall {A: eqType} (lo hi: Z) (s: seq A),
  uniq s ->
  uniq (sublist lo hi s).
Proof.
  move=> A lo hi s Huniq.
  rewrite /sublist skipn_drop firstn_take.
  by apply drop_uniq, take_uniq.
Qed.

Lemma sublist_concat: forall {A: Type} (d: seq A) (n: nat) (s: seq (seq A)) (i: nat),
  i < (size s) ->
  all (fun l => size l == n) s ->
  sublist (Z.of_nat (i * n)) (Z.of_nat ((i + 1) * n)) (concat s) = 
  nth d s i.
Proof.
  move=> A d n s i Hi Hall.
  rewrite /sublist (*skipn_drop firstn_take*) !Nat2Z.id.
  move: s n Hi Hall. elim : i => 
    [//= [//= | h t /=] n | i' /= IH [//= | h t /=] n].
  - move => Hi /andP[/eqP Hszh Hall].
    by rewrite add0n mul1n -cat_app firstn_take take_size_cat.
  - move=> Hi /andP[/eqP Hszh Hall].
    rewrite -cat_app firstn_take skipn_drop.
    have->:((i'.+1 + 1) * n) = (n + i'.+1 * n) by
      rewrite mulnDl mul1n addnC.
    rewrite takeD take_size_cat // (@drop_size_cat _ n) // 
      drop_cat !Hszh.
    have->:(i'.+1 * n < n) = false.
      rewrite ltnNge. apply negbF.
      by rewrite -addn1 mulnDl mul1n addnC leq_addr.
    have->:(i'.+1 * n - n) = i' * n by
      rewrite -addn1 mulnDl mul1n -subnBA // subnn subn0.
    rewrite -firstn_take -skipn_drop -addn1. by apply IH.
Qed.

Lemma pmap_id_inv: forall {A: Type}(s: seq (option A)) (t: seq A),
  map Some t = s ->
  t = pmap id s.
Proof.
  move=> A s t Hall. subst. elim: t => [// | h t /= IH].
  by rewrite -IH.
Qed.

Lemma mem_sublist: forall {A: eqType} (s: seq A) (lo hi: Z) (x: A),
  x \in sublist lo hi s ->
  x \in s.
Proof.
  move=> A s lo hi x. rewrite /sublist skipn_drop firstn_take => Hin.
  apply mem_drop in Hin.
  by apply mem_take in Hin.
Qed.

Lemma map_uniq_inj {A B: eqType} (f: A -> B) (s: seq A) (x y: A):
  uniq (map f s) ->
  x \in s ->
  y \in s ->
  f x = f y ->
  x = y.
Proof.
  elim: s=>[// |h t /= IH /andP[Hnotin Huniq]].
  rewrite !in_cons => /orP[/eqP Hxh | Hinxt] /orP[/eqP Hyh | Hinyt] Hfeq; 
    subst =>//.
  - exfalso. move: Hnotin => /negP; apply.
    rewrite Hfeq. apply /mapP. by exists y.
  - exfalso. move: Hnotin => /negP; apply.
    rewrite -Hfeq. apply /mapP. by exists x.
  - by apply IH.
Qed.


(*Now we prove the following crucial condition we need:
  every packet in the original list (except for possibly the
  last unfinished part) is in some block in the output, and
  for this block, we can find all (k+h) of its packets between
  position i(k+h) and (i+1)(k+h) of the output, for some i*)
Theorem encoder_boundaries_exist: forall (k h: Z) p orig,
  (*Some assumptions on the orig stream and parameters for our
    invariants*)
  (0 < k <= fec_n - 1 - fec_max_h)%Z ->
  (0 < h <= fec_max_h)%Z ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) -> (*TODO: we will require that this
    is the index but don't need until reorder stuff later*)
  p \in (sublist 0 (Z.of_nat ((size orig %/ (Z.to_nat k) * (Z.to_nat k)))) orig) ->
  let sent := 
    concat (encoder_concat_nochange k h orig).2 in
  exists (b: block) (f: fpacket) (i: nat),
    p_packet f = p /\
    ~~ fd_isParity f /\ (*TODO: do we need?*)
    b \in (get_blocks sent) /\
    packet_in_block f b /\ (*TODO: do we need, or just eq of blockId?*)
    block_encoded b /\
    block_wf b /\
    let n := Z.to_nat (k + h) in
    i < size sent %/ n /\
    let l := (sublist (Z.of_nat (i * n)) 
      (Z.of_nat ((i+1) * n)) sent) in
    uniq l /\
    all (fun (p': fpacket) => packet_in_block p' b) l.
Proof.
  move=> k h p orig Hkbound Hhbound Hval Henc Huniqseq/= Hinp.
  have Hallinbounds: (forall k0 h0 : Z_eqtype,
    (k0, h0) \in zseq (Zlength orig) (k, h) ->
    (0 < k0 <= fec_n - 1 - fec_max_h)%Z /\ (0 < h0 <= fec_max_h)%Z) by
    move=> k' h'; rewrite /zseq mem_nseq => /andP[_ /eqP []]->->.
  have Hsz: size orig = size (zseq (Zlength orig) (k, h)) by
    rewrite size_nseq ZtoNat_Zlength -size_length.
  have/=:=(@encode_boundary_h_all (Z.to_nat k) (Z.to_nat h) orig).
  rewrite /encode_boundary_h_invar.
  have:= (encoder_all_steps_blocks Hallinbounds Hval Henc Huniqseq Hsz).
  (*Get info about how orig relates to output from 
    [encoder_all_steps_sent_data]*)
  have:=(encoder_all_steps_sent_data Hsz).
  (*Remove unneeded assumptions and get relevant [encoder_props] 
    in context*)
  rewrite {Hallinbounds Hval Henc Hsz}.
  rewrite !(proj1 (encoder_all_steps_concat_aux orig _))
    !encoder_all_steps_concat -!encoder_concat_nochange_eq.
  rewrite !Z2Nat.id; try lia.
  move => Horig [ [Hperm [Hallwf [_ [_ [_ [_ [_ [Henc [Hinprog [Hwf [Huniq Huniqdat]]]]]]]]]]] Hzidx] Hallh.
  (*Now get results from [encode_boundary_invar]*)
  have Hk0: (Z.to_nat k) != 0 by apply /eqP; lia.
  have/=:=(encode_boundary_invar_all (Z.to_nat h) Hk0 orig).
  rewrite !Z2Nat.id; try lia.
  move => [[l [last [Hconcat [Hdatpar [Hlastsome Hlastnone]]]]] H].
  (*First, get f*)
  have Hpin': p \in orig. {
    move: Hinp => /inP Hinp. apply sublist_In in Hinp.
    by apply /inP. 
  }
  have:=Hpin'. rewrite -{1}Horig => /mapP [f].
  rewrite mem_filter => /andP[Hnotpar Hinf] Hpf. 
  (*Now, get block b*)
  have [b /andP[Hinb Hinfb]]:=(get_blocks_allin Hwf Hinf).
  exists b. exists f. 
  (*Getting i is a bit more complicated - we use the boundary
    invariant to get the list that contains 
      (data_packets b ++ parity_packet b)*)
  have Hinb': b \in (block_option_list
  ((encoder_concat_nochange k h orig).1.1,
  (encoder_concat_nochange k h orig).1.2)) by
    rewrite -(perm_mem Hperm).
  (*Need to know that b cannot be in the last block, or else the sublist
    assumption is violated (because the output is uniq). This
    is surprisingly tricky to prove*)
  have Hinb_fst: b \in (encoder_concat_nochange k h orig).1.1. {
    move: Hinb'. rewrite /block_option_list/=.
    move: Hlastsome. 
    case Hcurr: ((encoder_concat_nochange k h orig).1.2) => [curr /= | //].
    move=> /(_ curr erefl) [filled [Hdatcurr Hlast]]; subst.
    rewrite in_cons => /orP[/eqP Hbcurr | //]. subst.
    (*Can prove that f is in data_packets curr*)
    (*Idea: prove that sublist of orig is data packets part of
      (concat l) and that rest is (filled), then, prove that f
      is in both - contradicts uniqueness*)
    have Hinffill: f \in filled. {
      move: Hinprog => /( _ curr Hcurr). 
      rewrite /block_in_progress => /allP Hprog.
      move: Hinfb. rewrite packet_in_block_eq => /orP[ | Hinpar];
      last by move: Hprog => /(_ _ Hinpar).
      rewrite Hdatcurr mem_cat => /orP[/mapP [f'] Hinf' []->// | ].
      by rewrite mem_nseq => /andP [].
    }
    (*Now we want to show that f \in concat l*)
    have Horig':=Horig.
    move: Horig. rewrite Hconcat filter_cat !map_cat => Horig.
    (*Quite complicated to show: relies on concat results and
      knowing that all data/parities are filled and have correct
      fd_isParity values*)
    have Hsz1: size [seq i | i <- concat l & ~~ fd_isParity (p_fec_data' i)] =
      (size l) * (Z.to_nat k). {
      (*TODO: repetitive below - can we improve?*)
      rewrite concat_flatten filter_flatten -concat_flatten size_map.
      rewrite (@size_concat _ (Z.to_nat k)); first by
        rewrite !size_map.
      apply /allP => pkts Hpkts.
      apply /eqP.
      have [pkts' []]: exists l',
        map Some l' \in [seq [seq Some i | i <- l1] | l1 <- l] /\
        pkts = filter (fun (x: fpacket) => ~~ fd_isParity x) l'. {
        move: Hpkts => /mapP [pkts'] Hinpkts->.
        exists pkts'. split=>//. apply /mapP. by exists pkts'. 
      }
      rewrite Hdatpar => /mapP [b']. 
      rewrite mem_rev => Hinb' Hpkts' => ->.
      have Hpkts'':=Hpkts'.
      apply pmap_id_inv in Hpkts''. 
      rewrite Hpkts'' pmap_cat filter_cat size_cat.
      have->/=:[seq x <- pmap id (data_packets b') | 
        ~~ fd_isParity (p_fec_data' x)] =
        pmap id (data_packets b'). {
        apply /all_filterP. apply /allP. move=> p'.
        rewrite -pmap_id_some => Hindat.
        have->//: fd_isParity (p_fec_data' p') = false. 
        by apply (Hallwf _ (in_block_option_list _ Hinb')).
      }
      have->/=:[seq x <- pmap id (parity_packets b') | 
        ~~ fd_isParity (p_fec_data' x)] = nil. {
        rewrite -(filter_pred0 (pmap id (parity_packets b'))).
        apply eq_in_filter => p'/=. rewrite -pmap_id_some => Hinpar.
        apply negbF. by apply (Hallwf _ (in_block_option_list _ Hinb')).
      }
      rewrite addn0 size_pmap -size_filter.
      have->:[seq x <- data_packets b' | isSome x] = data_packets b'.
        apply /all_filterP. apply /allP. move => o Hoin.
        have: o \in (data_packets b' ++ parity_packets b') by 
          rewrite mem_cat Hoin.
        by rewrite -Hpkts' => /mapP [x] _ ->.
      apply H. apply (in_block_option_list _ Hinb').
    }
    (*Now we need to know that filled is not too large*)
    have Hsz2: size filled < Z.to_nat k. {
      have Hszdatcurr:=Hdatcurr.
      apply (f_equal size) in Hszdatcurr. move: Hszdatcurr.
      rewrite size_cat size_map size_nseq.
      have Hinopt: curr \in block_option_list
        ((encoder_concat_nochange k h orig).1.1,
        (encoder_concat_nochange k h orig).1.2) by
        rewrite Hcurr/block_option_list/=mem_head.
      have->: size (data_packets curr) = Z.to_nat k by apply H.
      rewrite -maxnE => Hmax. symmetry in Hmax.
      move: Hmax => /maxn_idPr.
      rewrite leq_eqVlt => /orP[/eqP Hsz | //].
      move: Hdatcurr. rewrite Hsz subnn/= cats0 => Hdat.
      (*Contradiction: all are Some, so Zindex is too large*)
      move: Hzidx => /(_ curr Hcurr).
      have->: blk_k curr = (Z.of_nat (Z.to_nat k)) by apply H.
      rewrite -Hsz. have->: size filled = size (data_packets curr) by
        rewrite Hdat size_map.
      by rewrite -Zlength_size Zindex_In Hdat => /inP /mapP [x].
    }
    (*Now, we can reason about the size of orig vs the
      size of l*)
    move: Hinp; rewrite -{2}Horig sublist_app1.
    - move=> Hinf'. apply mem_sublist in Hinf'. move: Hinf'.
      move => /mapP [f']. rewrite mem_filter => 
        /andP[Hnotpar' Hinf'] Heq.
      (*We prove equality from the uniqueness of the
        data packets in the output*)
      have Heq': f = f'. {
        have Hinforig: (f_packet f') \in orig. rewrite -Horig'.
          apply /mapP. exists f'=>//. 
          by rewrite Hconcat filter_cat mem_cat mem_filter 
            Hnotpar' Hinf'.
        apply (map_uniq_inj Huniqdat)=>//; rewrite mem_filter;
        apply /andP; split=>//.
        by rewrite Hconcat mem_cat Hinf'.
      }
      (*Now we get a contradiction from the uniqueness of the
        output stream*)
      move: Huniq. rewrite Hconcat cat_uniq => /andP[_ /andP[/negP Hmem _]].
      exfalso. apply Hmem. apply /hasP.
      exists f=>//=. by rewrite Heq'.
    - (*now prove the size bounds*)
      split; lia.
    - rewrite Zlength_size -Horig size_cat !size_map. 
      rewrite size_map in Hsz1.
      (*Here, we need the div/mod relation for sizes we proved
        above*)
      rewrite !Hsz1 divnMDl; last by apply /ltP; lia.
      rewrite divn_small; first by rewrite addn0; lia.
      rewrite size_filter. by apply (leq_ltn_trans (count_size _ _)).
  }
  (*Now we can continue the main proof*)
  have Hinb_rev: b \in rev (encoder_concat_nochange k h orig).1.1 
    by rewrite mem_rev.
  (*integer value is just location of this block in block output*)
  exists ((index b (rev (encoder_concat_nochange k h orig).1.1))).
  (*Need some results about length/ints*)
  have Hszeq: size (encoder_concat_nochange k h orig).1.1 = size l. {
    apply (f_equal size) in Hdatpar. rewrite !size_map in Hdatpar.
    by rewrite Hdatpar size_rev.
  }
  have Hallsz: all (fun l0 : seq fpacket => size l0 == Z.to_nat (k + h)) l. {
    apply /allP. move=> pkts Hinpkts.
    apply /eqP. 
    have: map Some pkts \in [seq [seq Some i | i <- l1] | l1 <- l] by
      apply /mapP; exists pkts.
    rewrite Hdatpar => /mapP [b']. rewrite mem_rev => Hbin Hpkts.
    apply (f_equal size) in Hpkts. move: Hpkts.
    rewrite size_map =>->; rewrite size_cat.
    have->:size (data_packets b') = Z.to_nat k by apply H;
      apply in_block_option_list.
    have->:size (parity_packets b') = Z.to_nat h by apply Hallh;
      apply in_block_option_list.
    rewrite Z2Nat.inj_add //; lia.
  }
  have Hszl: (size (concat l) = (size l) * (Z.to_nat (k+h))) by
    apply size_concat. 
  have Hge0: 0 < Z.to_nat (k + h) by
    rewrite Z2Nat.inj_add; try lia; apply /ltP; lia.
  split_all=>//.
  - by apply Henc.
  - by apply Hallwf.
  - move: Hinb_rev. rewrite -index_mem => Hlt. apply (ltn_leq_trans Hlt).
    by rewrite size_rev Hszeq Hconcat size_cat Hszl divnMDl // leq_addr.
  - by apply uniq_sublist.
  - (*Here, we use the fact that this sublist consists
    only of [data_packets b ++ parity_packets b]*)
    apply /allP => p'.
    have Hidxl: 
      index b (rev (encoder_concat_nochange k h orig).1.1) < size l by
      move: Hinb_rev; rewrite -index_mem size_rev Hszeq. 
    (*Core of the proof:*)
    have Hmapeq: map Some (sublist
      (Z.of_nat
        (index b (rev (encoder_concat_nochange k h orig).1.1) *
          Z.to_nat (k + h)))
      (Z.of_nat
        ((index b (rev (encoder_concat_nochange k h orig).1.1) + 1) *
          Z.to_nat (k + h))) (concat (encoder_concat_nochange k h orig).2)) =
      data_packets b ++ parity_packets b. {
      rewrite Hconcat. rewrite sublist_app1; try lia.
      2: by split; try lia; apply inj_le; apply /leP;
        rewrite mulnDl mul1n leq_addr.
      2 : by rewrite Zlength_size; apply inj_le; apply /leP;
        rewrite Hszl leq_pmul2r // addn1.
      rewrite (sublist_concat nil _ Hallsz) //.
      (*Very awkward to use because of double map*)
      have /=Hallnth: forall d1 d2 i,
        i < size l ->
        let bs := rev (encoder_concat_nochange k h orig).1.1 in
        (map Some (nth d1 l i)) = 
          data_packets (nth d2 bs i) ++ parity_packets (nth d2 bs i). {
        move=> d1 d2 i/= Hi.
        apply (f_equal (fun (l: seq (seq (option fpacket))) => 
          (nth nil l i))) in Hdatpar.
        move: Hdatpar. rewrite (nth_map d1) //. move->.
        rewrite (nth_map d2) //. by rewrite size_rev Hszeq.
      }
      by rewrite (Hallnth _ block_inhab) // !nth_index.
    }
    (*Now the proof is easy*)
    move=> Hinp'.
    have Hinp'': (Some p') \in (data_packets b ++ parity_packets b) by
      rewrite -Hmapeq; apply /mapP; exists p'.
    by rewrite packet_in_block_eq -mem_cat.
Qed.

(*Plan: 
1. prove for all steps (DONE)
2. prove condition for each block (in terms of just index i,
  uniq packets with that block index) (DONE)
3. give arrival condition (prob in EncodeDecodeCorrectness) (DONE)
4. prove that 2 + 3 implies subblock condition
5. work with subblock condition in decoder*)
