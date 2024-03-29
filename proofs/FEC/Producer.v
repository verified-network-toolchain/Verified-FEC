Require Export Block.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
(** Producer **)

Section Producer.

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

(*We will write our Producer first as a function (with inputted k and h), then write the predicate, where
  we quantify over k and h*)
(*We include 2 pieces of state: the list of blocks include all previous blocks, and the current block is
  represented separately as a block option*)

(*For the situations when we start a new block*)
Definition produce_new (p: packet) (k' h': Z) : list block * option block * list fpacket :=
    let blk := create_block_with_packet_red p k' h' in
    let t := encode_block blk (Some p) in
    if Z.eq_dec k' 1 then ([:: t.1], None, new_fec_packet p k' h' :: t.2) else (nil, Some blk, [ :: new_fec_packet p k' h']).

(*For the situation when we add to an existing block*)
Definition produce_exist (p :packet) (b: block) : list block * option block * list fpacket :=
    let newBlock := add_packet_to_block_red p b in
    let t := encode_block newBlock (Some p) in
    if Z.eq_dec (Zlength (filter isSome (data_packets newBlock))) (blk_k newBlock) then
      ([:: t.1], None, get_fec_packet p b :: t.2) else (nil, Some newBlock, [ :: get_fec_packet p b]).

Definition producer_one_step (blocks: list block) (currBlock : option block) (curr: packet)
  (k h: Z) : list block * option block * list fpacket :=
  match currBlock with
  | None => (*last block finished, need to create a new one*)
    let t := produce_new curr k h in
    (t.1.1 ++ blocks, t.1.2, t.2)
  | Some b =>
      if ~~(Z.eq_dec (blk_k b) k) || ~~(Z.eq_dec (blk_h b) h)
      then let t1 := encode_block b None in
           let t2 := produce_new curr k h in
           (t2.1.1 ++ [:: t1.1] ++ blocks, t2.1.2, t1.2 ++ t2.2)
      else
        let t := produce_exist curr b in
        (t.1.1 ++ blocks, t.1.2, t.2)
  end.

(*For proofs, a version which concatenates all of the results of producer_one_step*)
Definition producer_all_steps (orig: list packet) (params: list (Z * Z)) : list block * option block * list fpacket :=
  foldl (fun (acc: list block * option block * list fpacket) (x : packet * (Z * Z)) =>
   let t := producer_one_step acc.1.1 acc.1.2 x.1 x.2.1 x.2.2 in
    (t.1.1, t.1.2, acc.2 ++ t.2)) (nil, None, nil) (combine orig params).

Definition rse_produce_func orig params curr k h :=
  (producer_one_step (producer_all_steps orig params).1.1 (producer_all_steps orig params).1.2 curr k h).2.

(*For the final predicate, we need to find the past parameters that were used. We can do so with
  the following:*)

Definition get_produce_params (l: list fpacket) : option (Z * Z) :=
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

Lemma produce_func_get_params: forall l orig params curr k h,
  l = rse_produce_func orig params curr k h ->
  get_produce_params l = Some (k, h).
Proof.
  move => l orig params curr k h. rewrite /rse_produce_func /producer_one_step/produce_new/produce_exist/=/get_produce_params.
  case : (producer_all_steps orig params).1.2 => [b | ].
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

Corollary produce_func_get_params': forall orig params curr k h,
  get_produce_params (rse_produce_func orig params curr k h) = Some (k, h).
Proof.
  move => orig params curr k h. by eapply produce_func_get_params.
Qed. 

End Producer.

(*We want to prove the properties we will need of our producer.
  We express this (eventually) through a large invariant. Unlike the
  decoder, we only need to consider 1 version, and we prove all
  the properties we may need in 1 go.
  The main result: all blocks from the Producer are well formed
  (as is the resulting packet stream) and they are complete if
  they are recoverable.*)

Section ProducerBlocks.

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
  rewrite mem_filter/=. rewrite (@mem_map fpacket); last first.
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

Lemma produce_new_uniq: forall p k h,
  uniq (produce_new p k h).2.
Proof.
  move=> p k h. rewrite /produce_new.
  case: (Z.eq_dec k 1)=>//= ->. 
  rewrite encode_block_aux_uniq; last by simpl; lia.
  rewrite andbT. apply /negP => /mapP [[p' z]]/=.
  rewrite -zip_combine => Hin.
  apply mem_zip in Hin.
  rewrite /new_fec_packet => Heq. inversion Heq.
Qed.

Lemma in_produce_new_kh: forall p k h (p': fpacket),
  p' \in (produce_new p k h).2 ->
  fd_k p' = k /\ fd_h p' = h.
Proof.
  move=> p k h p'. rewrite /produce_new.
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

Lemma produce_exist_uniq: forall p b,
  uniq (produce_exist p b).2.
Proof.
  move=> p b. rewrite /produce_exist.
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

End Uniq.

(** Producer properties *)

(*To prove the main theorem about the Producer, we need to show that a number of properties are preserved in
  each run of producer_one_step. To reduce repetition and make things
  cleaner, we group the properties together and prove the 3 different cases we need before proving the full theorem*)

Definition block_option_list (x: list block * option block) : list block :=
  match x.2 with
  | None => x.1
  | Some b => b :: x.1
  end.

Definition producer_props (orig: list packet) (blks: list block) (currBlock: option block) 
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

Lemma producer_props_orig_rev: forall orig blks currBlock pkts,
  producer_props orig blks currBlock pkts ->
  producer_props (rev orig) blks currBlock pkts.
Proof.
  move => orig blks currBlock pkts. rewrite /producer_props => Henc; split_all; try apply Henc.
  move => b p Hinp Hin. rewrite mem_rev. move: Hinp Hin. by apply Henc.
Qed.

Lemma producer_props_orig_rev_iff: forall orig blks currBlock pkts,
  producer_props orig blks currBlock pkts <->
  producer_props (rev orig) blks currBlock pkts.
Proof.
  move => orig blks currBlock pkts. split; move => Henc.
  - by apply producer_props_orig_rev.
  - rewrite -(revK orig). by apply producer_props_orig_rev.
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
  producer_props orig blks None pkts ->
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
Lemma producer_props_new_block: forall p orig blks pkts k h,
  0 < k <= fec_n - 1 - fec_max_h ->
  0 < h <= fec_max_h ->
  packet_valid p ->
  encodable p ->
  p_seqNum p \notin (map p_seqNum orig) ->
  producer_props orig blks None pkts ->
  producer_props (p :: orig) blks (Some (create_block_with_packet_red p k h))
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
  rewrite /producer_props /block_option_list/=; split_all =>//.
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

(*Case 2: We can encode the current block and add all such packets to the output, preserving the invariant*)
Lemma producer_props_encode: forall orig b blks pkts model,
  (Some model) \in (map (omap (@p_packet _)) (data_packets b)) ->
  producer_props orig blks (Some b) pkts ->
  producer_props orig ((encode_block b (Some model)).1 :: blks) None
    (pkts ++ ((encode_block b (Some model)).2)).
Proof.
  move => orig b blks pkts model Hinmodel.
  rewrite {1}/producer_props/block_option_list/=.
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
  rewrite /producer_props/block_option_list/=; split_all => //;
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
Lemma producer_props_add: forall p orig b blks pkts,
  packet_valid p ->
  encodable p ->
  Zindex None (data_packets b) < blk_k b ->
  p_seqNum p \notin (map p_seqNum orig) ->
  producer_props orig blks (Some b) pkts ->
  producer_props (p :: orig) blks (Some (add_packet_to_block_red p b)) (pkts ++ [:: get_fec_packet p b]).
Proof.
  move => p orig b blks pkts Hval Henc  Hzidx Hseqnotin.
  rewrite {1}/producer_props/block_option_list/=.
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
  rewrite /producer_props/block_option_list/=. split_all;
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

(*The key theorem about the Producer: producer_props holds. We need all of these properties for a strong enough
  IH, even though only a few are important in the final theorem we need*)
(*We have 1 other statement (about Zindex). We don't have this in [producer_props] because it doesn't hold at
  all the intermediate steps*)
Theorem producer_all_steps_blocks: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, (k, h) \in params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  producer_props orig (producer_all_steps orig params).1.1 (producer_all_steps orig params).1.2 (producer_all_steps orig params).2 /\
  (forall b, (producer_all_steps orig params).1.2 = Some b -> Zindex None (data_packets b) < blk_k b).
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz.
  (*First, switch to foldr*)
  rewrite /producer_all_steps -(revK (combine _ _)) foldl_rev -zip_combine rev_zip // {Hsz}.
  have Hparam': forall k h, (k, h) \in (rev params) -> 0 < k <= fec_n - 1 - fec_max_h /\ 0 < h <= fec_max_h. {
    move => k h Hin. apply Hparam. by rewrite -mem_rev. }
  move: Hparam Hparam' => _ Hparam. forget (rev params) as p. rewrite {params}.
  have: forall p, p \in rev (orig) -> packet_valid p by apply in_pred_rev.
  have: forall p, p \in rev orig -> encodable p by apply in_pred_rev.
  have: uniq (map p_seqNum (rev orig)) by rewrite map_rev rev_uniq. 
  move: Hvalid Henc Huniq => _ _ _ Huniq Henc Hvalid. rewrite producer_props_orig_rev_iff.
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
          ((producer_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).1.1,
          (producer_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).1.2,
          z.2 ++ (producer_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).2)) ([::], None, [::]) 
         (zip t pt)). (*once again, don't care what ind is, just that we can use IH*)
      rewrite /producer_one_step/produce_new/produce_exist.
      case : ind => [[blks currBlock] pkts]/=.
      have [Hph1 Hph2]: 0 < ph.1 <= fec_n - 1 - fec_max_h /\ 0 < ph.2 <= fec_max_h. {
        apply Hp. rewrite {Hp}. by case: ph => [a b]/=; rewrite in_cons eq_refl. }
      have Hhval: packet_valid h. { apply Hvalid. by rewrite in_cons eq_refl. }
      have Hhenc: encodable h. { apply Henc. by rewrite in_cons eq_refl. }
      case currBlock => [/= b | /=]; last first.
      * move => [IH Hzindex]. case: (Z.eq_dec ph.1 1) => HHl1/=; last first.
          split. by apply producer_props_new_block. move => b [Hb]. subst.
          rewrite create_red_Zindex/=; lia.
        apply (@producer_props_new_block h t _ _ ph.1 ph.2) in IH => //.
        set b := (create_block_with_packet_red h ph.1 ph.2).
        have->:(pkts ++ new_fec_packet h ph.1 ph.2 :: (encode_block b (Some h)).2) =
          (pkts ++ [:: new_fec_packet h ph.1 ph.2]) ++ (encode_block b (Some h)).2 by rewrite -catA.
        split => //. apply producer_props_encode => //. subst b. 
        apply create_block_in. lia.
      * move => [IH Hzindex].
        case Hchange : (~~ Z.eq_dec (blk_k b) ph.1 || ~~ Z.eq_dec (blk_h b) ph.2) => /=.
        -- have Hdat: data_elt b. apply IH => /=. rewrite /block_option_list/=.
           by rewrite in_cons eq_refl.
           apply encode_block_none_some in Hdat. case : Hdat => [model [Hinmod Hencns]].
           rewrite Hencns. apply (producer_props_encode Hinmod) in IH.
           (*similar cases as before now*)
           case: (Z.eq_dec ph.1 1) => HHl1/=; last first.
              rewrite catA.  split. by apply producer_props_new_block. move => b' [Hb']. subst.
              rewrite create_red_Zindex/=; lia.
           apply (@producer_props_new_block h t _ _ ph.1 ph.2) in IH => //. move: IH.
           set b' := (create_block_with_packet_red h ph.1 ph.2) => IH.
           rewrite (cons_app (new_fec_packet _ _ _)) (catA _ _ (encode_block b' (Some h)).2).
           apply (@producer_props_encode _ _ _ _ h) in IH.
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
          ++ split. apply producer_props_add => //.
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
            apply (producer_props_add Hhval) in IH => //.
            apply (producer_props_encode) with(model:=h) in IH. by rewrite -catA in IH.
            apply add_block_in.  have->//: Zlength(data_packets b) = blk_k b.
            apply Hwfb.
Qed.

(*Corollaries: the specific properties we need*)

(*1. The resulting packet stream is well formed*)
Corollary rse_produce_stream_wf: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, (k, h) \in params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  wf_packet_stream (producer_all_steps orig params).2.
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz.
  by apply producer_all_steps_blocks.
Qed.

(*2. Every data packet in the output came from the input*)
Corollary rse_produce_stream_from_orig: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, (k, h) \in params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  (forall (p: fpacket), p \in (producer_all_steps orig params).2 -> 
    fd_isParity p = false -> 
    p_packet p \in orig).
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz p Hp Hpar.
  (*It's not quite as trivial as the last one*)
  have [Hprops _]:=(producer_all_steps_blocks Hparam Hvalid Henc Huniq Hsz).
  case Hprops => [Hperm [Hallwf [_ [producer_all_steps_ [_ [Hinorig [_ [_ [_ [Hwf _]]]]]]]]]].
  have [b /andP[Hb Hpb]]:= get_blocks_allin Hwf Hp.
  apply (Hinorig b).
  - by rewrite -(perm_mem Hperm).
  - have Hwfb: block_wf b. apply Hallwf. by rewrite -(perm_mem Hperm).
    move: Hpb. rewrite packet_in_block_eq => /orP[Hdat // | Hinpar].
    have: fd_isParity p. by apply Hwfb. by rewrite Hpar.
Qed.

(*3. Every block in [get_blocks] of the output is well-formed*)
Corollary rse_produce_stream_blocks_wf: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, (k, h) \in params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  (forall b, b \in (get_blocks (producer_all_steps orig params).2) -> block_wf b).
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz b Hb.
  have [Hprops _]:=(producer_all_steps_blocks Hparam Hvalid Henc Huniq Hsz).
  apply Hprops. case Hprops => [Hperm _].
  by rewrite -(perm_mem Hperm).
Qed.

(*4. Every recoverable block in [get_blocks] of the output is encoded. This one does not appear
  directly in [encoded_props] but can be derived without too much trouble*)
Corollary rse_produce_stream_recoverable_encoded: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, (k, h) \in params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  (forall b, b \in (get_blocks (producer_all_steps orig params).2) -> recoverable b -> block_encoded b).
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz b Hb.
  have [Hprops Hinprog]:=(producer_all_steps_blocks Hparam Hvalid Henc Huniq Hsz).
  move => Hrec. apply Hprops. move: Hb. case Hprops => [Hperm _].
  rewrite (perm_mem Hperm)/block_option_list/=.
  case Hb: (producer_all_steps orig params).1.2 => [b' |//].
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
Corollary rse_produce_stream_uniq: forall (orig: list packet) (params: list (Z * Z)),
  (forall k h, (k, h) \in params -> 
      0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
      0 < h <= ByteFacts.fec_max_h) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  uniq (producer_all_steps orig params).2.
Proof.
  move => orig params Hparam Hvalid Henc Huniq Hsz.
  by apply producer_all_steps_blocks.
Qed.

End ProducerBlocks.

(*One more theorem: the data packets the encoder outputs are exactly
  the packets in the original list.*)

Lemma produce_new_filter: forall p k h,
  map f_packet (filter (fun (p: fpacket) => ~~ (fd_isParity p))
    (produce_new p k h).2) = [:: p].
Proof.
  move=> p k h. rewrite /produce_new.
  case : (Z.eq_dec k 1) => //= _.
  by rewrite encode_block_filter/=.
Qed.

Lemma produce_exist_filter: forall p b,
  map f_packet (filter (fun (p: fpacket) => ~~ (fd_isParity p))
    (produce_exist p b).2) = [:: p].
Proof.
  move=> p b. rewrite /produce_exist.
  case: (Z.eq_dec
  (Zlength
      [seq x <- data_packets (add_packet_to_block_red p b)
        | isSome x]) (blk_k (add_packet_to_block_red p b))) =>//= _.
  by rewrite encode_block_filter.
Qed.

Theorem producer_all_steps_sent_data: forall (orig: list packet) 
  (params: list (Z * Z)),
  size orig = size params ->
  map f_packet 
    ((filter (fun b => negb (fd_isParity (p_fec_data' b)))) 
      (producer_all_steps orig params).2) =
  orig.
Proof.
  move=> orig params Hsz.
  (*switch to foldr*)
  rewrite /producer_all_steps -(revK (combine _ _)) foldl_rev -zip_combine
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
      ((producer_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).1.1,
      (producer_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).1.2,
      z.2 ++ (producer_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).2))
      ([::], None, [::]) (zip ptl part)) => [[blks inprog] send].
    rewrite /producer_one_step/=.
    case: inprog => [//= blk | //=]; last by
      rewrite produce_new_filter.
    case: (~~ proj_sumbool (Z.eq_dec (blk_k blk) parh.1)
    || ~~ proj_sumbool (Z.eq_dec (blk_h blk) parh.2)); last by
      rewrite produce_exist_filter.
    by rewrite /= filter_cat map_cat encode_block_filter produce_new_filter.
Qed.

(*Concat version of Producer*)
Section Concat.

Definition producer_concat (orig: seq packet) (params: seq (Z * Z)) :=
  foldl
  (fun (acc : seq block * option block * seq (seq (fpacket))) (x : packet * (Z * Z)) =>
   let t := producer_one_step acc.1.1 acc.1.2 x.1 x.2.1 x.2.2 in 
    (t.1.1, t.1.2, acc.2 ++ [ :: t.2]))
  ([::], None, [::]) (combine orig params).

Opaque producer_one_step.

Lemma producer_all_steps_concat_aux: forall orig params,
  (producer_all_steps orig params).1 = (producer_concat orig params).1 /\ 
  (producer_all_steps orig params).2 = concat (producer_concat orig params).2.
Proof.
  move => orig params. rewrite /producer_all_steps/producer_concat/= -(revK (combine _ _)) !foldl_rev. 
  remember (rev (combine orig params)) as l. rewrite {orig params Heql}. elim : l => [// | h t /= [IH1 IH2]]. 
  by rewrite !IH1 !IH2//= !concat_app/= !cat_app app_nil_r.
Qed.

Lemma producer_all_steps_concat: forall orig params,
  (producer_all_steps orig params).2 = concat (producer_concat orig params).2.
Proof.
  move => orig params. by apply producer_all_steps_concat_aux.
Qed.

(*This lemma will actually be quite easy with previous result*)
(*From here, we can describe each element of [producer_concat] purely in terms of [rse_produce_func])*)
Lemma rse_concat_mkseqZ: forall orig params,
  Zlength orig = Zlength params ->
  (producer_concat orig params).2 = mkseqZ (fun i => rse_produce_func (sublist 0 i orig) (sublist 0 i params)
    (Znth i orig) (Znth i params).1 (Znth i params).2) (Zlength orig).
Proof.
  move => orig params Hlens. rewrite /producer_concat /rse_produce_func /producer_all_steps.
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
  Znth i (producer_concat orig params).2 = 
  rse_produce_func (sublist 0 i orig) (sublist 0 i params) (Znth i orig) (Znth i params).1 (Znth i params).2.
Proof.
  move => orig params i Hi Hlens. by rewrite rse_concat_mkseqZ //; zlist_simpl.
Qed.

Corollary rse_concat_Zlength: forall orig params,
  Zlength orig = Zlength params ->
  Zlength (producer_concat orig params).2 = Zlength orig.
Proof.
  move => orig params Hlen. by rewrite rse_concat_mkseqZ //; zlist_simpl.
Qed.

End Concat.

(* Part 2: Reasoning about block boundaries*)

(*Now we want to say something more so that we can express that
  not too many packets are lost without exposing information about blocks.
  To do this, we first assume that all parameters are equal; we give
  such an encoder and prove it equivalent*)
Section Boundaries.

(*Encoder with only 1 param*)
Section Simple.

Variable k : Z.
Variable h : Z.

Definition producer_one_step_nochange (blocks: seq block) (currBlock: option block) (curr: packet) :=
  match currBlock with
  | Some b => 
      let t := produce_exist curr b in (t.1.1 ++ blocks, t.1.2, t.2)
  | None => 
      let t := produce_new curr k h in (t.1.1 ++ blocks, t.1.2, t.2)
  end.

Definition producer_concat_nochange (orig: seq packet) : 
  list block * option block * list (list fpacket) :=
  foldl (fun acc x =>
    let t := producer_one_step_nochange acc.1.1 acc.1.2 x in
    (t.1.1, t.1.2, acc.2 ++ [:: t.2])) (nil, None, nil) orig.

(*can easily get producer_all_steps_nochange from this if we need it*)

(*Equality with full encoder*)
(*Coq has trouble if we don't include the return Prop*)
Lemma producer_one_step_nochange_eq: forall blks (curr: option block) p,
  match curr with
  | Some b => blk_k b = k /\ blk_h b = h
  | None => True
  end ->
  (producer_one_step_nochange blks curr p) = (producer_one_step blks curr p k h).
Proof.
  move=> blks curr p.
  rewrite /producer_one_step_nochange/producer_one_step.
  case: curr => [curr /= [Hk Hh] | //=].
  rewrite Hk Hh.
  case: (Z.eq_dec k k)=>//.
  by case: (Z.eq_dec h h).
Qed.

(*This is equivalent to the original encoder with all the parameters being (k, h)*)
Lemma producer_concat_nochange_eq: forall orig,
  producer_concat_nochange orig = producer_concat orig (zseq (Zlength orig) (k, h)).
Proof.
  move=> orig. rewrite /producer_concat/producer_concat_nochange.
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
    rewrite producer_one_step_nochange_eq //=. do 3 f_equal. list_solve.
  - (*Invariant preservation*) 
    rewrite /producer_one_step_nochange/=.
    move: Hcurr. case: curr => [curr /= [Hk Hh] | //= _].
    + rewrite /produce_exist.
      by case: (Z.eq_dec
      (Zlength
         [seq x <- data_packets (add_packet_to_block_red p curr) | isSome x])
      (blk_k (add_packet_to_block_red p curr))).
    + rewrite /produce_new. by case: (Z.eq_dec k 1).
Qed.

End Simple.

(*Here, we use nats instead so that we can use mathcomp's results about
  nat division*)
Variable k: nat.
Variable h: nat.

Local Open Scope nat_scope.

(*Now we can reason about the block boundaries*)

(*Our invariant is the following*)
(*Much nicer than working with nat division and multiplication everywhere*)
Definition produce_boundary_invar (blks: seq block) (curr: option block) (sent: seq fpacket) :=
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
   (*somewhat redundant with invar -should fix*)
   (forall b, curr = Some b -> (Zindex None (data_packets b) < Z.of_nat k)%Z).

Lemma add_red_data_size: forall p curr,
  size (data_packets (add_packet_to_block_red p curr)) = size (data_packets curr).
Proof.
  move=> p curr/=.
  by rewrite !size_Zlength Zlength_upd_Znth.
Qed.

(*Need that k is nonzero*)
Variable k_not0: k != 0.

(*Prove that this invariant is preserved. We don't need any other
  assumptions.*)
Lemma produce_boundary_invar_pres: forall blks curr sent p,
  produce_boundary_invar blks curr sent ->
  let t := producer_one_step_nochange (Z.of_nat k) (Z.of_nat h) blks curr p in
  produce_boundary_invar t.1.1 t.1.2 (sent ++ t.2).
Proof.
  move=> blks curr sent p. 
  rewrite /=/producer_one_step_nochange/=/produce_boundary_invar =>
    [[[l [ last [ Hsent [Hprevs []]]]]]].
  case: curr => [curr /= Hsome Hnone [Hallk Hindexlt] | /= Hsome Hnone [Hallk Hindexlt]].
  - (*We need to consider if we finish this block or not*)
    rewrite /produce_exist.
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
        rewrite rev_cons -cats1 map_rev. f_equal. 
        rewrite cat_cons'. f_equal. 
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
    rewrite /produce_new.
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
          split=>//=. rewrite /zseq. to_ssrnat. 
          move: Hk1 k_not0. case: k =>// n. case: n => // n _ _/=.
          by rewrite upd_Znth0.
      * move=> b. rewrite /block_option_list/= in_cons 
        => /orP[/eqP ->/= | Hinb].
        -- split=>//. 
          by rewrite size_Zlength Zlength_upd_Znth zseq_Zlength; lia. 
        -- by apply Hallk.
      * move=> b [] <-/=; rewrite /zseq; to_ssrnat.
        move: k_not0 Hk1. case: k => // n. case: n => // n _ _.
        rewrite /Zindex. to_ssrnat.
        by rewrite /= upd_Znth0/=.
Qed.

(*Lift to all steps*)
Lemma produce_boundary_invar_all: forall orig,
  let t := producer_concat_nochange (Z.of_nat k) (Z.of_nat h) orig in
  produce_boundary_invar t.1.1 t.1.2 (concat t.2).
Proof.
  (*Almost trivial, just need to generalize IH appropriately*)
  move=> orig/=.
  rewrite /producer_concat_nochange.
  remember (@nil block) as blks.
  remember (@None block) as curr.
  remember (@nil (seq fpacket)) as sent.
  rewrite {1 3 5} Heqsent.
  have: produce_boundary_invar blks curr (concat sent). {
    rewrite Heqblks Heqcurr Heqsent /produce_boundary_invar//; split_all=>//.
    exists nil. by exists nil.
  }
  rewrite {Heqblks Heqcurr Heqsent}. move: blks curr sent.
  elim: orig => [// | p otl /= IH blks curr sent Hinvar].
  apply IH.
  rewrite concat_app/= -!cat_app cats0.
  by apply (produce_boundary_invar_pres p).
Qed. 

(*We need one more (small invariant) - we prove separately because
  this is much simpler and doesn't need everything else*)
Definition produce_boundary_h_invar (blks: seq block) (curr: option block) :=
  (forall b, b \in block_option_list (blks, curr) ->
    blk_h b = Z.of_nat h /\
    size (parity_packets b) = h).

Lemma produce_boundary_h_pres: forall blks curr p,
  produce_boundary_h_invar blks curr ->
  let t := producer_one_step_nochange (Z.of_nat k) (Z.of_nat h) blks curr p in
  produce_boundary_h_invar t.1.1 t.1.2.
Proof.
  move=> blks curr p.
  rewrite /=/producer_one_step_nochange/=/produce_boundary_h_invar
  /block_option_list.
  case: curr => [curr /= Hinvar | /= Hinvar].
  - rewrite /produce_exist.
    case: (Z.eq_dec
    (Zlength
       [seq x <- data_packets (add_packet_to_block_red p curr)
          | isSome x]) (blk_k (add_packet_to_block_red p curr))) =>/= Hk b.
    + rewrite in_cons => /orP[/eqP -> | Hinb]; last by 
        apply Hinvar; rewrite in_cons Hinb orbT.
      move: Hinvar => /(_ curr (mem_head _ _)) [Hh1 Hh2].
      split_all; first by rewrite encode_block_h add_red_h.     
      rewrite encode_some/= size_map.
      rewrite size_Zlength Zlength_map_with_idx populate_packets_Zlength
      encoder_list_Zlength //; try lia.
      by apply blk_c_nonneg.
    + rewrite in_cons => /orP[/eqP ->/= | Hinb]; last by
        apply Hinvar; rewrite in_cons Hinb orbT.
      by apply Hinvar; rewrite mem_head.
  - rewrite /produce_new.
    case: (Z.eq_dec (Z.of_nat k) 1)=>/= Hk1 b.
    + (*same proof*) 
      rewrite in_cons => /orP[/eqP -> | Hinb]; last by apply Hinvar.
      rewrite encode_block_h/= encode_some/= size_map. split=>//.
      rewrite size_Zlength Zlength_map_with_idx populate_packets_Zlength
      encoder_list_Zlength; try lia. by apply blk_c_nonneg.
    + rewrite in_cons => /orP[/eqP -> /= | Hinb]; last by apply Hinvar.
      split=>//. by rewrite /zseq size_nseq; to_ssrnat.
Qed. 

(*All steps version*)
Lemma produce_boundary_h_all: forall orig,
  let t := producer_concat_nochange (Z.of_nat k) (Z.of_nat h) orig in
  produce_boundary_h_invar t.1.1 t.1.2.
Proof.
  (*Almost trivial, just need to generalize IH appropriately*)
  move=> orig/=.
  rewrite /producer_concat_nochange.
  remember (@nil block) as blks.
  remember (@None block) as curr.
  remember (@nil (seq fpacket)) as sent.
  rewrite {1 3} Heqsent {Heqsent}.
  have: produce_boundary_h_invar blks curr by
    rewrite Heqblks Heqcurr /produce_boundary_h_invar.
  rewrite {Heqblks Heqcurr}. move: blks curr sent.
  elim: orig => [// | p otl /= IH blks curr sent Hinvar].
  apply IH.
  by apply produce_boundary_h_pres.
Qed. 

End Boundaries.

Local Open Scope nat_scope.

Lemma in_block_option_list: forall (o: option block) 
  (b: block) (l: seq block),
  b \in l ->
  b \in (block_option_list (l, o)).
Proof.
  move=> [a b l Hbl/= |b l //].
  rewrite /block_option_list/=. by rewrite in_cons Hbl orbT.
Qed.

(*The crucial result which lets us reason about the blocks
  in order (and relate the ith batch of the input and output
  of the Producer):
  the ith block in the Producer's history (which is reversed)
  contains the packets i * n to (i+1) * n in the encoded list;
  the first k of these are packets i * k to (i+1) * k in the original
  list, the number of completed blocks is |O| /k, and the
  number of encoded packets is (|O| / k) * n (completed) +
  |O| mod k (in progress)*)
(*This proof is ugly; a better [produce_boundary_invar]
  would have helped most likely*)
Theorem block_boundaries k h orig (i: nat):
(*Some assumptions on the orig stream and parameters for our
  invariants*)
  (0 < k <= fec_n - 1 - fec_max_h)%Z ->
  (0 < h <= fec_max_h)%Z ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  i < size orig %/ Z.to_nat k ->
  let output :=
    producer_concat_nochange k h orig in
  let sent := 
    concat output.2 in
  let b :=
    nth block_inhab (rev output.1.1) i in
  let n := Z.to_nat k + Z.to_nat h in
  let encoded :=
    (sublist (Z.of_nat (i * n)) (Z.of_nat ((i+1) * n)) sent) in
  (map Some encoded) =
    data_packets b ++ parity_packets b /\
  (sublist (Z.of_nat i * k) ((Z.of_nat (i + 1)) * k) orig =
    (map (@p_packet _) (sublist 0 k encoded))) /\
  size sent = (size orig %/ (Z.to_nat k)) * n +
    (size orig %% (Z.to_nat k)) /\
  size output.1.1 = size orig %/ (Z.to_nat k).
Proof.
  move=> Hkbound Hhbound Hval Henc Huniqseq Hi output sent b n encoded.
  have Hallinbounds: (forall k0 h0 : Z,
    (k0, h0) \in zseq (Zlength orig) (k, h) ->
    (0 < k0 <= fec_n - 1 - fec_max_h)%Z /\ (0 < h0 <= fec_max_h)%Z) by
    move=> k' h'; rewrite /zseq mem_nseq => /andP[_ /eqP []]->->.
  have Hsz: size orig = size (zseq (Zlength orig) (k, h)) by
    rewrite size_nseq !size_Zlength.
  have/=:=(@produce_boundary_h_all (Z.to_nat k) (Z.to_nat h) orig).
  rewrite /produce_boundary_h_invar.
  have:= (producer_all_steps_blocks Hallinbounds Hval Henc Huniqseq Hsz).
  (*Get info about how orig relates to output from 
    [producer_all_steps_sent_data]*)
  have:=(producer_all_steps_sent_data Hsz).
  (*Remove unneeded assumptions and get relevant [producer_props] 
    in context*)
  rewrite {Hallinbounds Hval Henc Hsz}.
  rewrite !(proj1 (producer_all_steps_concat_aux orig _))
    !producer_all_steps_concat -!producer_concat_nochange_eq.
  (*rewrite !Z2Nat.id; try lia.*)
  (*Now get results from [produce_boundary_invar]*)
  have Hk0: (Z.to_nat k) != 0 by apply /eqP; lia.
  have/=:=(produce_boundary_invar_all (Z.to_nat h) Hk0 orig).
  rewrite !Z2Nat.id; try lia.
  (*Redo abbreviations*)
  subst b.
  subst encoded.
  subst output.
  subst sent.
  set (output := producer_concat_nochange k h orig).
  set (sent := concat output.2).
  set (b:= nth block_inhab (rev output.1.1) i).
  set (encoded := (sublist (Z.of_nat (i * n)) (Z.of_nat ((i+1) * n)) sent)).
  move => [[l [last [Hconcat [Hdatpar [Hlastsome Hlastnone]]]]] [Hallk Hidx]].
  move => Horig [ [Hperm [Hallwf [_ [_ [_ [_ [_ [Henc [Hinprog [Hwf [Huniq Huniqdat]]]]]]]]]]] Hzidx] Hallh.
  (*Now we begin the main proof*)
  (*These invariants are pretty difficult to work with*)
  (*First, we need to know lots of size info*)
  have Hszeq: size (output).1.1 = size l. {
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
    have->:size (data_packets b') = Z.to_nat k by apply Hallk;
      apply in_block_option_list.
    have->:size (parity_packets b') = Z.to_nat h by apply Hallh;
      apply in_block_option_list.
    rewrite Z2Nat.inj_add //; lia.
  }
  have Hszl: (size (concat l) = (size l) * (Z.to_nat (k+h))) by
    apply size_concat. 
  (*Prove this*)
  (*Quite complicated to show: relies on concat results and
    knowing that all data/parities are filled and have correct
    fd_isParity values*)
  have Hallpar: all (fun l0 : seq fpacket => size l0 == Z.to_nat k)
    [seq [seq i1 <- i0 | ~~ fd_isParity (p_fec_data' i1)] | i0 <- l]. {
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
    apply Hallk. apply (in_block_option_list _ Hinb').
  }
  have Hsz1: size [seq i | i <- concat l & ~~ fd_isParity (p_fec_data' i)] =
    (size l) * (Z.to_nat k). {
    (*Note: repetitive below - can we improve?*)
    rewrite concat_flatten filter_flatten -concat_flatten size_map.
    by rewrite (@size_concat _ (Z.to_nat k)); first by
      rewrite !size_map.
  }
  (*First, prove that all packets in last 
    are not parities*)
  have Hlastdat: all (fun x => negb(fd_isParity (p_fec_data' x))) last. {
    move: Hlastnone Hlastsome Hconcat.
    case Hcurr: (output.1.2) => [curr |//]; last by
    move=> /(_ erefl) ->// _ _.
    move=> _ /(_ curr erefl) [filled [Hdatcurr Hlast]].
    have Hszdatcurr:=Hdatcurr.
    move=> Hconcat. apply /allP => fp Hfp.
    apply negbT. apply (Hallwf curr).
      by rewrite Hcurr/block_option_list/=mem_head.
    rewrite /packet_in_data Hdatcurr mem_cat -Hlast mem_map.
      by rewrite Hfp.
    by apply some_inj.
  }
  (*Then, prove last is small, prove mod after*)
  have Hlast_sm: size last < Z.to_nat k. {
    move: Hlastnone Hlastsome Hconcat.
    case Hcurr: (output.1.2) => [curr |//]; last first.
      move=> /(_ erefl) ->/= _ _. apply /ltP; lia.
    move=> _ /(_ curr erefl) [filled [Hdatcurr Hlast]].
    have Hszdatcurr:=Hdatcurr.
    apply (f_equal (@size _)) in Hszdatcurr. move: Hszdatcurr.
    rewrite size_cat size_map size_nseq.
    have Hinopt: curr \in block_option_list
      ((producer_concat_nochange k h orig).1.1,
      (producer_concat_nochange k h orig).1.2) by
      rewrite Hcurr/block_option_list/=mem_head.
    have->: size (data_packets curr) = Z.to_nat k by apply Hallk.
    rewrite -maxnE => Hmax. symmetry in Hmax.
    move: Hmax => /maxn_idPr.
    rewrite leq_eqVlt => /orP[/eqP Hsz | //].
    move: Hdatcurr. rewrite Hsz subnn/= cats0 => Hdat.
    (*Contradiction: all are Some, so Zindex is too large*)
    move: Hzidx => /(_ curr Hcurr).
    have->: blk_k curr = (Z.of_nat (Z.to_nat k)) by apply Hallk.
    rewrite -Hsz. have->: size filled = size (data_packets curr) by
      rewrite Hdat size_map.
    by rewrite -Zlength_size Zindex_In Hdat => /inP /mapP [x].
    by rewrite Hlast.
  }
  (*Now prove size of blocks list and orig*)
  have Hszout: size output.1.1 = size orig %/ Z.to_nat k. {
    rewrite -Horig Hconcat !filter_cat map_cat size_cat.
    move: Hsz1. rewrite !size_map=> ->.
    rewrite divnDl.
    + rewrite mulnK; last by apply /ltP; lia.
      rewrite divn_small; first by rewrite addn0.
      apply (@leq_ltn_trans (size last))=>//.
      by rewrite size_filter count_size.
    + apply dvdn_mull. by rewrite dvdnn.
  }
  (*Now we can prove the relation between [size orig] and [size l]*)
  have Hszorig_strong: size orig = size l * (Z.to_nat k) +
    size last. {
    rewrite -Horig Hconcat !filter_cat map_cat size_cat.
    move: Hsz1. rewrite !size_map=>->. f_equal. apply /eqP.
    by rewrite filter_all_size.
  }
  
  (*have Horig':=Horig.
  move: Horig. rewrite Hconcat filter_cat !map_cat => Horig.*)
  move: Hsz1; rewrite size_map => Hsz1.
  have Hkgt0: 0 < Z.to_nat k by apply /ltP; lia.
  (*Two corollaries: *)
  have Hszorig: size orig %/ Z.to_nat k = size l
    by rewrite -Hszout.
  have Hlastmod: size last = (size orig) %% (Z.to_nat k)
    by rewrite Hszorig_strong modnMDl modn_small.
  have Hn: n = Z.to_nat (k+ h)
    by rewrite Z2Nat.inj_add; try lia.
  (*Step 2: Get information about [size sent]*)
  have Hsz_sent1: size sent = (size orig %/ (Z.to_nat k)) * n +
    (size orig %% (Z.to_nat k)) by
    rewrite Hszorig Hconcat size_cat Hszl Hlastmod Hn.
  (*Now we can start proving the goals*)
  have Hnthl: map Some (nth nil l i) = 
    data_packets b ++ parity_packets b. {
    apply (f_equal (fun l => nth (@nil (option fpacket)) l i)) in Hdatpar.
    move: Hdatpar. rewrite (nth_map nil);
      last by rewrite -Hszorig.
    move->. by rewrite (nth_map block_inhab) // size_rev Hszout.
  }
  have Halln: all (fun l0 : seq fpacket => size l0 == n) l. {
    erewrite eq_all. apply Hallsz. move=> x. by rewrite Hn.
  }
  have Hiplus1: (0 <= Z.of_nat (i * n) <= Z.of_nat ((i + 1) * n))%Z. {
    rewrite (mulnDl i 1 n) mul1n. split; try lia; to_ssrnat.
    by rewrite leq_addr.
  }
  have Hiplus1': (Z.of_nat ((i + 1) * n) <= Zlength (concat l))%Z. {
    rewrite Zlength_size Hszl -Hszorig.
    move: Hi.
    case: (size orig %/ Z.to_nat k) => [//| j].
    rewrite ltnS => Hij.
    rewrite addn1 -Hn. to_ssrnat. rewrite leq_pmul2r //.
    apply /ltP; lia.
  }
  have Hinb: b \in output.1.1
    by rewrite -mem_rev mem_nth // size_rev Hszeq -Hszorig.
  have Hinb': b \in block_option_list (output.1.1, output.1.2) by
    apply in_block_option_list.
  move: Hallwf => /(_ _ Hinb') Hwfb.
  move: Henc => /( _ _ Hinb) Henc.
  move: Hallk => /( _ _ Hinb') [Hk Hdat].
  split_all=>//.
  - subst encoded. rewrite Hconcat sublist_app1; try lia.
    by rewrite (sublist_concat nil) // -Hszorig. 
  - (*Idea: suppose we have (concat l) and we filter by p
    and we know that all  *)
    have Hkex : k = Z.of_nat (Z.to_nat k) by lia.
    subst encoded.
    rewrite -Horig !Hconcat filter_cat map_cat !sublist_app1; try lia.
    + rewrite sublist_map filter_concat.
      have Hhex: h = Z.of_nat (Z.to_nat h) by lia.
      rewrite Hkex. to_ssrnat.
      rewrite (sublist_concat nil).
      * rewrite (sublist_concat nil).
        -- rewrite (nth_map nil); last by rewrite -Hszorig.
          have Hbk: blk_k b = k by rewrite Hk -Hkex.
          have Hbh: blk_h b = h by move: Hallh => /( _ _ Hinb') [] ->.
          rewrite (filter_block_encoded Hnthl)=>//.
          ++ by rewrite -Hkex Hbk.
          ++ rewrite Hbk Hbh. apply /eqP.
            move: Hallsz =>/allP -> //. 
            by rewrite mem_nth // -Hszorig. 
        -- by rewrite -Hszorig.
        -- by [].
      * by rewrite size_map -Hszorig.
      * by [].
    + rewrite addn1. lia.
    + rewrite Zlength_size size_map Hsz1 -Hszorig.
      move: Hi.
      case: (size orig %/ Z.to_nat k) => [//| j].
      rewrite ltnS => Hij.
      rewrite {1}Hkex addn1. to_ssrnat.
      by rewrite leq_pmul2r. 
Qed.

(*From this, we prove the main result we need: for any packet p
  between packets i*k and (i+1)*k in the original list, we can find
  a well-formed, encoded block containing p and all 
  packets i * n to (i+1) * n in the encoded list.*)
Theorem producer_boundaries_i: forall (k h: Z) p orig (i: nat),
(*Some assumptions on the orig stream and parameters for our
    invariants*)
  (0 < k <= fec_n - 1 - fec_max_h)%Z ->
  (0 < h <= fec_max_h)%Z ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) -> 
  p \in sublist (Z.of_nat i * k) (Z.of_nat (i + 1) * k) orig ->
  i < size orig %/ Z.to_nat k ->
  let sent := 
    concat (producer_concat_nochange k h orig).2 in
  let b := nth block_inhab (rev (producer_concat_nochange k h orig).1.1) i in
  b \in (get_blocks sent) /\
  block_encoded b /\
  block_wf b /\
  blk_k b = k /\
  let n := Z.to_nat k + Z.to_nat h in
    (*i < size sent %/ n /\*)
    let l := (sublist (Z.of_nat (i * n)) 
      (Z.of_nat ((i+1) * n)) sent) in
    uniq l /\
    all (fun (p': fpacket) => packet_in_block p' b) l /\
  size sent = (size orig %/ (Z.to_nat k)) * n +
    (size orig %% (Z.to_nat k)) /\
  exists (f: fpacket),
    p_packet f = p /\
    ~~ fd_isParity f /\
    packet_in_block f b.
Proof.
  move=> k h p orig i Hkbound Hhbound Hval Henc Huniqseq Hinp Hi
  sent b.
  have Hallinbounds: (forall k0 h0 : Z,
    (k0, h0) \in zseq (Zlength orig) (k, h) ->
    (0 < k0 <= fec_n - 1 - fec_max_h)%Z /\ (0 < h0 <= fec_max_h)%Z) by
    move=> k' h'; rewrite /zseq mem_nseq => /andP[_ /eqP []]->->.
  have Hsz: size orig = size (zseq (Zlength orig) (k, h)) by
    rewrite size_nseq !size_Zlength. 
  have/=:=(@produce_boundary_h_all (Z.to_nat k) (Z.to_nat h) orig).
  rewrite /produce_boundary_h_invar.
  have:= (producer_all_steps_blocks Hallinbounds Hval Henc Huniqseq Hsz).
  (*Get info about how orig relates to output from 
    [producer_all_steps_sent_data]*)
  have:=(producer_all_steps_sent_data Hsz).
  (*Now get results from [block_boundaries]*)
  have:= (block_boundaries Hkbound Hhbound Hval Henc Huniqseq Hi) => [[Hpackb [Hsubeq[Hszsent Hszblks]]]].
  (*Remove unneeded assumptions and get relevant [producer_props] 
    in context*)
  rewrite {Hallinbounds Hval Henc Hsz}.
  rewrite !(proj1 (producer_all_steps_concat_aux orig _))
    !producer_all_steps_concat -!producer_concat_nochange_eq.
  rewrite !Z2Nat.id; try lia.
  move => Horig [ [Hperm [Hallwf [_ [_ [_ [_ [_ [Henc [Hinprog [Hwf [Huniq Huniqdat]]]]]]]]]]] Hzidx] Hallh.
  (*Now get results from [produce_boundary_invar]*)
  have Hk0: (Z.to_nat k) != 0 by apply /eqP; lia.
  have/=:=(produce_boundary_invar_all (Z.to_nat h) Hk0 orig).
  rewrite !Z2Nat.id; try lia.
  move => [[l [last [Hconcat [Hdatpar [Hlastsome Hlastnone]]]]] [Hallk Hidx]].
  
  have Hisz: i < size (producer_concat_nochange k h orig).1.1. {
    by rewrite Hszblks.
  }
  have Hinb1: b \in (producer_concat_nochange k h orig).1.1. {
    rewrite -mem_rev.
    apply mem_nth. by rewrite size_rev.
  } 
  have Hbin: b \in (block_option_list (producer_concat_nochange k h orig).1) 
    by apply in_block_option_list.
  (*Prove all first*)
  have Hall: all (packet_in_block^~ b)
  (sublist (Z.of_nat (i * (Z.to_nat k + Z.to_nat h)))
     (Z.of_nat ((i + 1) * (Z.to_nat k + Z.to_nat h))) sent). {
    apply /allP => p' Hinp'.
    by rewrite packet_in_block_eq -mem_cat -Hpackb mem_map //;
    apply some_inj.
  }
  (*Also wf*)
  move: Hallwf => /(_ _ Hbin) Hwfb.
  move: Hallk => /(_ _ Hbin) [Hbk Hszdb].
  split_all.
  - by rewrite (perm_mem Hperm).
  - by apply Henc.
  - by [].
  - by rewrite Hbk Z2Nat.id //; lia.
  - by apply uniq_sublist.
  - by [].
  - by []. 
  - move: Hinp. rewrite Hsubeq => /mapP [f Hfin Hpf].
    exists f. 
    have Hinf: packet_in_data f b. {
      rewrite /packet_in_data.
      apply (f_equal (sublist 0 k)) in Hpackb.
      move: Hpackb.
      rewrite sublist_map sublist_app1; try lia; last by
        rewrite Zlength_size Hszdb; lia.
      rewrite (sublist_same 0 k (data_packets _)); try lia;
        last by rewrite Zlength_size Hszdb; lia.
      move <-. apply /mapP. by exists f.
    }
    (*This gives us everything we need*)
    split_all =>//; last by apply data_in_block.
    apply negbT. by apply Hwfb.
Qed.

(*One additional result we need from the invariant:
  if two packets in the encoded stream have the same blockId,
  their index is separated by at most k+h*)
Lemma same_block_index: forall (k h : Z) (orig: seq packet) (p1 p2: fpacket),
  (*Need full invariant for knowing that blockIDs are unique*)
  (0 < k <= fec_n - 1 - fec_max_h)%Z ->
  (0 < h <= fec_max_h)%Z ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  let encoded := (concat (producer_concat_nochange k h orig).2) in
  p1 \in encoded ->
  p2 \in encoded ->
  fd_blockId p1 = fd_blockId p2 ->
  nat_abs_diff (index p1 encoded) (index p2 encoded) <= Z.to_nat k + Z.to_nat h.
Proof.
  (*Lots of boilerplate to get assumptions we need*)
  move=> k h orig p1 p2 Hkbound Hhbound Hval Henc Huniqseq/=.
  have Hallinbounds: (forall k0 h0 : Z,
    (k0, h0) \in zseq (Zlength orig) (k, h) ->
    (0 < k0 <= fec_n - 1 - fec_max_h)%Z /\ (0 < h0 <= fec_max_h)%Z) by
    move=> k' h'; rewrite /zseq mem_nseq => /andP[_ /eqP []]->->.
  have Hsz: size orig = size (zseq (Zlength orig) (k, h)) by
    rewrite size_nseq !size_Zlength.
  have/=:=(@produce_boundary_h_all (Z.to_nat k) (Z.to_nat h) orig).
  rewrite /produce_boundary_h_invar.
  have:= (producer_all_steps_blocks Hallinbounds Hval Henc Huniqseq Hsz).
  rewrite {Hallinbounds Hval Henc Hsz}.
  rewrite !(proj1 (producer_all_steps_concat_aux orig _))
    !producer_all_steps_concat -!producer_concat_nochange_eq.
  rewrite !Z2Nat.id; try lia.
  move => [ [Hperm [Hallwf [_ [_ [_ [_ [_ [Henc [Hinprog [Hwf [Huniq Huniqdat]]]]]]]]]]] Hzidx] Hallh.
  (*Now get results from [produce_boundary_invar]*)
  have Hk0: (Z.to_nat k) != 0 by apply /eqP; lia.
  have/=:=(produce_boundary_invar_all (Z.to_nat h) Hk0 orig).
  rewrite !Z2Nat.id; try lia.
  move => [[l [last [Hconcat [Hdatpar [Hlastsome Hlastnone]]]]] [Hallk Hidx]].
  (*Now the real proof starts*)
  rewrite Hconcat. 
  (*Need to know either both are in [concat l] or both are in [last]*)
  (*Idea: if one is in last, its blockId is id of last block
    If other is in [concat l], there is some block in 
    past blocks with the same id. Result follows from [get_blocks]
    invariant and uniqueness of blocks by id*)
  have Hnoids: forall (p1 p2 : fpacket), 
    p1 \in concat l -> p2 \in last ->
    fd_blockId p1 <> fd_blockId p2. {
    move=> p1' p2'. move: Hperm. rewrite Hconcat.
    case Hlast: ((producer_concat_nochange k h orig).1.2) => [bl | ]; 
      last by move: Hlastnone => /(_ Hlast) ->//.
    move: Hlastsome => /(_ bl Hlast) [filled [Hdatbl Hlastfill]].
    subst => Hperm Hp1' Hp2'.
    (*Deal with packet in last*)
    have Hinp2b: packet_in_data p2' bl. {
      rewrite /packet_in_data Hdatbl mem_cat. apply /orP; left.
      apply /mapP. by exists p2'.
    }
    have->:fd_blockId p2' = blk_id bl. apply (get_blocks_ids Hwf)=>//.
      by rewrite Hconcat (perm_mem Hperm) /block_option_list/= mem_head.
      by apply data_in_block.
    (*Deal with packet in [concat l]*)
    have:=Hp1'; rewrite concat_flatten =>/flattenP [l2] Hinl2 Hinp1l2.
    have: (map Some l2) \in [seq [seq Some i | i <- l1] | l1 <- l] by
      apply /mapP; exists l2.
    rewrite Hdatpar => /mapP [b1].
    rewrite mem_rev => Hb1 Hdatb1.
    have Hinp1b: packet_in_block p1' b1 by
      rewrite packet_in_block_eq -mem_cat -Hdatb1; 
      apply /mapP; exists p1'.
    have->:fd_blockId p1' = blk_id b1 by apply (get_blocks_ids Hwf)=>//;
      rewrite Hconcat (perm_mem Hperm) /block_option_list/= 
      in_cons Hb1 orbT.
    (*Now, use fact that [get_blocks] is unique by blockId*)
    have:=(get_blocks_id_uniq Hwf).
    rewrite Hconcat. (*apply (perm_map blk_id) in Hperm.*)
    rewrite (perm_uniq (perm_map blk_id Hperm)) /block_option_list/=
      => /andP[Hnotin _].
    case: (blk_id b1 == blk_id bl) /eqP =>//= Heqid.
    rewrite -Heqid in Hnotin. exfalso.
    move: Hnotin => /mapP/=; apply. by exists b1.
  }
  rewrite !mem_cat => /orP[Hinp1l | Hp1last] /orP[Hinp2l | Hp2last] Heqid; last first.
  2 : { by exfalso; apply (Hnoids p2 p1). }
  2 : { by exfalso; apply (Hnoids p1 p2). }
  - (*Case for last is easier - know size of last*)
    rewrite !index_cat.
    case Hinp1l: (p1 \in concat l); first by
      exfalso; apply (Hnoids p1 p1).
    case Hinpl2: (p2 \in concat l); first by
      exfalso; apply (Hnoids p2 p2).
    rewrite nat_abs_diff_add.
    apply (leq_trans (index_diff_le_size _ _ _)).
    case Hlast: ((producer_concat_nochange k h orig).1.2) => [bl | ]; 
    last by move: Hlastnone=> /(_ Hlast)->//.
    move: Hlastsome => /(_ bl Hlast) [filled [Hdatbl Hlastfill]].
    subst. 
    have Hle: size filled <= size (data_packets bl) by
      rewrite Hdatbl size_cat size_map leq_addr.
    apply (leq_trans Hle).
    have->: size (data_packets bl) = Z.to_nat k by apply Hallk;
      rewrite Hlast/block_option_list/= mem_head.
    by rewrite leq_addr.
  - (*Otherwise, we need to get the block that the packets are in
      and show it is the same*)
    move: Hinp1l Hinp2l. rewrite !concat_flatten => Hin1 Hin2.
    rewrite !index_cat Hin1 Hin2.
    (*Need info about both packets, so do separately*)
    have Hgetb: forall (p: fpacket), p \in flatten l ->
      exists l1 b1,
        l1 \in l /\
        p \in l1 /\
        b1 \in (producer_concat_nochange k h orig).1.1 /\
        [seq Some i | i <- l1] = data_packets b1 ++ parity_packets b1 /\
        packet_in_block p b1. {
      move=> p /flattenP [l1] Hinl1 Hinpl1. exists l1.
      have: map Some l1 \in [seq [seq Some i | i <- l1] | l1 <- l] by
        apply /mapP; exists l1.
      rewrite Hdatpar=> /mapP [b1]. rewrite mem_rev => Hinb1 Hbl1.
      exists b1. split_all=>//. 
      by rewrite packet_in_block_eq -mem_cat -Hbl1; 
        apply /mapP; exists p.
    }
    have [l1 [b1 [Hinl1 [Hinp1 [Hinb1 [Hlb1 Hinpb1]]]]]]:=
      (Hgetb p1 Hin1).
    have [l2 [b2 [Hinl2 [Hinp2 [Hinb2 [Hlb2 Hinpb2]]]]]]:=
      (Hgetb p2 Hin2).
    have Hgb1: b1 \in 
      get_blocks (concat (producer_concat_nochange k h orig).2) by
      rewrite (perm_mem Hperm); apply in_block_option_list.
    have Hgb2: b2 \in 
      get_blocks (concat (producer_concat_nochange k h orig).2) by
      rewrite (perm_mem Hperm); apply in_block_option_list.
    have Heqb: b1 = b2. {
      apply (map_uniq_inj (get_blocks_id_uniq Hwf))=>//.
      by rewrite -(get_blocks_ids Hwf Hgb1 Hinpb1) 
      -(get_blocks_ids Hwf Hgb2 Hinpb2).
    }
    subst. rewrite {Hgb2 Hinb2}.
    have Heql: l1 = l2. {
      have: [seq Some i | i <- l1] = [seq Some i | i <- l2] by 
        rewrite Hlb1 Hlb2.
      move=> Heq. apply (f_equal (pmap id)) in Heq.
      by rewrite !map_pK in Heq.
    } subst.
    rewrite {Hlb2 Hinl2}.
    have Huniq': uniq (flatten l). {
      move: Huniq. 
      by rewrite Hconcat concat_flatten cat_uniq => /andP []->.
    }
    apply (leq_trans (index_flatten_same Hinp1 Hinp2 Hinl1 Huniq')).
    rewrite -(size_map Some) Hlb1 size_cat.
    have->:size (data_packets b2) = Z.to_nat k by apply Hallk;
      apply in_block_option_list.
    by have->:size(parity_packets b2) = Z.to_nat h by apply Hallh;
      apply in_block_option_list.
Qed.

(*We need some bounds of the resulting integer values*)
Section Bounds.

(*First, show all block k and h values are from the input*)

Lemma producer_block_kh (orig: seq packet) (params: seq (Z * Z)) (b: block) :
  size orig = size params ->
  b \in block_option_list (producer_all_steps orig params).1 ->
  (blk_k b, blk_h b) \in params.
Proof.
  move=> Hsz.
  (*First, switch to foldr*)
  rewrite /producer_all_steps -(revK (combine _ _)) foldl_rev -zip_combine rev_zip // {Hsz}.
  rewrite -(mem_rev params).
  move: (rev orig) => o.
  move: (rev params) => p.
  rewrite {orig params}. 
  move: p b. elim: o => [//= p b | curr pkts /= IH [|phd ptl/=] b]; first by
    rewrite zip_nil.
    by rewrite zip_nil_r.
  move: IH => /(_ ptl).
  move: ((foldr
  (fun (x : packet * (Z * Z))
     (z : seq block * option block * seq fpacket) =>
   ((producer_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).1.1,
   (producer_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).1.2,
   z.2 ++ (producer_one_step z.1.1 z.1.2 x.1 x.2.1 x.2.2).2))
  ([::], None, [::]) (zip pkts ptl)).1) => blks.
  rewrite /block_option_list/= /producer_one_step.
  (*Lots of tedious cases: do a few here*)
  move=> IH.
  have: forall b, b \in blks.1 -> (blk_k b, blk_h b) \in (phd :: ptl). {
    move: IH. case: blks => [blks [currb |]/= IH b' Hinb']; 
    rewrite in_cons IH //; try by rewrite orbT.
    by rewrite in_cons Hinb' orbT.
  }
  have: forall curr, blks.2 = Some curr -> (blk_k curr, blk_h curr) \in
    (phd :: ptl). {
      move: IH. case: blks=>[blks [currb | //]/= IH currb' []<-].
      rewrite in_cons IH. by rewrite orbT. by rewrite mem_head.
  }
  move: IH.
  case: blks => [blks [currb |]/=] IH.
  - move=> /(_ currb erefl) Hcurr Hallin.  
    (*Repeated case*)
    have Hnew: b
      \in match (produce_new curr phd.1 phd.2).1.2 with
        | Some b0 =>
            b0
            :: (produce_new curr phd.1 phd.2).1.1 ++
              (encode_block currb None).1 :: blks
        | None =>
            (produce_new curr phd.1 phd.2).1.1 ++
            (encode_block currb None).1 :: blks
        end -> (blk_k b, blk_h b) \in phd :: ptl. {
      rewrite /produce_new. (*same proof*)
      case: Z.eq_dec=>Hk1/=;rewrite in_cons in_cons => /orP[/eqP -> | /orP[/eqP -> | Hinb]];
      try (by rewrite encode_block_k encode_block_h/= mem_head);
      try (by rewrite encode_block_k encode_block_h);
      try (by rewrite Hallin).
      by rewrite mem_head.
    }
    case: Z.eq_dec => Hkeq//=.
    case: Z.eq_dec=> Hheq//=.
    rewrite /produce_exist/=.
    case: Z.eq_dec=>/= _.
    + rewrite in_cons => /orP[/eqP -> | Hinb]; last by
      apply Hallin.
      by rewrite encode_block_k encode_block_h
      add_red_k add_red_h.
    + rewrite in_cons => /orP[/eqP -> | Hinb]; last by
      apply Hallin.
      by rewrite add_red_k add_red_h.
  - move=> _ Hallin.
    rewrite /produce_new/=.
    case: Z.eq_dec=>Hk1/=.
    + rewrite in_cons => /orP[/eqP -> | Hinb]; last by apply Hallin.
      by rewrite encode_block_k encode_block_h/= mem_head.
    + rewrite in_cons=> /orP[/eqP-> /= | Hinb]; last by apply Hallin.
      by rewrite mem_head.
Qed.

(*Then, get the bounds we need:*)
Local Open Scope Z_scope.

(*These bounds are weak, actually the blockIndex is bounded by
  fec_max_n and k is bounded by fec_max_k. But these bounds suffice
  for what we need.*)
Lemma encoder_bounds (orig: list packet) (params: list (Z * Z)) :
(forall k h, (k, h) \in params -> 
  (0 < k <= ByteFacts.fec_n - 1 - ByteFacts.fec_max_h /\
  0 < h <= ByteFacts.fec_max_h)) ->
  (forall p, p \in orig -> packet_valid p) ->
  (forall p, p \in orig -> encodable p) ->
  uniq (map p_seqNum orig) ->
  size orig = size params ->
  (forall (p: packet), p \in orig ->
    Z.of_nat (p_seqNum p) < Int64.half_modulus) ->
  forall (p: fpacket), p \in (producer_all_steps orig params).2 ->
  Z.of_nat (fd_blockId p) < Int64.half_modulus /\
  Z.of_nat (fd_blockIndex p) <= Int.max_unsigned /\ 
  0 <= fd_k p < Int.modulus.
Proof.
  move=> Hparams Hallval Hallenc Huniq Hsz Hseqbound p Hinp.
  have [[Hperm [_ [_ [_ [_ [Hinorig [Hids [_ [_ [Hwf _]]]]]]]]]] _]:=
    (producer_all_steps_blocks Hparams Hallval Hallenc Huniq Hsz).
  (*For many of these, need block that p is in and use WF assumptions
    to relate p's metadata to block metadata*)
  have [b /andP[Hinbs Hinpb]]:=(get_blocks_allin Hwf Hinp).
  split.
  - move: Hids => /(_ b).
    rewrite -(perm_mem Hperm) => /(_ Hinbs) [p' [Hinp' Hidp']].
    rewrite (get_blocks_ids Hwf Hinbs Hinpb) Hidp'.
    apply Hseqbound.
    apply (Hinorig b p')=>//.
    by rewrite -(perm_mem Hperm).
  - (*First, do k bound - use [producer_block_kh] and bounds on
      params*)
    have[Hkeq Hheq]:=(get_blocks_kh Hwf Hinp Hinbs 
    (get_blocks_ids Hwf Hinbs Hinpb)).
    have [Hk Hh]: (0 <= fd_k p <= fec_n - 1 - fec_max_h) /\ 
      0 <= fd_h p <= fec_max_h. {
      rewrite Hkeq Hheq.
      rewrite (perm_mem Hperm) in Hinbs.
      have:=(producer_block_kh Hsz Hinbs) => Hin.
      move: Hparams => /(_ _ _ Hin). rep_lia.
    }
    split; last by rep_lia.
    (*Now we bound block_index by k*)
    have: Z.of_nat (fd_blockIndex p) < fd_k p + fd_h p; try rep_lia.
    by apply Hwf.
Qed.

End Bounds.