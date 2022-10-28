Require Import AbstractEncoderDecoder.
Require Import DecoderGeneric.
Require Import VST.floyd.functional_base.
Require Import ByteFacts.
Require Import Block.


From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.

Definition triv_upd_time : Z -> fpacket -> list block -> Z :=
  fun z _ _ => 0.

Definition triv_timeout : Z -> block -> bool :=
  fun _ _ => true.

Definition decoder_one_step_nto :=
  decoder_one_step_gen triv_upd_time triv_timeout.

Definition decoder_multiple_steps_nto:=
  decoder_multiple_steps_gen triv_upd_time triv_timeout.
Definition decoder_all_steps_nto:=
  decoder_all_steps_gen triv_upd_time triv_timeout.

(*First we prove that with this decoder, it doesn't matter what
  time updating mechanism you use as long as you never timeout.
  Neither the intermediate functions nor the state are affected
  beyond just having different time information.*)
Section TimeDoesntMatter.

(*This is not quite as trivial as it may appear, since we need to prove
  that all the intermediate steps (creating/adding to blocks, decoding,
  etc) are all not affected by time.*)

(*An obvious lemma but one that doesn't just compute automatically*)
Lemma black_time_eq: forall b1 b2,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  blk_id b1 = blk_id b2 /\
  data_packets b1 = data_packets b2 /\
  parity_packets b1 = parity_packets b2 /\
  blk_k b1 = blk_k b2 /\
  blk_h b1 = blk_h b2 /\
  black_complete b1 = black_complete b2.
Proof.
  by move=> [id1 dat1 par1 k1 h1 comp1 t1] [id2 dat2 par2 k2 h2 comp2 t2] []/=.
Qed.

Lemma block_eq: forall b1 b2,
  blk_id b1 = blk_id b2 ->
  data_packets b1 = data_packets b2 ->
  parity_packets b1 = parity_packets b2 ->
  blk_k b1 = blk_k b2 ->
  blk_h b1 = blk_h b2 ->
  black_complete b1 = black_complete b2 ->
  black_time b1 = black_time b2 ->
  b1 = b2.
Proof.
  by move=> [id1 dat1 par1 k1 h1 comp1 t1] 
  [id2 dat2 par2 k2 h2 comp2 t2]/=->->->->->->->.
Qed.

Lemma create_black_time_eq: forall p t1 t2,
  (create_block_with_packet_black p t1).1 <| black_time := 0 |> =
  (create_block_with_packet_black p t2).1 <| black_time := 0 |>.
Proof.
  move=> p t1 t2/=. by case: (Z.eq_dec (fd_k p) 1).
Qed.

Lemma add_fec_packet_time_eq: forall b1 b2 p,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  (add_fec_packet_to_block p b1) <| black_time := 0 |> =
  (add_fec_packet_to_block p b2) <| black_time := 0 |>.
Proof.
  move=> b1 b2 p Heq.
  have [Hid [Hdat [Hpar [Hk [Hh Hcomp]]]]] := (black_time_eq Heq).
  rewrite /add_fec_packet_to_block Hk Hh Hdat Hpar.
  by apply block_eq.
Qed.

Lemma recoverable_time_eq: forall b1 b2,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  recoverable b1 = recoverable b2.
Proof.
  move=> b1 b2 Heq.
  have [Hid [Hdat [Hpar [Hk [Hh Hcomp]]]]] := (black_time_eq Heq).
  rewrite /recoverable.
  by rewrite Hdat Hpar.
Qed.

Lemma add_black_time_eq: forall b1 b2 p,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  (add_packet_to_block_black p b1).1 <| black_time := 0 |> =
  (add_packet_to_block_black p b2).1 <| black_time := 0 |>.
Proof.
  move=> b1 b2 p Heq.
  have [Hid [Hdat [Hpar [Hk [Hh Hcomp]]]]] := (black_time_eq Heq).
  rewrite /add_packet_to_block_black.
  rewrite Hcomp. case: (black_complete b2)=>/=.
  - by apply add_fec_packet_time_eq.
  - rewrite (@recoverable_time_eq _ (add_fec_packet_to_block p b2));
    last by apply add_fec_packet_time_eq.
    case: (recoverable (add_fec_packet_to_block p b2)).
    + by apply block_eq=>//=; rewrite Hk Hdat Hpar // Hh.
    + by apply add_fec_packet_time_eq.
Qed.

(*[decoder_list_block] is not affected by times*)
Lemma decoder_list_block_time_eq:  forall b1 b2,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  decoder_list_block b1 = decoder_list_block b2.
Proof.
  move=> b1 b2 Heq.
  have [Hid [Hdat [Hpar [Hk [Hh Hcomp]]]]] := (black_time_eq Heq).
  rewrite /decoder_list_block. f_equal=>//=.
  - by rewrite /blk_c Hpar Hdat.
  - by rewrite /packet_mx Hdat.
  - by rewrite /parity_mx Hpar.
  - by rewrite /stats Hdat.
  - by rewrite /lengths/blk_c Hpar Hdat .
  - by rewrite /find_decoder_list_param Hpar Hdat.
Qed.

(*[decode_block] is not affected by times*)
Lemma decode_block_time_eq: forall b1 b2,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  decode_block b1 = decode_block b2.
Proof.
  move=> b1 b2 Heq.
  have [Hid [Hdat [Hpar [Hk [Hh Hcomp]]]]] := (black_time_eq Heq).
  by rewrite /decode_block Hdat (decoder_list_block_time_eq Heq) Hk.
Qed. 

Lemma add_black_time_eq_packets:  forall b1 b2 p,
  b1 <| black_time := 0 |> =
  b2 <| black_time := 0 |> ->
  (add_packet_to_block_black p b1).2 =
  (add_packet_to_block_black p b2).2.
Proof.
  move=> b1 b2 p Heq.
  have [Hid [Hdat [Hpar [Hk [Hh Hcomp]]]]] := (black_time_eq Heq).
  rewrite /add_packet_to_block_black.
  rewrite Hcomp. case: (black_complete b2)=>//=. f_equal.
  rewrite (@recoverable_time_eq _ (add_fec_packet_to_block p b2));
    last by apply add_fec_packet_time_eq.
  case: (recoverable (add_fec_packet_to_block p b2))=>//.
  apply decode_block_time_eq.
  by apply add_fec_packet_time_eq.
Qed.

(*Any timing mechanism will result in the same output if we never
  timeout packets*)

Lemma decoder_notimeout_upd_time:
  forall u1 u2 blks1 blks2 prev packs time1 time2 sent,
  map (fun b => b <| black_time := 0 |>) blks1 =
  map (fun b => b <| black_time := 0|> ) blks2 ->
  (decoder_multiple_steps_gen u1 triv_timeout prev 
    packs blks1 sent time1).1.1.2 =
  (decoder_multiple_steps_gen u2 triv_timeout prev 
    packs blks2 sent time2).1.1.2.
Proof.
  move=> u1 u2 blks1 blks2 prev packs. move: blks1 blks2 prev.
  rewrite /decoder_multiple_steps_gen.
  elim: packs => [//= | p ptl /= 
    IH blks1 blks2 prev time1 time2 sent Heqblks].
  (*All of the interesting stuff is in this proof, we separate it
    to reduce duplication*)
  have [Hupd1 Hupd2]: 
  (update_dec_state_gen blks1 p (u1 time1 p blks1)).2 =
  (update_dec_state_gen blks2 p (u2 time2 p blks2)).2 /\
  [seq b <| black_time := 0 |>
    | b <- (update_dec_state_gen blks1 p (u1 time1 p blks1)).1] =
  [seq b <| black_time := 0 |>
    | b <- (update_dec_state_gen blks2 p (u2 time2 p blks2)).1]. {
    rewrite {IH}.
    move: (u1 time1 p blks1) => t1.
    move: (u2 time2 p blks2) => t2.
    clear -Heqblks.
    move: blks2 t1 t2 Heqblks. elim: blks1 => 
      [// [//= | bhd2 btl2 //] t1 t2 _ | bhd1 btl1 /= IH].
    - split; f_equal. 
      apply create_black_time_eq. 
    - move=> [// | bhd2 btl2 /= t1 t2  Heq].
      apply cons_inv in Heq. case: Heq => [Hhd Htl].
      have Hideq: blk_id bhd1 = blk_id bhd2 by apply black_time_eq.
      rewrite -!Hideq.
      case: (fd_blockId p == blk_id bhd1) /eqP => Heq/=.
      + rewrite /=. f_equal=>//. split. by apply add_black_time_eq_packets.
        f_equal=>//. by apply add_black_time_eq.
      + case Hlt: (fd_blockId p < blk_id bhd1)%N.
        * rewrite /=. split=>//. f_equal=>//. apply create_black_time_eq.
          by f_equal.
        * rewrite /=. split. by apply IH. f_equal=>//. by apply IH.
  }
  (*The rest of the proof is basically trivial*)
  rewrite (IH _ ((update_dec_state_gen
  [seq x <- blks2 | triv_timeout (u2 time2 p blks2) x] p
  (u2 time2 p blks2)).1) _ _ (u2 time2 p blks2) _ ) // {IH}
  /triv_timeout/= !filter_predT/=.
  - by rewrite Hupd1.
  - by rewrite Hupd2.
Qed.

(*Lift this result to all packets*)
Lemma decoder_notimeout_upd_time_all:
  forall u1 u2 packs,
  (decoder_all_steps_gen u1 triv_timeout packs).1.2 =
  (decoder_all_steps_gen u2 triv_timeout packs).1.2.
Proof.
  move=> u1 u2 packs. rewrite /decoder_all_steps_gen.
  by apply decoder_notimeout_upd_time.
Qed.

End TimeDoesntMatter.

(*Now we need to prove the main result: all packets of recoverable,
  encoded blocks are recovered. First, we need an invariant and
  several results*)
Section AllRecovered.

Local Open Scope nat_scope.

Definition decoder_nto_invar (blks: seq block) (prev: list fpacket) 
  (output: list packet) : Prop :=
  (*blks sorted by blk_id in strictly increasing order*)
  sorted blk_order blks /\
  (*Each block is subblock of block in (get_blocks prev)*)
  (forall b, b \in blks -> exists b', b' \in (get_blocks prev) /\
  subblock b b') /\
  (*All previous packets are stored in blocks (note: this is
    where having no timeouts is crucial)*)
  (forall (p: fpacket), p \in prev -> 
    exists b, b \in blks /\ packet_in_block p b) /\
  (*All data packets are in output*)
  (forall (p: fpacket), p \in prev ->
    ~~ fd_isParity p -> p_packet p \in output).

Lemma decoder_nto_invar_pres: forall blks prev output time p,
  wf_packet_stream (prev ++ [:: p]) ->
  decoder_nto_invar blks prev output ->
  decoder_nto_invar (decoder_one_step_nto blks p time).1.1
    (prev ++ [:: p]) (output ++ (decoder_one_step_nto blks p time).1.2).
Admitted.

Lemma decoder_nto_invar_multiple: forall blks prev output time rec,
  wf_packet_stream (prev ++ rec) ->
  decoder_nto_invar blks prev output ->
  decoder_nto_invar (decoder_multiple_steps_nto prev rec blks output time).1.1.1
    (prev ++ rec) (decoder_multiple_steps_nto prev rec blks output time).1.1.2.
Proof.
  move=> blks prev output time rec Hwf Hinvar.
  rewrite -(prev_packets_multiple triv_upd_time triv_timeout prev rec blks output time).
  rewrite /decoder_multiple_steps_nto.
  move: blks prev output time Hwf Hinvar. 
  elim: rec=>[// | curr tl /= IH blks prev output time Hwf Hinvar].
  apply IH=>//=. by rewrite -catA.
  apply decoder_nto_invar_pres=>//.
  apply (wf_substream Hwf). move=> x.
  by rewrite !mem_cat!in_cons!orbF orbA=>->.
Qed.

Lemma decoder_nto_invar_all: forall rec,
  wf_packet_stream rec ->
  decoder_nto_invar (decoder_all_steps_nto rec).1.1
    rec (decoder_all_steps_nto rec).1.2.
Proof.
  move=> rec Hwf. rewrite /decoder_all_steps_nto.
  by apply decoder_nto_invar_multiple.
Qed.



(*Suppose there are at least unique k items in a list in another list. 
  Then, we can find the point at which the kth
  unique item appears.*)
Section FindLast.
(*TODO: move most of this?*)
(*Alternate induction principle for lists - adding to the end*)
Lemma seq_ind' {A: Type} (P: seq A -> Prop):
  P nil ->
  (forall (a: A) (l: seq A), P l -> P (rcons l a)) ->
  forall l: seq A, P l.
Proof.
  move=> Pnil Prcons l.
  rewrite -(revK l).
  elim: (rev l) =>//= h t Hp.
  rewrite rev_cons. by apply Prcons.
Qed.

Lemma filter_partition_perm: forall {A: eqType} (p: pred A) (s: seq A),
  perm_eq s ([seq x <- s | p x] ++ [seq x <- s | predC p x]).
Proof.
  move=> A p s. by have:=(perm_filterC p s) => /(_ s);
  rewrite perm_refl perm_sym.
Qed.

Lemma count_perm: forall {A: eqType} (p: pred A) (s1 s2: seq A),
  perm_eq s1 s2 ->
  count p s1 = count p s2.
Proof. 
  by move=> A p s1 s2 /permP => /(_ p).
Qed.

Lemma filter_pred1_uniq' {A: eqType} (s: seq A) (x: A):
  uniq s ->
  [seq x0 <- s | pred1 x x0] = if x \in s then [:: x] else nil.
Proof.
  elim:s => [// | h t /= IH /andP[Hnotin Huniq]].
  rewrite in_cons (eq_sym x h).
  case: (h == x) /eqP =>//= Hhx; subst.
  - by rewrite IH // (negbTE Hnotin).
  - by apply IH.
Qed. 

(*Surprisingly tricky to prove: if at least k unique items satisfy
  a predicate, we can identify the first ocurrence of the kth such
  item.*)
Lemma find_kth_item {A: eqType} (p: pred A) (k: nat) (s: seq A) :
  k != 0 ->
  count p (undup s) >= k ->
  exists l1 x l2,
    s = l1 ++ [:: x] ++ l2 /\
    count p (undup l1) = k - 1 /\
    p x /\
    x \notin l1.
Proof.
  rewrite -count_rev.
  (*want to go backwards over the list, so we can tell when we find x*)
  move: s k. induction s as [| h t IH] using seq_ind' =>/= k Hk0.
  - by rewrite leqn0 (negbTE Hk0).
  - rewrite undup_rcons rev_rcons/=.
    have Hcounteq: count p (rev (undup t)) = 
      count p [seq y <- undup t | y != h] + ((h \in t) && p h). {
      erewrite count_perm; last first.
      eapply perm_trans. rewrite perm_sym. apply perm_rev'.
      apply (filter_partition_perm (fun x => x != h)).
      rewrite count_cat/=. f_equal.
      rewrite (@eq_in_filter _ _ (pred1 h)).
      - rewrite filter_pred1_uniq'; last by apply undup_uniq.
        rewrite mem_undup.
        case Hin: (h \in t)=>//=.
        by rewrite addn0.
      - move=> x _. by rewrite negbK.
    }
    case Hinht: (h \in t).
    + rewrite count_rev => Hk. 
      (*In this case, we have the condition for the IH, which we need
        because h cannot be the first occurrence of the kth item*)
      have Hk': k <= count p (rev (undup t)) by
        rewrite Hcounteq Hinht/= addnC.
      move: IH => /(_ k Hk0 Hk') [l1 [x [l2 [Ht [Hcount [Hpx Hx]]]]]].
      exists l1. exists x. exists (rcons l2 h). split_all=>//.
      rewrite Ht. by rewrite rcons_cat.
    + (*Now we know this is a new element, but we need to see
      if it satisfies the predicate or not*)
      move: Hcounteq.
      case Hh: (p h)=>/=; last first.
        rewrite andbF addn0 add0n
        (count_rev _ (filter _ _)) => <-=> Hk.
        (*If not, the IH gives the result easily*)
        move: IH => /(_ k Hk0 Hk) [l1 [x [l2 [Ht [Hcount [Hpx Hx]]]]]].
        exists l1. exists x. exists (rcons l2 h). split_all=>//.
        by rewrite Ht rcons_cat.
      (*Now see if h is the kth item or not*)
      rewrite andbT Hinht addn0 (count_rev _ (filter _ _)) => <-.
      rewrite addnC addn1 leq_eqVlt ltnS => /orP[/eqP | Hk]; last first.
        (*If not, again use IH*)
        move: IH => /(_ k Hk0 Hk) [l1 [x [l2 [Ht [Hcount [Hpx Hx]]]]]].
        exists l1. exists x. exists (rcons l2 h). split_all=>//.
        by rewrite Ht rcons_cat.
      (*In this case, h is the kth item*)
      move => Hk. exists t. exists h. exists nil.
      split_all=>//.
      * by rewrite cats1.
      * by rewrite Hk count_rev subn1 -pred_Sn.
      * by rewrite Hinht.
Qed.

Lemma perm_catC': forall [T : eqType] (s1 s2 : seq T), 
  perm_eq (s1 ++ s2) (s2 ++ s1).
Proof.
  move=> T s1 s2. by have:=(perm_catC s1 s2) => /(_ (s2 ++ s1));
  rewrite perm_refl.
Qed.

Lemma filter_orb_perm: forall {A: eqType} (s: seq A) (p1 p2: pred A),
  (forall x, ~~((p1 x) && (p2 x))) ->
  perm_eq [seq x <- s | p1 x || p2 x] 
    ([seq x <- s | p1 x] ++ [seq x <- s | p2 x]).
Proof.
  move=> A s p1 p2 Hp. elim: s => [// | h t /= IH].
  case Hp1: (p1 h)=>//=.
  - case Hp2: (p2 h)=>//=; last by rewrite perm_cons.
    exfalso. apply (negP (Hp h)). by rewrite Hp1 Hp2.
  - case Hp2: (p2 h)=>//=.
    eapply perm_trans; last by apply perm_catC'.
    rewrite /= perm_cons. apply (perm_trans IH).
    apply perm_catC'.
Qed.

Lemma perm_filter_in_cons: forall {A: eqType} (s: seq A) (h: A) (t: seq A),
  h \notin t ->
  perm_eq [seq x <- s | x \in h :: t] 
    ([seq x <- s | x == h] ++ [seq x <- s | x \in t]).
Proof.
  move=> A s h t Hnotin.
  rewrite (@eq_in_filter _ _ (fun x => (x == h) || (x \in t))); 
  last by move=> x; rewrite !in_cons.
  apply filter_orb_perm => x.
  by case: (x == h) /eqP => //= Hxh1; subst.
Qed.

Lemma double_cons_cat {A: Type} (x1 x2: A) (s: seq A):
  x1 :: x2 :: s = [:: x1; x2] ++ s.
Proof.
  by [].
Qed.

(*The number of unique items in s1 that are in s2 equals
  the number of unique items in s2 that are in s1*)
Lemma num_uniq_same {A: eqType} (s1 s2: seq A):
  uniq s1 ->
  uniq s2 ->
  perm_eq [seq x <- s1 | x \in s2]
  [seq x <- s2 | x \in s1].
Proof.
  move: s2. elim: s1 => [// [|h2 t2]//= _ _ | 
    h1 t1 IH [//= _ _ | h2 t2 /andP[Hnot1 Hun1] /andP[Hnot2 Hun2]]].
  - rewrite perm_sym. apply /perm_nilP.
    apply /eqP. rewrite -(negbK (_ == _)) -has_filter.
    by apply /hasP => [[x]].
  - apply /perm_nilP.
    apply /eqP.  rewrite -(negbK (_ == _)) -has_filter.
    by apply /hasP => [[x]].
  - apply (perm_trans (perm_filter_in_cons (h1 :: t1) Hnot2)).
    eapply perm_trans; last by rewrite perm_sym; 
    apply (perm_filter_in_cons (h2 :: t2) Hnot1).
    rewrite !filter_pred1_uniq' //; try by apply /andP.
    rewrite /= !in_cons eq_sym.
    case: (h1 == h2) /eqP =>/= Heq; subst.
    + rewrite (negbTE Hnot1) (negbTE Hnot2) perm_cons.
      by apply IH.
    + case Hh21: (h2 \in t1)=>/=;
      case Hh12: (h1 \in t2)=>/=; try rewrite perm_cons; 
      try by apply IH.
      rewrite double_cons_cat (double_cons_cat h1 h2).
      apply perm_cat; last by apply IH.
      (*This one we can prove from first principles*)
      apply /allP=>/= x; rewrite !in_cons orbF !(eq_sym h2 x) 
        !(eq_sym h1 x).
      by case: (x == h2); case: (x == h1).
Qed.

(*Lift the previous result to a slightly different setting, 
  in which at least k unique items in s1 (in which everything
  satisfies p) are in s2, and we find the kth item satisfying p*)
Lemma find_kth_item_in {A: eqType} (p: pred A) (k: nat) (s1 s2: seq A) :
  k != 0 ->
  all p s1 ->
  (count (fun (x: A) => x \in s2) (undup s1)) >= k ->
  exists l1 x l2,
    s2 = l1 ++ [:: x] ++ l2 /\
    count p (undup l1) = k - 1 /\
    p x /\
    x \notin l1.
Proof.
  move=> Hk0 Hall Hk.
  apply find_kth_item=>//.
  apply (leq_trans Hk).
  (*Now we have to prove that the number of unique elements in s1
    that are in s2 is at most the number of unique elements in s2
    satisfying p. This holds because every element in s1 satisfies p,
    but it is not the easiest to show.*)
  have Hperm := (filter_partition_perm (fun x => x \in mem s1) (undup s2)).
  rewrite (count_perm _ Hperm) count_cat/=.
  have /eqP->: count p [seq x <- undup s2 | x \in mem s1] ==
    size [seq x <- undup s2 | x \in mem s1]. {
    rewrite -all_count. apply /allP => x. 
    rewrite !mem_filter=> /andP[Hins1 Hins2].
    by move: Hall => /allP/(_ x Hins1).
  }
  rewrite -size_filter.
  rewrite (@eq_in_filter _ (fun x => x \in s2) 
    (fun x => x \in (undup s2))); last by
    move=> x; rewrite !mem_undup.
  rewrite (perm_size (num_uniq_same (undup_uniq s1) (undup_uniq s2))).
  rewrite (@eq_in_filter _ (fun x => x \in undup s1)
    (fun x => x \in s1)); last by
    move=> x; rewrite ! mem_undup.
  by rewrite leq_addr.
Qed.

End FindLast.

(*TODO: prove in DecoderGeneric*)
Lemma decoder_multiple_steps_gen_cat: 
  forall upd timeout prev_packs rec1 rec2 blks sent time,
    decoder_multiple_steps_gen upd timeout prev_packs 
      (rec1 ++ rec2) blks sent time =
    let t := decoder_multiple_steps_gen upd timeout prev_packs
      rec1 blks sent time in
    decoder_multiple_steps_gen upd timeout (prev_packs ++ rec1)
      rec2 t.1.1.1 t.1.1.2 t.1.2.
Proof.
  move=> upd timeout prev rec1 rec2 blks sent time/=.
  rewrite -(prev_packets_multiple upd timeout prev rec1 blks sent time).
  rewrite /decoder_multiple_steps_gen foldl_cat//=.
  move: (foldl
  (fun (acc : seq block * seq packet * Z * seq fpacket) (p : fpacket) =>
   ((update_dec_state_gen
       [seq x <- acc.1.1.1 | timeout (upd acc.1.2 p acc.1.1.1) x] p
       (upd acc.1.2 p acc.1.1.1)).1,
   acc.1.1.2 ++
   (update_dec_state_gen
      [seq x <- acc.1.1.1 | timeout (upd acc.1.2 p acc.1.1.1) x] p
      (upd acc.1.2 p acc.1.1.1)).2, upd acc.1.2 p acc.1.1.1, 
   acc.2 ++ [:: p]))) => f.
  by case: (f (blks, sent, time, prev) rec1)=>/= [[[a b] c] d]/=.
Qed.

Lemma decoder_multiple_steps_gen_cons:
  forall upd timeout prev_packs p rec blks sent time,
  decoder_multiple_steps_gen upd timeout prev_packs 
    (p:: rec) blks sent time =
  let t := decoder_one_step_gen upd timeout
    blks p time in
  decoder_multiple_steps_gen upd timeout (prev_packs ++ [:: p])
    rec t.1.1 (sent ++ t.1.2) t.2.
Proof.
  move=> upd timeout prev p rec blks sent time.
  by rewrite -(prev_packets_multiple upd timeout prev [:: p] blks sent time).
Qed.

Lemma decoder_multiple_output_grows: forall 
  upd timeout prev_packs rec blks sent time p,
  p \in sent ->
  p \in (decoder_multiple_steps_gen upd timeout prev_packs rec blks sent time).1.1.2.
Proof.
  move=> upd timeout prev rec. move: prev. 
  elim: rec=>[// | h t /= IH prev blks sent time p Hinp].
  rewrite decoder_multiple_steps_gen_cons/=. apply IH.
  by rewrite mem_cat Hinp.
Qed.

(*A silly lemma*)
Lemma or_impl {P Q R S: Prop}:
  (P -> Q) ->
  (R -> S) ->
  (P \/ R) -> (Q \/ S).
Proof.
  move=> Hpq Hrs [Hp | Hr].
  - left. by apply Hpq.
  - right. by apply Hrs.
Qed. 

(*The theorem that we want: For any well-formed, encoded block from sent,
  if at least k packets from this block arrive in the received stream,
  then all data packets in this block will be in the output. *)
Theorem all_packets_in_block_recovered: forall k i j (sent rec: seq fpacket) 
  (b: block),
  wf_packet_stream sent ->
  (forall (p: fpacket), p \in rec -> p \in sent) ->
  block_wf b ->
  block_encoded b ->
  b \in (get_blocks sent) ->
  blk_k b = k ->
  all (fun x => packet_in_block x b) (sublist i j sent) ->
  (count (fun x => (x \in rec)) (undup (sublist i j sent)) 
    >= Z.to_nat k) ->
  forall (p: fpacket), packet_in_data p b ->
     (p_packet p) \in (decoder_all_steps_nto rec).1.2 \/
     (p_packet p) <| p_seqNum := 0 |> \in (decoder_all_steps_nto rec).1.2.
Proof.
  move=> k i j sent rec b Hwf Hsubstream Hwfb Henc Hbin Hbk Hall 
    Hcount p Hinp.
  rewrite /decoder_all_steps_nto/decoder_all_steps_gen.
  have Hk0: (Z.to_nat k) != 0. {
    case Hwfb => [Hk _]. apply /eqP. lia.
  }
  (*We examine the decoder at the time when we get the kth packet
    in this block*)
  have[l1 [p1 [l2 [Hrec [Hcountl1 [Hinp1b Hnotin]]]]]]:=
    (find_kth_item_in Hk0 Hall Hcount).
  (*Get invariant*)
  have Hwfrec: wf_packet_stream rec := (wf_substream Hwf Hsubstream).
  have Hwfl1: wf_packet_stream l1 by
    apply (wf_substream Hwfrec) => x; rewrite Hrec mem_cat =>->.
  have:=(decoder_nto_invar_all Hwfl1).
  rewrite /decoder_all_steps_nto/decoder_all_steps_gen.
  rewrite Hrec decoder_multiple_steps_gen_cat/= 
  decoder_multiple_steps_gen_cons/=/triv_timeout !filter_predT/triv_upd_time.
  move=> [Hsort [Hsubblocks [Hinblocks Hinoutput]]].
  apply (or_impl (@decoder_multiple_output_grows _ _ _ _ _ _ _ _)
    (@decoder_multiple_output_grows _ _ _ _ _ _ _ _)).
  rewrite !mem_cat.
  (*Idea: 2 cases: either p has appeared in l1 or not.
    If it appeared in l1, it is the output by the invariant.
    Otherwise, it is NOT in the current block with this id
    (because everything in this block in prev by subblock - TODO
      is in decodertimeout probably)
    so it will be in the output of [decode_block] - but we need to
    show that the block is recoverable*)
  case Hinpl1: (p \in l1).
  - left. apply /orP. left. apply Hinoutput=>//.
    apply negbT. by apply Hwfb.
  - (*Hard case: need to show that block recoverable*)