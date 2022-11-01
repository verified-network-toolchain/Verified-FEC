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
    ~~ fd_isParity p -> p_packet p \in output) /\
  (*All blocks are nonempty*)
  (*TODO: can we prove this?*)
  (forall (b: block), b \in blks -> exists (p: fpacket),
    packet_in_block p b).

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

Lemma blk_order_sort_uniq: forall blks,
  sorted blk_order blks ->
  uniq (map blk_id blks).
Proof.
  move=> blks. elim: blks=>[// | bhd btl /= IH].
  rewrite path_sortedE; [|apply blk_order_trans].
  move=> /andP[/allP Hall Hsort].
  rewrite IH // andbT.
  apply /negP => /mapP [b'] Hinb' Hidb.
  move: Hall => /(_ _ Hinb').
  by rewrite /blk_order Hidb ltnn.
Qed.

(*TODO: copied from encoder, move to COmmon or something*)
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

(*Any two blocks with same blockId are equal, given a list
  sorted by blockId*)
Lemma blk_sort_eq (blks: seq block) (b1 b2: block):
  sorted blk_order blks ->
  b1 \in blks ->
  b2 \in blks ->
  blk_id b1 = blk_id b2 ->
  b1 = b2.
Proof.
  move=> Hsort. apply blk_order_sort_uniq in Hsort.
  by apply map_uniq_inj.
Qed.

Lemma get_block_diff_in (s: seq fpacket) (b1 b2: block) (p: fpacket):
  (*Need some info from [wf_packet_stream] about injectivity*)
  wf_packet_stream s ->
  b2 \in (get_blocks s) ->
  block_wf b2 ->
  subblock b1 b2 ->
  packet_in_data p b2 ->
  ~~ packet_in_data p b1 ->
  ((p_packet p) <| p_seqNum := 0 |> \in (get_block_diff b1 b2)).
Proof.
  move=> Hwf Hinb2 Hwfb2 Hsub Hin2 Hin1.
  rewrite /get_block_diff.
  apply /mapP. exists (p_packet p)=>//. apply /mapP.
  exists p =>//. rewrite /get_diff -CommonSSR.pmap_id_some.
  apply /mapP. exists (None, Some p)=>//.
  apply /inP.
  rewrite CommonSSR.zip_combine In_Znth_iff Zlength_combine.
  have Hleneq: Zlength (data_packets b1) = Zlength (data_packets b2) by
    case Hsub => [_ [Hdat _]]; apply Hdat.
  rewrite Hleneq Z.min_id. exists (Z.of_nat (fd_blockIndex p)).
  have:=Hin2. rewrite /packet_in_data => /inP; 
  rewrite In_Znth_iff => [[i [Hi Hith]]].
  have Hieq: i = Z.of_nat (fd_blockIndex p). apply Hwfb2.
  by apply data_in_block. rewrite Znth_app1=>//. simpl in *; lia.
  split. simpl in *; lia.
  rewrite Znth_combine=>//. f_equal; last by rewrite -Hieq.
  have Hwfb1: block_wf b1 by apply (subblock_wf Hwfb2).
  case Hnth: (Znth (Z.of_nat (fd_blockIndex p)) (data_packets b1)) => [p1 | //].
  (*Now we need a few things*)
  have Hdat: packet_in_data p1 b1. { apply /inP. rewrite In_Znth_iff.
    exists (Z.of_nat (fd_blockIndex p)). split=>//; simpl in *; lia. }
  (*Show that ids are equal*)
  have Hidp:=(get_blocks_ids Hwf Hinb2 (data_in_block Hin2)).
  have Hidp2: (fd_blockId p1 = blk_id b2). {
    apply (get_blocks_ids Hwf)=>//. apply (subblock_in Hsub).
    by apply data_in_block.
  }
  (*Show that indices are equal*)
  have Hidxp2: Z.of_nat (fd_blockIndex p1) = Z.of_nat (fd_blockIndex p). {
    case Hwfb1 => [_ [_ [_ [_ [/(_ p1 (Z.of_nat (fd_blockIndex p)) 
      (data_in_block Hdat)) His _]]]]].
    symmetry. apply His; rewrite Znth_app1=>//. simpl in *; lia.
  }
  (*Now, show that both are in s*)
  have Hinps:=(get_blocks_in_orig Hwf Hinb2 (data_in_block Hin2)).
  have Hinp1s: (p1 \in s). {
    apply (get_blocks_in_orig Hwf Hinb2). apply (subblock_in Hsub).
    by apply data_in_block.
  }
  have Heq: p = p1. { apply Hwf=>//. by rewrite Hidp Hidp2.
    by apply Nat2Z.inj. }
  subst. 
  (*Finally, a contradiction*)
  by rewrite Hdat in Hin1.
Qed.

Require Import CommonSSR.
Require Import ZSeq.

Lemma size_filter_lt: forall {A: Type} (p: pred A) (s: seq A),
  (size (filter p s) < size s) = ~~ all p s.
Proof.
  move=> A p s. rewrite size_filter all_count.
  have:=(count_size p s).
  rewrite leq_eqVlt => /orP[/eqP -> | Hlt].
  - by rewrite ltnn eq_refl.
  - rewrite Hlt. move: Hlt. by rewrite ltn_neqAle => /andP[Hneq _].
Qed. 

(*TODO; move to block*)
Lemma filter_none_Zlength: forall {A: eqType} (p: pred A) (s: seq A),
  Zlength [seq x <- s | p x] = 0%Z <-> ~~ has p s.
Proof.
  move=> A p s. rewrite Zlength_correct -size_length has_filter.
  have->: 0%Z = Z.of_nat 0 by [].
  rewrite Nat2Z.inj_iff negbK -size_eq0. 
  by apply (reflect_iff _ _ eqP).
Qed.

Lemma filter_Zlength_lt: forall {A: eqType} (p: pred A) (s: seq A),
  (Zlength [seq x <- s | p x] < Zlength s)%Z <-> ~~ all p s.
Proof.
  move=> A p s. 
  rewrite -size_filter_lt !Zlength_correct -!size_length -Nat2Z.inj_lt.
  by apply (reflect_iff _ _ ltP).
Qed.

Lemma new_block_recoverable: forall (p: fpacket) (t: Z),
  fd_k p = 1%Z ->
  (0 < fd_h p)%Z ->
  (0 <= Z.of_nat (fd_blockIndex p) < fd_k p + fd_h p)%Z ->
  recoverable (create_block_with_fec_packet p t).
Proof.
  move=> p t Hk Hh Hidx.
  rewrite /recoverable.
  match goal with | |- is_true (proj_sumbool ?x) => case: x end=>//=.
  (*rewrite !Zlength_correct -!size_length -Nat2Z.inj_add.
  rewrite -Nat2Z.inj_lt => /ltP.
  have->: (forall x y, (x + y)%coq_nat = x + y) by [].*)
  have [Hfst | Hsnd]: (0 <= (Z.of_nat (fd_blockIndex p)) < fd_k p)%Z \/
    (fd_k p <= (Z.of_nat (fd_blockIndex p)) < fd_k p + fd_h p)%Z by lia.
  - (*Prove that 1 list has length 1, so not lt*)
    rewrite sublist_upd_Znth_lr; try lia; last by rewrite zseq_Zlength; lia.
    rewrite sublist_upd_Znth_r; try lia; last by rewrite zseq_Zlength; lia.
    rewrite !zseq_sublist; try lia.
    rewrite !Z.sub_0_r.
    rewrite upd_Znth_Zlength zseq_Zlength; try lia.
    have->: (@Zlength (option fpacket) [seq x <- zseq (fd_k p + fd_h p - fd_k p) None | isSome x]) = 
      0%Z. {
      apply filter_none_Zlength. apply /hasP => [[x]]. 
      by rewrite /zseq mem_nseq => /andP[_ /eqP ->].
    }
    rewrite Z.add_0_r.
    have: all isSome (upd_Znth (Z.of_nat (fd_blockIndex p)) 
    (zseq (fd_k p) None) (Some p)). {
      apply /allP. rewrite Hk/= /zseq/=.
      have->:Z.of_nat (fd_blockIndex p) = 0%Z by lia.
      rewrite upd_Znth0 => x.
      by rewrite in_cons orbF => /eqP ->.
    }
    rewrite -(negbK (all _ _)) => /negP. 
    by rewrite -filter_Zlength_lt upd_Znth_Zlength zseq_Zlength; try lia.
  - (*Similar proof but in reverse (and a bit trickier because 
    we don't know h)*)
    rewrite sublist_upd_Znth_l; try lia; last by rewrite zseq_Zlength; lia.
    rewrite !sublist_upd_Znth_lr; try lia; last by rewrite zseq_Zlength; lia.
    rewrite !zseq_sublist; try lia.
    rewrite !Z.sub_0_r !zseq_Zlength; try lia.
    have->/=: (@Zlength (option fpacket) [seq x <- zseq (fd_k p) None | isSome x] = 0%Z). {
      apply filter_none_Zlength. apply /hasP => [[x]].
      by rewrite /zseq mem_nseq => /andP[_ /eqP ->].
    }
    rewrite Z.add_0_l Z.add_simpl_l.
    have: has isSome (upd_Znth (Z.of_nat (fd_blockIndex p) - fd_k p)
    (zseq (fd_h p) None) (Some p)). {
      apply /hasP. exists (Some p)=>//.
      apply /inP. apply upd_Znth_In; rewrite zseq_Zlength; lia. 
    }
    rewrite Hk -(negbK (has _ _)) => /negP.
    rewrite -filter_none_Zlength => Hnot0 Hlt1.
    have Hge0: (0 <= (Zlength
    [seq x <- upd_Znth (Z.of_nat (fd_blockIndex p) - 1)
                (zseq (fd_h p) None) (Some p)
       | isSome x]))%Z by  list_solve. simpl in *.
    (*TODO: why doesn't lia work? Shouldn't need this*)
    have: forall z, (0 <= z)%Z -> (z < 1)%Z -> z = 0%Z.
      move=> z. lia.
    by move=> /(_ _ Hge0 Hlt1).
Qed. 

Lemma recoverableP (b: block):
  reflect (recoverable b)
    (size (filter isSome (data_packets b ++ parity_packets b)) >=
      size (data_packets b)).
Proof.
  apply iff_reflect. rewrite /recoverable.
  rewrite -Zlength_app -cat_app -filter_cat !Zlength_correct -!size_length.
  case : (Z_ge_lt_dec
  (Z.of_nat (size [seq x <- data_packets b ++ parity_packets b | isSome x]))
  (Z.of_nat (size (data_packets b)))) =>//= Hsz.
  - apply Nat2Z.inj_ge in Hsz.
    split=>// _. by move: Hsz => /leP.
  - apply Nat2Z.inj_lt in Hsz. split=>// Hle.
    move: Hsz => /ltP. by rewrite ltnNge Hle.
Qed. 

(*TODO: from DecoderTimeouts, move*)
Lemma decoder_invar_inprev: forall (blocks: seq block) prev,
  wf_packet_stream prev ->
  (forall b, b \in blocks -> exists b', b' \in (get_blocks prev) /\
  subblock b b') ->
  forall (b: block) (p: fpacket),
    b \in blocks -> packet_in_block p b -> p \in prev.
Proof.
  move=> blocks prev Hwf Hsubblock b p' Hinb Hinpb'.
  move: Hsubblock => /(_ b Hinb) [b1 [Hinb1 Hsub]].
  apply (get_blocks_in_orig Hwf Hinb1).
  apply (subblock_in Hsub Hinpb').
Qed.

(*Can we prove this? Crucial lemma for bounding size - if we have
  a list of elements such that all elements are unique, satisfy
  a predicate, and are in s2, then size s <= count p2 (undup s2).
  We add an injective mapping as well for generality (we need this
  to remove the Some in the block-> stream mapping).*)
Lemma all_in_count_lt {A B: eqType} (p2: pred B) (s: seq A) 
  (s2: seq B) (f: A -> B):
  uniq s ->
  {in s &, injective f} ->
  all (fun x => p2 (f x) && (f x \in s2)) s ->
  size s <= count p2 (undup s2).
Proof.
  move=> Huniq Hinj Hall.
  erewrite count_perm; last by 
    apply (filter_partition_perm (fun x => x \in (map f s))).
  rewrite count_cat.
  rewrite count_filter/=/predI.
  have->:size s = 
    count [pred x | p2 x & x \in [seq f i | i <- s]] (undup s2);
  last by rewrite leq_addr.
  (*The main lemma: we can get one element in (undup s2) per element
    of s1*)
  move: Huniq Hinj Hall. move: s2. elim: s => 
    [//= s2 _ _ _ | h1 t1 /= IH s2 /andP[Hnotin Huniq] Hinj
      /andP[/andP[Hp2h1 Hins2] Hall]].
  - rewrite -size_filter. apply /eqP. 
    rewrite eq_sym size_eq0 -(negbK (_ == _)) -has_filter.
    by apply /hasP => [[x]]/= _ /andP[_ Hf].
  - rewrite -count_filter.
    erewrite count_perm.
    2: { 
      apply perm_filter_in_cons; apply /mapP => [[x]] Hint1 Hfeq.
      have Hx: h1 = x. apply Hinj=>//. by rewrite mem_head.
      by rewrite in_cons Hint1 orbT.
      subst. by rewrite Hint1 in Hnotin.
    }
    rewrite filter_pred1_uniq'; last by rewrite undup_uniq.
    rewrite mem_undup Hins2/= Hp2h1 count_filter (IH s2)=>//.
    move=> x y Hinx Hiny Hfxy. apply Hinj=>//; rewrite in_cons.
    by rewrite Hinx orbT.
    by rewrite Hiny orbT.
Qed. 

(*filter is unique if all elements in the original list satisfying
  the predicate have only one ocurrence*)
Lemma nth_filter_uniq: forall {A: eqType} (p: pred A) (d: A) (s: seq A),
  (forall i j, i < size s -> j < size s -> p (nth d s i) -> p (nth d s j) ->
    nth d s i = nth d s j -> i = j) ->
  uniq (filter p s).
Proof.
  move=> A p d. elim => [// | h t /= IH Hall].
  have Hih: (forall i j : nat,
  i < size t ->
  j < size t ->
  p (nth d t i) -> p (nth d t j) -> nth d t i = nth d t j -> i = j). {
    move=> i j Hi Hj Hp1 Hp2 Hntheq.
    apply eq_add_S.
    by apply (Hall i.+1 j.+1).
  }
  move: IH => /(_ Hih) Huniq. rewrite {Hih}.
  case Hph: (p h)=>//=.
  rewrite Huniq andbT.
  apply /negP. rewrite mem_filter => /andP[_ Hhint].
  have:=Hhint => /nthP => /(_ d) [i] Hi Hnthi.
  have//: 0 = i.+1. apply Hall=>//=. by rewrite Hnthi.
Qed.

(*The packets in a block are unique (TODO: move)*)
Lemma block_pkts_uniq: forall (b: block),
  block_wf b ->
  uniq [seq x <- data_packets b ++ parity_packets b | isSome x].
Proof.
  move=> b [Hkb [Hhb [Hallkh [Hallid [Hallith [Hlendat 
    [Hlenpar [Henc [Hval [Halldat Hallpar]]]]]]]]]].
  apply (@nth_filter_uniq _ isSome None) => i j Hi Hj.
  case Hith: (nth None (data_packets b ++ parity_packets b) i) => [p1 | //].
  case Hjth: (nth None (data_packets b ++ parity_packets b) j) => [p2 | //].
  move=> _ _ [Hp12]; subst.
  have Hinb1p: packet_in_block p2 b by
    rewrite packet_in_block_eq -mem_cat -Hith mem_nth.
  move: Hith Hjth.
  rewrite !nth_nth !nth_Znth' => Hith Hjth.
  have Hi': Z.of_nat i = Z.of_nat (fd_blockIndex p2) by
    apply Hallith.
  have Hj': Z.of_nat j = Z.of_nat (fd_blockIndex p2) by 
    apply Hallith.
  rewrite -Hj' in Hi'.
  by apply Nat2Z.inj in Hi'.
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
  move=> [Hsort [Hsubblocks [Hinblocks [Hinoutput Hblknonemp]]]].
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
  case Hinpl1: (p \in l1); first by 
    left; apply /orP; left; apply Hinoutput=>//;
    apply negbT; apply Hwfb.
  (*Hard case: need to show that block recoverable*)
  rewrite update_dec_state_gen_eq //.
  (*Make goal nicer - TODO do we need this?*)
  forget (decoder_multiple_steps_gen (fun=> (fun=> (fun=> 0%Z)))
  (fun=> xpredT) [::] l1 [::] [::] 0) as state.
  move: Hsort Hsubblocks Hinblocks Hinoutput Hblknonemp.
  set blks:=state.1.1.1.
  set output:=state.1.1.2.
  move=> Hsort Hsubblocks Hinblocks Hinoutput Hblknonemp.
  (*A few useful results*)
  have Hinps: p \in sent :=
    (get_blocks_in_orig Hwf Hbin (data_in_block Hinp)).
  have Hidp: fd_blockId p = blk_id b :=
    (get_blocks_ids Hwf Hbin (data_in_block Hinp)).
  have Hidp1: fd_blockId (p_fec_data' p1) = blk_id b by
    apply (get_blocks_ids Hwf).
  have Hinp1: p1 \in sent by 
    apply Hsubstream; rewrite Hrec mem_cat mem_head !orbT.
  have Hhpos: (0 <= fd_h (p_fec_data' p1))%Z by apply Hwf.
  case Hhas: (has (fun b0 : block => blk_id b0 == 
    fd_blockId (p_fec_data' p1)) blks); last first.
  - (*Case 1: no previous block, so this is the first packet
      to arrive*)
    move: Hhas => /hasP Hnotex/=.
    case: (Z.eq_dec (fd_k (p_fec_data' p1)) 1) =>//= Hk1.
    + (*Here, we are finishing the packet*)
      case Hpar: (fd_isParity (p_fec_data' p1))=>/=.
      * right. apply /orP. right. 
        have Hsubnew: subblock (create_block_with_fec_packet p1 0) b. {
          
          have [b1 [Hinb1 Hsubb1]]:=(create_block_subblock 0 Hwf Hinp1).
          (*Prove blocks same because they have the same ids*)
          have->//:b = b1. {
            apply (map_uniq_inj (get_blocks_id_uniq Hwf))=>//.
            by rewrite -(proj1 Hsubb1) create_black_id.
          }
          move: Hsubb1. rewrite /create_block_with_packet_black Hk1.
          by case: (Z.eq_dec 1 1).
        }
      (*Use [decode_block_correct] (from RS decoder theorem)*) 
        rewrite (decode_block_correct Hwfb)=>//.
        -- (*TODO: separate?*)
          apply (get_block_diff_in Hwf)=>//.
          rewrite /packet_in_data/=. apply /negP=> /inP.
          rewrite In_Znth_iff Zlength_sublist; try lia; last by
            rewrite Zlength_upd_Znth zseq_Zlength; lia.
          move=> [idx] [Hidx]. rewrite Znth_sublist; try lia.
          rewrite Z.add_0_r.
          case: (Z.eq_dec idx  (Z.of_nat (fd_blockIndex (p_fec_data' p1))))
            =>//= Hidxeq.
          ++ subst. rewrite upd_Znth_same; last by
            rewrite zseq_Zlength; lia.
            move=> [Hpp1]. subst. (*contradiction - p not parity*)
            have: fd_isParity p = false by apply Hwfb.
            by rewrite Hpar.
          ++ rewrite upd_Znth_diff; try rewrite zseq_Zlength; try lia.
            by rewrite zseq_Znth; try lia.
            split; try lia. by apply Hwf.
        -- (*proved in other lemma, surprisingly difficult*)
          apply new_block_recoverable=>//; last
          by split; try lia; by apply Hwf.
          have->:fd_h (p_fec_data' p1) = blk_h b by apply Hwfb.
          by apply Hwfb.
      * (*In this case, we get a data packet - since k =1, it must
          be that p = p1*)
        left. apply /orP. right. rewrite in_cons; apply /orP.
        left. have->//: p = p1.
        (*apply Hwf=>//=. by rewrite Hidp1 .*)
        (*To prove blockIndex equal, use wf of block*)
        have Hkeq: fd_k (p_fec_data' p1) = blk_k b by apply Hwfb.
        case Hwfb => [_ [_ [_ [_ [Hith [Hdatlen [_ [_ [_ [_ Hpars]]]]]]]]]].
        have Hinp1dat: packet_in_data p1 b. {
          move: Hinp1b. rewrite /packet_in_block => /orP[// | Hinpar].
          have: fd_isParity (p_fec_data' p1) by apply Hpars.
          by rewrite Hpar. 
        }
        have:=Hinp. have:=Hinp1dat. 
        rewrite /packet_in_data => /inP H /inP; move: H.
        rewrite !In_Znth_iff !Hdatlen -!Hkeq !Hk1 => 
          [[i1] [Hi1 Hith1]] [i2] [Hi2 Hith2].
        have Hi10: i1 = 0%Z by lia.
        have Hi20: i2 = 0%Z by lia. subst.
        rewrite Hith2 in Hith1. by case: Hith1.
    + (*Now in the case where k <> 1 - we have to show we
        have a contradiction, since this means we have a block
        with some packet in b*)
      exfalso. have /hasP: has (packet_in_block^~b) (undup l1). {
        rewrite has_count Hcountl1.
        have Hkeq: fd_k (p_fec_data' p1) = blk_k b by apply Hwfb.
        move: Hk0 => /eqP => Hk0. 
        apply /ltP. have->: (Z.to_nat k - 1) = (Z.to_nat k - 1)%coq_nat by [].
        lia.
      }
      move=> [p2] Hinp2 Hinbp2.
      (*Contradiction since every previous packet is in a block*)
      rewrite mem_undup in Hinp2.
      move: Hinblocks => /(_ _ Hinp2) [b1 [Hinb1 Hinp2b1]].
      (*Now we need to show that blockId is the same*)
      apply Hnotex. exists b1=>//. apply /eqP.
      (*Show that b1 is a subblock of some block in [get_blocks]
        By uniquness, this is b*)
      have Hsubb: subblock b1 b. {
        move: Hsubblocks => /( _ _ Hinb1) [b2 [Hinb2 Hsub2]].
        have [b3 [Hinb3 Hsub3]]: exists b', b' \in (get_blocks sent) 
          /\ subblock b2 b'. apply get_blocks_sublist with(l2:=l1)=>//=.
          move=> x Hinx. apply Hsubstream. by rewrite Hrec mem_cat Hinx.
        have Hbeq: b = b3. {
          apply (map_uniq_inj (get_blocks_id_uniq Hwf))=>//.
          rewrite -(get_blocks_ids Hwf Hbin Hinbp2).
          apply (get_blocks_ids Hwf)=>//.
          by apply (subblock_in (subblock_trans Hsub2 Hsub3)). 
        }
        subst. by apply (subblock_trans Hsub2).
      }
      by rewrite (proj1 Hsubb).
  - (*Here we deal with the case where a block exists*)
    (*TODO*)
    have:=Hhas => /hasP [b1] Hinb1 /eqP Hidb1/=.
    have->: (nth block_inhab blks
      (find (fun b0 : block => blk_id b0 == 
        fd_blockId (p_fec_data' p1)) blks)) = b1. {
      apply (map_uniq_inj (blk_order_sort_uniq Hsort))=>//.
      apply mem_nth. by rewrite -has_find.
      have /(_ block_inhab)/eqP:= (nth_find _ Hhas).
      by rewrite Hidb1. 
    }
    rewrite /add_packet_to_block_black.
    (*TODO: add to invariant*)
    have Hcomp: (forall b, b \in blks -> black_complete b ->
      recoverable b) by admit.
    case Hblackcomp: (black_complete b1).
    + (*If black complete, then recoverable, so we must have seen
      at least k packets with this blockIndex, a contradiction*)
      move: Hcomp => /( _ _ Hinb1 Hblackcomp) Hrecover.
      exfalso.
      have: count (packet_in_block^~ b) (undup l1) >= Z.to_nat k. {
        (*How can we prove this?*)
        move: Hrecover => /recoverableP.
        (*Now we want to show that b1 is a subblock of b*)
        have Hsub: subblock b1 b. {
          move: Hsubblocks => /(_ b1 Hinb1) [b2 [Hinb2 Hsub2]].
          have [b3 [Hinb3 Hsubb3]]: 
            exists b3, b3 \in get_blocks sent /\ subblock b2 b3 by
            apply get_blocks_sublist with(l2:=l1)=>//; (*TODO: repetitive*)
            move=> x Hinx; apply Hsubstream; rewrite Hrec mem_cat Hinx.
          have->: b = b3; last by apply (subblock_trans Hsub2).
          apply (map_uniq_inj (get_blocks_id_uniq Hwf))=>//.
          by rewrite -(proj1 Hsubb3) -(proj1 Hsub2) Hidb1.
         }
        have Hwfb1: block_wf b1:=(subblock_wf Hwfb Hsub).
        have->: (size (data_packets b1) = Z.to_nat k). {
          rewrite size_length -ZtoNat_Zlength. f_equal.
          have->: (Zlength (data_packets b1) = blk_k b1) by apply Hwfb1.
          by have->: (blk_k b1 = blk_k b) by apply Hsub.
        }
        move=> Hsz.
        apply (leq_trans Hsz).
        apply all_in_count_lt with (f:= fun (x: option fpacket) =>
          match x with | Some p => p | None => fpacket_inhab end)=>//.
        - by apply block_pkts_uniq.
        - move=> o1 o2. rewrite !mem_filter.
          by case: o1; case :o2 =>//= x y _ _ ->.
        - apply /allP => o. rewrite mem_filter. case: o=>// f /andP[_  Hinf].
          have Hinfb1: packet_in_block f b1 by 
            rewrite packet_in_block_eq -mem_cat.
          rewrite (subblock_in Hsub Hinfb1)/=.
          by apply (decoder_invar_inprev Hwfl1 Hsubblocks Hinb1).
      }
      by rewrite Hcountl1 leq_subrR /= (negbTE Hk0).
    + (*Block is not yet complete*)
      case Hrecover: (recoverable (add_fec_packet_to_block p1 b1)) =>//=; last first.
      * (*TODO: separate lemma that recoverable => at least k so far 
        (prove subblock for (l1 ++ [:: p1]))*)
        admit.
      * (*Here, need to case on whether p was seen already
          or if it is p1, or else not seen already so in output
          of [decode_block]*)

      
      
      Search (?x <= ?x - ?y). lia.
          Search packet_in_block subblock.
          rewrite Hinfb1/=.

          
     
        
        move=> x.


          all ()

        case Hwfb1.
         
         Search block_wf subblock.
        rewrite /recoverable.
      }

    rewrite Hb1eq {Hb1eq}. rewrite Hb1eq in Hnth. rewrite {Hb1eq Hnth}.

    rewrite /add_packet_to_block_black.
    Search nth find.
    Print add_packet_to_block_black.
    (*Need to know that if complete, then all packets
      are in the output stream (or we should say: if complete,
      at least k packets have been received - in invariant?)*)
    rewrite /=.