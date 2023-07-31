Require Import CommonSSR.
Require Import Lia.
Require Import CommonFEC.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".



(** Sequence numbers and reordering*)

(*We follow the notation of the RD metric for measuring reordering. We don't need the full histogram; instead,
  we will place a bound on the maximum allowable displacement*)

(*First, we need to define the displacement*)

Section SeqNums.

Open Scope nat_scope.


Variable pack : eqType.

Section Defs.

Variable sent : seq pack.
Variable received : seq pack.

(*All received packets were sent*)
Variable rec_sub: {subset received <= sent}.

(*We view this as a completed transcript, so we know  
  which packets are missing.*)

Definition o_seqNum (p: pack) :=
  index p sent.

Lemma o_seqNum_inj: forall p1 p2,
  p1 \in sent ->
  p2 \in sent ->
  o_seqNum p1 = o_seqNum p2 ->
  p1 = p2.
Proof.
  move=> p1 p2. rewrite /o_seqNum.
  apply index_inj.
Qed.

Definition u_seqNum (p: pack) := index p (undup_fst received).

(*Definition n_seqNum (p : pack) :=
  index p received.*)

(*Receive index - we can calculate by taking the set of received packet sequence numbers, sorting it,
  then associating the ith packet in the received list with the ith packet in this sorted list*)
(*This differs slightly from the standard definition, since it ignores duplicates*)
Definition ri (p : pack) : nat :=
  let l := map o_seqNum (filter (fun x => x \in received) sent) in 
  (*sort Nat.ltb (map o_seqNum (undup received)) in*)
  nth 0%N l (u_seqNum p).

(*Displacement - measures amount of reordering*)
Definition displ (p: pack) : nat :=
  nat_abs_diff (ri p) (o_seqNum p).

(* should change to sorted by lt*)
Fixpoint s_incr (s: seq nat) :=
  match s with
  | nil => true
  | x :: tl =>
    match tl with
    | nil => true
    | y :: tl' => (x < y) && s_incr tl
    end
  end.

(*The crucial lemma we need for [uniq_incr_nats] and [s_incr_nth_ltn] - 
  since each element is
  strictly greater than the last, the nth element in the list must be at
  least as large as the first element + n*)
Lemma s_incr_nth_bound: forall d y t n,
  n < size (y :: t) ->
  s_incr (y :: t) ->
  y + n <= nth d (y :: t) n.
Proof.
  move=> d y t. move: y. elim: t => [//= y n | x t /=].
  - rewrite ltn1 => /eqP Hn _. by rewrite Hn addn0.
  - move=> IH y n. case: n => [//= | /= n].
    + by rewrite addn0.
    + rewrite ltnS => Hn /andP[Hyx Ht].
      move: IH => /( _ x n Hn Ht) => Hle.
      have Hxy: y + n.+1 <= x + n
        by rewrite -addn1 addnA addnC addnA leq_add2r addnC addn1.
      by apply (leq_trans Hxy).
Qed.

(*The list is increasing, so elements at earlier positions are 
  smaller than those at later positions*)
Lemma s_incr_nth_ltn: forall d s n1 n2,
  n1 < size s ->
  n2 < size s ->  
  s_incr s ->
  n1 < n2 ->
  (nth d s n1) < (nth d s n2).
Proof.
  move=> d s. elim: s => [//= | x [|y t] //=].
  - move => _ n1 n2. by rewrite !ltn1 => /eqP Hn1 /eqP Hn2; subst.
  - move=> IH n1 n2. case: n1 => [| n1]; case: n2 => [//= | n2 /=].
    + move => _ Hn2 /andP[Hxy Ht] _.
      apply (ltn_leq_trans Hxy).
      have Hyle: y <= y + n2 by rewrite leq_addr.
      apply (leq_trans Hyle).
      by apply s_incr_nth_bound.
    + move => Hn1 Hn2 /andP[Hxy Ht] Hn12. by apply IH.
Qed.

(*An obvious corollary*)
Lemma s_incr_nth_leq: forall d s n1 n2,
  n1 < size s ->
  n2 < size s ->  
  s_incr s ->
  n1 <= n2 ->
  (nth d s n1) <= (nth d s n2).
Proof.
  move=>d s n1 n2 Hn1 Hn2 Hincr.
  rewrite leq_eqVlt => /orP[/eqP Hn12 | Hn12].
  - by rewrite Hn12.
  - apply ltnW. by apply s_incr_nth_ltn.
Qed.


(*A key lemma: given a strictly increasing list, if we look at
  the list at two positions (n1 and n2), the distance between the list elements
  at n1 and n2 can only be larger*)
Lemma uniq_incr_nats: forall (d: nat) n1 n2 (s: seq nat),
  n1 < size s ->
  n2 < size s ->  
  s_incr s ->
  n1 <= n2 ->
  n2 - n1 <= (nth d s n2) - (nth d s n1).
Proof.
  move=> d n1 n2 s. move: n1 n2. elim: s => [// | x t /=].
  case: t => [//= _ n1 n2 | y t /=].
  - by rewrite !ltn1 => /eqP Hn1 /eqP Hn2 _ _; subst.
  - move=> IH n1 n2.
    case: n1 => [/= | n1]; case: n2 => [//= | //= n2].
    + move => _ Hn2 /andP[Hxy Ht] _.
      rewrite subn0 ltn_subRL.
      have Hxy': x + n2 < y + n2 by rewrite ltn_add2r.
      apply (CommonSSR.ltn_leq_trans Hxy').
      by apply s_incr_nth_bound.
    + rewrite !ltnS subSS. move => Hn1 Hn2 /andP[Hxy Ht] Hn12.
      by apply IH.
Qed.

(*Lift to [nat_abs_diff]*)
Lemma uniq_incr_nats_abs: forall (d: nat) n1 n2 (s: seq nat),
  n1 < size s ->
  n2 < size s ->
  s_incr s ->
  nat_abs_diff n1 n2 <= nat_abs_diff (nth d s n1) (nth d s n2).
Proof.
  move => d n1 n2 s Hn1 Hn2 Hincr.
  case: (orP (leq_total n1 n2)) => [Hn12 | Hn21].
  - rewrite !nat_abs_diff_leq //.
    by apply uniq_incr_nats.
    by apply s_incr_nth_leq.
  - rewrite !nat_abs_diff_leq' //.
    by apply uniq_incr_nats.
    by apply s_incr_nth_leq.
Qed.


(*A slightly different (and weaker) form of [s_incr_nth_bound] *)
Lemma s_incr_in_bound: forall n h t,
  n \in (h :: t) ->
  s_incr (h :: t) ->
  h <= n.
Proof.
  move => n h t Hin Hincr.
  have Hhidx: h + (index n (h :: t)) <= n; last first.
    eapply leq_trans. 2: apply Hhidx. by rewrite leq_addr.
  have Hn: n = nth 0 (h :: t) (index n (h :: t)) by
    symmetry; apply nth_index.
  rewrite {2}Hn. apply s_incr_nth_bound => //.
  by rewrite index_mem.
Qed.

Lemma s_incr_subseq: forall (s1 s2: seq nat),
  subseq s1 s2 ->
  s_incr s2 ->
  s_incr s1.
Proof.
  move => s1 s2. move: s1. elim: s2 => 
    [//= s1 /eqP -> // | a2 /= [//= | b2 t2] IH].
  - move => [//| a1 t1].
    by case Ha12: (a1 == a2) => // /eqP ->.
  - move => [//| a1 t1].
    case Ha12: (a1 == a2) => //.
    + move => Hsub /andP[Hab2 Hincr] /=.
      move: Hsub. case: t1 => [//| b1 t1 Hsub].
      have->: s_incr (b1 :: t1) by apply IH.
      rewrite andbT.
      move: Ha12 => /eqP Ha12; subst.
      have Hinb1: b1 \in (b2 :: t2). { apply mem_subseq in Hsub.
        apply Hsub. by rewrite in_cons eq_refl.
      }
      apply (ltn_leq_trans Hab2).
      eapply s_incr_in_bound. apply Hinb1. by apply Hincr.
    + move=> Hsub /andP[Hab2 Hincr]. by apply IH.
Qed.

(*An alternate way to show that something is increasing*)
Lemma s_incr_alt: forall s,
  reflect (forall d n1 n2, n1 < size s -> n2 < size s -> n1 < n2 ->
  nth d s n1 < nth d s n2) (s_incr s).
Proof.
  move => s. elim: s => [//= | h [//| n t] /= IH].
  - by apply ReflectT.
  - apply ReflectT => d n1 n2. by rewrite !ltn1 => /eqP Hn1 /eqP Hn2; subst.
  - case Hhn: (h < n) => /=; last first.
    + apply ReflectF => /(_ 0 0 1) /=. rewrite Hhn => C.
      have//: false. by apply C.
    + move: IH. case Ht: (match t with
        | [::] => true
        | y :: _ => (n < y) && s_incr t
        end) => IH; [apply elimT in IH | apply elimF in IH] => //.
      * apply ReflectT. move => d [//| n1 /=] [// | n2 /=].
        -- move => _ Hn2 _. apply (ltn_leq_trans Hhn).
          eapply s_incr_in_bound. by apply mem_nth. by [].
        -- move => Hn1 Hn2 Hn12. by apply IH.
      * apply ReflectF => C.
        apply IH. move => d n1 n2 Hn1 Hn2 Hn12. by move: C => /(_ d n1.+1 n2.+1) ->.
Qed.


Lemma index_list_incr: forall {A: eqType} (p: pred A) (s: seq A),
  uniq s ->
  s_incr (map (fun x => index x s) (filter p s)).
Proof.
  move=> A p s Huniq.
  have Hsub: subseq ([seq index x s | x <- s & p x]) (map (fun x => index x s) s). {
    apply map_subseq. apply filter_subseq.
  }
  (*this is NOT true - if packets repeat, we need the assumption that we have
    no duplicate packets
    for now, we will use this assumption - later we might remove, if we can
    get some local property (in the sublist we care about) - but even this may
    not hold *)
  apply (s_incr_subseq Hsub). 
  rewrite {Hsub}. move: Huniq.
  case: s => [// | h t].
  remember (h :: t) as s.
  rewrite {Heqs t} => Huniq.
  apply /s_incr_alt. rewrite !size_map.
  move=> d n1 n2 Hn1 Hn2 Hn12. by rewrite !(nth_map h) // !index_uniq.
Qed.


(*The lemma that allows us to relate differences in [u_seqNum] to
  differences in [ri] (which we can bound by d).
  Mostly a corollary of [uniq_incr_nats_abs] and [index_list_incr] *)
(*BUT: we need the uniqueness of the sending list for this -
  It is also obvious why this is a problem - if the sequence numbers wrap around,
  the receive index will not wrap around also, making the first difference
  very large. Even some local property will not hold)*)
Lemma u_seqNum_RI: forall p1 p2,
  uniq sent ->
  p1 \in received ->
  p2 \in received ->
  nat_abs_diff (u_seqNum p1) (u_seqNum p2) <=
  nat_abs_diff (ri p1) (ri p2).
Proof.
  move=> p1 p2 Huniq Hp1 Hp2. rewrite /ri.
  (*The size subgoals are the same*)
  have Hszs: forall p, p \in received ->
    u_seqNum p < size [seq o_seqNum i | i <- sent & i \in received]. {
      move => p Hinp. rewrite size_map /u_seqNum.
      have: p \in (undup_fst received) by rewrite mem_undup_fst.
      rewrite -index_mem => Hidx.
      apply (ltn_leq_trans Hidx).
      by apply size_undup_fst.
    }
  apply uniq_incr_nats_abs; try by apply Hszs.
  by apply index_list_incr.
Qed. 

(*We expand on this bound, but first, we need a version of the triangle inequality*)
Lemma u_seqNum_bound: forall p1 p2 n d,
  uniq sent ->
  p1 \in received ->
  p2 \in received ->
  nat_abs_diff (o_seqNum p1) (o_seqNum p2) <= n ->
  displ p1 <= d ->
  displ p2 <= d ->
  nat_abs_diff (u_seqNum p1) (u_seqNum p2) <= n + 2 * d.
Proof.
  move=> p1 p2 n d Huniq Hp1 Hp2 Hoseq.
  rewrite /displ => Hd1 Hd2.
  apply (leq_trans (u_seqNum_RI Huniq Hp1 Hp2)).
  apply (leq_trans (nat_abs_diff_triag _ _ (o_seqNum p1))).
  have->: n + 2 * d = d + (d + n) by rewrite addnA addnn -mul2n addnC.
  apply leq_add. apply Hd1.
  apply (leq_trans (nat_abs_diff_triag _ _ (o_seqNum p2))).
  by apply leq_add.
Qed.

(*Finally, we can give the condition we want: if all displacements are bounded,
  then any two packets that are n apart in the original list are at most n+2d apart
  in the resulting list (where we only consider the first ocurrence of each packet)*)


(*We note that the displacement is only defined for the first occurrence of a packet*)
(*The condition we want*)
Definition reorder_bounded (d: nat) : bool := 
  all (fun p => (displ p <= d)%N) received.

(*Note that |u_seqNum p1 - u_seqNum p2| is equivalent to the number of
  packets that arrive for the first time between p1 and p2 (we will prove
  this later)*)
Theorem u_seqNum_reorder_bound: forall p1 p2 n d,
  uniq sent ->
  reorder_bounded d ->
  p1 \in received ->
  p2 \in received ->
  nat_abs_diff (o_seqNum p1) (o_seqNum p2) <= n ->
  nat_abs_diff (u_seqNum p1) (u_seqNum p2) <= n + 2 * d.
Proof.
  move=> p1 p2 n d Huniq /allP Hbound Hp1 Hp2 Hn.
  by apply u_seqNum_bound => //; apply Hbound.
Qed.

(*Part 2: Dealing with duplicates*)
  

(*The second condition: if there are any duplicates, they are separated by at most k
  packets*)
(*this condition will be important in showing that our implementation correctly
keeps track of the number of unique packets seen. But it is not needed for our
bounds here*)
Definition duplicates_bounded (default: pack) (k: nat) : Prop :=
  forall i j, 
  (i <= j) -> 
  (j < length received) ->
  nth default received  i = nth  default received j ->
  (j - i <= k).

(*We want to show the following: suppose we have some condition
  on packets that implies that the difference in their [u_seqNum] is
  at most a, and suppose duplicates are bounded by k. Then
  we can bound the number of unique packets between them by a + k*)

(*The crucial lemma we need which gives the entire relation:
  If the reordering is bounded by a and the duplicate packets
  are bounded by k, then for ANY instances of two packets with
  bounded reordering,
  the "time" between the two occurrences is at most a + k*)
Lemma packets_reorder_dup_bound (default: pack) (P: pack -> Prop) 
  (a k: nat):
  (forall p1 p2, P p1 -> P p2 -> 
    nat_abs_diff (u_seqNum p1) (u_seqNum p2) <= a) ->
  duplicates_bounded default k ->
  forall p1 p2 l1 l2 l3,
  received = l1 ++ [:: p1] ++ l2 ++ [:: p2] ++ l3 ->
  p1 \notin l1 ->
  P p1 ->
  P p2 ->
  size (undup_fst (l1 ++ [:: p1] ++ l2)) -
  size (undup_fst l1) <= a + k.
Proof.
  rewrite /duplicates_bounded => Hallp Hdups p1 p2 l1 l2 l3 Hrec 
    Hnotin1 Hpp1 Hpp2.
  (*Need a few results/bounds first for multiple cases*)
  have Hnth3: nth default received (size l1 + size l2 + 1) = p2.
    rewrite Hrec nth_cat.
    have->:size l1 + size l2 + 1 < size l1 = false by solve_by_lia.
    rewrite /=.
    have->/=: size l1 + size l2 + 1 - size l1 = (size l2).+1 by solve_by_lia.
    by rewrite nth_cat ltnn subnn.
  have Hle1: size (undup_fst (l1 ++ [:: p1] ++ l2)) <=
    size (undup_fst l1) + size l2 + 1.
    eapply leq_trans. apply size_undup_fst_app.
    rewrite -addnA leq_add2l.
    eapply leq_trans. apply size_undup_fst_le.
    by rewrite addn1.
  (*Proof idea: consider first ocurrence of p2, it can be
    in l1, it can be p1 or it can be the [p2] we have. The proof is
    tedious but not terribly hard.*)
  case Hp2in: (p2 \in l1).
  - have Hnth1: nth default l1 (index p2 l1) = p2 by apply nth_index.
    have Hnth2: nth default received (index p2 l1) = p2.
      rewrite Hrec nth_cat.
      have->//: index p2 l1 < size l1 by rewrite index_mem.
    (*maybe generalize for cases (just index in received and size one)*)
    have Hbound: (size l1 + size l2 + 1) - (index p2 l1) <= k.
      apply Hdups => //.
      eapply leq_trans. apply index_size. by rewrite -addnA leq_addr.
      rewrite Hrec -!size_length !size_cat /=; solve_by_lia.
      by rewrite Hnth2 Hnth3.
    have Hidx: index p2 l1 <= size l1 by apply index_size.
    solve_by_lia.
  - (*Otherwise, first ocurrence is after. It could be equal to p1,
      or it could be in l2, or it could be our occurence of p2.
      We need to consider each case. First, we prove a general lemma*)
    have Hseqp1:size (undup_fst l1) = u_seqNum p1. {
      symmetry.
      by rewrite /u_seqNum Hrec u_seqNum_size_eq.
    }
    rewrite Hseqp1.
    (*Now we have to know whether p1 = p2 or not*)
    case: (p1 == p2) /eqP => Hp12.
    + (*In this case, we use the 2 locations of p2 to get the
        k bound directly*) rewrite Hp12 in Hrec. 
      have Hnth1: nth default received (size l1) = p2 by
        rewrite Hrec nth_cat ltnn subnn.
      have Hbound: size l2 + 1 <= k. {
        have->:size l2 + 1 = (size l1 + size l2 + 1) - size l1 by solve_by_lia.
        apply Hdups. solve_by_lia. rewrite Hrec -size_length !size_cat /=.
        solve_by_lia. by rewrite Hnth1 Hnth3.
      }
      eapply leq_trans. apply leq_sub2r. apply Hle1.
      rewrite Hseqp1.
      solve_by_lia.
    + (*Now we consider whether p2 is in l2 or not. This is the case
      that requires the sum, rather than just a max - we need to use
      the a bound between p1 and the first ocurrence of p2, then use
      the k bound between the first ocurrence of p2 and the one we care
      about*)
      case Hinp2: (p2 \in l2).
      * (*The harder case, with 2 bounds*)
        (*We would like a separate lemma for this case, because it
          is quite similar to above, but we
          cannot get a tight enough bound if we prove p1 -> p2
          and dups separately (first bound only max(a, k))*)
        have [l2_a [l2_b [Hl2 Hnotin2]]]:= find_first Hinp2. 
        rewrite Hl2.
        have Hseqp2: size (undup_fst (l1 ++ [:: p1] ++ l2_a)) =
          u_seqNum p2.
        {
          rewrite /u_seqNum Hrec Hl2 -!catA.
          have->: (l1 ++ [:: p1] ++ l2_a ++ [:: p2] ++ l2_b ++ [:: p2] ++ l3) =
          ((l1 ++ [:: p1] ++ l2_a) ++ [::p2] ++ (l2_b ++ [:: p2] ++ l3)) by
          rewrite !catA.
          rewrite u_seqNum_size_eq // !mem_cat Hp2in in_cons in_nil
            (negbTE Hnotin2) !orbF /=. apply /eqP. by auto.
        }
        have->:(l1 ++ [:: p1] ++ l2_a ++ [:: p2] ++ l2_b) =
        (l1 ++ [:: p1] ++ l2_a) ++ ([::p2] ++ l2_b) by rewrite !catA.
        eapply leq_trans. apply leq_sub2r.
        apply size_undup_fst_app.
        have Hleseq: u_seqNum p1 <= u_seqNum p2.
          rewrite -Hseqp1 -Hseqp2.
          eapply leq_trans. 2: apply size_undup_fst_le_app.
          by apply leqnn.
        rewrite Hseqp2 -addnBAC //.
        apply leq_add. 
        have->: u_seqNum p2 - u_seqNum p1 = nat_abs_diff (u_seqNum p1) (u_seqNum p2) by
        rewrite nat_abs_diff_leq.
        by apply Hallp.
        eapply leq_trans. apply size_undup_fst_le.
        have Hnth1: nth default received (size l1 + size l2_a + 1) = p2. {
          rewrite Hrec Hl2 nth_cat.
          have->: size l1 + size l2_a + 1 < size l1 = false by solve_by_lia.
          have->:(size l1 + size l2_a + 1 - size l1 = size l2_a + 1) by
            solve_by_lia.
          rewrite addn1/= nth_cat !size_cat/=.
          have->: size l2_a < size l2_a + (size l2_b).+1 by solve_by_lia.
          by rewrite nth_cat ltnn subnn.
        }
        have: (size l1 + size l2 + 1) - (size l1 + size l2_a + 1) <= k.
          apply Hdups. rewrite Hl2 !size_cat /=. solve_by_lia.
          rewrite Hrec -size_length !size_cat /=. solve_by_lia.
          by rewrite Hnth1 Hnth3.
        rewrite Hl2 size_cat /= => Hle. solve_by_lia.
      * (*The easier case: can use a bound directly*)
        have Hseqp2: size (undup_fst (l1 ++ [:: p1] ++ l2)) =
        u_seqNum p2.
        {
          rewrite /u_seqNum Hrec.
          have->:  (l1 ++ [:: p1] ++ l2 ++ [:: p2] ++ l3) =
            (l1 ++ [:: p1] ++ l2) ++ [::p2] ++ l3 by rewrite !catA.
          rewrite u_seqNum_size_eq // !mem_cat Hinp2 Hp2in in_cons in_nil !orbF.
          apply /eqP. by auto.
        }
        have Hleseq: u_seqNum p1 <= u_seqNum p2.
          rewrite -Hseqp1 -Hseqp2.
          eapply leq_trans. 2: apply size_undup_fst_le_app.
          by apply leqnn.
        rewrite Hseqp2. eapply leq_trans. 2: apply leq_addr.
        rewrite -nat_abs_diff_leq //. by apply Hallp.
Qed.

(*We need this version, a simple corollary*)
Lemma packets_reorder_dup_bound' (default: pack) (P: pack -> Prop) 
  (a k: nat):
  (forall p1 p2, P p1 -> P p2 -> 
    nat_abs_diff (u_seqNum p1) (u_seqNum p2) <= a) ->
  duplicates_bounded default k ->
  forall p1 p2 l1 l2 l3,
  received = l1 ++ [:: p1] ++ l2 ++ [:: p2] ++ l3 ->
  p1 \notin l1 ->
  P p1 ->
  P p2 ->
  size (undup_fst (l1 ++ [:: p1] ++ l2 ++ [:: p2])) -
  size (undup_fst (l1 ++ [:: p1])) <= a + k.
Proof.
  move=> Hallp Hdups p1 p2 l1 l2 l3 Hrec Hnotin1 Hpp1 Hpp2.
  rewrite !catA !undup_fst_rcons (negbTE Hnotin1) size_cat/= -!catA.
  have Hle: size (undup_fst (l1 ++ [:: p1] ++ l2)) + 1 - 
    (size (undup_fst l1) + 1) <= a + k by
    rewrite subnDr; apply (packets_reorder_dup_bound Hallp Hdups Hrec).
  case Hin: (p2 \in l1 ++ [:: p1] ++ l2).
  - eapply leq_trans;[| apply Hle]. rewrite -addnBAC.
    by rewrite leq_addr.
    have Hmid: (size (undup_fst (l1 ++ [:: p1])) <= 
      size (undup_fst (l1 ++ [:: p1] ++ l2))) by 
      rewrite catA; apply size_undup_fst_le_app.
    eapply leq_trans;[|apply Hmid].
    by rewrite undup_fst_rcons (negbTE Hnotin1) size_cat.
  - by rewrite size_cat.
Qed.

End Defs.

End SeqNums.