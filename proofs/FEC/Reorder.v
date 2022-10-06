(*Require Import AbstractEncoderDecoder.
Require Import RSEEncoderDecoder.
Require Import VST.floyd.functional_base.
Require Import ByteFacts.
Require Import Block. *)
Require Import CommonSSR.
Require Import Lia.
(*Require Import AssocList.
Require Import IP.
Require Import AbstractEncoderDecoder.
Require Import CommonSSR.
Require Import ReedSolomonList.
Require Import ZSeq.
Require Import Endian.*)

(*Require Import ByteField. (*For byte equality - TODO: move to ByteFacts*)*)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(*Versions without changing params or timeouts*) (*TODO: move*)
(*
Section Simple.

Variable k : Z.
Variable h : Z.
Variable Hkbound: 0 < k <= fec_n - 1 - fec_max_h.
Variable Hhbound: 0 < h <= fec_max_h.

Definition rse_encode_gen_nochange (blocks: seq block) (currBlock: option block) (curr: packet) :=
  match currBlock with
  | Some b => 
      let t := encode_exist curr b in (t.1.1 ++ blocks, t.1.2, t.2)
  | None => 
      let t := encode_new curr k h in (t.1.1 ++ blocks, t.1.2, t.2)
  end.

Definition rse_encode_concat_nochange (orig: seq packet) : list block * option block * list (list fec_packet_act) :=
  foldl (fun acc x =>
    let t := rse_encode_gen_nochange acc.1.1 acc.1.2 x in
    (t.1.1, t.1.2, acc.2 ++ [:: t.2])) (nil, None, nil) orig.
(*can easily get rse_encode_all_nochange from this if we need it*)

End Simple.
*)

(** Sequence numbers and reordering*)

(*We follow the notation of the RD metric for measuring reordering. We don't need the full histogram; instead,
  we will place a bound on the maximum allowable displacement*)

(*First, we need to define the displacement*)

Section SeqNums.

Open Scope nat_scope.

(*TODO: move*)
Definition nat_abs_diff (n1 n2: nat) : nat :=
  maxn (n1 - n2) (n2 - n1).

Lemma nat_abs_diff_sym: forall n1 n2,
  nat_abs_diff n1 n2 = nat_abs_diff n2 n1.
Proof.
  move => n1 n2. by rewrite /nat_abs_diff maxnC.
Qed.

(*TODO: move*)
Lemma maxn_0: forall n m,
  maxn n m = 0 ->
  n = 0 /\ m = 0.
Proof.
  move=> n. case: n=> [//|/= n'  [//| m' //]].
  move => m. by rewrite max0n => ->.
  rewrite /maxn. by case: (n'.+1 < m'.+1).
Qed.

Lemma nat_abs_diff_0: forall n1 n2,
  nat_abs_diff n1 n2 = 0 ->
  n1 = n2.
Proof.
  move=> n1 n2. rewrite /nat_abs_diff => Hmax.
  apply maxn_0 in Hmax.
  case: Hmax => /eqP Hn12 /eqP. move: Hn12.
  rewrite !subn_eq0 => Hn12 Hn21.
  apply /eqP. by rewrite eqn_leq Hn12 Hn21.
Qed.

Lemma maxn_r: forall n1 n2,
  n1 <= n2 ->
  maxn n1 n2 = n2.
Proof.
  move=> n1 n2 Hn12. rewrite /maxn.
  move: Hn12; rewrite leq_eqVlt => /orP[/eqP Hn12 | -> //].
  by rewrite Hn12 ltnn.
Qed.

Lemma nat_abs_diff_leq: forall n1 n2,
  n1 <= n2 ->
  nat_abs_diff n1 n2 = n2 - n1.
Proof.
  move=> n1 n2 Hn12. rewrite /nat_abs_diff.
  apply maxn_r.
  have Hn0: n1 - n2 <= 0 by
    rewrite -subn_eq0 in Hn12; move: Hn12 => /eqP ->.
  apply (leq_trans Hn0). by rewrite leq_subRL // addn0.
Qed.

Lemma nat_abs_diff_leq': forall n1 n2,
  n2 <= n1 ->
  nat_abs_diff n1 n2 = n1 - n2.
Proof.
  move=> n1 n2 Hn12. rewrite nat_abs_diff_sym. by apply nat_abs_diff_leq.
Qed.

(*Useful in expanding [nat_abs_diff]*)
Lemma abs_ineq: forall n1 n2,
  (n1 < n2) =
  (n1 - n2 < n2 - n1).
Proof.
  move=> n1 n2. case Hn12: (n1 < n2).
  - have ->: n1 - n2 = 0. apply /eqP. rewrite subn_eq0. by apply ltnW.
    by rewrite subn_gt0.
  - have->: n2 - n1 = 0. apply /eqP. by rewrite subn_eq0 leqNgt Hn12.
    by rewrite ltn0.
Qed.

(*Inequalities with nats are annoying to prove manually*)
Ltac solve_by_lia :=
  repeat match goal with
  | H: is_true (?x < ?y) |- _ => move: H => /ltP H
  | H: is_true (?x <= ?y) |- _ => move: H => /leP H
  | H: (?x < ?y) = ?b |- _ => move: H => /ltP H
  | H: (?x <= ?y) = ?b |- _ => move: H => /leP H
  | |- context [ ?x - ?y] => have->: (x - y = (x - y)%coq_nat) by []
  | |- context [?x + ?y] => have->: (x + y = (x + y)%coq_nat) by []
  | |- is_true (?x < ?y) => apply /ltP
  | |- is_true (?x <= ?y) => apply /leP
  end; lia. 

(*A version of the triangle inequality:
  |n2 - n3| <= |n2 - n1| + |n3 - n1|*)
Lemma nat_abs_diff_triag: forall n1 n2 n3,
  nat_abs_diff n1 n2 <=
  nat_abs_diff n1 n3 + nat_abs_diff n2 n3.
Proof.
  move=> n1 n2 n3. rewrite /nat_abs_diff/maxn -!abs_ineq.
  case Hn12: (n1 < n2); case Hn23: (n2 < n3); case Hn13: (n1 < n3); solve_by_lia.
Qed.

Variable pack : eqType.

Section Defs.

Variable sent : seq pack.
Variable received : seq pack.

(*All received packets were sent*)
Variable rec_sub: {subset received <= sent}.
(*forall x, x \in received -> x \in sent.*)

(*Problem: are we looking at this as a completed transcript or as an ongoing one? If completed, can calcuate
  the displacement. If not, then need to use DT. We will try a DT-based method. But this is annoying and imperative
  let's first try to assume we know the missing packets*)

Definition o_seqNum (p: pack) :=
  index p sent.

  (*TODO: move*)
Lemma index_inj: forall {A: eqType} (l: list A) (x y: A),
  x \in l ->
  y \in l ->
  index x l = index y l ->
  x = y.
Proof.
  move=> A l. elim : l => [// | /= h t IH x y].
  rewrite !in_cons.
  case : (x == h) /eqP => Hxh;
  case : (y == h) /eqP => Hy; subst; try rewrite eq_refl //=.
  - have->//: h == y = false. apply /eqP; auto.
  - have->//: h == x = false. apply /eqP; auto.
  - move => /= Hinx Hiny. 
    have->/=: h == x = false by apply /eqP; auto.
    have->/=: h == y = false by apply /eqP; auto.
    move=> [Hidx]. by apply IH.
Qed.

Lemma o_seqNum_inj: forall p1 p2,
  p1 \in sent ->
  p2 \in sent ->
  o_seqNum p1 = o_seqNum p2 ->
  p1 = p2.
Proof.
  move=> p1 p2. rewrite /o_seqNum.
  apply index_inj.
Qed.

(*Keep first appearance rather than last*)
Definition undup_fst {A: eqType} (s: seq A) :=
  rev (undup (rev s)).

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

Fixpoint s_incr (s: seq nat) :=
  match s with
  | nil => true
  | x :: tl =>
    match tl with
    | nil => true
    | y :: tl' => (x < y) && s_incr tl
    end
  end.

Lemma ltn1: forall n,
  n < 1 = (n == 0).
Proof.
  by move=>[|n].
Qed.

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


(*The key lemma in TODO: given a strictly increasing list, if we look at
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

(*Stuff about [uniq_fst] TODO move*)
(*NOTE: we don't use the fact that it keeps the first ocurrence. We will
  use this when we need to mantain info in the implementation*)

Lemma undup_fst_uniq: forall {A: eqType} (s : seq A),
  uniq (undup_fst s).
Proof.
  move=> A s. rewrite /undup_fst rev_uniq.
  by apply undup_uniq.
Qed.

Lemma mem_undup_fst: forall {A: eqType} (s: seq A),
  undup_fst s =i s.
Proof.
  move=> A s. rewrite /undup_fst => x.
  by rewrite mem_rev mem_undup mem_rev.
Qed. 

Lemma undup_fst_subset: forall {A: eqType} (s1 s2: seq A),
  {subset s1 <= s2} ->
  {subset (undup_fst s1) <= (filter (fun x => x \in s1) s2) }.
Proof.
  move=> A s1 s2 Hsub x.
  rewrite mem_undup_fst => Hin.
  rewrite mem_filter Hin. by apply Hsub.
Qed.

Lemma size_undup_fst: forall {A: eqType} (s1 s2: seq A),
  {subset s1 <= s2} ->
  size (undup_fst s1) <= size (filter (fun x => x \in s1) s2).
Proof.
  move=> A s1 s2 Hsub. apply uniq_leq_size.
  apply undup_fst_uniq. by apply undup_fst_subset.
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
(*BUT: we need the uniqueness of the sending list for this - TODO: 
  is this a problem (we will probably not be able to allow duplicates
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
  

(*The second condition: if there are any duplicates, they are separated by at most k
  packets*)
(*TODO: this condition will be important in showing that our implementation correctly
keeps track of the number of unique packets seen. But it is not needed for our
bounds here*)
Definition duplicates_bounded (default: pack) (k: nat) : Prop :=
  forall i j, 
  (i <= j) -> 
  (j < length received) ->
  nth default received  i = nth  default received j ->
  (j - i <= k).

End Defs.

End SeqNums.


(*TODO: 
  1. (DONE) version of decoder with explicit timeouts (compare time of packet), show this is a refinement
  of previous (ie: exists some state that makes this ok)
  2. show that encoder is equivalent to previous where all states are (k, h)
  3. Define version of decoder without any timeouts
  4. Define props from before about reordering, seqNum, time
  5. Show that if these props hold, the two decoder versions are equivalent (hence, no timeouts)
  6. Define props from before about limited losses
  7. (big one) show that whole correctness theorem applies with simpler decoder/encoder*)