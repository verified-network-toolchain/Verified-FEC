(*More general results we need in various places in the FEC proofs*)
Require Import VST.floyd.functional_base.
Require Import CommonSSR.

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Ltac split_all := repeat match goal with | |- ?p /\ ?q => split end.

(*Put inequalities and numeric goals in a form such that
  we can use ssreflect lemmas*)
Ltac to_ssrnat :=
  repeat match goal with
  (*First, try to simplify the goal directly*)
  | |- (?x < ?y)%coq_nat => apply /ltP
  | |- (?x <= ?y)%coq_nat => apply /leP
  | |- (Z.of_nat ?x < Z.of_nat ?y)%Z => apply inj_lt
  | |- (Z.of_nat ?x <= Z.of_nat ?y)%Z => apply inj_le
  | |- Z.of_nat ?x = Z.of_nat ?y => apply Nat2Z.inj_iff
  (*Then search for rewrites*)
  | |- context [ Z.to_nat (Z.of_nat ?x)] => rewrite Nat2Z.id
  | |- context [(?x + ?y)%coq_nat] => have->:(x + y)%coq_nat = x+y by []
  | |- context [(?x * ?y)%coq_nat] => have->:(x*y)%coq_nat = x*y by []
  | |- context[(Z.of_nat ?x < Z.of_nat ?y)%Z] => rewrite -Nat2Z.inj_lt
  | |- context[(Z.of_nat ?x <= Z.of_nat ?y)%Z] => rewrite -Nat2Z.inj_le
  | |- context [(?x < ?y)%coq_nat] => rewrite (rwP ltP)
  | |- context [(?x <= ?y)%coq_nat] => rewrite (rwP leP)
  | |- context [ Z.of_nat ?x = Z.of_nat ?y] => rewrite (@Nat2Z.inj_iff x y)
  | |- context [Z.of_nat ?x = 0%Z] => have->: 0%Z = Z.of_nat 0 by []
  | |- context [(Z.of_nat ?x * Z.of_nat ?y)%Z] => rewrite -Nat2Z.inj_mul
  end.

(*We have lots of general results:*)

Local Open Scope nat_scope.

(*Rewriting lemmas*)
Section Rewrite.

Lemma cons_app: forall {A: Type} (x : A) (l: seq A),
  x :: l = [:: x] ++ l.
Proof.
  by [].
Qed.

Lemma map_nil {A B: eqType} (f: A -> B) (s: seq A):
  (map f s == [::]) = (s == [::]).
Proof.
  by case: s.
Qed.

Lemma cat_cons': forall {A: Type} (s1 s2: seq A) (x: A),
  s1 ++ x :: s2 = (s1 ++ [:: x]) ++ s2.
Proof.
  move=> A s1 s2 x. by rewrite -catA.
Qed.

Lemma double_cons_cat {A: Type} (x1 x2: A) (s: seq A):
  x1 :: x2 :: s = [:: x1; x2] ++ s.
Proof.
  by [].
Qed.

Lemma Zlength_size: forall {A: Type} (s: seq A),
  Zlength s = Z.of_nat (size s).
Proof.
  move=> A s. by rewrite Zlength_correct size_length.
Qed.

Lemma size_Zlength: forall {A: Type} (s: seq A),
  size s = Z.to_nat (Zlength s).
Proof.
  move=> A s. by rewrite ZtoNat_Zlength size_length.
Qed.

Lemma Zlength_rev: forall {A: Type} (s: seq A),
  Zlength (rev s) = Zlength s.
Proof.
  move => A s. by rewrite !Zlength_size size_rev.
Qed.

Lemma concat_flatten: forall {A: Type} (s: seq (seq A)),
  concat s = flatten s.
Proof. by []. Qed.

End Rewrite.

Section Perm.

Lemma count_perm: forall {A: eqType} (p: pred A) (s1 s2: seq A),
  perm_eq s1 s2 ->
  count p s1 = count p s2.
Proof. 
  by move=> A p s1 s2 /permP => /(_ p).
Qed.

Lemma perm_catC': forall [T : eqType] (s1 s2 : seq T), 
  perm_eq (s1 ++ s2) (s2 ++ s1).
Proof.
  move=> T s1 s2. by have:=(perm_catC s1 s2) => /(_ (s2 ++ s1));
  rewrite perm_refl.
Qed.

Lemma perm_rev': forall {T: eqType} (s: seq T),
  perm_eq s (rev s).
Proof.
  move => T s. have /(_ s):=(perm_rev s). by rewrite perm_refl perm_sym.
Qed.

End Perm.

(*Results about [filter]*)
Section Filter.

Section FilterSize.

Lemma Zlength_filter: forall {A: Type} (p: pred A) (l: list A),
  (Zlength (filter p l) <= Zlength l)%Z.
Proof.
  move => A p l. rewrite !Zlength_size size_filter.
  to_ssrnat. by rewrite count_size.
Qed.

Lemma filter_all_Zlength: forall {A: eqType} (p: pred A) (s: seq A),
  Zlength (filter p s) = Zlength s <-> all p s.
Proof.
  move => A p s. rewrite !Zlength_size. to_ssrnat. split;
  by rewrite -filter_all_size => /eqP.
Qed.

Lemma size_filter_lt: forall {A: Type} (p: pred A) (s: seq A),
  (size (filter p s) < size s) = ~~ all p s.
Proof.
  move=> A p s. rewrite size_filter all_count.
  have:=(count_size p s).
  rewrite leq_eqVlt => /orP[/eqP -> | Hlt].
  - by rewrite ltnn eq_refl.
  - rewrite Hlt. move: Hlt. by rewrite ltn_neqAle => /andP[Hneq _].
Qed. 

Lemma filter_none_Zlength: forall {A: eqType} (p: pred A) (s: seq A),
  Zlength [seq x <- s | p x] = 0%Z <-> ~~ has p s.
Proof.
  move=> A p s. rewrite Zlength_size has_filter. to_ssrnat. 
  rewrite negbK -size_eq0. 
  by apply (reflect_iff _ _ eqP).
Qed.

Lemma filter_Zlength_lt: forall {A: eqType} (p: pred A) (s: seq A),
  (Zlength [seq x <- s | p x] < Zlength s)%Z <-> ~~ all p s.
Proof.
  move=> A p s. rewrite -size_filter_lt !Zlength_size. 
  by to_ssrnat.
Qed.

End FilterSize.

Lemma filter_concat {A: Type} (l: list (list A)) (p: A -> bool):
  filter p (concat l) = concat (map (fun x => filter p x) l).
Proof.
  elim: l=>[//|h t IH/=].
  by rewrite filter_cat IH.
Qed.

Lemma mem_filter': forall {T: eqType} (a: pred T) (x: T) (s: seq T),
  x \in [seq x <- s | a x] ->
  x \in s.
Proof.
  move=> T a x s. by rewrite mem_filter => /andP[_].
Qed.


Lemma filter_partition_perm: forall {A: eqType} (p: pred A) (s: seq A),
  perm_eq s ([seq x <- s | p x] ++ [seq x <- s | predC p x]).
Proof.
  move=> A p s. by have:=(perm_filterC p s) => /(_ s);
  rewrite perm_refl perm_sym.
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

End Filter.

Local Open Scope nat_scope.

Section Zip.

Lemma zip_nil: forall {A B: Type} (l: list B),
  zip (@nil A) l = nil.
Proof.
  move => A B l. by case: l.
Qed.

Lemma zip_nil_r: forall {A B: Type} (s: seq A),
  zip s (@nil B) = [::].
Proof.
  move => A B s. by case: s.
Qed. 

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

End Zip.

(*Inequalities with nats are annoying to prove manually*)
Ltac solve_by_lia :=
  (*Convert addition and subtraction in terms in hypothesis H*)
  let rec simpl_expr e H :=
    try match e with
    | context [ ?x - ?y] => let temp:= fresh in
       have temp: (x - y = (x - y)%coq_nat) by [];
       rewrite temp in H; clear temp;
        simpl_expr x H; simpl_expr y H
    | context [?x + ?y] => let temp := fresh in 
      have temp: (x + y = (x + y)%coq_nat) by [];
      rewrite temp in H; clear temp;
      simpl_expr x H; simpl_expr y H
    end in
  repeat match goal with
  | H: is_true (?x < ?y) |- _ =>  simpl_expr x H; simpl_expr y H; move: H => /ltP H
  | H: is_true (?x <= ?y) |- _ =>  simpl_expr x H; simpl_expr y H;  move: H => /leP H
  | H: (?x < ?y) = ?b |- _ => simpl_expr x H; simpl_expr y H; move: H => /ltP H
  | H: (?x <= ?y) = ?b |- _ => simpl_expr x H; simpl_expr y H; move: H => /leP H
  | |- context [ ?x - ?y] => have->: (x - y = (x - y)%coq_nat) by []
  | |- context [?x + ?y] => have->: (x + y = (x + y)%coq_nat) by []
  | |- is_true (?x < ?y) => apply /ltP
  | |- is_true (?x <= ?y) => apply /leP
  | |- (?x < ?y) = ?b => apply /ltP
  | |- (?x <= ?y) = ?b => apply /leP 
  end; lia. 

Section Nat.

Lemma ltn_0: forall (n m: nat),
  n < m ->
  0 < m.
Proof.
  move=> n m. case: n=>// n' Hn'.
  by eapply ltn_trans; last by apply Hn'.
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

Lemma ltn1: forall n,
  n < 1 = (n == 0).
Proof.
  by move=>[|n].
Qed.

Lemma len1: forall (n: nat),
  (n <= 1)%N = (n == 0)%N || (n == 1)%N.
Proof.
  move=> n. case: n=>//= n'.
  by rewrite ltn1.
Qed.

Section NatAbsDiff.

(* | n1 - n2 | *)

Definition nat_abs_diff (n1 n2: nat) : nat :=
  maxn (n1 - n2) (n2 - n1).

Lemma nat_abs_diff_sym: forall n1 n2,
  nat_abs_diff n1 n2 = nat_abs_diff n2 n1.
Proof.
  move => n1 n2. by rewrite /nat_abs_diff maxnC.
Qed.

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

(*A version of the triangle inequality:
  |n2 - n3| <= |n2 - n1| + |n3 - n1|*)
Lemma nat_abs_diff_triag: forall n1 n2 n3,
  nat_abs_diff n1 n2 <=
  nat_abs_diff n1 n3 + nat_abs_diff n2 n3.
Proof.
  move=> n1 n2 n3. rewrite /nat_abs_diff/maxn -!abs_ineq.
  case Hn12: (n1 < n2); case Hn23: (n2 < n3); case Hn13: (n1 < n3); solve_by_lia.
Qed.

Lemma nat_abs_diff_add: forall (m n1 n2: nat),
  nat_abs_diff (m + n1) (m + n2) =
  nat_abs_diff n1 n2.
Proof.
  move=> m n1 n2. by rewrite /nat_abs_diff !subnDl.
Qed.

(*For any two elements, the difference between their indicies
  is at most the size of the list*)
Lemma index_diff_le_size: forall {A: eqType} (s: seq A) (x1 x2: A),
  nat_abs_diff (index x1 s) (index x2 s) <= size s.
Proof.
  move=> A s x1 x2. wlog: x1 x2 / (index x1 s <= index x2 s).
  - move=> Hgen. 
    case: (orP (leq_total (index x1 s) (index x2 s))) => [Hle | Hle].
    + by apply Hgen.
    + rewrite nat_abs_diff_sym. by apply Hgen.
  - move=> Hle. rewrite nat_abs_diff_leq //.
    apply (leq_trans (leq_subr _ _)).
    by rewrite index_size.
Qed.

End NatAbsDiff.

End Nat.

Section SublistConcat.

Lemma size_concat: forall {A: Type} (n: nat) (s: seq (seq A)),
  all (fun l => size l == n) s ->
  size (concat s) = size s * n.
Proof.
  move=> A n s. elim: s => [// | h t /= IH /andP[/eqP Hsz Hall]].
  by rewrite size_cat Hsz IH.
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
  rewrite /sublist. to_ssrnat.
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

Lemma mem_sublist: forall {A: eqType} (s: seq A) (lo hi: Z) (x: A),
  x \in sublist lo hi s ->
  x \in s.
Proof.
  move=> A s lo hi x. rewrite /sublist skipn_drop firstn_take => Hin.
  apply mem_drop in Hin.
  by apply mem_take in Hin.
Qed.

Lemma index_flatten_same_eq: forall {A: eqType} (s: seq (seq A)) (s1: seq A)
  (x1 x2: A),
  x1 \in s1 ->
  x2 \in s1 ->
  s1 \in s ->
  uniq (flatten s) ->
  (*Key: n is the same for both, so we can reason about the
    difference*)
  exists n,
    index x1 (flatten s) = n + index x1 s1 /\
    index x2 (flatten s) = n + index x2 s1.
Proof.
  move=> A s. elim s=>//= h t IH s1 x1 x2 Hinx1 Hinx2.
  rewrite in_cons => /orP[/eqP Hs1h | Hs1t] Huniq.
  - subst. exists 0.
    by rewrite !index_cat Hinx1 Hinx2.
  - rewrite !index_cat. 
    move: Huniq. rewrite cat_uniq => /andP[Huniqh /andP[Hnotin Huniqt]].
    move: IH => /(_ s1 x1 x2 Hinx1 Hinx2 Hs1t Huniqt) [n [Hidx1 Hidx2]].
    exists (size h + n).
    case Hinx1': (x1 \in h).
      exfalso. move: Hnotin => /hasP. apply. exists x1=>//.
      apply /flattenP. by exists s1.
    case Hinx2': (x2 \in h).
      exfalso. move: Hnotin => /hasP. apply. exists x2=>//.
      apply /flattenP. by exists s1.
    by rewrite Hidx1 Hidx2 !addnA.
Qed.

(*If two elements are in a list, the difference between their
  indicies is smaller than the size of the list*)
Lemma index_flatten_same: forall {A: eqType} (s: seq (seq A)) (s1: seq A)
  (x1 x2: A),
  x1 \in s1 ->
  x2 \in s1 ->
  s1 \in s ->
  uniq (flatten s) ->
  nat_abs_diff (index x1 (flatten s)) (index x2 (flatten s)) <= size s1.
Proof.
  move=> A s s1 x1 x2 Hinx1 Hinx2 Hins1 Huniq.
  have[n [Hidx1 Hidx2]]:=(index_flatten_same_eq Hinx1 Hinx2 Hins1 Huniq).
  rewrite Hidx1 Hidx2 nat_abs_diff_add.
  by rewrite index_diff_le_size.
Qed.

End SublistConcat.

Section Map.

Lemma pmap_id_inv: forall {A: Type}(s: seq (option A)) (t: seq A),
  map Some t = s ->
  t = pmap id s.
Proof.
  move=> A s t Hall. subst. elim: t => [// | h t /= IH].
  by rewrite -IH.
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

End Map.

Section Mem.

(*Should we replace in CommonSSR?*)
Lemma inP: forall {A: eqType} (x: A) (l: seq A),
  reflect (In x l) (x \in l).
Proof.
  move=> A x l. elim: l => [//= | h t /= IH].
  - by apply ReflectF.
  - rewrite in_cons. apply orPP => //.
    rewrite eq_sym. apply eqP.
Qed.

Lemma mem_rev_orig: forall {T: eqType} (l: seq T) (y x: T),
  y \in rem x l ->
  y \in l.
Proof.
  move=> T l y x. elim: l =>[// | h t /= IH].
  case: (h == x) /eqP => Heq.
  - rewrite in_cons =>->. by rewrite orbT.
  - rewrite !in_cons => /orP[Hyh | Ht]. by rewrite Hyh.
    by rewrite IH // orbT.
Qed.

Lemma existsbP: forall {A: eqType} {s: seq A} {P: A -> bool},
  reflect (exists x, (x \in s) && P x) (List.existsb P s).
Proof.
  move=> A s P. elim: s => [//= | hd tl /= IH].
  - by apply ReflectF => [[]].
  - case Hhd: (P hd).
    + apply ReflectT. exists hd. by rewrite mem_head Hhd.
    + move: IH. case Htl: (List.existsb P tl) => IH.
      * apply ReflectT. apply elimT in IH =>//.
        case: IH => [x /andP[Hintl Hp]].
        exists x. by rewrite in_cons Hintl orbT.
      * apply ReflectF. apply elimF in IH=>//.
        move => [x]. 
        rewrite in_cons => /andP[/orP[/eqP Hx | Hintl] Hpx]; subst.
        by rewrite Hpx in Hhd. apply IH. exists x.
        by rewrite Hintl Hpx.
Qed.

End Mem.

(*Suppose there are at least unique k items in a list in another list. 
  Then, we can find the point at which the kth
  unique item appears.*)
Section FindLast.

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

Section Count.

(*Crucial lemmas for relating the size of the current block
  with the number of elements satisfying a predicate in the stream.*)

Lemma all_in_count_aux {A B: eqType} (p2: pred B) (s: seq A) 
  (s2: seq B) (f: A -> B):
  uniq s ->
  {in s &, injective f} ->
  all (fun x => p2 (f x) && (f x \in s2)) s ->
  size s = 
  count [pred x | p2 x & x \in [seq f i | i <- s]] (undup s2).
Proof.
  move: s2. elim: s => 
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
  by rewrite count_cat count_filter/=/predI 
    (all_in_count_aux Huniq Hinj Hall) leq_addr.
Qed.

(*In fact, we can say something stronger if everything satisfying
  p2 in s2 is in s1*)
Lemma all_in_count_eq {A B: eqType} (p2: pred B) (s: seq A) 
  (s2: seq B) (f: A -> B):
  uniq s ->
  {in s &, injective f} ->
  all (fun x => p2 (f x) && (f x \in s2)) s ->
  all (fun x => x \in (map f s)) (filter p2 s2) ->
  size s = count p2 (undup s2).
Proof.
  move=> Huniq Hinj Hall1 Hall2.
  erewrite count_perm; last by 
    apply (filter_partition_perm (fun x => x \in (map f s))).
  rewrite count_cat count_filter/=/predI 
    (all_in_count_aux Huniq Hinj Hall1).
  have->: count p2 [seq x <- undup s2 | x \notin [seq f i | i <- s]] = 0;
    last by rewrite addn0.
  rewrite -size_filter -filter_predI. apply /eqP.
  rewrite size_eq0 -(negbK (_ == _)) -has_filter /predI/=.
  apply /hasP => [[x]] Hinx/= /andP[Hp2] Hnotin.
  have Hinx': x \in ([seq x <- s2 | p2 x]) by 
    rewrite mem_filter Hp2 -mem_undup.
  move: Hall2 => /allP /(_ _ Hinx').
  by rewrite (negbTE Hnotin).
Qed.

End Count.

(*Insert in sorted list*)
Section Insert.

Fixpoint insert {T: Type} (r: rel T) (x: T) (s: seq T) :=
  match s with
  | nil => [:: x]
  | y :: tl => if r x y then x :: y :: tl else
    y :: insert r x tl
  end.

Lemma mem_insert: forall {T: eqType} {r: rel T} (x: T) (s: seq T) (y: T),
  y \in (insert r x s) = (y == x) || (y \in s).
Proof.
  move=> T r x s y. elim: s =>[// | h t /= IH].
  case Hxh: (r x h).
  - by rewrite !in_cons.
  - by rewrite !in_cons IH (orbC (y == h)) -orbA (orbC (y \in t)).
Qed.

Lemma insert_hd: forall {T: eqType} (r: rel T) (x: T) (s: seq T),
  all (r x) s ->
  insert r x s = x :: s.
Proof.
  move=> T r x s /allP. case: s =>[// | h t /= Hall].
  have->//: r x h. apply Hall. by rewrite mem_head.
Qed.  

End Insert.

Section FindUniq.

(*We want to show the following: suppose we have lists l1 and l2, and
  in both, there is 1 element satisfying a predicate. Then, if
  we "find" the element from each list, these are equal.*)

 (*If there is only at most 1 element satisfying a predicate in a list,
  then any two elements in the last satisfying the predicate must be
  equal*)
Lemma nth_uniq_eq: forall {A: eqType} (s: seq A) (p: pred A) (x y: A),
  (count p s <= 1)%N ->
  p x ->
  p y ->
  x \in s ->
  y \in s ->
  x = y.
Proof.
  move=> A s p x y. rewrite -size_filter len1 => /orP[/eqP Hnil | 
    /size1P [z Hs]] Hpx Hpy Hinx Hiny.
  - apply size0nil in Hnil.
    have: x \in [seq x <- s | p x] by rewrite mem_filter Hpx.
    by rewrite Hnil.
  - have: x \in [seq x <- s | p x] by rewrite mem_filter Hpx.
    have: y \in [seq x <- s | p x] by rewrite mem_filter Hpy.
    rewrite !Hs !in_cons !orbF => /eqP Hyz /eqP Hxz.
    by rewrite Hyz Hxz.
Qed.

(*The lemma we want*)
Lemma find_uniq_eq: forall {A: eqType} (s1 s2: seq A) (p: pred A) (d: A),
  (count p s1 <= 1)%N ->
  (count p s2 <= 1)%N ->
  has p s1 ->
  has p s2 ->
  (forall x, x \in s1 -> x \in s2) ->
  nth d s1 (find p s1) = nth d s2 (find p s2).
Proof.
  move=> A s1 s2 p def Hc1 Hc2 Hhas1 Hhas2 Hsub.
  case: (findP p s1). by rewrite Hhas1.
  move=> i1 Hi1 Hnth1 Hbef1.
  case: (findP p s2). by rewrite Hhas2.
  move=> i2 Hi2 Hnth2 Hbef2.
  have Hin1: nth def s1 i1 \in s1 by apply mem_nth.
  have Hin2: nth def s1 i1 \in s2 by apply Hsub.
  have Hin2': nth def s2 i2 \in s2 by apply mem_nth.
  by apply (nth_uniq_eq Hc2).
Qed.

End FindUniq.

Section UndupFst.

(*undup_fst*)
(*Keep first appearance rather than last*)
Definition undup_fst {A: eqType} (s: seq A) :=
  rev (undup (rev s)).

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

(*u_seqNum doesn't change when lists are extended*)
Lemma undup_fst_index_cat: forall {A: eqType} (x: A) (l1 l2: list A),
  x \in l1 ->
  index x (undup_fst (l1 ++ l2)) = index x (undup_fst l1).
Proof.
  move=> A x l1 l2 Hin. rewrite /undup_fst.
  rewrite rev_cat undup_cat rev_cat index_cat.
  have->//: x \in rev (undup (rev l1)) by rewrite mem_rev mem_undup mem_rev.
Qed.

(*Can get bound on size of [undup_fst] by considering each separately
(note: lists may be larger because we may be counting later ocurrence)*)
Lemma size_undup_fst_app: forall {A: eqType} (l1 l2: list A),
  size (undup_fst (l1 ++ l2)) <= size (undup_fst l1) + size (undup_fst l2).
Proof.
  move=> A l1 l2. 
  by rewrite /undup_fst !size_rev rev_cat undup_cat size_cat addnC 
    leq_add2l size_filter count_size.
Qed.

Lemma size_undup_fst_le: forall {A: eqType} (l: list A),
  size (undup_fst l) <= size l.
Proof.
  move=> A l. by rewrite /undup_fst size_rev -(size_rev l) size_undup.
Qed.

Lemma size_undup_fst_le_app: forall {A: eqType} (l1 l2: list A),
  size (undup_fst l1) <= size (undup_fst (l1 ++ l2)).
Proof.
  move=> A l1 l2. rewrite /undup_fst !size_rev rev_cat undup_cat size_cat.
  solve_by_lia.
Qed.

(*This is why we define [undup_fst] rather than [undup], which
  keeps the last ocurrence of each element*)
Lemma undup_fst_rcons: forall {A: eqType} (s: seq A) (x: A),
  undup_fst (s ++ [:: x]) = if x \in s then undup_fst s 
    else undup_fst s ++ [:: x].
Proof.
  move=> A s x. rewrite /undup_fst rev_cat/=.
  case Hin: (x \in rev s); rewrite mem_rev in Hin; rewrite Hin =>//.
  by rewrite rev_cons -cats1.
Qed. 

(*Relate [size (undup_fst)] to [u_seqNum]*)
Lemma u_seqNum_size_eq: forall {A: eqType} (l1: list A) (x: A) (l2: list A),
  x \notin l1 ->
  index x (undup_fst (l1 ++ [:: x] ++ l2)) = size (undup_fst l1).
Proof.
  move=> A l1 x l2 Hnotin.
  rewrite catA undup_fst_index_cat; last by rewrite mem_cat in_cons eq_refl orbT.
  rewrite /undup_fst rev_cat undup_cat rev_cat index_cat.
  have->/=: x \in rev (undup (rev l1)) = false by 
    rewrite mem_rev mem_undup mem_rev; apply negbTE.
  have->/=: x \notin rev l1 by rewrite mem_rev.
  by rewrite eq_refl addn0.
Qed.

End UndupFst.

Section OtherList.

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

Lemma find_first {A: eqType} (x: A) (l1: list A):
  x \in l1 ->
  exists l2 l3, l1 = l2 ++ [:: x] ++ l3 /\ x \notin l2.
Proof.
  elim: l1 => [//|h t /= IH].
  rewrite in_cons. case: (x == h) /eqP => Hxh/= => [_ | Hint].
  - rewrite Hxh. exists nil. by exists t.
  - move: IH => /(_ Hint) => [[l2 [l3 [Ht Hxl2]]]].
    rewrite Ht. exists (h :: l2). exists l3. split. by [].
    rewrite in_cons (negbTE Hxl2) orbF. by apply /eqP.
Qed. 

Lemma cat_inj {A: Type} (s1 s2 s3 s4: seq A):
  s1 ++ s2 = s3 ++ s4 ->
  size s1 = size s3 ->
  s1 = s3 /\ s2 = s4.
Proof.
  move: s3. elim: s1 => [[|x3 t3] // | 
    x1 t1 IH [//|x3 t3/=] [Hxs] Htls [Hsz]].
  move: IH => /(_ _ Htls Hsz) [Ht1 Hs2].
  by rewrite Hxs Ht1 Hs2.
Qed.

End OtherList.

(*A few other random results*)

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

Lemma proj_sumbool_false: forall {P Q: Prop} (a: {P} + {Q}), Coqlib.proj_sumbool a = false -> Q.
Proof.
  move => P Q a.
  by case: a.
Qed. 

Require Import ZSeq.

Section MapWithIdx.

Local Open Scope Z_scope.
  
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
    rewrite Heqints /Ziota size_map size_iota size_Zlength.
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

End MapWithIdx.

(*General list lemmas*)
Section List. 

Lemma in_sublist_widen {A: Type} `(H: Inhabitant A) (lo1 lo2 hi1 hi2: Z)
  (l: list A) (x: A):
  In x (sublist lo1 hi1 l) ->
  (0 <= lo2 <= lo1)%Z ->
  (lo1 <= hi1)%Z ->
  (hi1 <= hi2 <= Zlength l)%Z ->
  In x (sublist lo2 hi2 l).
Proof.
  move=> Hin Hlo Hlohi Hhi.
  have:=(In_Znth _ _ Hin)=>/(_ H) [i [Hi Hnth]].
  rewrite Zlength_sublist in Hi; try lia.
  rewrite Znth_sublist in Hnth; try lia.
  rewrite In_Znth_iff. exists (i + (lo1-lo2))%Z.
  rewrite Zlength_sublist; try lia.
  rewrite Znth_sublist; try lia.
  split; try lia. rewrite -Hnth. f_equal. lia.
Qed.

Lemma in_Znth_sublist {A: Type} `{H: Inhabitant A} (i: Z) (l: list A) lo hi:
  (0 <= i < Zlength l)%Z ->
  (0 <= lo <= i)%Z ->
  (i < hi <= Zlength l)%Z ->
  In (Znth i l) (sublist lo hi l).
Proof.
  move=> Hi Hlo Hhi.
  apply (@in_sublist_widen _ _ i _ (i+1)%Z); try lia.
  rewrite sublist_len_1 //=. by left.
Qed.

End List.


Section Mod.

(*Helpful with mod*)
Lemma ltSmod (d n m: nat):
  0 < d ->
  d %| m ->
  n < m ->
  (n %/ d + 1) * d <= m.
Proof.
  move=> Hd Hdiv Hlt.
  rewrite -(divnK Hdiv) leq_pmul2r // addn1 ltn_divRL //.
  by apply (leq_ltn_trans (leq_trunc_div n d)).
Qed.

(*For a list of length n * m, find which m-batch an element is in*)
Lemma find_batch {A: eqType} (l: list A) (m: nat) (x: A):
  0 < m ->
  m %| size l ->
  x \in l ->
  exists i, i < size l %/ m /\ x \in 
    (sublist (Z.of_nat i * Z.of_nat m) (Z.of_nat (i+1) *Z.of_nat m)) l.
Proof.
  move=> H0m Hmdiv Hinx.
  (*The value of i is [index x l] %/ m (could just put this in lemma)*)
  exists (index x l %/ m).
  split.
  - by rewrite ltn_divLR // divnK // index_mem.
  - have Hx: nth x l (index x l) = x by apply nth_index.
    rewrite -{1}Hx nth_nth nth_Znth'.
    apply /inP.
    have Hindex: index x l < size l by rewrite index_mem.
    apply in_Znth_sublist.
    + rewrite Zlength_size. split; try lia. 
      by to_ssrnat.
    + split; try lia. to_ssrnat. 
      by apply leq_trunc_div.
    + to_ssrnat. split.
      * by rewrite {1}(divn_eq (index x l) m) 
          mulnDl ltn_add2l mul1n ltn_pmod.
      * rewrite Zlength_size. to_ssrnat. by apply ltSmod.
Qed.

End Mod.