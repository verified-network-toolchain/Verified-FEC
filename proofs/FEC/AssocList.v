Require Import Coq.Lists.List.
Require Import CommonSSR.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(*We want to define a special association list with 1 constructor (empty) and 1 operation: update_or_add, 
  which updates an element if there using some function or adds if not*)
Section AssocList.

Variable K: eqType.
Variable V : Type.

Definition assoc_list := list (K * V).

Definition empty': assoc_list := nil.

Lemma empty_uniq: uniq (map fst empty').
Proof.
  by [].
Qed.

Fixpoint updateWith (k: K) (f: V -> V) (a: assoc_list) : assoc_list :=
  match a with
  | nil => nil
  | (k', v') :: tl => if k == k' then (k, f v') :: tl else (k', v') :: updateWith k f tl
  end.

Lemma updateWith_same: forall k f a v',
  uniq (map fst a) ->
  In (k, v') (updateWith k f a) ->
  exists v, In (k, v) a /\ v' = f v.
Proof.
  move => k f a v'. elim : a => [//= | h t /= IH]. case : h => [kh vh]/=.
  move => /andP[Hnotin Huniq]. case: (k == kh) /eqP => Hkkh/=.
  - move => [Heq | Hin].
    + case : Heq =><-. rewrite Hkkh. exists vh. split. by left. by [].
    + move: Hnotin. rewrite -Hkkh.
      have->//: k \in [seq i.1 | i <- t]. rewrite in_mem_In in_map_iff. by exists (k, v').
  - move => [Heq | Hin]. case: Heq => Hkkh'. by rewrite Hkkh' in Hkkh.
    apply IH in Hin. case : Hin => [v [Hinv Hv']]. exists v. split. by right. by []. by [].
Qed.

Lemma updateWith_diff: forall k f a k' v',
  k != k' ->
  In (k', v') (updateWith k f a) <->
  In (k', v') a.
Proof.
  move => k f a k' v'. elim : a => [//= | h t /= IH]. case : h => [kh vh]/=.
  move => (*/andP[Hnotin Huniq]*) Hkk'. case: (k == kh) /eqP => Hkkh/=.
  - split; move => [Heq | Hin].
    + case: Heq => Hk. move: Hkk'. by rewrite Hk eq_refl.
    + by right.
    + case : Heq => Hk. subst. by rewrite eq_refl in Hkk'.
    + by right.
  - split; move => [Heq | Hin]; try (by left); by (right; apply IH).
Qed.

Lemma updateWith_keys: forall k f a,
  map fst a = map fst (updateWith k f a).
Proof.
  move => k f a. elim : a => [//= | h t /= IH].
  case : h => [kh kt]/=. case Hkkh: (k == kh) => /=.
  - f_equal. symmetry. by apply /eqP.
  - by rewrite IH.
Qed. 

Definition get (k: K) (a: assoc_list) : option V :=
  foldr (fun x acc => if k == x.1 then Some x.2 else acc) None a.

Lemma get_some: forall (k: K) (v: V) (a: assoc_list),
  uniq (map fst a) ->
  get k a = Some v <-> In (k, v) a.
Proof.
  move => k v a. elim : a => [//= | h t /= IH]. case : h => [kh vh]/=.
  move => /andP[Hnotin Huniq]. case Hkkh: (k == kh).
  - move: Hkkh => /eqP Hkkh. rewrite Hkkh. split.
    + move => [Hvh]. rewrite Hvh. by left.
    + move => [[Heq] | Hin]. by rewrite Heq. 
      move: Hnotin. have->//: kh \in [seq i.1 | i <- t]. rewrite in_mem_In in_map_iff.
      by exists (kh, v).
  - move: Hkkh => /eqP Hkkh. rewrite IH //. split.
    + move => Hin //. by right.
    + move => [[Heq] | Hin //]. by rewrite Heq in Hkkh.
Qed.

Lemma get_none: forall (k: K) (a: assoc_list),
  get k a = None <-> (forall v, ~In(k, v) a).
Proof.
  move => k a. elim : a => [//= | h t /= IH].
  - split => //. auto.
  - case : h => [kh vh]/=. case Hkkh: (k == kh).
    + move : Hkkh => /eqP Hkkh. split => //.
      move => /(_ vh). rewrite Hkkh. tauto.
    + rewrite IH. move : Hkkh => /eqP Hkkh. split => Hallin v.
      * move => [[Heq] | Hc]. auto. by apply (Hallin v).
      * move => Hc. move: Hallin => /(_ v) Hor. apply Decidable.not_or in Hor. by apply (proj2 Hor).
Qed.

(*Add entry (k, v) to front of list*)
Definition add (k: K) (v: V) (a: assoc_list) : assoc_list :=
  (k, v) :: a.

Lemma add_uniq: forall (k: K) (v: V) (a: assoc_list),
  uniq (map fst a) ->
  get k a = None ->
  uniq (map fst (add k v a)).
Proof.
  move => k v a Huniq Hget. rewrite /add/=. apply /andP. split => //.
  case Hin: (k \in [seq i.1 | i <- a]) => //.
  move: Hin. rewrite -is_true_true_eq in_mem_In in_map_iff => [[x [Hx1 Hin]]].
  move: Hx1 Hin. case : x => [k' v']/=-> => Hin.
  rewrite get_none in Hget. exfalso. by apply (Hget v').
Qed.

Lemma add_in_same: forall (k: K) (v: V) (a: assoc_list) (v': V),
  uniq (map fst a) ->
  get k a = None ->
  In (k, v') (add k v a) ->
  v = v'.
Proof.
  move => k v a v' Huniq Hget. rewrite /add /= => [[[Heq] // | Hin]].
  rewrite get_none in Hget. exfalso. by apply (Hget v').
Qed.

(*If (k, v1) is in list, update with (k, f v1). Otherwise, add (k, v) to list*)
Definition update_or_add' (k: K) (v: V) (f: V -> V) (a: assoc_list) : assoc_list :=
  match (get k a) with
  | None => add k v a
  | Some _ => updateWith k f a
  end.

Lemma update_or_add_same': forall (k: K) (v: V) (f: V -> V) (a: assoc_list) (v': V),
  uniq (map fst a) ->
  In (k, v') (update_or_add' k v f a) ->
  (exists oldV, In (k, oldV) a /\ v' = f oldV) \/
  (v' = v /\ (forall oldV, ~In(k, oldV) a)).
Proof.
  move => k v f a v' Huniq. rewrite /update_or_add'. case Hget : (get k a) => [vd | ].
  - move => Hin. apply (updateWith_same Huniq) in Hin. by left.
  - move => Hin. apply (add_in_same Huniq Hget) in Hin. right. split => //.
    by apply get_none.
Qed.

Lemma update_or_add_diff': forall (k: K) (v: V) (f: V -> V) (a: assoc_list) k' v',
  k != k' ->
  In (k', v') (update_or_add' k v f a) <->
  In (k', v') a.
Proof.
  move => k v f a k' v' Hkk'. rewrite /update_or_add'. case Hget: (get k a) => [vd |].
  - by apply updateWith_diff.
  - rewrite /add/=. split.
    + move => [[Heq] | Hin //]. move: Hkk'. by rewrite Heq eq_refl.
    + move => Hin. by right.
Qed.

Lemma update_or_add_uniq: forall (k: K) (v: V) (f: V -> V) (a: assoc_list),
  uniq (map fst a) ->
  uniq (map fst (update_or_add' k v f a)).
Proof.
  move => k v f a. rewrite /update_or_add' /=. case Hget : (get k a).
  - by rewrite -updateWith_keys.
  - move => Huniq. by apply add_uniq.
Qed.

Lemma update_or_add_exists': forall (k: K) (v: V) (f: V -> V) (a: assoc_list),
  uniq (map fst a) -> (*technically don't need but makes proofs easier*)
  exists v', In (k, v') (update_or_add' k v f a).
Proof.
  move => k v f a Huniq. rewrite /update_or_add'. case Hget: (get k a) => [d |].
  - rewrite (get_some _ _ Huniq) in Hget. have: k \in map fst a. { rewrite in_mem_In in_map_iff. by exists (k, d). }
    rewrite (updateWith_keys k f a) in_mem_In in_map_iff => [[[k1 v1]/= [Hk Hin]]]. rewrite Hk in Hin.
    by exists v1.
  - rewrite /add. exists v. by left.
Qed.

(*Now we should package this into a nicer association list that has uniq keys*)

Inductive alist := Alist (al: assoc_list) of (uniq (map fst al)).
Coercion al (a: alist) : list (K * V) := let: Alist x _ := a in x.
Definition al_uniq (a: alist) : uniq (map fst a) := let :Alist _ x := a in x.
Canonical alist_subType := [subType for al].

Definition empty : alist := Alist empty_uniq.
Definition update_or_add (k: K) (v: V) (f: V -> V) (a: alist) : alist :=
  Alist (update_or_add_uniq k v f (al_uniq a)).

(*Now, we provide lemmas for export*)
Lemma update_or_add_same: forall (k: K) (v: V) (f: V -> V) (a: alist) (v': V),
  In (k, v') (update_or_add k v f a) ->
  (exists oldV, In (k, oldV) a /\ v' = f oldV) \/
  (v' = v /\ (forall oldV, ~In(k, oldV) a)).
Proof.
  move => k v f a v' Hin. apply update_or_add_same'. apply (al_uniq a).
  by [].
Qed.

Lemma update_or_add_diff: forall (k: K) (v: V) (f: V -> V) (a: alist) k' v',
  k != k' ->
  In (k', v') (update_or_add k v f a) <->
  In (k', v') a.
Proof.
  move => k v f a k' v'.
  apply update_or_add_diff'.
Qed.

Lemma update_or_add_exists: forall (k: K) (v: V) (f: V -> V) (a: alist),
  exists v', In (k, v') (update_or_add k v f a).
Proof.
  move => k v f a. apply update_or_add_exists'. apply (al_uniq a).
Qed.

End AssocList.