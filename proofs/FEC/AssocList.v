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

Variable K V: eqType.

Notation assoc_list := (list (K * V)).

(*Definition assoc_eqMixin := seq_eqMixin (prod_eqType K V).
Canonical assoc_eqType : eqType := EqType assoc_list assoc_eqMixin. *)

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
  (k, v') \in (updateWith k f a) ->
  exists v, (k, v) \in a /\ v' = f v.
Proof.
  move => k f a v'. elim : a => [//= | h t /= IH]. case : h => [kh vh]/=.
  move => /andP[Hnotin Huniq]. case: (k == kh) /eqP => Hkkh/=.
  - rewrite in_cons =>/orP[/eqP [Heq] | Hin].
    + subst. exists vh. by rewrite in_cons eq_refl.
    + move: Hnotin. rewrite -Hkkh.
      have->//: k \in [seq i.1 | i <- t]. apply /mapP. by exists (k, v').
  - rewrite in_cons => /orP[/eqP [Hkeq] Hveq | Hin]; subst => //.
    apply IH in Hin => //. case : Hin => [v [Hinv Hv']]. subst.
    exists v. by rewrite in_cons Hinv orbT.
Qed.

Lemma updateWith_diff: forall k f a k' v',
  k != k' ->
  ((k', v') \in (updateWith k f a)) =
  ((k', v') \in a).
Proof.
  move => k f a k' v'. elim : a => [//= | h t /= IH]. 
  case : h => [kh vh]/=.
  move => /eqP Hkk'. case: (k == kh) /eqP => Hkkh/=.
  - rewrite !in_cons; subst.
    case: ((k', v') == (kh, f vh)) /eqP => [[Hk2]|/= _];
    by case: ((k', v') == (kh, vh)) /eqP => [[Hk2']| /= _]; subst.
  - rewrite !in_cons IH //. by apply /eqP.
Qed.

Lemma updateWith_keys: forall k f a,
  map fst a = map fst (updateWith k f a).
Proof.
  move => k f a. elim : a => [//= | h t /= IH].
  case : h => [kh kt]/=. case Hkkh: (k == kh) => /=.
  - f_equal. symmetry. by apply /eqP.
  - by rewrite IH.
Qed. 

Lemma updateWith_notin: forall k f a,
  (k \notin (map fst a)) ->
  updateWith k f a = a.
Proof.
  move => k f a. elim : a => [//= | h t /= IH].
  case : h => [k1 v1]/=. rewrite negb_or => /andP[Hkk1 Hin].
  by rewrite (negbTE Hkk1) IH.
Qed.

Lemma updateWith_app: forall k f a1 a2,
  k \notin (map fst a2) ->
  updateWith k f (a1 ++ a2) = updateWith k f a1 ++ a2.
Proof.
  move => k f a1. elim : a1 => [/= a2 Hin | h t /= IH a2 Hin].
  - by apply updateWith_notin.
  - case: h => [k1 v1].
    case : (k == k1) /eqP => [->// | Hkk1].
    by rewrite IH.
Qed.

Definition get (k: K) (a: assoc_list) : option V :=
  foldr (fun x acc => if k == x.1 then Some x.2 else acc) None a.

Lemma get_some_in: forall (k : K) (v: V) (a: assoc_list),
  get k a = Some v -> (k, v) \in a.
Proof.
  move => k v a. elim : a => [//= | h t /= IH]. case : h => [kh vh]/=.
  case :(k == kh) /eqP => [->|Hkkh].
  - move => [Hvh]. subst. by rewrite in_cons eq_refl.
  - move => Hget. by rewrite in_cons IH // orbT.
Qed.

Lemma get_in_some: forall (k : K) (v: V) (a: assoc_list),
  uniq (map fst a) ->
  (k, v) \in a ->
  get k a = Some v.
Proof.
  move => k v a. elim : a => [//= | h t /= IH]. case : h => [kh vh]/=.
  move => /andP[Hnotin Huniq]. case: (k == kh) /eqP => [->|Hkkh].
  - rewrite in_cons => /orP[/eqP [] -> // | Hin].
    move: Hnotin. have->//: kh \in [seq i.1 | i <- t].
    apply /mapP. by exists (kh, v).
  - rewrite in_cons=>/orP[/eqP[] Hk Hv // | Hin]. 
    by apply IH.
Qed. 

Lemma get_none: forall (k: K) (a: assoc_list),
  get k a = None <-> (forall v, (k, v) \notin a).
Proof.
  move => k a. elim : a => [//= | h t /= IH].
  case: h => [h1 h2]/=; subst.
  case: (k == h1) /eqP => Hkh2; subst; split => //.
  + move=>/(_ h2). by rewrite in_cons eq_refl.
  + rewrite IH => Hnotin v. rewrite in_cons.
    case: ((k, v) == (h1, h2)) /eqP => [[] Hk //| _/=].
    by apply Hnotin.
  + move => Hnotin. apply IH. move=> v. move: Hnotin => /(_ v).
    by rewrite in_cons negb_or => /andP[_ ].
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
  move: Hin => /mapP [x Hx1 Hin]; subst. move: Hget.
  rewrite get_none => /(_ x.2).
  have->:(x.1, x.2) = x by clear; case: x. by rewrite Hx1.
Qed. 

Lemma add_in_same: forall (k: K) (v: V) (a: assoc_list) (v': V),
  uniq (map fst a) ->
  get k a = None ->
  (k, v') \in (add k v a) ->
  v = v'.
Proof.
  move => k v a v' Huniq Hget. rewrite /add /= in_cons => 
    /orP[/eqP [Heq] // | Hin]. move: Hget.
  by rewrite get_none => /(_ v'); rewrite Hin.
Qed.

(*If (k, v1) is in list, update with (k, f v1). Otherwise, add (k, v) to list*)
Definition update_or_add' (k: K) (v: V) (f: V -> V) (a: assoc_list) : assoc_list :=
  match (get k a) with
  | None => add k v a
  | Some _ => updateWith k f a
  end.

Lemma update_or_add_same': forall (k: K) (v: V) (f: V -> V) (a: assoc_list) (v': V),
  uniq (map fst a) ->
  (k, v')  \in (update_or_add' k v f a) ->
  (exists oldV, (k, oldV) \in a /\ v' = f oldV) \/
  (v' = v /\ (forall oldV, (k, oldV) \notin a)).
Proof.
  move => k v f a v' Huniq. rewrite /update_or_add'. case Hget : (get k a) => [vd | ].
  - move => Hin. apply (updateWith_same Huniq) in Hin. by left.
  - move => Hin. apply (add_in_same Huniq Hget) in Hin. right. split => //.
    by apply get_none.
Qed.

Lemma update_or_add_diff': forall (k: K) (v: V) (f: V -> V) (a: assoc_list) k' v',
  k != k' ->
  ((k', v') \in (update_or_add' k v f a)) =
  ((k', v') \in a).
Proof.
  move => k v f a k' v' Hkk'. rewrite /update_or_add'. case Hget: (get k a) => [vd |].
  - by apply updateWith_diff.
  - rewrite /add/= !in_cons.
    case:((k', v') == (k, v)) /eqP => [[Heq']| _ //]; subst.
    by rewrite eq_refl in Hkk'.
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
  exists v', (k, v') \in (update_or_add' k v f a).
Proof.
  move => k v f a Huniq. rewrite /update_or_add'. case Hget: (get k a) => [d |].
  - apply get_some_in in Hget. have: k \in map fst a. { apply /mapP. by exists (k, d). }
    rewrite (updateWith_keys k f a) => /mapP[[k1 v1]/= Hin Hk]; subst.
    by exists v1.
  - rewrite /add. exists v. by rewrite in_cons eq_refl.
Qed.

Lemma update_or_add_app': forall (k: K) (v: V) (f: V -> V) (a1 a2: assoc_list),
  k \notin (map fst a2) ->
  update_or_add' k v f (a1 ++ a2) = update_or_add' k v f a1 ++ a2.
Proof.
  move => k c f a1 a2 Hin. rewrite /update_or_add'.
  case Hg1: (get k a1) => [v |/=].
  - case Hg2: (get k (a1 ++ a2)) => [v2 |/=].
    + by apply updateWith_app.
    + rewrite get_none in Hg2.
      move: Hg2 => /(_ v); rewrite mem_cat.
      have->//:(k, v) \in a1 by apply get_some_in.
  - case Hg2: (get k (a1 ++ a2)) => [v2 |//].
    apply get_some_in in Hg2. move: Hg2.
    rewrite mem_cat => /orP[Hin1 | Hin2].
    + rewrite get_none in Hg1. by move: Hg1 => /(_ v2); rewrite Hin1.
    + exfalso. move: Hin => /mapP Hin; apply Hin.
      by exists (k, v2).
Qed.

(*Now we should package this into a nicer association list that has uniq keys*)

Inductive alist := Alist (al: assoc_list) of (uniq (map fst al)).
Coercion al (a: alist) : assoc_list := let: Alist x _ := a in x.
Definition al_uniq (a: alist) : uniq (map fst (al a)) := let :Alist _ x := a in x.
Canonical alist_subType := [subType for al].
Definition alist_eqMixin := SubEqMixin alist_subType.
Definition alist_eqType := EqType alist alist_eqMixin.

Definition empty : alist := Alist empty_uniq.
Definition update_or_add (k: K) (v: V) (f: V -> V) (a: alist) : alist :=
  Alist (update_or_add_uniq k v f (al_uniq a)).

(*Now, we provide lemmas for export*)
Lemma update_or_add_same: forall (k: K) (v: V) (f: V -> V) (a: alist) (v': V),
  (k, v') \in al (update_or_add k v f a) ->
  (exists oldV, (k, oldV) \in al a /\ v' = f oldV) \/
  (v' = v /\ (forall oldV, (k, oldV) \notin al a)).
Proof.
  move => k v f a v' Hin. apply update_or_add_same'. apply (al_uniq a).
  by [].
Qed.

Lemma update_or_add_diff: forall (k: K) (v: V) (f: V -> V) (a: alist) k' v',
  k != k' ->
  ((k', v') \in al (update_or_add k v f a)) =
  ((k', v') \in al a).
Proof.
  move => k v f a k' v'.
  apply update_or_add_diff'.
Qed.

Lemma update_or_add_exists: forall (k: K) (v: V) (f: V -> V) (a: alist),
  exists v', (k, v') \in al (update_or_add k v f a).
Proof.
  move => k v f a. apply update_or_add_exists'. apply (al_uniq a).
Qed.

End AssocList.