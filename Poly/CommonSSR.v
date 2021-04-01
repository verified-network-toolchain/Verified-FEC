(** Generic Results about mathcomp and ssreflect functions, some used in multiple places*)
Require Import Coq.Lists.List.
From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Ltac eq_subst H := move : H => /eqP H; subst.

(*Used only for other tactics*)
Ltac case_view E P H :=
  destruct E eqn : H; [ apply (elimT P) in H | apply (elimF P) in H].

(** Lemmas about Nats*)

Lemma ltn_total: forall (n1 n2: nat),
  (n1 < n2) || (n1 == n2) || (n2 < n1).
Proof.
  move => n1 n2. case: (orP (leq_total n1 n2)); rewrite leq_eqVlt.
  - move => le_n12; case (orP le_n12) => [Heq | Hlt].  rewrite Heq /=.
    by rewrite orbT orTb. by rewrite Hlt !orTb.
  - move => le_n21; case (orP le_n21) => [Heq | Hlt]. rewrite eq_sym Heq /=.
    by rewrite orbT orTb. by rewrite Hlt !orbT.
Qed. 

(*exists in the library but this version is move convenient*)
Lemma leq_both_eq: forall m n,
  ((m <= n) && (n <= m)) = (m == n).
Proof.
  move => m n. case (orP (ltn_total m n)) => [/orP[Hlt | Heq] | Hgt].
  - have : ( m == n = false). rewrite ltn_neqAle in Hlt. move : Hlt.
    by case: (m == n). move ->. 
    have: (n <= m = false). rewrite ltnNge in Hlt. move : Hlt.
    by case : (n <= m). move ->. by rewrite andbF.
  - by rewrite Heq leq_eqVlt Heq orTb leq_eqVlt eq_sym Heq orTb.
  - have : ( m == n = false). rewrite ltn_neqAle in Hgt. move : Hgt.
    rewrite eq_sym. by case: (m == n). move ->. 
    have: (m <= n = false). rewrite ltnNge in Hgt. move : Hgt.
    by case : (m <= n). move ->. by rewrite andFb.
Qed.

Lemma ltn_leq_trans: forall [n m p : nat], m < n -> n <= p -> m < p.
Proof.
  move => m n p Hmn. rewrite leq_eqVlt => /orP[Hmp | Hmp]. eq_subst Hmp. by [].
  move : Hmn Hmp. apply ltn_trans.
Qed.

Lemma ltn_pred: forall m n,
  0 < n ->
  (m < n) = (m <= n.-1).
Proof.
  move => m n Hpos. have: n.-1 == (n - 1)%N by rewrite eq_sym subn1. move => /eqP Hn1. by rewrite Hn1 leq_subRL.
Qed.

Lemma pred_lt: forall n, 0 < n -> n.-1 < n.
Proof.
  move => n Hn. by rewrite ltn_predL.
Qed.

Lemma ltn_leq_total: forall n m,
  (n < m) || (m <= n).
Proof.
  move => m n.   
  pose proof (ltn_total m n). move : H => /orP[/orP[Hlt | Heq] | Hgt].
  + by rewrite Hlt.
  + by rewrite (leq_eqVlt n) eq_sym Heq orbT.
  + by rewrite (leq_eqVlt n) Hgt !orbT.
Qed. 

Lemma ltn_add2rl: forall n1 n2 m1 m2,
  n1 < n2 ->
  m1 < m2 ->
  n1 + m1 < n2 + m2.
Proof.
  move => n1 n2 m1 m2 Hn Hm. have Hleft: n1 + m1 < n1 + m2 by rewrite ltn_add2l.
  have Hright: n1 + m2 < n2 + m2 by rewrite ltn_add2r. by apply (ltn_trans Hleft Hright).
Qed.

(*A few lemmas for working with division by 2*)

Lemma div_lt_bound: forall (n: nat),
  (n < n./2 + 1) = (n == 0)%N.
Proof.
  move => n. elim : n => [//= | n IH /=].
  rewrite -(addn1 n) ltn_add2r. rewrite uphalf_half. case  Hodd: (odd n) => [/=|/=].
  - rewrite addnC IH. case Hn0 : (n == 0)%N. by eq_subst Hn0.
    rewrite addn1. by [].
  - rewrite add0n. have->: n < n./2 = false. rewrite -divn2.
    case Hn : (n < n %/ 2) =>[|//]. have Hnle : (n %/ 2 <= n) by apply leq_div.
    have: (n < n) by apply (ltn_leq_trans Hn Hnle). by rewrite ltnn.
    by rewrite addn1.
Qed.

Lemma sub_half_lower: forall (n: nat),
  n./2 <= n - n./2.
Proof.
  move => n. rewrite leq_subRL. rewrite addnn -{2}(odd_double_half n).
  case : (odd n) =>[/=|/=]. by rewrite addnC addn1 leqnSn. by rewrite add0n leqnn.
  rewrite -divn2. apply leq_div.
Qed.

Lemma sub_half_upper: forall n,
  n - n./2 <= n./2 + 1.
Proof.
  move => n. rewrite leq_subLR addnA addnn -{1}(odd_double_half n) addnC leq_add2l.
  by case (odd n).
Qed.

Lemma div_2_pos: forall n,
  1 < n ->
  0 < n./2.
Proof.
  move => n H1n. by rewrite -divn2 divn_gt0.
Qed.

(** Lemmas about Ordinals*)

(*If an 'I_m exists, then 0 < m*)
Lemma ord_nonzero {m} (r: 'I_m) : 0 < m.
Proof.
  case : r. move => m'. case (orP (ltn_total m 0)) => [/orP[Hlt | Heq] | Hgt].
  - by [].
  - by eq_subst Heq.
  - by [].
Qed.

Lemma remove_widen: forall {m n} (x: 'I_m) (H: m <= n),
  nat_of_ord (widen_ord H x) = nat_of_ord x.
Proof.
  by [].
Qed.

Definition pred_ord (n: nat) (Hn: 0 < n) : 'I_n := Ordinal (pred_lt Hn).


Lemma widen_ord_inj: forall {m n: nat} (H: m <= n) x y, widen_ord H x = widen_ord H y -> x = y.
Proof.
  move => m n H x y Hw. apply (elimT eqP).
  have: nat_of_ord (widen_ord H x) == x by []. have: nat_of_ord (widen_ord H y) == y by [].
  move => /eqP Hy /eqP Hx. rewrite Hw in Hx. have: nat_of_ord x == nat_of_ord y by rewrite -Hx -Hy. by [].
Qed.

(** Other lemmas*)

Lemma rwN: forall [P: Prop] [b: bool], reflect P b -> ~ P <-> ~~ b.
Proof.
  move => P b Hr. split. by apply introN. by apply elimN.
Qed.

Lemma rem_impl: forall b : Prop,
  (true -> b) -> b.
Proof.
  move => b. move => H. by apply H.
Qed.

Lemma iota_plus_1: forall x y,
  iota x (y.+1) = iota x y ++ [ :: (x + y)%N].
Proof.
  move => x y. by rewrite -addn1 iotaD /=.
Qed.


(** Lemmas about [find] *)

(*Results about [find] that mostly put the library lemmas into a more convenient form*)

Lemma find_iff: forall {T: eqType} (a: pred T) (s: seq T) (r : nat) (t: T),
  r < size s ->
  find a s = r <-> (forall x, a (nth x s r)) /\ forall x y, y < r -> (a (nth x s y) = false).
Proof.
  move => T a s r t Hsz. split.
  - move => Hfind. subst. split. move => x. apply nth_find. by rewrite has_find.
    move => x. apply before_find.
  - move => [Ha Hbef]. have Hfind := (findP a s). case : Hfind.
    + move => Hhas. have H := (rwN (@hasP T a s)). rewrite Hhas in H.
      have:~ (exists2 x : T, x \in s & a x) by rewrite H. move : H => H{H} Hex.
      have : nth t s r \in s by apply mem_nth. move => Hnthin. 
      have: (exists2 x : T, x \in s & a x) by exists (nth t s r). by [].
    + move => i Hisz Hanth Hprev.
      have Hlt := ltn_total i r. move : Hlt => /orP[H1 | Hgt].
      move : H1 => /orP[Hlt | Heq].
      * have : a (nth t s i) by apply Hanth. by rewrite Hbef.
      * by eq_subst Heq.
      * have : a (nth t s r) by apply Ha. by rewrite Hprev.
Qed.

(*Similar for None case*)
Lemma find_none_iff: forall {T: eqType} (a: pred T) (s: seq T),
  find a s = size s <-> (forall x, x \in s -> ~~ (a x)).
Proof.
  move => T a s. split.
  - move => Hfind. have: ~~ has a s. case Hhas : (has a s). 
    move : Hhas. rewrite has_find Hfind ltnn. by []. by [].
    move => Hhas. by apply (elimT hasPn).
  - move => Hnotin. apply hasNfind. apply (introT hasPn). move => x. apply Hnotin. 
Qed.

(** Lemmas about [all]*)

Lemma all_in: forall {A: eqType} (l: seq A) (p: pred A),
  all p l <-> forall x, x \in l -> p x.
Proof.
  move => A l. elim: l =>[p // | h t IH p /=].
  split. move => /andP[Hh Htl x]. rewrite in_cons => /orP[/eqP Hxh | Hxt].
  by subst. by apply IH.
  move => Hall. rewrite Hall. rewrite IH. move => x Hint. apply Hall. by rewrite in_cons Hint orbT.
  by rewrite in_cons eq_refl.
Qed.

(** Relating ssreflect and standard library functions*)


Lemma in_mem_In: forall {A: eqType} (l: list A) x,
  x \in l <-> In x l.
Proof.
  move => A l x. elim: l => [//| h t IH /=].
  rewrite in_cons -IH eq_sym. split => [/orP[/eqP Hx | Ht]| [Hx | Hlt]]. by left. by right.
  subst. by rewrite eq_refl. by rewrite Hlt orbT.
Qed.

Lemma uniq_NoDup: forall {A: eqType} (l: list A),
  uniq l <-> NoDup l.
Proof.
  move => A l. elim : l => [//=|h t IH].
  - split =>[H{H}|//]. by apply NoDup_nil.
  - rewrite /=. split => [/andP[Hnotin Hun]| ].
    constructor. rewrite -in_mem_In. move => Hin. by move : Hin Hnotin ->.
    by apply IH.
    move => Hnod. inversion Hnod as [|x l Hnotin Hnodup] ; subst.
    have->: h \notin t. case Hin: (h\in t). have: h\in t by []. by rewrite in_mem_In =>{} Hin.
    by []. by rewrite IH.
Qed. 

Lemma size_length: forall {A : Type} (l: list A),
  size l = Datatypes.length l.
Proof.
  move => A l. elim: l => [//|h t IH /=].
  by rewrite IH.
Qed.

(** Bounded lists of finTypes are finite *)
Section BoundedSeq.

Variable T : finType.

Section TypeDefs.

Variable n : nat.

Definition bseq : Type := { s: seq T | size s < n}.
Coercion bseq_to_seq (b: bseq) : seq T := proj1_sig b.

Definition bseq_eqMixin := Eval hnf in [eqMixin of bseq by <:].
Canonical bseq_eqType := Eval hnf in EqType bseq bseq_eqMixin.

Definition bseq_choiceMixin := [choiceMixin of bseq by <:].
Canonical bseq_choiceType := Eval hnf in ChoiceType bseq bseq_choiceMixin.

Definition bseq_countMixin := [countMixin of bseq by <:].
Canonical bseq_countType := Eval hnf in CountType bseq bseq_countMixin.
(*don't need bf of [sig_subCountType]*)
(*
Canonical bseq_subCountType := [subCountType of bseq].*)

End TypeDefs.

(*To show this is finite, we need to construct a list of all instances of this type. This is a bit complicated.*)
Definition cons_one {A: Type} (x: A) (c: seq (seq A)) :=
  map (fun y => x :: y) c.

Lemma cons_oneP: forall {A: eqType} (x: A) (c: seq (seq A)) (s: seq A),
  reflect (exists2 l1 : seq A, l1 \in c & s = x :: l1) (s \in cons_one x c).
Proof.
  move => A x c s. rewrite /cons_one. apply mapP.
Qed.

Lemma cons_one_uniq: forall {A: eqType} (x: A) c,
  uniq (cons_one x c) = uniq c.
Proof.
  move => A x c. rewrite /cons_one. apply map_inj_uniq. by move => a b [Heq].
Qed.

Definition cons_all_aux {A: Type}  (c: seq (seq A)) (l: seq A) : seq (seq A) :=
  foldr (fun x acc => (cons_one x c) ++ acc) nil l.

(*Probably a way to use finite exists, maybe see*)
Lemma cons_all_aux_in: forall {A: eqType} (c: seq (seq A)) l s,
  s \in (cons_all_aux c l) <-> exists x l1, (x \in l) && (l1 \in c) && (s == x :: l1).
Proof.
  move => A c l s. elim : l => [//= | h t /= IH].
  - rewrite in_nil. split => [// | //[x [y H]] //].
  - rewrite mem_cat. split.
    + move => /orP[/cons_oneP [l1 Hl1 Hhl1] | Hst].
      * subst. exists h. exists l1. by rewrite in_cons !eq_refl Hl1.
      * apply IH in Hst. case : Hst => [x [l1 /andP[/andP[Hxt Hl1c] /eqP Hsxl1]]]. subst.
        exists x. exists l1. by rewrite in_cons Hxt orbT Hl1c eq_refl.
    + move => [x [l1 /andP[/andP[Hxt Hl1c] /eqP Hsxl1]]]. subst. apply /orP.
      move: Hxt; rewrite in_cons => /orP[/eqP Hxh | Hxt].
      * subst. left. apply /cons_oneP. exists l1. by rewrite Hl1c. by []. 
      * right. apply IH. exists x. exists l1. by rewrite Hxt Hl1c eq_refl.
Qed.

Lemma cons_all_aux_uniq: forall {A: eqType} (c: seq (seq A)) l,
  uniq l ->
  uniq c ->
  uniq (cons_all_aux c l).
Proof.
  move => A c l Hl Hc. move: Hl. elim : l => [//= | h t /= IH /andP [Hht Hunt]].
  rewrite cat_uniq cons_one_uniq Hc /= IH // andbT. apply /hasPn => l Hl.
  case Hin:(mem (cons_one h c) l) => [|//]. 
  have /cons_oneP [h1 Hhc Hl1]: l \in (cons_one h c) by [].
  move : Hl; rewrite cons_all_aux_in => [[x [l2 /andP[/andP[Hxt Hl21] /eqP Hl]]]]. subst.
  case : Hl => [Hxh Hh12]. subst. by rewrite Hxt in Hht.
Qed.

Definition cons_all (c: seq (seq T)) : seq (seq T) :=
  cons_all_aux c (enum T).

Lemma in_enum: forall (x: T),
  x \in (enum T).
Proof.
  move => x. rewrite enumT. pose proof (@enumP T) as Hfin. move: Hfin; rewrite /Finite.axiom => /(_ x) Hx.
  case Hin: (x \in Finite.enum T) => [// | ].
  have / count_memPn Hnotin: (x \notin Finite.enum T) by rewrite Hin. by rewrite Hnotin in Hx.
Qed.

Lemma cons_all_in: forall (c: seq (seq T)) s,
  s \in cons_all c <-> exists x l1, (l1 \in c) && (s == x :: l1).
Proof.
  move => c s. rewrite cons_all_aux_in. split.
  - move => [x [l1 /andP[/andP[Hxt Hl1c] /eqP Hsxl1]]]. subst. exists x. exists l1. by rewrite Hl1c eq_refl.
  - move => [x [l1 /andP[Hl1c /eqP Hs]]]. subst. exists x. exists l1. by rewrite in_enum Hl1c eq_refl.
Qed.

Lemma cons_all_uniq: forall (c: seq (seq T)),
  uniq c ->
  uniq (cons_all c).
Proof.
  move => c Hunc. apply cons_all_aux_uniq. by rewrite enum_uniq. by [].
Qed.

(*First list contains all lists of length <= n, second list contains all lists of length = n*)
Fixpoint bseq_seqs (n: nat) : seq (seq T) * seq (seq T) :=
  match n with
  | 0 => ([:: nil], [:: nil])
  | n'.+1 => let (leq_seq, eq_seq) := (bseq_seqs n') in
             let plus_1_seq := cons_all eq_seq in
             (leq_seq ++ plus_1_seq, plus_1_seq)
  end.

(*First we prove the correctness of the right half (which is independent of the rest)*)
Lemma bseq_seqs_snd: forall n (s: seq T),
  (s \in (bseq_seqs n).2) = (size s == n).
Proof.
  move => n s. move: s. elim : n => [//= s | n /= IH s ].
  - by rewrite in_cons in_nil orbF size_eq0.
  - case Hbseq: (bseq_seqs n) => [ leq_seq eq_seq /=].
    case Hin: (s \in cons_all eq_seq).
    + have: (is_true (s \in cons_all eq_seq)) by rewrite Hin. rewrite cons_all_in => [[x [l1 /andP[Hl1 /eqP Hs]]]].
      subst. move: IH => /(_ l1). by rewrite Hbseq /= Hl1.
    + case Hsz: (size s == n.+1) => [|//].
      move: Hsz Hin. case : s => [// | h t /=]. rewrite eqSS => Hsz Hin.
      have: (h :: t \in cons_all eq_seq). rewrite cons_all_in. exists h. exists t.
      move: IH => /(_ t). rewrite Hbseq /= Hsz; move->. by rewrite eq_refl.
      by rewrite Hin.
Qed.

Lemma bseq_seqs_fst: forall n (s: seq T),
  (s \in (bseq_seqs n).1) = (size s <= n).
Proof.
  move => n s. move: s. elim : n => [//= s | n /= IH s].
  - by rewrite leqn0 in_cons in_nil orbF size_eq0.
  - case Hbseq: (bseq_seqs n) => [ leq_seq eq_seq /=].
    have Hlast: (s \in cons_all eq_seq) = (size s == n.+1)
      by rewrite -bseq_seqs_snd /= Hbseq /=.
    by rewrite mem_cat leq_eqVlt Hlast ltnS -IH Hbseq /= orbC.
Qed.

Lemma bseq_seq_snd_uniq: forall n,
  uniq (bseq_seqs n).2.
Proof.
  move => n. elim : n => [//= | n /= IH].
  case Hbseq: (bseq_seqs n) => [ leq_seq eq_seq /=].
  move: IH; rewrite Hbseq /= => IH. by rewrite cons_all_uniq.
Qed.

Lemma bseq_seq_fst_uniq: forall n,
  uniq (bseq_seqs n).1.
Proof.
  move => n. elim : n => [//= | n /= IH].
  case Hbseq: (bseq_seqs n) => [ leq_seq eq_seq /=].
  have Heq: eq_seq = (bseq_seqs n).2 by rewrite Hbseq.
  move: IH; rewrite Hbseq /= => IH. rewrite cat_uniq IH /= cons_all_uniq //; last first.
  rewrite Heq; apply bseq_seq_snd_uniq. rewrite andbT.
  have Hcons: (cons_all eq_seq) = (bseq_seqs n.+1).2 by rewrite /= Hbseq.
  rewrite Hcons.
  apply /hasPn => l. rewrite bseq_seqs_snd => /eqP Hlsz.
  case Hmem: (mem leq_seq l) => [|//].
  have Hin : l \in leq_seq by [].
  have: (size l <= n) by rewrite -bseq_seqs_fst Hbseq /=. by rewrite Hlsz ltnn.
Qed. 

(*Do this to avoid dependent type issues*)
Definition bseq_seq_full_aux (n: nat) (m: nat) (Hmn: n = m) : seq (bseq n) :=
  match m with
  | 0 => pmap insub nil
  | m'.+1 => pmap insub (bseq_seqs m').1
  end.

Definition bseq_seq_full (n: nat) := bseq_seq_full_aux (erefl n). 

(*Prove finType*)
Lemma bseq_seq_full_aux_uniq: forall n m (Hmn: n = m), uniq (@bseq_seq_full_aux n m Hmn).
Proof.
  move => n m. move: n. case : m => [//= | m /= n Hmn]. apply pmap_sub_uniq.
  by apply bseq_seq_fst_uniq.
Qed.

Lemma bseq_seq_full_aux_axiom: forall n m (Hmn: n = m), Finite.axiom (@bseq_seq_full_aux n m Hmn).
Proof.
  move => n m. move: n. rewrite /Finite.axiom. case : m => [//= x Hx0 [h Hl] // | m /= n Hmn x]. by subst.
  rewrite count_uniq_mem. 2: { apply pmap_sub_uniq. apply bseq_seq_fst_uniq. }
  rewrite mem_pmap_sub. case : x => [l Hl /=].
  rewrite bseq_seqs_fst -ltnS. subst. by rewrite Hl.
Qed.

Lemma bseq_seq_full_uniq: forall n, uniq (bseq_seq_full n).
Proof.
  move => n. apply bseq_seq_full_aux_uniq.
Qed.

Lemma bseq_seq_full_axiom: forall n, Finite.axiom (bseq_seq_full n).
Proof.
  move => n. by apply bseq_seq_full_aux_axiom.
Qed.

Section BseqFinType.

Variable n : nat.

Definition bseq_finMixin := FinMixin (@bseq_seq_full_axiom n).
Canonical bseq_finType := FinType (bseq n) bseq_finMixin.

End BseqFinType.

End BoundedSeq.