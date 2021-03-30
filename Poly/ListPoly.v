(*We define polynomials as lists of field elements so that we can compute with them, unlike mathcomp's. However,
  to use the theorems in mathcomp, we relate lpolys to polys*)
From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.poly.
Require Import mathcomp.algebra.polydiv.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import CommonSSR.

(*Stuff from helper, mathcomp versions*)
Section Helper.

(* function (from Haskell) to remove all values from end of list that satisfy a predicate. *)
Definition dropWhileEnd {A: Type} (p: pred A) (l: seq A) : seq A :=
  foldr (fun x acc => if (nilp acc) && (p x) then nil else x :: acc) nil l.

Lemma dropWhileEnd_nil: forall {A} p (l: seq A),
  reflect (dropWhileEnd p l = nil) (all p l).
Proof.
  move => A p l. apply Bool.iff_reflect. elim : l => [//= | h t /= IH].
  case Hnil: (nilp (dropWhileEnd p t)) => [/= | /=].
  - case Hp: (p h) => [//= | //=]. rewrite -IH. apply (elimT nilP) in Hnil. by rewrite Hnil.
  - split; move => Hcon.
    + by [].
    + move: Hcon => /andP[Hph Ht]. have: all p t = true by rewrite Ht. rewrite -IH => Htl.
      by rewrite Htl in Hnil.
Qed.

Lemma dropWhileEnd_end: forall {A: Type} p (l1 l2: seq A),
  all p l2 ->
  dropWhileEnd p (l1 ++ l2) = dropWhileEnd p l1.
Proof.
  move => A p l1. elim : l1 => [//= l2 Hall | h t /= IH l2 Hall].
  - by apply /dropWhileEnd_nil.
  - by rewrite IH.
Qed.

(*Could do with In instead of \in but eqType should be fine for our purposes*)
Lemma dropWhileEnd_spec: forall {A: eqType} p (l: seq A) (x: A) res,
  dropWhileEnd p l = res <->
  (exists l1, l = res ++ l1 /\ forall x, x \in l1 -> p x) /\ (~~nilp res -> ~~p(last x res)).
Proof.
  move => A p l x. elim : l => [//= | h t /= IH res]; split.
  - move <-. split. by exists nil. by [].
  - move => [[l1 [Hl1 Hall]] Hlast]. move: Hl1 Hlast. by case : res.
  - case Hdrop: (nilp (dropWhileEnd p t)) => [//= | //=].
    + case Hph : ( p h) => [/= | /=].
      * move <-. rewrite /=. split. exists (h :: t). split. by [].
        have Ht: forall x, x \in t -> p x. apply all_in. apply /dropWhileEnd_nil. by apply /nilP.
        move => y. rewrite in_cons => /orP[/eqP Hyh | Hyt]. by subst. by apply Ht. by [].
      * case : res => [// | r1 t1 /= [Hhr1 Htl]]. rewrite Hhr1. move: Htl; rewrite IH => [[[l1 [Hl1 Hinl1]] Hlast]].
        subst. split. by exists l1. move => {Hdrop} {IH}. move: Hlast. case : t1 => [//= | //=].
        move => Htriv Htriv1. by rewrite Hph.
    + case : res => [//= | r1 t1 /= [Hhr1 Hdt1]]. rewrite Hhr1.
      move: Hdt1; rewrite IH => [[[l1 [Hl1 Hinl1]] Hlast]]. subst. split. by exists l1.
      move: Hdrop. rewrite dropWhileEnd_end. move : Hlast => {IH}. by case : t1. by rewrite all_in.
  - move => [[l1 [Hl1 Hinl1]] Hlast]. move: Hl1 Hlast. case : res => [//= Hl1 | r1 t1 /=[Hhr1 Ht]].
    + subst. move => Htriv. rewrite Hinl1. rewrite andbT.
      have->: nilp (dropWhileEnd p t). apply /nilP. apply /dropWhileEnd_nil. rewrite all_in.
      move => y Hy. apply Hinl1. by rewrite in_cons Hy orbT. by []. by rewrite in_cons eq_refl.
    + move => Hlast. subst. have Hdrop: dropWhileEnd p (t1 ++ l1) = t1. apply IH. split.
      by exists l1. move: Hlast {IH}. by case : t1.
      rewrite Hdrop. case Hnil: (nilp t1) => [/= | //=].
      * apply (elimT nilP) in Hnil. subst. move: Hlast; rewrite /= => Hpr1.
        have->: p r1 = false. apply (elimT negPf). by apply Hpr1. by [].
Qed.

End Helper.

Section LPoly.

Local Open Scope ring_scope.

Variable F : fieldType.

Definition lpoly := polynomial F.

(*Transform an arbitrary list into a valid lpoly*)

Definition rem_trail_zero (s: seq F) : seq F := dropWhileEnd (fun x => x == 0) s.

Lemma rem_trail_zero_wf: forall s,
  last 1 (rem_trail_zero s) != 0.
Proof.
  move => s. rewrite /rem_trail_zero.
  have: (dropWhileEnd (eq_op^~ 0) s) = (dropWhileEnd (eq_op^~ 0) s) by [].
  rewrite (dropWhileEnd_spec _ _ 1) => [[[l1 [Hl1 Hinl1]] Hlast]].
  case Hdrop: (dropWhileEnd (eq_op^~ 0) s) => [/= | h t /=].
  - apply GRing.oner_neq0.
  - rewrite Hdrop in Hlast. by apply Hlast.
Qed.

Lemma rem_tail_zero_nth: forall s i,
  nth 0 s i = nth 0 (rem_trail_zero s) i.
Proof.
  move => s i. rewrite /rem_trail_zero.
  have: (dropWhileEnd (eq_op^~ 0) s) = (dropWhileEnd (eq_op^~ 0) s) by [].
  rewrite (dropWhileEnd_spec _ _ 1) => [[[l1 [Hl1 Hinl1]] Hlast]].
  rewrite {1}Hl1 nth_cat. 
  case Hi: (i < size (dropWhileEnd (eq_op^~ 0) s)).
  - by [].
  - rewrite (@nth_default _ 0 (dropWhileEnd (eq_op^~ 0) s) i). 
    case Hi': (i - size (dropWhileEnd (eq_op^~ 0) s) < size l1).
    + move: Hinl1. rewrite -all_in => /all_nthP Hall. apply /eqP. by apply Hall.
    + by rewrite nth_default // leqNgt Hi'.
    + by rewrite leqNgt Hi.
Qed.

Lemma lpolyP: forall (p q : lpoly), nth 0 p =1 nth 0 q <-> p = q.
Proof.
  move => p q. apply polyP.
Qed.

Definition seq_to_lpoly (s: seq F) : lpoly :=
  Polynomial (rem_trail_zero_wf s).

Definition lpoly_to_seq (l: lpoly) : seq F := l.

(*We want a computable Euclidean division algorithm, so we need computable polynomial operations. We start with
  addition*)
Section Add.

(*Can't define with [zip] and [map] because we need to handle case when 1 poly has ended with implicit zeroes.
  It is inefficient to add zeroes to the end of the list before summing*)
Fixpoint lpoly_add_aux (s1 s2: seq F) : seq F :=
  match (s1, s2) with
  | (x1 :: t1, x2 :: t2) => (x1 + x2) :: lpoly_add_aux t1 t2
  | (_, _ :: _) => s2
  | (_, _) => s1
  end.

Definition lpoly_add (l1 l2: lpoly) : lpoly :=
  seq_to_lpoly (lpoly_add_aux l1 l2).

Lemma lpoly_add_aux_nth: forall s1 s2 i,
  (lpoly_add_aux s1 s2)`_i = s1`_i + s2`_i.
Proof.
  move => s1. elim : s1 => [/= s2 i | h t /= IH s2 i].
  - case : s2 => [//=| h t /=].
    + by rewrite nth_nil GRing.addr0.
    + by rewrite nth_nil GRing.add0r.
  - case : s2 => [//= | h1 t1 /=].
    + by rewrite nth_nil GRing.addr0.
    + case : i => [//= | i /=]. apply IH.
Qed.

Lemma lpoly_add_nth: forall l1 l2 i,
  (lpoly_add l1 l2)`_i = l1`_i + l2`_i.
Proof.
  move => l1 l2 i. by rewrite /lpoly_add -rem_tail_zero_nth lpoly_add_aux_nth.
Qed.

Lemma lpoly_add_spec: forall l1 l2,
  Poly (lpoly_add l1 l2) = Poly l1 + Poly l2.
Proof.
  move => l1 l2. rewrite -polyP => i.
  by rewrite coef_add_poly !polyseqK lpoly_add_nth.
Qed.

(*TODO: need info about degrees: in particular, leq the max degree, and if the last element of both are additive
  inverses, degree is strictly smaller*)
(*maybe, maybe not if just equivalence, their version uses fuel*)
End Add.

(*In Euclidean division, we only need to multiply a polynomial p by kx^n for some scalar k. We can do this
  more efficiently than general multiplication by just using a single append and map*)

Section Shift.

(*Scalar multiply*)
Definition lpoly_sc_mul_aux (s: seq F) (k: F) : seq F :=
  map (fun x => k * x) s.

Lemma lpoly_sc_mul_aux_nth: forall s k i,
  (lpoly_sc_mul_aux s k)`_i = k * s`_i.
Proof.
  move => s k i. case Hi : (i < size s).
  - by rewrite (nth_map 0).
  - rewrite !nth_default //. by rewrite GRing.mulr0. by rewrite leqNgt Hi.
    by rewrite size_map leqNgt Hi.
Qed.

Lemma lpoly_sc_mul_aux_wf: forall (l: lpoly) k,
  k != 0 ->
  last 1 (lpoly_sc_mul_aux l k) != 0.
Proof.
  move => l k Hk0. rewrite /lpoly_sc_mul_aux.
  have->: 1 = k * k^-1 by rewrite GRing.mulfV. rewrite last_map.
  case : l => [s Hlast]. rewrite /= GRing.mulf_neq0 //.
  move : Hlast. case : s => [/= H10|//]. by apply GRing.invr_neq0.
Qed.

Definition lpoly_sc_mul_aux_full (s: seq F) (k: F) : seq F :=
  if k == 0 then nil else lpoly_sc_mul_aux s k.

Lemma lpoly_sc_mul_aux_full_nth: forall s k i,
  (lpoly_sc_mul_aux_full s k)`_i = k * s`_i.
Proof.
  move => s k i. rewrite /lpoly_sc_mul_aux_full. case Hk : (k == 0) => [/= | /=].
  - apply (elimT eqP) in Hk. subst. by rewrite nth_nil GRing.mul0r.
  - apply lpoly_sc_mul_aux_nth.
Qed.

Lemma lpoly_sc_mul_aux_full_wf: forall (l: lpoly) k,
  last 1 (lpoly_sc_mul_aux_full l k) != 0.
Proof.
  move => l k. rewrite /lpoly_sc_mul_aux_full. case Hk : (k == 0) => [/= | /=].
  - apply GRing.oner_neq0.
  - apply lpoly_sc_mul_aux_wf. by rewrite Hk.
Qed.

Definition lpoly_sc_mul (l: lpoly) k : lpoly :=
  Polynomial (lpoly_sc_mul_aux_full_wf l k).

Lemma lpoly_sc_mul_spec: forall (l: lpoly) k,
  Poly (lpoly_sc_mul l k) = k%:P * (Poly l).
Proof.
  move => l k. rewrite /= -polyP => i.
  rewrite !polyseqK /=. rewrite (@PolyK _ 1). 2: apply lpoly_sc_mul_aux_full_wf.
  by rewrite coefCM lpoly_sc_mul_aux_full_nth.
Qed.

(*Now similarly, multiply by x^n*)
Definition lpoly_shift_aux (s: seq F) (n: nat) :=
  nseq n 0 ++ s.

Lemma lpoly_shift_aux_nth: forall s n i,
  (lpoly_shift_aux s n)`_i = if i < n then 0 else s`_(i - n).
Proof.
  move => s n i. rewrite /lpoly_shift_aux nth_cat size_nseq nth_nseq.
  by case : (i < n).
Qed.

Lemma lpoly_shift_aux_wf: forall (l: lpoly) n,
  ~~ nilp l ->
  last 1 (lpoly_shift_aux l n) != 0.
Proof.
  move => l n. rewrite /lpoly_shift_aux last_cat. case : l => [s Hlast].
  rewrite /=. move: Hlast. by case : s.
Qed.

Definition lpoly_shift_aux_full (s: seq F) (n: nat) :=
  if nilp s then nil else (lpoly_shift_aux s n).

Lemma lpoly_shift_aux_full_nth: forall s n i,
  (lpoly_shift_aux_full s n)`_i = if i < n then 0 else s`_(i - n).
Proof.
  move => s n i. rewrite /lpoly_shift_aux_full. case : s => [/= | h t /=].
  - rewrite !nth_nil. by case : (i < n).
  - apply lpoly_shift_aux_nth.
Qed.

Lemma lpoly_shift_aux_full_wf: forall (l: lpoly) n,
  last 1 (lpoly_shift_aux_full l n) != 0.
Proof.
  move => l n. rewrite /lpoly_shift_aux_full.
  case Hs: (nilp l) => [//= | //=].
  - apply GRing.oner_neq0.
  - apply lpoly_shift_aux_wf. by rewrite Hs.
Qed.

Definition lpoly_shift (l: lpoly) (n: nat) : lpoly :=
  Polynomial (lpoly_shift_aux_full_wf l n).

Lemma lpoly_shift_spec: forall l n,
  Poly (lpoly_shift l n) = 'X^n * Poly l.
Proof.
  move => l n. rewrite -polyP => i. rewrite /= coefXnM polyseqK (@PolyK _ 1).
  by rewrite lpoly_shift_aux_full_nth. apply lpoly_shift_aux_full_wf.
Qed.

(*For our purposes, we would like to multiply by kx^n. We can make this more efficient by only mapping
  over the extra part*)
Definition lpoly_sc_mul_shift_aux (s: seq F) (k: F) (n: nat) :=
  nseq n 0 ++ map (fun x => k * x) s.

Lemma lpoly_sc_mul_shift_aux_equiv: forall s k n,
  lpoly_sc_mul_shift_aux s k n = lpoly_sc_mul_aux (lpoly_shift_aux s n) k.
Proof.
  move => s k n. rewrite /lpoly_sc_mul_shift_aux /lpoly_sc_mul_aux /lpoly_shift_aux.
  rewrite map_cat. f_equal. apply (@eq_from_nth _ 0). by rewrite size_map.
  move => i. rewrite size_nseq => Hi. rewrite (nth_map 0). by rewrite !nth_nseq Hi GRing.mulr0.
  by rewrite size_nseq.
Qed.

Definition lpoly_sc_mul_shift_aux_full s k n :=
  if (nilp s) || (k == 0) then nil else lpoly_sc_mul_shift_aux s k n.

Lemma lpoly_sc_mul_shift_aux_full_wf: forall (l: lpoly) k n,
  last 1 (lpoly_sc_mul_shift_aux_full l k n) != 0.
Proof.
  move => l k n. rewrite /lpoly_sc_mul_shift_aux_full.
  case Hl: (nilp l) => [/= | /=].
  - apply GRing.oner_neq0.
  - case Hk: (k == 0) => [/= | /=].
    + apply GRing.oner_neq0.
    + rewrite lpoly_sc_mul_shift_aux_equiv.
      have: last 1 (lpoly_sc_mul_aux (lpoly_shift l n) k) != 0.
        apply lpoly_sc_mul_aux_wf. by rewrite Hk. by rewrite /= /lpoly_shift_aux_full Hl.
Qed.

Definition lpoly_sc_mul_shift (l: lpoly) k n :=
  Polynomial (lpoly_sc_mul_shift_aux_full_wf l k n).

Lemma lpoly_sc_mul_shift_spec: forall (l: lpoly) k n,
  Poly (lpoly_sc_mul_shift l k n) = k%:P * ('X^n * Poly l).
Proof.
  move => l k n; rewrite /= /lpoly_sc_mul_shift_aux_full.
  case Hl: (nilp l) => [/= | /=].
  - apply (elimT nilP) in Hl. rewrite Hl /=. by rewrite !GRing.mulr0.
  - case Hk: (k == 0).
    + apply (elimT eqP) in Hk. subst. by rewrite GRing.mul0r.
    + rewrite lpoly_sc_mul_shift_aux_equiv.
      have->: Poly (lpoly_sc_mul_aux (lpoly_shift_aux l n) k) =
              k %:P * Poly (lpoly_shift_aux l n). {
      have Hnil: ~~(nilp l) by rewrite Hl.
      pose proof lpoly_sc_mul_spec as Hmul; move : Hmul => /(_ (Polynomial (lpoly_shift_aux_wf n Hnil)) k) /=.
      by rewrite /lpoly_sc_mul_aux_full Hk. }
      f_equal. pose proof lpoly_shift_spec as Hspec; move: Hspec. by rewrite /lpoly_shift /= /lpoly_shift_aux_full =>
      /( _ l n); rewrite Hl.
Qed.

End Shift.

Section Monomial.

Definition lpoly_mono_aux (n: nat) : seq F := rcons (nseq n 0) 1.

Lemma lpoly_mono_aux_wf: forall n,
  last 1 (lpoly_mono_aux n) != 0.
Proof.
  move => n. rewrite /lpoly_mono_aux. rewrite last_rcons. apply GRing.oner_neq0.
Qed.

Definition lpoly_mono (n: nat) : lpoly := Polynomial (lpoly_mono_aux_wf n).

Lemma lpoly_mono_spec: forall n,
  Poly (lpoly_mono n) = 'X^n.
Proof.
  move => n. by rewrite /= /lpoly_mono_aux /= -polyseqXn polyseqK.
Qed.

End Monomial.
  

(*Euclidean Division*)
Section Div.

(*Lots of definitions to unfold*)
Definition lpoly_redivp_rec (l: lpoly) :=
  let sq := size l in
  let cq := last 0 l in
  fix loop (k: nat) (qq r : lpoly) (n: nat) {struct n} : nat * lpoly * lpoly :=
    if size r < sq then (k, qq, r)
    else
      let lc := last 0 r in
      let qq1 := lpoly_add (lpoly_sc_mul qq cq) (lpoly_sc_mul (lpoly_mono (size r - sq)) lc) in
      let r1 := lpoly_add (lpoly_sc_mul r cq) (lpoly_sc_mul_shift l (- lc) (size r - sq)) in
      match n with
      | 0 => (k.+1, qq1, r1)
      | n1.+1 => loop k.+1 qq1 r1 n1
      end.

Definition tuple_to_poly (x: (nat * lpoly * lpoly)) : nat * {poly F} * {poly F} :=
  match x with
  | (n, p1, p2) => (n, Poly p1, Poly p2)
  end.

Lemma size_Poly: forall (l: lpoly),
  size (Poly l) = size l.
Proof.
  move => l. f_equal. by rewrite polyseqK.
Qed.

Lemma lead_coef_Poly: forall (l: lpoly),
  (lead_coef (Poly l)) = last 0 l.
Proof.
  move => l. by rewrite /lead_coef nth_last /= polyseqK.
Qed. 

Lemma lpoly_redivp_rec_spec: forall l k qq r n,
  tuple_to_poly (lpoly_redivp_rec l k qq r n) = Pdiv.Ring.redivp_rec (Poly l) k (Poly qq) (Poly r) n.
Proof.
  move => l k qq r n. move: l k qq r. elim : n => [/= l k qq r | n /= IH l k qq r].
  - rewrite !size_Poly. case Hsz: (size r < size l).
    + by [].
    + rewrite /tuple_to_poly !lpoly_add_spec !lpoly_sc_mul_spec !lead_coef_Poly !lpoly_mono_spec
      lpoly_sc_mul_shift_spec /=. f_equal. 
      * f_equal. rewrite GRing.mulrC. f_equal. by rewrite mul_polyC.
      * rewrite GRing.mulrC. f_equal. by rewrite -!mul_polyC polyCN !GRing.mulrA !GRing.mulNr.
  - rewrite !size_Poly. case Hsz: (size r < size l).
    + by [].
    + rewrite !lead_coef_Poly IH. f_equal.
      * by rewrite !lpoly_add_spec !lpoly_sc_mul_spec !lpoly_mono_spec -!mul_polyC GRing.mulrC.
      * rewrite !lpoly_add_spec !lpoly_sc_mul_spec !lpoly_sc_mul_shift_spec -!mul_polyC GRing.mulrC. f_equal.
        by rewrite polyCN GRing.mulNr GRing.mulrA.
Qed.

Lemma zero_nil : 0%R = seq_to_lpoly nil.
Proof.
  apply /eqP. rewrite eq_sym.
  by rewrite -nil_poly /=.
Qed.

Definition lpoly_redivp (p q: lpoly) : nat * lpoly * lpoly :=
  match (polyseq q) with
  | nil => (0%N, 0, p) 
  | _ :: _ => lpoly_redivp_rec q 0 (seq_to_lpoly nil) p (size p)
  end.

Lemma lpoly_zero: forall (l: lpoly),
  (Poly l == 0) = nilp l.
Proof.
  move => l. by rewrite nil_poly polyseqK.
Qed. 

Lemma lpoly_redivp_spec: forall p q,
  tuple_to_poly (lpoly_redivp p q) = Pdiv.Ring.redivp (Poly p) (Poly q).
Proof.
  move => p q. rewrite /lpoly_redivp locked_withE /Pdiv.Ring.redivp_expanded_def lpoly_zero.
  case Hq: (nilp q).
  - move: Hq; case : (polyseq q) => [//= Htriv | //=]. rewrite /=. f_equal. f_equal. by rewrite polyseqK.
  - move : Hq; case : q => [l Hl]. move: Hl; case : l => [// | h t Hl Hq].
    have->: polyseq (Polynomial Hl) = h :: t by [].
    rewrite lpoly_redivp_rec_spec. f_equal. by rewrite polyseqK.
Qed.

Definition lpoly_edivp (p q: lpoly) : nat * lpoly * lpoly :=
  let '(k, d, r) := lpoly_redivp p q in
  let lc := last 0 q in
  if lc \is a GRing.unit then (0%N, lc ^- k *: d, lc ^-k *: r) else (k, d, r).

Lemma lpoly_edivp_spec: forall p q,
  tuple_to_poly (lpoly_edivp p q) = Pdiv.Field.edivp (Poly p) (Poly q).
Proof.
  move => p q. rewrite /lpoly_edivp /Pdiv.Field.edivp locked_withE /Pdiv.Field.edivp_expanded_def !lead_coef_Poly.
  rewrite -lpoly_redivp_spec /= /tuple_to_poly.
  case Hdiv: (lpoly_redivp p q) => [[k d] r] . 
  case Hun: ( last 0 q \is a GRing.unit).
  - by rewrite !polyseqK.
  - by [].
Qed.

End Div.


(*TODO: When working over GF(2), we can give simpler functions because all leading coefficients are 1. This
  results in more efficient code*)



(*
Definition lpoly_to_poly : lpoly -> {poly F} := Poly. (*id*)
Definition poly_to_lpoly : {poly F} -> lpoly := id.

Lemma lpoly_to_poly_inv: forall (l: lpoly), poly_to_lpoly (lpoly_to_poly l) = l.
Proof.
  move => l. rewrite /poly_to_lpoly /lpoly_to_poly. apply polyseqK.
Qed.

Lemma poly_to_poly_inv: forall (p: {poly F}), lpoly_to_poly (poly_to_lpoly p) = p.
Proof.
  move => p. apply polyseqK. 
Qed.*)


End LPoly.

(*Tests for computability*)

Require Import BoolField.

Check lpoly_redivp_rec.

Eval compute in (lpoly_to_seq (lpoly_redivp_rec (seq_to_lpoly [:: true; false; true]) 0%N (seq_to_lpoly nil)
  (seq_to_lpoly [:: true; true; false; true]) 4).1.2).

Eval compute in rem_trail_zero(lpoly_add_aux (lpoly_sc_mul_aux_full (nil) true)
            (lpoly_sc_mul_aux_full (lpoly_mono_aux bool_fieldType (4 - 3)) true)).

Eval compute in (nilp ((seq_to_lpoly [:: true; false; true]))).

Eval compute in (lpoly_to_seq (lpoly_redivp (seq_to_lpoly [:: true; true; false; true]) 
  (seq_to_lpoly [:: true; true])).1.2).

(*need to remove unit check (could change to =0 for general case*)

Eval compute in (lpoly_to_seq (lpoly_edivp (seq_to_lpoly [:: true; true; false; true]) 
  (seq_to_lpoly [:: true; false; true])).1.2).

Eval compute in (lpoly_to_seq (lpoly_add (seq_to_lpoly ( [:: true; false; false])) 
  (seq_to_lpoly( [:: true; false; true])))).

Eval compute in (lpoly_to_seq (lpoly_shift (seq_to_lpoly ([:: true; false; true])) 3)).


Eval compute in (poly_to_lpoly 
  (@lpoly_to_poly bool_fieldType ([:: true; false; false]) + Poly [:: true; false; false])%R).