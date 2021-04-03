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
Section LPoly.

Local Open Scope ring_scope.

Variable F : fieldType.

Definition lpoly := polynomial F.

(*Transform an arbitrary list into a valid lpoly*)
Lemma lpoly_Poly_eq: forall (p q : lpoly),
  Poly p = Poly q -> p = q.
Proof.
  move => p q. by rewrite !polyseqK.
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
  move => l1 l2 i. by rewrite /lpoly_add -rem_trail_zero_nth lpoly_add_aux_nth.
Qed.

Lemma lpoly_add_spec: forall l1 l2,
  Poly (lpoly_add l1 l2) = Poly l1 + Poly l2.
Proof.
  move => l1 l2. rewrite -polyP => i.
  by rewrite coef_add_poly !polyseqK lpoly_add_nth.
Qed.

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

Lemma lpoly_sc_mul_1: forall (l: lpoly),
  lpoly_sc_mul l 1 = l.
Proof.
  move => l. apply lpoly_Poly_eq. by rewrite lpoly_sc_mul_spec GRing.mul1r.
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

Lemma lpoly_sc_mul_shift_1: forall (l: lpoly) n,
  lpoly_sc_mul_shift l 1 n = lpoly_shift l n.
Proof.
  move => l n. apply lpoly_Poly_eq. by rewrite lpoly_sc_mul_shift_spec lpoly_shift_spec GRing.mul1r.
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

Lemma size_Poly_lpoly: forall (l: lpoly),
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
  - rewrite !size_Poly_lpoly. case Hsz: (size r < size l).
    + by [].
    + rewrite /tuple_to_poly !lpoly_add_spec !lpoly_sc_mul_spec !lead_coef_Poly !lpoly_mono_spec
      lpoly_sc_mul_shift_spec /=. f_equal. 
      * f_equal. rewrite GRing.mulrC. f_equal. by rewrite mul_polyC.
      * rewrite GRing.mulrC. f_equal. by rewrite -!mul_polyC polyCN !GRing.mulrA !GRing.mulNr.
  - rewrite !size_Poly_lpoly. case Hsz: (size r < size l).
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
  if nilp q then (0%N, 0, p) else lpoly_redivp_rec q 0 (seq_to_lpoly nil) p (size p).

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

(*For computability reasons, we don't want to use "==". Luckily we are in a field, so testing
  for a unit is easily computable*)
Lemma f_eq_dec : forall (x y : F), { x = y } + { x <> y}.
Proof.
  move => x y. apply (decP eqP).
Defined.

Definition lpoly_edivp (p q: lpoly) : nat * lpoly * lpoly :=
  let '(k, d, r) := lpoly_redivp p q in
  let lc := last 0 q in
  if (f_eq_dec lc 0) then (k, d, r) else (0%N, (lpoly_sc_mul d (lc ^- k)), lpoly_sc_mul r (lc ^-k)). 

Lemma lpoly_edivp_spec: forall p q,
  tuple_to_poly (lpoly_edivp p q) = Pdiv.Field.edivp (Poly p) (Poly q).
Proof.
  move => p q. rewrite /lpoly_edivp /Pdiv.Field.edivp locked_withE /Pdiv.Field.edivp_expanded_def !lead_coef_Poly.
  rewrite -lpoly_redivp_spec /= /tuple_to_poly.
  case Hdiv: (lpoly_redivp p q) => [[k d] r] .
  rewrite GRing.unitfE. case: (f_eq_dec (last 0 q) 0) => [Hlast /= | Hlast].
  - by rewrite Hlast eq_refl /=.
  - rewrite /=. apply (introF eqP) in Hlast. rewrite Hlast !polyseqK /=. f_equal. f_equal.
    by rewrite lpoly_sc_mul_spec /= mul_polyC polyseqK.
    by rewrite lpoly_sc_mul_spec /= mul_polyC polyseqK.
Qed.

End Div.

End LPoly.

(*We will be working over GF(2), so we can give simpler functions because all leading coefficients are 1. The
  code will be more efficient, which is important because this will be run many times in a loop*)
Require Import BoolField.

Section BoolPolyDiv.

Local Open Scope ring_scope.

Definition F := bool_fieldType.

(*Some facts about the field of booleans*)
Lemma bool_1_0: forall (f: F),
  (f != 0) = (f == 1).
Proof.
  move => f. by case : f.
Qed.

Lemma bool_lc: forall (l: lpoly F),
  ~~(nilp l) ->
  last 0 l = 1.
Proof.
  move => l. case : l => [l /=]. case : l => [// | h t /= Hlast Htriv]. apply /eqP. by rewrite -bool_1_0.
Qed.

Lemma neg_one: GRing.one F = - 1.
Proof.
  by [].
Qed.


Definition bool_redivp_rec (l: lpoly F) :=
  let sq := size l in
  fix loop (qq r : lpoly F) (n: nat) {struct n} : lpoly F * lpoly F :=
    if size r < sq then (qq, r)
    else
      let qq1 := lpoly_add qq (lpoly_mono F (size r - sq)%N) in
      let r1 := lpoly_add r (lpoly_shift l (size r - sq)) in
      match n with
      | 0 => (qq1, r1)
      | n1.+1 => loop qq1 r1 n1
      end.

(*TODO: move*)
Lemma size_not_nil: forall {A: Type} (l: seq A),
  (0 < size l) = ~~ (nilp l).
Proof.
  move => A l. case Hsz: (size l) => [/= | n /=].
  - apply size0nil in Hsz. by subst.
  - move: Hsz. by case : l.
Qed.

(*TODO: move maybe, only in separate lemma so I don't need to do it twice in the following proof*)
Lemma larger_not_nil: forall {A: Type} (l1 l2: seq A),
  ~~ nilp l2 ->
  (size l1 < size l2) = false ->
  ~~ nilp l1.
Proof.
  move => A l1 l2 Hl2 Hsz. rewrite ltnNge in Hsz. apply negbFE in Hsz. move : Hl2;
  rewrite -!size_not_nil => Hl2. by apply (ltn_leq_trans Hl2).
Qed.

(*Last two elts of a tuple*)
Definition last_two {A B C : Type} (x: A * B * C) : B * C :=
  match x with
  | (a, b, c) => (b, c)
  end.

Lemma bool_redivp_rec_spec: forall (l: lpoly F) q r n k,
  ~~(nilp l) ->
  (bool_redivp_rec l q r n) = last_two (lpoly_redivp_rec l k q r n).
Proof.
  move => l q r n. move: l q r. elim : n => [/= l q r k Hl | n /= IH l q r k Hl].
  - case Hsz: (size r < size l).
    + by [].
    + rewrite /= !bool_lc //. by rewrite !lpoly_sc_mul_1 -neg_one lpoly_sc_mul_shift_1. by apply (larger_not_nil Hl). 
  - case Hsz: (size r < size l).
    + by [].
    + rewrite /= !bool_lc //. by rewrite !lpoly_sc_mul_1 /= -neg_one lpoly_sc_mul_shift_1 -IH.
      by apply (larger_not_nil Hl).
Qed.

Definition bool_edivp (p q : lpoly F) : lpoly F * lpoly F :=
  if nilp q then (0, p) else bool_redivp_rec q (seq_to_lpoly nil) p (size p).

Lemma bool_edivp_spec: forall p q,
  bool_edivp p q = last_two (lpoly_edivp p q).
Proof.
  move => p q. rewrite /bool_edivp /lpoly_edivp /lpoly_redivp /=.
  case Hq: (nilp q) => [/= | /=].
  - case: (f_eq_dec (last 0 q) 0) => [Hz //= | Hz /=].
    move : Hz Hq. case : q => q. by case : q.
  - rewrite (bool_redivp_rec_spec _ _ _ 0); last first. by rewrite Hq.
    case Hr: (lpoly_redivp_rec q 0 (seq_to_lpoly [::]) p (size p)) => [ [k d] r].
    case : (f_eq_dec (last 0 q) 0) => [Hz //= | Hz /=].
    rewrite !bool_lc; last first. by rewrite Hq. by rewrite !GRing.expr1n !GRing.invr1 !lpoly_sc_mul_1.
Qed.

(*Test for computability*)
(*x^4+x^3+1 = (x^2+1) * (x^2 + x + 1) + x in GF(2)*)
Eval compute in (lpoly_to_seq (bool_edivp (seq_to_lpoly [:: true; false; false; true; true]) 
  (seq_to_lpoly [:: true; false; true])).1).
Eval compute in (lpoly_to_seq (bool_edivp (seq_to_lpoly [:: true; false; false; true; true]) 
  (seq_to_lpoly [:: true; false; true])).2).

(*We need to enumerate all polynomials up to a certain length. This takes a bit of work due to the dependent types*)
Fixpoint seq_of_polyseqs (n: nat) : (seq (seq F)) * (seq (seq F)) :=
  match n with
  | 0 => ([:: [:: true]], [:: [:: true]])
  | n'.+1 => let (leq_seq, eq_seq) := (seq_of_polyseqs n') in
             let new_eq_seq := (map (cons true) eq_seq) ++ (map (cons false) eq_seq) in
             (leq_seq ++ new_eq_seq, new_eq_seq)
  end.

Lemma nil_notin_seq: forall n,
  (nil \notin (seq_of_polyseqs n).1) && (nil \notin (seq_of_polyseqs n).2).
Proof.
  move => n. elim : n => [//= | n /=].
  case Hseq : (seq_of_polyseqs n) => [leq_seq eq_seq]. rewrite /= => /andP[Hle Heq].  
  rewrite !mem_cat !negb_or Hle /= {1}andbC andbA -(andbA ([::] \notin [seq false :: i | i <- eq_seq])) 
  andbb andbC andbA andbb. apply /andP. split; apply /mapP => [[x Hx] //].
Qed. 

Lemma zero_notin_seq: forall n,
  ([:: 0] \notin (seq_of_polyseqs n).1) && ([:: 0] \notin (seq_of_polyseqs n).2).
Proof.
  move => n. elim : n => [//= | n /=].
  case Hseq : (seq_of_polyseqs n) => [leq_seq eq_seq]. rewrite /= => /andP[Hle Heq].  
  rewrite !mem_cat !negb_or Hle /= {1}andbC andbA -(andbA ([:: 0] \notin [seq false :: i | i <- eq_seq])) 
  andbb andbC andbA andbb. apply /andP.
  pose proof (nil_notin_seq n) as Hnil. move: Hnil; rewrite Hseq /= => /andP[Hnileq Hnilleq].
  split. apply /mapP => [[x Hin [Hx]]]. subst. by rewrite Hin in Hnilleq.
  by apply /mapP => [[x Hin [Hx]]].
Qed.

Lemma seq_of_polyseqs_last: forall n s,
  (s \in (seq_of_polyseqs n).1) || (s \in (seq_of_polyseqs n).2) ->
  last 1 s != 0.
Proof.
  move => n. elim : n => [//= s | n /=].
  - rewrite !in_cons in_nil orbF orbb => /eqP Hs. rewrite Hs. by [].
  - case Hseq: (seq_of_polyseqs n) => [leq_seq eq_seq]. rewrite /=. move => IH s.
    rewrite !mem_cat -orbA -orbA orbC -orbA (orbC (s \in [seq false :: i | i <- eq_seq])) -!orbA
    (orbA (s \in [seq false :: i | i <- eq_seq])) !orbb orbA orbb => 
    /orP[/mapP [x Hx Hs] | /orP[/mapP [x Hx Hs] | Hleq]].
    + rewrite Hs /=. apply IH. by rewrite Hx orbT.
    + rewrite Hs /=. have->: (last false x) = (last 1 x). move: Hx Hs. case : x => [//= Hnil | //=].
      pose proof (nil_notin_seq n) as Hnil'; move: Hnil'. by rewrite Hseq Hnil /= andbF.
      apply IH. by rewrite Hx orbT.
    + apply IH. by rewrite Hleq.
Qed.

Lemma size1P: forall {T: Type} (s: seq T),
  reflect (exists (x: T), s = [:: x]) (size s == 1%N) .
Proof.
  move => T s. case : s => [/= | h t /=].
  - apply ReflectF. by move =>[x Hx].
  - case : t => [|h' t' /=].
    + apply ReflectT. by exists h.
    + apply ReflectF. by move => [x Hx].
Qed.

Lemma in_seq_of_polyseqs_snd: forall n s,
  s \in (seq_of_polyseqs n).2 = ((last 1 s != 0) && (size s == n.+1)).
Proof.
  move => n. elim : n => [//= s | n /=].
  - rewrite !in_cons in_nil orbF.
    case Hs: (s == [:: true]). apply (elimT eqP) in Hs. by rewrite Hs.
    case  Hsz: ((size s) == 1%N).
    + apply (elimT (size1P s)) in Hsz. case : Hsz => [x Hsx]. move: Hsx; case : x =>[ //=|->//=].
      move => /eqP Hst. by rewrite Hst in Hs.
    +  by rewrite andbF.
  - case Hseq: (seq_of_polyseqs n) => [leq_seq eq_seq]. rewrite /= => IH s. rewrite !mem_cat.
    case Hfst: (s \in [seq true :: i | i <- eq_seq]) =>[/= | /=].
    + move: Hfst => /mapP [x Hx Hs]. subst. by rewrite /= eqSS -IH Hx.
    + case Hsnd: (s \in [seq false :: i | i <- eq_seq]).
      * move : Hsnd => /mapP [x Hx Hs]. subst. rewrite /= eqSS.
        have->: (last false x = last 1 x). move : {Hfst} Hx. case : x =>[/= Hnil|//].
        by pose proof (nil_notin_seq n) as Hnils; move : Hnils; rewrite Hseq /= Hnil andbF.
        by rewrite -IH Hx.
      * case Hin: (((last 1 s) != 0) && ((size s) == (n.+2))) =>[|//].
        move: Hin Hsnd Hfst. case : s => [//= | h]. 
        case : h => [  t /= /andP[Hlast Hsz] Hsnd Hfst |  t /= /andP[Hlast Hsz] Hsnd Hfst];
        rewrite eqSS in Hsz.
        -- have Htin: (t \in eq_seq) by rewrite IH Hlast Hsz. by rewrite map_f in Hfst.
        -- have Hlast': (last false t = last 1 t). move {Hsnd Hfst Hsz}. move: Hlast.
           by case : t. rewrite Hlast' in Hlast. have Htin: (t \in eq_seq) by rewrite IH Hlast Hsz.
           by rewrite map_f in Hsnd.
Qed.

Lemma in_seq_of_polyseqs_fst: forall n s,
  s \in (seq_of_polyseqs n).1 = (last 1 s != 0) && (0 < size s <= n.+1).
Proof.
  move => n. elim : n => [//= s | n /=].
  - pose proof (in_seq_of_polyseqs_snd 0 s) as Hsnd. move: Hsnd; rewrite /=; move ->.
    f_equal. by rewrite eq_sym eqn_leq.
  - case Hseq: (seq_of_polyseqs n) => [leq_seq eq_seq]. rewrite /= => IH s. rewrite mem_cat.
    pose proof (in_seq_of_polyseqs_snd (n.+1) s) as Hsnd. move: Hsnd; rewrite /= Hseq /=.
    move ->. rewrite IH /=. rewrite -(andb_orr). f_equal. rewrite (leq_eqVlt _ (n.+2)).
    rewrite andb_orr orbC. rewrite (@andb_idl _ (size s == n.+2)) //.
    move => /eqP Hsz. by rewrite Hsz.
Qed.

Lemma seq_of_polyseqs_all_last: forall n,
  all (fun x => last 1 x != 0) (seq_of_polyseqs n).1.
Proof.
  move => n. rewrite all_in => x Hin. apply (@seq_of_polyseqs_last n).
  by rewrite Hin.
Qed.

Definition seq_of_lpoly (n: nat) : (seq (lpoly F)) :=
  sub_seq (polynomial_subType F) (seq_of_polyseqs_all_last n).

(*Finally we have what we want: an lpoly is in the list iff it is a nonzero polynomial of degree at most n*)
Lemma seq_of_lpoly_in: forall n (l: lpoly F),
  (l \in seq_of_lpoly n) = (0 < size l <= n.+1).
Proof.
  move => n l. rewrite sub_seq_in /= in_seq_of_polyseqs_fst /=.
  case : l => [s Hs /=]. by rewrite Hs.
Qed.

Eval compute in (map (@lpoly_to_seq F) (seq_of_lpoly 2)).

(*TODO: may need lemmas about equivalence with mathcomp mod (which is easy)*)

End BoolPolyDiv.

(*Tests for computability for original functions*)

Require Import BoolField.

Eval compute in (lpoly_to_seq (lpoly_redivp_rec (seq_to_lpoly [:: true; false; true]) 0%N (seq_to_lpoly nil)
  (seq_to_lpoly [:: true; true; false; true]) 4).1.2).
(*
Eval compute in rem_trail_zero(lpoly_add_aux (lpoly_sc_mul_aux_full (nil) true)
            (lpoly_sc_mul_aux_full (lpoly_mono_aux bool_fieldType (4 - 3)) true)).

Eval compute in (nilp ((seq_to_lpoly [:: true; false; true]))).
*)
Eval compute in (lpoly_to_seq (lpoly_redivp (seq_to_lpoly [:: true; true; false; true]) 
  (seq_to_lpoly [:: true; true])).1.2).

(*need to remove unit check (could change to =0 for general case*)

Eval compute in lpoly_to_seq(lpoly_add (lpoly_sc_mul (seq_to_lpoly [::]) true)
            (lpoly_sc_mul (lpoly_mono bool_fieldType (4 - 3)) true)).


Eval compute in (lpoly_to_seq (lpoly_edivp (seq_to_lpoly [:: true; true; false; true]) 
  (seq_to_lpoly [:: true; false; true])).1.2).

Eval compute in (lpoly_to_seq (lpoly_add (seq_to_lpoly ( [:: true; false; false])) 
  (seq_to_lpoly( [:: true; false; true])))).

Eval compute in (lpoly_to_seq (lpoly_shift (seq_to_lpoly ([:: true; false; true])) 3)).