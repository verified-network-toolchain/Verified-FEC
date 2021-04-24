From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.poly.
Require Import mathcomp.algebra.polydiv.
Require Import mathcomp.algebra.finalg.
Require Import mathcomp.ssreflect.tuple.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import CommonSSR.

(*Definition of field constructed from polynomials modulo an irreducible polynomial*)
Section Field.

Local Open Scope ring_scope.

(*We only work with polynomials over finite fields, the proof that this is a field is easier. In particular,
  we will want to prove that a certain map is bijective, and the injectivity is clear. We use [injF_bij]
  to prove that the map is therefore bijective. And since we are constructing finite fields anyway, it is
  OK to assume that the base field is finite*)
Variable F : finFieldType.

Variable p : {poly F}.
Variable Hirred: irreducible_poly p.

(*The type of polynomials of degree less than p*)
Inductive qpoly : predArgType := Qpoly (qp : {poly F}) of (size qp < size p).

Coercion qp (q: qpoly) : {poly F} := let: Qpoly x _ := q in x.
Definition qsz (q: qpoly) : size q < size p := let: Qpoly _ x := q in x.

Canonical qpoly_subType := [subType for qp].
Definition qpoly_eqMixin := Eval hnf in [eqMixin of qpoly by <:].
Canonical qpoly_eqType := Eval hnf in EqType qpoly qpoly_eqMixin.

Definition qpoly_choiceMixin := [choiceMixin of qpoly by <:].
Canonical qpoly_choiceType := Eval hnf in ChoiceType qpoly qpoly_choiceMixin.

Definition qpoly_countMixin := [countMixin of qpoly by <:].
Canonical qpoly_countType := Eval hnf in CountType qpoly qpoly_countMixin.
Canonical qpoly_subCountType := [subCountType of qpoly].

Lemma qpoly_eq: forall (p1 p2: {poly F}) (Hp1: size p1 < size p) (Hp2: size p2 < size p),
  p1 = p2 ->
  Qpoly Hp1 = Qpoly Hp2.
Proof.
  move => p1 p2 Hp1 Hp2 Hp12. subst. f_equal. apply bool_irrelevance.
Qed.

Lemma qpoly_eq': forall (q1 q2: qpoly),
  qp q1 = qp q2 ->
  q1 = q2.
Proof.
  move => [p1 Hp1] [p2 Hp2] /=. apply qpoly_eq.
Qed.

(** Size of the Finite Field*)

(*We want to prove that the cardinality of this set is |F|^(deg p) (and therefore that this
  set is finite). We do so with a mapping from qpolys to tuples of length (size p).-1*)

Definition qpoly_to_n_seq (q: qpoly) : seq F :=
  (qp q) ++ nseq ((size p).-1 - size (qp q)) 0.

Lemma p_gt_0: 0 < size p.
Proof.
  have H01: 0 < 1 by []. apply (ltn_trans H01). apply Hirred.
Qed.

Lemma qpoly_to_n_seq_size: forall q, size (qpoly_to_n_seq q) == (size p).-1.
Proof.
  move => q. apply /eqP. rewrite /qpoly_to_n_seq size_cat size_nseq subnKC //. case : q => [x Hx /=].
  by rewrite -ltn_pred // p_gt_0. 
Qed.

Definition qpoly_to_tuple q : ((size p).-1).-tuple F := Tuple (qpoly_to_n_seq_size q).

Definition tuple_to_poly (t: ((size p).-1).-tuple F) : {poly F} :=
  Poly (rem_trail_zero (tval t)).

Lemma tuple_to_poly_size: forall t,
  size (tuple_to_poly t) < size p.
Proof.
  move => t. rewrite /tuple_to_poly. have Ht: size t = ((size p).-1) by apply size_tuple.
  have Hlt: size t < size p. rewrite Ht. apply pred_lt. by rewrite p_gt_0.
  rewrite rem_trail_zero_polyseq. by apply (leq_ltn_trans (rem_trail_zero_size t)).
Qed.

Definition tuple_to_qpoly (t: ((size p).-1).-tuple F) : qpoly := Qpoly (tuple_to_poly_size t).

Lemma tuple_qpoly_cancel: cancel (tuple_to_qpoly) (qpoly_to_tuple).
Proof.
  move => x. rewrite /qpoly_to_tuple /tuple_to_qpoly /=. apply tuple_eq. rewrite /=.
  pose proof (dropWhileEnd_spec (eq_op^~ 0) x 1 (dropWhileEnd (eq_op^~ 0) x)) as Hdrop. 
  case : Hdrop => [Hdrop Htriv]; move => {Htriv}. case : Hdrop => [//|[l1 [Hx Hinl1 Hlast]]].
  rewrite /qpoly_to_n_seq /= /tuple_to_poly /= /rem_trail_zero.
  rewrite {3}Hx. f_equal.
  - apply rem_trail_zero_polyseq.
  - rewrite rem_trail_zero_polyseq /rem_trail_zero.
    have Hsz: size (nseq ((size p).-1 - size (dropWhileEnd (eq_op^~ 0) x)) (GRing.zero F)) = size l1. {
      rewrite size_nseq. have: size x = ((size p).-1) by apply size_tuple. rewrite {1}Hx size_cat addnC => Hszx.
      rewrite -{1}Hszx -addnBA. by rewrite subnn addn0. by rewrite leqnn. }
    apply (@eq_from_nth _ 0).
    + by [].
    + move => i. rewrite Hsz => Hi. rewrite nth_nseq. rewrite size_nseq in Hsz. rewrite Hsz Hi.
      apply /eqP. rewrite eq_sym. apply Hinl1. by rewrite mem_nth.
Qed.
  
Lemma qpoly_tuple_cancel: cancel (qpoly_to_tuple) (tuple_to_qpoly).
Proof.
  move => x. rewrite /qpoly_to_tuple /tuple_to_qpoly /=. apply qpoly_eq'. rewrite /=.
  rewrite /tuple_to_poly /= /qpoly_to_n_seq /=. rewrite /rem_trail_zero dropWhileEnd_end.
  rewrite (@dropWhileEnd_last _ _ _ 1). by rewrite polyseqK. case : x => [x' Hx']. rewrite /=. move : Hx'.
  by case : x'. rewrite all_in => a. by rewrite mem_nseq => /andP[H Ha].
Qed.

Lemma qpoly_to_tuple_bijective: bijective (qpoly_to_tuple).
Proof.
  apply (Bijective qpoly_tuple_cancel tuple_qpoly_cancel).
Qed.

Definition qpoly_finMixin := CanFinMixin qpoly_tuple_cancel.
Canonical qpoly_finType := Eval hnf in FinType qpoly qpoly_finMixin.

(*Finally, the result we want. This is a finite field of size |F|^(deg p)*)
Lemma qpoly_size: #|qpoly| = #|F|^((size p).-1).
Proof.
  by rewrite (bijective_card qpoly_to_tuple_bijective) card_tuple.
Qed.

(** Algebraic Structures*)

(*First, prove this is a Z Module*)
Lemma q0_bound: size (0 : {poly F}) < size p.
Proof.
  apply irredp_neq0 in Hirred. by rewrite size_poly0 size_poly_gt0 Hirred.
Qed.

Lemma q1_bound : size (1 : {poly F}) < size p.
Proof.
  rewrite size_poly1. apply Hirred.
Qed.

Definition q0 : qpoly := Qpoly q0_bound.
Definition q1 : qpoly := Qpoly q1_bound.

Lemma qadd_bound: forall (q1 q2: qpoly), size (val q1 + val q2) < size p.
Proof.
  move => [p1 Hp1] [p2 Hp2] /=. pose proof (size_add p1 p2) as Hmax. 
  apply (leq_ltn_trans Hmax). by rewrite gtn_max Hp1 Hp2.
Qed.

Definition qadd (q1 q2: qpoly) : qpoly := Qpoly (qadd_bound q1 q2).

Lemma qopp_bound: forall (q: qpoly), size (-(qp q)) < size p.
Proof.
  move => q. rewrite size_opp. apply qsz.
Qed. 

Definition qopp (q: qpoly) := Qpoly (qopp_bound q).

Lemma qpoly_qsz: forall (q: qpoly),
  Qpoly (qsz q) = q.
Proof.
  move => q. by case : q.
Qed.

Lemma qaddA : associative qadd.
Proof.
  move => q1 q2 q3. rewrite /qadd /=. apply qpoly_eq.
  by rewrite GRing.addrA. 
Qed.

Lemma qaddC : commutative qadd.
Proof.
  move => q1 q2. rewrite /qadd /=. apply qpoly_eq. by rewrite GRing.addrC.
Qed.

Lemma qaddFq : left_id q0 qadd.
Proof.
  move => q. rewrite /qadd /q0 /= -{3}(qpoly_qsz q). apply qpoly_eq.
  by rewrite GRing.add0r.
Qed.

Lemma qaddqq : left_inverse q0 qopp qadd.
Proof.
  move => q. rewrite /qadd /qopp /q0. apply qpoly_eq.
  by rewrite /= GRing.addrC GRing.subrr.
Qed.

Definition qpoly_zmodmixin := ZmodMixin qaddA qaddC qaddFq qaddqq.
Canonical qpoly_zmodtype := ZmodType qpoly qpoly_zmodmixin.

(*Ring*)
Lemma qmul_bound: forall (p1 p2: {poly F}), size ((p1 * p2) %% p) < size p.
Proof.
  move => p1 p2. rewrite ltn_modp. by apply irredp_neq0.
Qed.

Definition qmul (q1 q2 : qpoly) : qpoly := Qpoly (qmul_bound q1 q2).

Lemma qpoly_mulA : associative qmul.
Proof.
  move => q1 q2 q3. rewrite /qmul /=. apply qpoly_eq. 
  by rewrite (GRing.mulrC ((qp q1 * qp q2) %% p)) !modp_mul
  (GRing.mulrC _ (qp q1 * qp q2)) GRing.mulrA.
Qed.

Lemma qpoly_mulC: commutative qmul.
Proof.
  move => q1 q2. rewrite /qmul/=. apply qpoly_eq. by rewrite GRing.mulrC.
Qed.

Lemma qpoly_mul1q: left_id q1 qmul.
Proof.
  move => q. rewrite /qmul /q1 -{3}(qpoly_qsz q) /=. apply qpoly_eq. 
  rewrite GRing.mul1r modp_small//. apply qsz.
Qed.

Lemma qpoly_mulD : left_distributive qmul qadd.
Proof.
  move => x y z. rewrite /qmul /qadd /=. apply qpoly_eq.
  by rewrite -modpD GRing.mulrDl. 
Qed.

Lemma qpoly_1not0: q1 != q0.
Proof.
  case Heq : (q1 == q0) => [|//].
  apply (elimT eqP) in Heq. move: Heq. rewrite /q0 /q1 /= => [[H10]] //.
  have: (GRing.one (poly_ringType F)) != 0 by rewrite  GRing.oner_neq0. by rewrite H10 eq_refl.
Qed.

Definition qpoly_comringmixin := ComRingMixin qpoly_mulA qpoly_mulC qpoly_mul1q qpoly_mulD qpoly_1not0.
Canonical qpoly_ring := RingType qpoly qpoly_comringmixin.
Canonical qpoly_comring := ComRingType qpoly qpoly_mulC.


(*Now we want to show that inverses exist and are computable. We do this in several steps*)
Definition prime_poly (p: {poly F}) : Prop :=
  forall (a b : {poly F}), p %| (a * b) -> (p %| a) || (p %| b).

Lemma irreducibles_are_prime: forall p,
  irreducible_poly p -> prime_poly p.
Proof.
  move => p' Hp' a b Hpab.
  pose proof (Bezoutp p' a) as [[u v] Hbez]. rewrite /= in Hbez.
  case Ha: (p' %| a) => [// |].
  have Hgcdap: @size F (gcdp p' a) == 1%N. { case Hsz: (size (gcdp p' a) == 1%N) => [//|].
    pose proof (dvdp_gcdl p' a). apply Hp' in H. move: H. by rewrite /eqp dvdp_gcd Ha !andbF.
  by apply /negPf. }
  move: Hpab. by rewrite Gauss_dvdpr.
Qed.

Lemma qpoly_zero: forall (q: qpoly), (q == 0) = (qp q %% p == 0).
Proof.
  move => q. case : q => [x Hx] /=. have->: 0 = q0 by []. by rewrite /q0/= modp_small.
Qed.

(*The following will actually show that any finite integral domain is a field, but we don't generalize*)

(*We prove that it is an integral domain here, though the mathcomp Canonical instance comes later*)
Lemma qpoly_mulf_eq0 : forall x y : (qpoly), (x * y) = 0 -> (x == 0) || (y == 0).
Proof.
  move => x y. have->: (x * y) = qmul x y by []. have->: 0 = q0 by []. rewrite /qmul /= => [[/ modp_eq0P Hxy]].
  rewrite !qpoly_zero.
  have: ((p %| x) || (p %| y)). apply irreducibles_are_prime; by []. by [].
Qed.

Lemma qpoly_cancel: forall (a b c: qpoly), a != 0 -> a * b = a * c -> b = c.
Proof.
  move => a b c Ha Habc.
  have Haz: a * (b - c) = 0  by rewrite GRing.mulrBr Habc GRing.subrr.
  apply qpoly_mulf_eq0 in Haz. move: Haz => /orP [/eqP Ha0 | /eqP Hbc].
  - subst. by rewrite eq_refl in Ha.
  - by apply GRing.subr0_eq.
Qed.

(*To show that inverses exist, we will define the map mul_a(x) = a * x and show that this injective (and
  thus bijective) if a != 0*)
Definition mul_map (a: qpoly) := qmul a.

Lemma mul_map_inj: forall a,
  a != 0 ->
  injective (mul_map a).
Proof.
  move => a Haz x y; rewrite /mul_map. by apply qpoly_cancel.
Qed.

Lemma mul_map_bij: forall a,
  a !=0 ->
  bijective (mul_map a).
Proof.
  move => a Ha. apply injF_bij. by apply mul_map_inj.
Qed.

Lemma inverses_exist: forall (q: qpoly),
  q != 0 ->
  exists (inv: qpoly), inv * q = 1.
Proof.
  move => q Hq. apply mul_map_bij in Hq. case : Hq => g Hc1 Hc2. exists (g 1).
  move : Hc2 => /(_ 1) /=. by rewrite GRing.mulrC /mul_map.
Qed.

(*Now we need a computable inverse function. This is relatively straightforward*)

Definition find_inv (q: qpoly) :=
  find_val (fun x => x * q == 1) (enum qpoly) 0.

Lemma find_inv_correct: forall q,
  q != 0 ->
  (find_inv q) * q = 1.
Proof.
  move => q Hq. apply /eqP. rewrite /find_inv. 
  pose proof (@find_val_exists _ (fun x => x * q == 1) (enum qpoly) 0) as Hfind. rewrite /= in Hfind.
  apply Hfind. pose proof (inverses_exist Hq) as [inv Hinv]. exists inv. by rewrite in_enum /= Hinv eq_refl.
Qed.

Lemma find_inv_zero: find_inv 0 = 0.
Proof.
  rewrite /find_inv. apply find_val_none. rewrite all_in => x Hx. by rewrite GRing.mulr0 eq_sym GRing.oner_neq0.
Qed.

(*Now, we can finish the Canonical instances*)

(*[ComUnitRing] (ring with computable inverses*)

Definition qunit : pred qpoly :=
  fun x => x != q0.

Definition qinv := find_inv.

Lemma qpoly_mulVr : {in qunit, left_inverse q1 qinv qmul}.
Proof.
  move => q Hin. rewrite /qinv. by apply find_inv_correct.
Qed.

Lemma qpoly_mulrV : {in qunit, right_inverse q1 qinv qmul}.
Proof.
  move => q Hin. rewrite qpoly_mulC. by apply qpoly_mulVr.
Qed. 

Lemma qpoly_unitP : forall x y : qpoly, (y * x) = 1 /\ (x * y) = 1 -> qunit x.
Proof.
  move => x y [Hxy Hyx]. rewrite /qunit. case Hx: (x == 0) => [|//]. apply (elimT eqP) in Hx. subst.
  move: Hyx. rewrite GRing.mul0r => H01. have: GRing.one qpoly_ring != 0 by apply GRing.oner_neq0. 
  by rewrite H01 eq_refl.
Qed. 

Lemma qpoly_inv0id : {in [predC qunit], qinv =1 id}.
Proof.
  move => q Hun. have Hz: ~~ (q != 0) by []. move: Hz; rewrite negbK => /eqP Hz. subst. by apply find_inv_zero.
Qed.

Definition qpoly_unitringmixin := UnitRingMixin qpoly_mulVr qpoly_mulrV qpoly_unitP qpoly_inv0id.
Canonical qpoly_unitringtype := UnitRingType qpoly qpoly_unitringmixin.

(*Integral Domain*)

(*Need the comUnitRing first*)
Canonical qpoly_comunitring := [comUnitRingType of qpoly].
Canonical qpoly_idomaintype := IdomainType qpoly qpoly_mulf_eq0.

(*Field*)
Lemma qpoly_mulVf : GRing.Field.axiom qinv.
Proof.
  move => x Hnz. by apply qpoly_mulVr.
Qed.

Lemma qpoly_inv0: qinv 0%R = 0%R.
Proof.
  apply find_inv_zero.
Qed.

Definition qpoly_fieldmixin := FieldMixin qpoly_mulVf qpoly_inv0.
Canonical qpoly_fieldType := FieldType qpoly qpoly_fieldmixin.
Canonical qpoly_finFieldType := Eval hnf in [finFieldType of qpoly].

(*We needed the cardinality of qpolys because we want to consider primitive polynomials, 
  and we want to show that for any q!=0,
  there is an a such that x ^ a %% p = q. We define a mapping from 'I_(size p - 1) -> qpoly and show that
  it is injective. We need the above size result to conclude that the mapping is bijective and therefore
  surjective*)

(*Definition of primitive polynomial. Note that size p = 1 + deg p, and I believe the 2nd condition is
  always true, though we don't need to prove it*)
Definition primitive_poly (p: {poly F}) := irreducible_poly p /\ p %| 'X^((#|F|^((size p).-1)).-1) - 1 /\
  (forall n, p %| 'X^n - 1 -> (n == 0%N) || (((#|F|^((size p).-1)).-1) <= n)).

Variable Hprim: primitive_poly p.
(*Also, we assume that p <> cx for some constant c. This is not very interesting, since F[X] / (x) is isomorphic to F.
  And it makes some of the proofs much more annoying*)
Variable Hnotx: 2 < size p.

(*We want to know that, for all q != 0, exists a, 0 <= a < #|F|^(deg p) - 1 && (x ^ a %% p = q). We want to
  keep this entirely within qpolys as well*)
Lemma qx_bound: size (polyX F) < size p.
Proof.
  by rewrite size_polyX.
Qed.

Definition qx : qpoly := Qpoly (qx_bound).

Lemma qx_pow: forall (a: nat), qp (qx ^+ a) = ('X^a) %% p.
Proof.
  move => a. elim : a => [//= | a /= IH /=]. rewrite GRing.expr0 modp_small // size_poly1. apply Hirred.
  rewrite !GRing.exprSr. have->: qx ^+ a * qx = qmul (qx ^+ a) qx by []. 
  by rewrite /qmul /= IH GRing.mulrC modp_mul GRing.mulrC.
Qed.

Definition qpow_map (i: 'I_(#|F|^((size p).-1))) : qpoly := if (nat_of_ord i == 0%N) then q0 else qx ^+ i.

(*We need to know that p does not divide x^n for any n*)
Lemma irred_dvdn_Xn: forall (p: {poly F}) (n: nat),
  irreducible_poly p ->
  2 < size p ->
  ~~ (p %| 'X^n).
Proof.
  move => r n Hirr Hszr. elim : n => [//= | n /= IH].
  - rewrite GRing.expr0 dvdp1. case Hsz: (size r == 1%N) => [|//].
    apply (elimT eqP) in Hsz. by rewrite Hsz in Hszr.
  - rewrite GRing.exprS. case Hdiv: (r %| 'X * 'X^n) => [|//].
    have Hirr' : irreducible_poly r by [].
    apply (irreducibles_are_prime) in Hirr. apply Hirr in Hdiv.
    move : Hdiv => /orP[Hrx | Hrxn].
    + apply dvdp_leq in Hrx. move: Hrx. by rewrite size_polyX leqNgt Hszr. 
      by rewrite polyX_eq0.
    + by rewrite Hrxn in IH.
Qed. 

(*A weaker lemma than [modpD]*)
Lemma modpD': forall (d p q : {poly F}), d != 0 -> (p + q) %% d = (p %% d + q %% d) %% d.
Proof.
  move => d p' q Hd. rewrite modpD. apply esym. by rewrite modp_small // -modpD ltn_modp.
Qed.

Lemma qx_0: qx != 0.
Proof.
  have->: 0 = q0 by []. rewrite /qx/q0 /=. case Heq: (Qpoly qx_bound == Qpoly q0_bound) => [|//].
  apply (elimT eqP) in Heq. case : Heq => /eqP Hx0. have: ((polyX F) == 0 = false) by apply polyX_eq0.
  by rewrite Hx0.
Qed. 

Lemma qpow_map_bij: bijective qpow_map.
Proof.
  apply inj_card_bij; last first. by rewrite qpoly_size card_ord leqnn.
  move => a b. rewrite /qpow_map. case Ha0: (nat_of_ord a == 0%N).
  { apply (elimT eqP) in Ha0. case Hb0: (nat_of_ord b == 0%N).
    { apply (elimT eqP) in Hb0. move => Htriv. apply ord_inj. by rewrite Ha0 Hb0. }
    { move => Hx0. have: (qx ^+ b != q0). apply GRing.expf_neq0. apply qx_0.
      by rewrite Hx0 eq_refl. } }
  { case Hb0: (nat_of_ord b == 0%N).
    { move => Hx0. have: (qx ^+ a != q0). apply GRing.expf_neq0. apply qx_0. by rewrite Hx0 eq_refl. }
    { move: Ha0 Hb0. wlog: a b / (a <= b). 
  - move => Hall. case : (orP (leq_total a b)) => [Hab Ha0 Hb0 | Hab Ha0 Hb0].
    by apply Hall. move => Hab'. symmetry. by apply Hall.
  - move => Hab Ha0 Hb0 Hxab. have Hbsplit: nat_of_ord b = (a + (b - a))%N by rewrite subnKC.
    have: (qx ^+ b - qx ^+ a = 0) by rewrite Hxab GRing.subrr. rewrite Hbsplit GRing.exprD.
    rewrite -{2}(GRing.mulr1 (qx ^+ a)) -GRing.mulrBr => Hxab0. apply qpoly_mulf_eq0 in Hxab0.
    move: Hxab0 => /orP[|].
    + rewrite qpoly_zero qx_pow modp_mod => Hdiv.
      have: ~~ (p %| 'X^a) by apply irred_dvdn_Xn. by rewrite /dvdp Hdiv.
    + rewrite qpoly_zero /= qx_pow GRing.addrC modpD'; last first.
      rewrite -size_poly_eq0. case Hp: (size p == 0%N) =>[|//]. apply (elimT eqP) in Hp.
      by have: 2 < 0 by rewrite -{2}Hp. 
      rewrite  modp_mod GRing.addrC -modpD modp_mod => Hmod.
      have Hdiv: (p %| ('X^(b-a) - 1)) by [].
      apply Hprim in Hdiv. move: Hdiv => /orP [Hba0 | Hbabig].
      * rewrite subn_eq0 in Hba0. apply ord_inj. apply /eqP. by rewrite eqn_leq Hba0 Hab.
      * have Hb: b <   (#|F| ^ (size p).-1) by []. rewrite pred_leq in Hbabig.
        have Hba: (b - a).+1 <= b by rewrite ltn_subrL !neq0_lt0n.
        have: (#|F| ^ (size p).-1 <= b) by apply (leq_trans Hbabig Hba).
        by rewrite leqNgt Hb. } }
Qed.

(*The other definition was needed for the inverse of 0, but x^0=1. This map is NOT bijective, since
  0 is not in the codomain*)
Definition qpow_map_full (i: 'I_(#|F|^((size p).-1))): qpoly := qx ^+ i.

Lemma qpow_map_full_neq0: forall i,
  qpow_map_full i != 0.
Proof.
  move => i. rewrite /qpow_map_full. apply GRing.expf_neq0. apply qx_0.
Qed. 

Lemma qpow_exist: forall (q: qpoly),
  q != 0 ->
  exists (i: 'I_(#|F|^((size p).-1))), (nat_of_ord i != 0%N) && (qx ^+ i == q).
Proof.
  move => q Hq. case : (qpow_map_bij) => g Hqg Hgq.
  exists (g q). move: Hgq => /(_ q) /=. rewrite /qpow_map.
  case Hi: (nat_of_ord (g q) == 0%N).
  - move => Hq0. subst. move: Hq. have->: q0 = 0 by []. by rewrite eq_refl.
  - move->. by rewrite eq_refl.
Qed.

Lemma field_geq_0: 
  0 < #|F|^((size p).-1).
Proof.
  rewrite expn_gt0 /=. apply /orP. left. rewrite lt0n. apply /eqP. apply fintype0. apply 0%R.
Qed.

(*Computable function version*)
Definition find_qpow (q: qpoly) : 'I_(#|F|^((size p).-1)) :=
  find_val (fun i => (nat_of_ord i != 0%N) && (qx ^+ (nat_of_ord i) == q)) (enum  'I_(#|F|^((size p).-1))) 
  (Ordinal field_geq_0).

Lemma find_qpow_correct_aux: forall q,
  q != 0 ->
  (nat_of_ord (find_qpow q) != 0%N) && (qx ^+ (find_qpow q) == q).
Proof.
  move => q Hq. rewrite /find_qpow. 
  apply (@find_val_exists _ (fun i : 'I_(#|F| ^ (size p).-1) => (nat_of_ord i != 0%N) && (qx ^+ i == q))).
  rewrite /=. apply qpow_exist in Hq. case : Hq => [i /andP[Hi0 Hqx]].
  exists i. by rewrite in_enum Hi0 Hqx.
Qed.

Lemma find_qpow_nonzero: forall q,
  q != 0 ->
  nat_of_ord (find_qpow q) != 0%N.
Proof.
  move => q Hq. apply find_qpow_correct_aux in Hq. apply (elimT andP) in Hq. apply Hq.
Qed.

Lemma find_qpow_correct: forall q,
  q != 0 ->
  qx ^+ (find_qpow q) = q.
Proof.
  move => q Hq. apply /eqP. apply find_qpow_correct_aux in Hq. apply (elimT andP) in Hq. apply Hq.
Qed.

Lemma find_qpow_zero: nat_of_ord (find_qpow 0) == 0%N.
Proof.
  have Hfind: find_qpow 0 = (Ordinal field_geq_0). apply find_val_none. rewrite all_in.
  move => x Hx. 
  have Hnz: (qx ^+ x != 0). apply GRing.expf_neq0. apply qx_0.
  have->: (qx ^+ x == 0) = false by apply negbTE. by rewrite andbF.
  by rewrite Hfind /=.
Qed.

Lemma find_qpow_zero_iff: forall q, (nat_of_ord (find_qpow q) == 0%N) = (q == 0%R).
Proof.
  move => q. case Hq: (q == 0).
  - apply (elimT eqP) in Hq. rewrite Hq. apply find_qpow_zero.
  - have Hq': q != 0 by rewrite Hq. apply find_qpow_nonzero in Hq'. by rewrite -Bool.negb_true_iff.
Qed.

Lemma find_qpow_cancel: cancel find_qpow qpow_map.
Proof.
  move => q. rewrite /qpow_map. case Hq: (nat_of_ord (find_qpow q) == 0%N).
  - rewrite find_qpow_zero_iff in Hq. apply (elimT eqP) in Hq. by rewrite Hq.
  - apply find_qpow_correct. by rewrite -find_qpow_zero_iff Hq.
Qed.

Lemma qpow_map_cancel: cancel qpow_map find_qpow.
Proof.
  rewrite -bij_can_sym. apply find_qpow_cancel. apply qpow_map_bij.
Qed. 

Lemma find_qpow_bij: bijective find_qpow.
Proof.
  apply (bij_can_bij qpow_map_bij). apply qpow_map_cancel.
Qed.

Lemma find_qpow_inj: injective find_qpow.
Proof.
  apply bij_inj. apply find_qpow_bij.
Qed.
 
Lemma qpow_map_full_equiv: forall i,
  nat_of_ord i != 0%N ->
  qpow_map_full i = qpow_map i.
Proof.
  move => i. rewrite /qpow_map /qpow_map_full. by case : (nat_of_ord i == 0%N).
Qed. 

Lemma qpow_map_full_inv: forall i,
  nat_of_ord i != 0%N ->
  find_qpow (qpow_map_full i) = i.
Proof.
  move => i Hi. rewrite qpow_map_full_equiv //. by rewrite qpow_map_cancel.
Qed.

End Field.