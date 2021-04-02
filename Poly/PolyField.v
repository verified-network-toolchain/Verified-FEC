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
Require Import ListPoly. (*TODO: probably not - put [rem_trail_zero] in CommonSSR*)

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
(*Don't want p to be a constant*)
(*Variable Hnonconst: 1 < size p.*)

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

(*Want to prove that this is finite. We do this by proving a mapping into [bseq (size p)]
  (defined in CommonSSR.v)*)

Definition qpoly_to_bseq (q: qpoly) : bseq F (size p) :=
  exist (fun x => size x < size p) (qp q) (qsz q).

Definition bseq_to_qpoly (b: bseq F (size p)) : option qpoly :=
  insub (Poly b).

Lemma bseq_qpoly_cancel: pcancel (qpoly_to_bseq) (bseq_to_qpoly).
Proof.
  move => x. rewrite /qpoly_to_bseq /bseq_to_qpoly /=.
  rewrite insubT /=. rewrite polyseqK. apply qsz. case : x => [q Hq /= hszq].
  f_equal. apply qpoly_eq. by rewrite polyseqK.
Qed.

Definition qpoly_finMixin := PcanFinMixin bseq_qpoly_cancel.
Canonical qpoly_finType := Eval hnf in FinType qpoly qpoly_finMixin.

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

Lemma qadd_bound: forall (p1 p2: {poly F}),  size ((p1 + p2)%% p) < size p.
Proof.
  move => p1 p2. rewrite ltn_modp. by apply irredp_neq0.
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
  by rewrite !modpD !modp_mod GRing.addrA.
Qed.

Lemma qaddC : commutative qadd.
Proof.
  move => q1 q2. rewrite /qadd /=. apply qpoly_eq. by rewrite GRing.addrC.
Qed.

Lemma qaddFq : left_id q0 qadd.
Proof.
  move => q. rewrite /qadd /q0 /= -{3}(qpoly_qsz q). apply qpoly_eq.
  rewrite GRing.add0r modp_small //. apply qsz. 
Qed.

Lemma qaddqq : left_inverse q0 qopp qadd.
Proof.
  move => q. rewrite /qadd /qopp /q0. apply qpoly_eq.
  by rewrite /= GRing.addrC GRing.subrr mod0p.
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
  by rewrite -modpD modp_mod GRing.mulrC modp_mul GRing.mulrC GRing.mulrDl.
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

(*Unfortunately, the mathcomp [find] function returns the index, not the item*)
Definition find_val {T: Type} (p: pred T) (s: seq T) (d: T) : T :=
  match (filter p s) with
  | nil => d
  | h :: _ => h
  end.

Lemma find_val_none: forall {T: Type} (p: pred T) s d,
  all (fun x => ~~ p x) s ->
  find_val p s d = d.
Proof.
  move => T pr s d. elim : s => [//= | h t /= IH /andP[Hh Ht]].
  rewrite /find_val /=. have->: (pr h = false) by move: Hh; case : (pr h). move: IH; rewrite /find_val.
  by move ->.
Qed.

Lemma find_val_exists: forall {T: eqType} (p: pred T) s d,
  (exists x, (x \in s) && p x) ->
  p (find_val p s d).
Proof.
  move => T pr s d. elim : s => [//= [ Hfalse] // | h t //= IH [x /andP[Hin Hpx]]].
  move: IH; rewrite /find_val /= => IH. move: Hin; rewrite in_cons => /orP[/eqP Hxh | Hxt].
  - subst. by rewrite Hpx.
  - case Hh: (pr h) =>[//|]. apply IH. exists x. by rewrite Hxt Hpx.
Qed.

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

(*Now (TODO: maybe before), we want to find the size of this set. We do this by providing a bijection
  from the set of qpolys to the set of N-tuples. (TODO: maybe change finType to use this too)*)

(*TODO: move*)
Lemma bijective_card: forall {T T': finType} (f: T -> T'),
  bijective f ->
  #|T| = #|T'|.
Proof.
  move => T T' f Hb. have Htt': #|T| <= #|T'|. apply (leq_card f). by apply bij_inj.
  case : Hb => g Hfg Hgf. have Htt'': #|T'| <= #|T|. apply (leq_card g). apply (can_inj Hgf).
  apply /eqP. by rewrite eqn_leq Htt' Htt''.
Qed.

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

(*TODO: maybe move*)
Lemma rem_trail_zero_polyseq: forall (l: seq F),
  polyseq (Poly (rem_trail_zero l)) = (rem_trail_zero l).
Proof.
  move => l. have: polyseq (Poly (Polynomial (rem_trail_zero_wf l))) = rem_trail_zero l by rewrite polyseqK /=.
  by [].
Qed.

(*TODO: move*)
Lemma dropWhileEnd_size: forall {A: eqType} (p: pred A) (l: seq A),
  size (dropWhileEnd p l) <= size l.
Proof.
  move => A pr l. elim : l => [//= | h t /= IH ].
  case : (nilp (dropWhileEnd pr t) && pr h) => [//|/=].
  by rewrite ltnS.
Qed.

Lemma rem_trail_zero_size: forall (l: seq F),
  size (rem_trail_zero l) <= size l.
Proof.
  move => l. apply dropWhileEnd_size.
Qed. 

Lemma tuple_to_poly_size: forall t,
  size (tuple_to_poly t) < size p.
Proof.
  move => t. rewrite /tuple_to_poly. have Ht: size t = ((size p).-1) by apply size_tuple.
  have Hlt: size t < size p. rewrite Ht. apply pred_lt. by rewrite p_gt_0.
  rewrite rem_trail_zero_polyseq. by apply (leq_ltn_trans (rem_trail_zero_size t)).
Qed.

Definition tuple_to_qpoly (t: ((size p).-1).-tuple F) : qpoly := Qpoly (tuple_to_poly_size t).

Lemma tuple_eq: forall {A: Type} (n: nat) (t1 t2: n.-tuple A),
  tval t1 = tval t2 ->
  t1 = t2.
Proof.
  move => A n [l1 Hl1] [l2 Hl2]. rewrite /= => Hl12. subst. f_equal. apply bool_irrelevance.
Qed. 

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

Lemma dropWhileEnd_last: forall {A: eqType} (p: pred A) (l: seq A) (x: A),
  ~~ p (last x l) ->
  dropWhileEnd p l = l.
Proof.
  move => A pr l x Hlast. rewrite (dropWhileEnd_spec pr l x). split. exists nil. split. by rewrite cats0.
  by []. by rewrite Hlast.
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

(*Finally, the result we want. This is a finite field of size |F|^(deg p)*)
Lemma qpoly_size: #|qpoly| = #|F|^((size p).-1).
Proof.
  by rewrite (bijective_card qpoly_to_tuple_bijective) card_tuple.
Qed.

(*We needed this because we want to consider primitive polynomials, and we want to show that for any q!=0,
  there is an a such that x ^ a %% p = q. We define a mapping from 'I_(size p - 1) -> qpoly and show that
  it is injective. We need the above size result to conclude that the mapping is bijective and therefore
  surjective*)

(*Definition of primitive polynomial. Note that size p = 1 + deg p, and I believe the 2nd condition is
  always true, though we don't need to prove it*)
Definition primitive_poly (p: {poly F}) := irreducible_poly p /\ p %| 'X^(#|F|^(size p - 1) - 1) - 1 /\
  (forall n, p %| 'X^n - 1 -> (n == 0%N) || ((#|F|^(size p - 1) - 1) <= n)).

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

Definition qpoly_pow_map (i: 'I_((size p).-1)) : qpoly := qx ^+ i.

 

End Field.