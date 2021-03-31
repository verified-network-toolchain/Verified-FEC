From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.poly.
Require Import mathcomp.algebra.polydiv.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import CommonSSR.

(*Definition of field constructed from polynomials modulo an irreducible polynomial*)
Section Field.

Local Open Scope ring_scope.

Variable F : fieldType.

Variable p : {poly F}.
Variable Hirred: irreducible_poly p.
(*Don't want p to be a constant*)
Variable Hnonconst: 1 < size p.

Print Polynomial.

(*The type of polynomials of degree less than p*)
Inductive qpoly : predArgType := Qpoly (qp : {poly F}) of (size qp < size p).

Coercion qp (q: qpoly) : {poly F} := let: Qpoly x _ := q in x.
Definition qsz (q: qpoly) : size q < size p := let: Qpoly _ x := q in x.

Canonical qpoly_subType := [subType for qp].
Definition qpoly_eqMixin := Eval hnf in [eqMixin of qpoly by <:].
Canonical qpoly_eqType := Eval hnf in EqType qpoly qpoly_eqMixin.

Definition qpoly_choiceMixin := [choiceMixin of qpoly by <:].
Canonical qpoly_choiceType := Eval hnf in ChoiceType qpoly qpoly_choiceMixin.
(*These didn't work for some reason but its ok*)
(*
Definition qpoly_countMixin := [countMixin of qpoly by <:].
Canonical qpoly_countType := Eval hnf in CountType qpoly qpoly_countMixin.
Canonical qpoly_subCountType := [subCountType of qpoly].*)

(*First, prove this is a Z Module*)
Lemma q0_bound: size (0 : {poly F}) < size p.
Proof.
  apply irredp_neq0 in Hirred. by rewrite size_poly0 size_poly_gt0 Hirred.
Qed.

Lemma q1_bound : size (1 : {poly F}) < size p.
Proof.
  by rewrite size_poly1.
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

Lemma qpoly_eq: forall (p1 p2: {poly F}) (Hp1: size p1 < size p) (Hp2: size p2 < size p),
  p1 = p2 ->
  Qpoly Hp1 = Qpoly Hp2.
Proof.
  move => p1 p2 Hp1 Hp2 Hp12. subst. f_equal. apply bool_irrelevance.
Qed.

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

(*TODO: do ring axioms, then will take a bit of work to prove field*)