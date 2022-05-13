(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.poly.
Require Import mathcomp.algebra.polydiv.
Require Import mathcomp.algebra.finalg.
Require Import mathcomp.ssreflect.tuple.
Require Import mathcomp.field.finfield.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(* Construction of finite fields via irreducible polynomials *)

Section FieldConstr.

Local Open Scope ring_scope.

(*Some needed results about the Poly constructor - not general-purpose*)
Section MorePoly.

Variable R: ringType.

Lemma Poly_nil (s: seq R):
  (all (eq_op^~0) s) = (polyseq (Poly s) == nil).
Proof.
elim: s => [/=| h t /= IHs].
  by rewrite polyseq0.
rewrite polyseq_cons. 
have->: nilp (Poly t) = (polyseq (Poly t) == [::])
  by apply /nilP; case : (polyseq (Poly t) == [::]) /eqP. 
rewrite -IHs. 
case Allt: (all (eq_op^~ 0) t) =>/=; last by rewrite andbF.
case: (h == 0) /eqP => [ eq_h0 | /eqP neq_h0].
  by rewrite eq_h0 polyseqC eq_refl.
by rewrite polyseqC/= neq_h0.
Qed.

Lemma Poly_split (s: seq R):
  ~~(all (eq_op^~ 0) s) ->
  exists s1, (s == Poly s ++ s1) && (all (eq_op^~ 0) s1).
Proof.
elim: s => [//| h t/= IHs].
case Allt: (all (eq_op^~ 0) t) =>/=.
  move=> /nandP[eq_h0 | //]; exists t.
  rewrite polyseq_cons polyseqC eq_h0. 
  move: Allt; rewrite Poly_nil => /eqP->/=.
  by rewrite eq_refl. 
move=> _. rewrite polyseq_cons. 
have->/=: nilp (Poly t) = false
  by apply /nilP /eqP; rewrite -Poly_nil Allt.
apply negbT, IHs in Allt.
case: Allt => [s1 /andP[/eqP t_eq all_s1]].
exists s1.
by rewrite {1}t_eq all_s1 eq_refl.
Qed.

Lemma Poly_cat (s1 s2 : seq R):
  all (eq_op^~0) s2 ->
  Poly (s1 ++ s2) = Poly s1.
Proof.
elim: s1 => [/= all_s2| h t /= IHs all_s2].
  by apply poly_inj; rewrite polyseq0; apply /eqP; rewrite -Poly_nil.
by move: IHs => /(_ all_s2) ->.
Qed.

End MorePoly.

(* We require that the type is finite so that the resulting field is finite. *)
(* We need an integral domain for [irreducible_poly].                        *)
(* Every finite integral domain is a (finite) field.                         *)
Variable F : finFieldType.

Variable p : {poly F}.
Variable p_irred: irreducible_poly p.

(*A polynomial quotiented by p*)
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

Lemma qpoly_inj: injective qp. Proof. exact: val_inj. Qed.

(* Size of the Finite Field *)

(* We prove the cardinality of this set by giving a mapping from qpolys to    *)
(* tuples of length (size).-1                                                 *)

Definition qpoly_seq (q: qpoly) : seq F :=
  q ++ nseq ((size p).-1 - size q) 0.

Lemma p_gt_0: 0 < size p.
Proof.
have lt_01 : 0 < 1 by [].
apply (ltn_trans lt_01).
by apply p_irred.
Qed.

Lemma leq_predR m n :
  0 < n ->
  (m <= n.-1) = (m < n).
Proof. by case : n => [//|n/= _]; rewrite ltnS. Qed.

Lemma qpoly_seq_size q: size (qpoly_seq q) == (size p).-1.
Proof.
apply /eqP; rewrite /qpoly_seq size_cat size_nseq subnKC //.
case : q => [x Szx /=].
by rewrite leq_predR // p_gt_0. 
Qed.

Definition qpoly_tuple q : ((size p).-1).-tuple F := Tuple (qpoly_seq_size q).

Definition tuple_poly (t: ((size p).-1).-tuple F) : {poly F} := Poly t.

Lemma tuple_poly_size t: 
  size (tuple_poly t) < size p.
Proof.
have szt: size t = ((size p).-1) by apply size_tuple.
have lt_tp: size t < size p by rewrite szt ltn_predL p_gt_0.
by apply (leq_ltn_trans (size_Poly t)).
Qed.

Definition tuple_qpoly (t: ((size p).-1).-tuple F) : qpoly := 
  Qpoly (tuple_poly_size t).

Lemma tuple_qpoly_cancel: cancel tuple_qpoly qpoly_tuple.
Proof. 
move=> [t sz_t]; rewrite /qpoly_tuple /tuple_qpoly/=.
apply val_inj=>/=.
rewrite /tuple_poly/qpoly_seq/=.
move: sz_t => /eqP sz_t.
case Allt: (all (eq_op^~0) t). 
  have nseqt:=Allt; move: Allt.  
  rewrite Poly_nil => /eqP->/=.
  symmetry; rewrite subn0 -sz_t; apply /all_pred1P.
  exact: nseqt.
apply negbT, Poly_split in Allt.
case : Allt => [tl /andP[/eqP t_eq tl_all]]. 
rewrite {3}t_eq; f_equal. 
have <-: size tl = ((size p).-1 - size (Poly t))%N
  by rewrite -sz_t {1}t_eq size_cat -addnBAC // subnn.
by symmetry; apply /all_pred1P.
Qed.

Lemma qpoly_tuple_cancel: cancel qpoly_tuple tuple_qpoly.
Proof. 
move=> [q q_sz]; rewrite /qpoly_tuple /tuple_qpoly/=.
apply val_inj=>/=.
rewrite /tuple_poly /qpoly_seq /=. 
rewrite Poly_cat //; first by apply polyseqK. 
by apply /all_pred1P; rewrite size_nseq.
Qed.

Lemma qpoly_tuple_bij: bijective qpoly_tuple.
Proof.
  apply (Bijective qpoly_tuple_cancel tuple_qpoly_cancel).
Qed.

Definition qpoly_finMixin := CanFinMixin qpoly_tuple_cancel.
Canonical qpoly_finType := Eval hnf in FinType qpoly qpoly_finMixin. 

Lemma qpoly_size: #|qpoly| = (#|F|^((size p).-1))%N.
Proof.
by rewrite (bij_eq_card qpoly_tuple_bij) card_tuple.
Qed.

(* Algebraic Structures*)

(* Z Module *)

Lemma q0_size: size (0 : {poly F}) < size p.
Proof. 
by rewrite size_poly0 p_gt_0.
Qed.

Lemma q1_size : size (1 : {poly F}) < size p.
Proof. 
by rewrite size_poly1 p_irred.
Qed.

Definition q0 : qpoly := Qpoly q0_size.
Definition q1 : qpoly := Qpoly q1_size.

Lemma qadd_size (q1 q2: qpoly) : size (val q1 + val q2) < size p.
Proof.
apply (leq_ltn_trans (size_add q1 q2)).
rewrite gtn_max. 
by apply /andP; split; apply qsz.
Qed.

Definition qadd (q1 q2: qpoly) : qpoly := Qpoly (qadd_size q1 q2).

Lemma qopp_size (q: qpoly) : size (-(val q)) < size p.
Proof. 
by rewrite size_opp; apply qsz.
Qed.

Definition qopp (q: qpoly) := Qpoly (qopp_size q).

Lemma qaddA : associative qadd.
Proof.
move=> q1 q2 q3; rewrite /qadd; apply qpoly_inj=>/=.
by rewrite GRing.addrA. 
Qed.

Lemma qaddC : commutative qadd.
Proof. 
move=> q1 q2; rewrite /qadd; apply qpoly_inj=>/=. 
by rewrite GRing.addrC.
Qed.

Lemma qaddFq : left_id q0 qadd.
Proof. 
move=> q; rewrite /qadd /q0; apply qpoly_inj=>/=.
by rewrite GRing.add0r.
Qed.

Lemma qaddqq : left_inverse q0 qopp qadd.
Proof. 
move=> q; rewrite /qadd /qopp /q0; apply qpoly_inj=>/=.
by rewrite GRing.addrC GRing.subrr.
Qed.

Definition qpoly_zmodMixin := ZmodMixin qaddA qaddC qaddFq qaddqq.
Canonical qpoly_zmodType := ZmodType qpoly qpoly_zmodMixin.

(* Ring *)

Lemma qmul_size (p1 p2: {poly F}) : size ((p1 * p2) %% p) < size p.
Proof. 
by rewrite ltn_modp; apply irredp_neq0.
Qed.

Definition qmul (q1 q2 : qpoly) : qpoly := Qpoly (qmul_size q1 q2).

Lemma qpoly_mulA : associative qmul.
Proof. 
move=> q1 q2 q3; rewrite /qmul; apply qpoly_inj=>/=.
by rewrite (GRing.mulrC ((qp q1 * qp q2) %% p)) !modp_mul
  (GRing.mulrC _ (qp q1 * qp q2)) GRing.mulrA.
Qed.

Lemma qpoly_mulC: commutative qmul.
Proof.
move=> q1 q2; rewrite /qmul; apply qpoly_inj=>/=.
by rewrite GRing.mulrC.
Qed.

Lemma qpoly_mul1q: left_id q1 qmul.
Proof.
move=> q. rewrite /qmul /q1; apply qpoly_inj=>/=. 
by rewrite GRing.mul1r modp_small //; apply qsz.
Qed.

Lemma qpoly_mulD : left_distributive qmul qadd.
Proof. 
move=>q1 q2 q3; rewrite /qmul /qadd; apply qpoly_inj=>/=.
by rewrite -modpD GRing.mulrDl. 
Qed.

Lemma qpoly_1not0: q1 != q0.
Proof. 
case: (q1 == q0) /eqP => //.
rewrite /q0 /q1 /= => [[eq_1_0]].
have neq_1_0:=(GRing.oner_neq0 (poly_ringType F)).
move: neq_1_0.
by rewrite eq_1_0 eq_refl.
Qed. 

Definition qpoly_comRingMixin := ComRingMixin 
  qpoly_mulA qpoly_mulC qpoly_mul1q qpoly_mulD qpoly_1not0.
Canonical qpoly_ringType := RingType qpoly qpoly_comRingMixin.
Canonical qpoly_comRingType := ComRingType qpoly qpoly_mulC.

(* Now we want to show that inverses exist and are computable. *)
(* We do this in several steps                                 *)
Definition prime_poly (p: {poly F}) : Prop :=
  forall (q r : {poly F}), p %| (q * r) -> (p %| q) || (p %| r).

Lemma irred_is_prime (r : {poly F}):
  irreducible_poly r -> prime_poly r.
Proof.
move=> r_irred s t r_div_st.
have [[u v]/= bez] := (Bezoutp r s).
case r_div_s: (r %| s) =>//=.
have rs_coprime: size (gcdp r s) == 1%N; last by 
  rewrite -(Gauss_dvdpr _ rs_coprime). 
case gcd_sz: (size (gcdp r s) == 1%N) => //.
have gcd_div := (dvdp_gcdl r s). 
apply r_irred in gcd_div; last by apply negbT.
move: gcd_div.
by rewrite /eqp dvdp_gcd r_div_s !andbF.
Qed.

Lemma qpoly_zero (q: qpoly) : (q == 0) = (qp q %% p == 0).
Proof.
case: q => [q q_sz]/=. 
have->: 0 = q0 by [].
by rewrite /q0 modp_small.
Qed.

(* The following actually shows that any finite integral domain is a field *)
Lemma qpoly_mulf_eq0 (q1 q2: qpoly) : (q1 * q2) = 0 -> (q1 == 0) || (q2 == 0).
Proof.
have->:(q1 * q2) = qmul q1 q2 by [].
have->:0 = q0 by [].
rewrite /qmul /= => [[/ modp_eq0P p_div_q12]].
rewrite !qpoly_zero.
by apply irred_is_prime.
Qed. 

Lemma qpoly_cancel (q1 q2 q3: qpoly): q1 != 0 -> q1 * q2 = q1 * q3 -> q2 = q3.
Proof.
move=> q1_neq0 q12_13.
have q1_sub_q23: q1 * (q2 - q3) = 0 by rewrite GRing.mulrBr q12_13 GRing.subrr.
apply qpoly_mulf_eq0 in q1_sub_q23.
move: q1_sub_q23 => /orP[ /eqP q1_eq0 | /eqP eq_q23].
  by move: q1_neq0; rewrite q1_eq0 eq_refl.
by apply GRing.subr0_eq.
Qed.

(* To show that inverses exist, we define the map f_q(x) = q * x and we show *)
(* that this is injective (and thus bijective since the set is finite)       *)
(* if q != 0 *)
Definition qmul_map (q: qpoly) := qmul q.

Lemma qmul_map_inj (q: qpoly) : 
  q != 0 ->
  injective (qmul_map q).
Proof.
move=> q_neq_0 q1 q2.
by apply qpoly_cancel.
Qed.

Lemma mul_map_bij (q: qpoly): 
  q != 0 ->
  bijective (qmul_map q).
Proof.
move=> q_neq_0.
by apply injF_bij, qmul_map_inj.
Qed.

Lemma qpoly_inv_exist (q: qpoly):
  q != 0 ->
  exists (inv: qpoly), inv * q = 1.
Proof.
move=> q_neq_0. apply mul_map_bij in q_neq_0.
case : q_neq_0 => g can1 can2.
exists (g 1). 
move: can2 => /( _ 1).
by rewrite GRing.mulrC.
Qed.

(* A (slow) computable inverse function from the above *)
Definition qinv (q: qpoly) :=
  nth q0 (enum qpoly) (find (fun x => x * q == 1) (enum qpoly)).

Lemma qinv_correct (q: qpoly):
  q != 0 ->
  (qinv q) * q = 1.
Proof.
move=>q_neq_0.  
apply /eqP; rewrite /qinv.
have has_inv: has (fun x => x * q == 1) (enum qpoly); 
  last by apply (nth_find q0) in has_inv.
apply /hasP.
apply qpoly_inv_exist in q_neq_0.
case: q_neq_0 => [inv inv_correct].
exists inv; last by apply /eqP. 
have inv_count: count_mem inv (enum qpoly) = 1%N 
  by rewrite enumT; apply enumP.
apply /count_memPn.
by rewrite inv_count.
Qed.

Lemma qinv_zero: qinv 0 = 0.
Proof.
have not_has: ~~ has (fun x => x * 0 == 1) (enum qpoly).
  apply /hasP. 
  by move=>[r _ ]; rewrite GRing.mulr0 eq_sym GRing.oner_eq0.
by rewrite /qinv hasNfind // nth_default.
Qed.

(* The rest of the algebraic structures: *)

(* ComUnitRing *)

Definition qunit : pred qpoly :=
  fun x => x != q0.

Lemma qpoly_mulVr : {in qunit, left_inverse q1 qinv qmul}.
Proof.
move=> q q_in.
by apply qinv_correct.
Qed.

Lemma qpoly_mulrV : {in qunit, right_inverse q1 qinv qmul}.
Proof.
move=>q q_in.
by rewrite qpoly_mulC; apply qpoly_mulVr.
Qed. 

Lemma qpoly_unitP (q1 q2: qpoly): (q2 * q1) = 1 /\ (q1 * q2) = 1 -> qunit q1.
Proof.
move=> [q21_1 q12_1]. 
rewrite /qunit; apply /eqP => q1_eq_0.
move: q12_1; rewrite q1_eq_0.
by rewrite GRing.mul0r => /eqP; rewrite eq_sym GRing.oner_eq0.
Qed.

Lemma qpoly_inv0id : {in [predC qunit], qinv =1 id}.
Proof.
move=>q q_unit.
have: ~~ (q != 0) by []. 
rewrite negbK => /eqP->.
by rewrite qinv_zero.
Qed.

Definition qpoly_unitringmixin := 
  UnitRingMixin qpoly_mulVr qpoly_mulrV qpoly_unitP qpoly_inv0id.
Canonical qpoly_unitringtype := UnitRingType qpoly qpoly_unitringmixin.
Canonical qpoly_comunitring := [comUnitRingType of qpoly].

(*Integral Domain *)

Canonical qpoly_idomaintype := IdomainType qpoly qpoly_mulf_eq0.

(* Field *)

Lemma qpoly_mulVf : GRing.Field.axiom qinv.
Proof.
move=> q q_neq_0.
by apply qpoly_mulVr.
Qed.

Lemma qpoly_inv0: qinv 0%R = 0%R.
Proof.
exact: qinv_zero.
Qed.

Definition qpoly_fieldmixin := FieldMixin qpoly_mulVf qpoly_inv0.
Canonical qpoly_fieldType := FieldType qpoly qpoly_fieldmixin.
Canonical qpoly_finFieldType := Eval hnf in [finFieldType of qpoly].

(* Fields over primitive polynomials *)

Section Primitive.

Definition primitive_poly (p: {poly F}) : Prop := 
  irreducible_poly p /\ p %| 'X^((#|F|^((size p).-1)).-1) - 1 /\
  (forall n, p %| 'X^n - 1 -> (n == 0%N) || (((#|F|^((size p).-1)).-1) <= n)).

Variable p_prim: primitive_poly p.

(* We want to prove that discrete logs exist for all nonzero elements.   *)
(* We do not consider the trivial case where p = cx for constant c.      *)
(* This case is not very interesting, since F[X]/(x) is isomorphic to F. *)

Variable p_notx: 2 < size p.

Lemma qx_size: size (polyX F) < size p.
Proof.
by rewrite size_polyX.
Qed.

(* The primitive element x *)
Definition qx : qpoly := Qpoly qx_size.

Lemma qx_exp (n: nat): qp (qx ^+ n) = ('X^n) %% p.
Proof.
elim: n => [/= | n /= IHn]. 
  by rewrite GRing.expr0 modp_small // size_poly1; apply p_irred.
rewrite !GRing.exprSr.
have->: qx ^+ n * qx = qmul (qx ^+ n) qx by [].
by rewrite /qmul/= IHn GRing.mulrC modp_mul GRing.mulrC.
Qed.

(* To show that discrete logs exist, we use the following map and show that is *)
(* is bijective.                                                               *)

Section DlogEx.

Lemma qx_neq0: qx != 0.
Proof.
have->: 0 = q0 by [].
rewrite /qx/q0/=.
case: (Qpoly qx_size == Qpoly q0_size) /eqP => // [[/eqP eq_x0]].
by rewrite polyX_eq0 in eq_x0.
Qed.

Lemma qxn_neq0 (n: nat): qx ^+ n != 0.
Proof.
by apply GRing.expf_neq0, qx_neq0.
Qed.

Definition dlog_ord := 'I_((#|F|^((size p).-1)).-1).

(*Logs only exist for nonzero (or unit) qpolys*)
Inductive qpolyNZ : predArgType := Qnz (qq: qpoly) of (qunit qq).
Coercion qq (q: qpolyNZ) : qpoly := let: Qnz x _ := q in x.
Definition qun (q: qpolyNZ) : qunit q := let: Qnz _ x := q in x.

Canonical qpolyNZ_subType := [subType for qq].

Definition qpolyNZ_eqMixin := Eval hnf in [eqMixin of qpolyNZ by <:].
Canonical qpolyNZ_eqType := Eval hnf in EqType qpolyNZ qpolyNZ_eqMixin.
Definition qpolyNZ_choiceMixin := [choiceMixin of qpolyNZ by <:].
Canonical qpolyNZ_choiceType := Eval hnf in ChoiceType qpolyNZ qpolyNZ_choiceMixin.
Definition qpolyNZ_countMixin := [countMixin of qpolyNZ by <:].
Canonical qpolyNZ_countType := Eval hnf in CountType qpolyNZ qpolyNZ_countMixin.
Canonical qpolyNZ_subCountType := [subCountType of qpolyNZ].

Definition qpolyNZ_finMixin := Eval hnf in [finMixin of qpolyNZ by <:].
Canonical qpolyNZ_finType := Eval hnf in FinType qpolyNZ qpolyNZ_finMixin.
Canonical subFinType := [subFinType of qpolyNZ].

Lemma qpolyNZ_card: #|qpolyNZ| = #|qpoly|.-1.
Proof.
have uniq_sz:=(card_finField_unit qpoly_finFieldType).
move: uniq_sz; rewrite cardsT/= => <-.
by rewrite !card_sub.
Qed.

Lemma qx_unit : qunit qx.
Proof.
by rewrite /qunit qx_neq0.
Qed.

Lemma qpow_unit (n: nat) : qunit (qx ^+ n).
Proof.
by rewrite /qunit qxn_neq0.
Qed.

Definition qpow_map (i: dlog_ord) : qpolyNZ :=
  Qnz (qpow_unit i).

(* We need to know that p does not divide x^n for any n *)
Lemma irred_dvdn_Xn (r: {poly F}) (n: nat):
  irreducible_poly r ->
  2 < size r ->
  ~~ (r %| 'X^n).
Proof.
move=> r_irred r_size.
elim: n => [| n /= IHn].
  rewrite GRing.expr0 dvdp1.
  by apply /eqP => r_eq_1; rewrite r_eq_1 in r_size.
rewrite GRing.exprS.
case r_div: (r %| 'X * 'X^n) => //.
apply (irred_is_prime r_irred) in r_div.
move: r_div => /orP[r_divx | r_divxn]; last by rewrite r_divxn in IHn.
apply dvdp_leq in r_divx; last by rewrite polyX_eq0.
by move: r_divx; rewrite size_polyX leqNgt r_size.
Qed.

(* A weaker lemma than [modpD] *)
Lemma modpD_wk (d q r : {poly F}): 
  d != 0 -> (q + r) %% d = (q %% d + r %% d) %% d.
Proof.
move=> d_neq0; rewrite modpD.
by rewrite (@modp_small _ (_ + _)) // -modpD ltn_modp.
Qed.

Lemma qpow_map_bij: bijective qpow_map.
Proof.
apply inj_card_bij; last by rewrite qpolyNZ_card qpoly_size card_ord leqnn.
move=> n1 n2; rewrite /qpow_map/= => [[]].
wlog: n1 n2 / (n1 <= n2).
  move=> all_eq.
  case: (orP (leq_total n1 n2)) => [n1_leqn2 | n2_leqn1].
    by apply all_eq.
  by move=> qx_n12; symmetry; apply all_eq.
move=> n1_leqn2 qx_n12.
have: (qx ^+ n2 - qx ^+ n1 = 0) by rewrite qx_n12 GRing.subrr.
rewrite -(subnKC n1_leqn2) GRing.exprD.
rewrite -{2}(GRing.mulr1 (qx ^+ n1)) -GRing.mulrBr.
move=> /eqP; rewrite GRing.mulf_eq0 => /orP[/eqP xn_eq0|].
  by have /eqP qn1_x := (negbTE (qxn_neq0 n1)).
rewrite qpoly_zero/= qx_exp GRing.addrC modpD_wk; last by apply irredp_neq0.
rewrite modp_mod GRing.addrC -modpD modp_mod => n21_div_p.
apply p_prim in n21_div_p.
move: n21_div_p => /orP[| n12_big].
  rewrite subn_eq0 => n2_leqn1; apply ord_inj; apply /eqP; rewrite eqn_leq.
  by rewrite n1_leqn2 n2_leqn1.
have n2_bound: n2 < (#|F| ^ (size p).-1).-1 by [].
have n12_bound: n2 - n1 <= n2 by rewrite leq_subr.
have lt_contra:= (leq_ltn_trans (leq_trans n12_big n12_bound) n2_bound).
by rewrite ltnn in lt_contra.
Qed.

(* The inverse map (discrete log)*)

Lemma field_gt0: 
  0 < (#|F|^((size p).-1)).-1.
Proof.
rewrite -qpoly_size -qpolyNZ_card; apply /card_gt0P.
by exists (Qnz qx_unit).
Qed.

Definition dlog_map (q : qpolyNZ) : dlog_ord :=
  nth (Ordinal field_gt0) (enum dlog_ord)
    (find (fun i => (qx ^+ (nat_of_ord i) == q)) (enum dlog_ord)).

Lemma dlog_map_exist (q: qpolyNZ):
  exists (i: dlog_ord), (qx ^+ i == q).
Proof.
case: (qpow_map_bij) => g canqg cangq.
exists (g q).
move: cangq => /(_ q)/=; rewrite /qpow_map => q_eq.
apply (f_equal val) in q_eq. 
by move: q_eq =>/=->; rewrite eq_refl.
Qed. 

Lemma dlog_map_correct (q: qpolyNZ):
  (qx ^+ (dlog_map q) = q).
Proof.
rewrite /dlog_map.
have has_dlog: has 
  (fun i =>(qx ^+ (nat_of_ord i) == q)) 
  (enum dlog_ord);
  last by apply /eqP; apply (nth_find (Ordinal field_gt0)) in has_dlog.
apply /hasP.
have [n n_log]:=(dlog_map_exist q).
exists n => //.
have n_count: count_mem n (enum dlog_ord) = 1%N
  by rewrite enumT; apply enumP.
apply /count_memPn.
by rewrite n_count.
Qed.

Lemma dlog_map_can: cancel dlog_map qpow_map.
Proof.
move=> q; rewrite /qpow_map; apply val_inj=>/=.
by rewrite dlog_map_correct.
Qed.

Lemma qpow_map_can: cancel qpow_map dlog_map.
Proof.
rewrite -bij_can_sym.
  exact: dlog_map_can.
exact: qpow_map_bij.
Qed.

Lemma dlog_map_bij: bijective dlog_map.
Proof.
exact: (bij_can_bij qpow_map_bij qpow_map_can).
Qed.

Lemma dlog_map_inj: injective dlog_map.
Proof.
exact: (bij_inj dlog_map_bij).
Qed.

End DlogEx.

(* The full discrete log function, with dlog(0) = 0 *)

Definition dlog (q: qpoly) : dlog_ord :=
(match (qunit q) as u return (qunit q = u -> dlog_ord) with
| true => fun q_unit => dlog_map (Qnz q_unit)
| false => fun _ => (Ordinal field_gt0)
end) erefl.

Lemma exp_dlog (q: qpoly):
  q != 0 ->
  qx ^+ (dlog q) = q.
Proof.
move=> q_neq0.
have q_unit: qunit q by [].
rewrite /dlog; move: erefl.
case: {2 3}(qunit q); last by rewrite q_unit.
by move=> q_unit'/=; rewrite dlog_map_correct.
Qed.

Lemma dlog0: nat_of_ord (dlog 0) = 0%N.
Proof.
rewrite /dlog; move: erefl.
have unit_zero: qunit 0 = false by rewrite /qunit eq_refl.
case: {2 3}(qunit 0) => //.
move=> zero_unit.
have: qunit 0 = true by [].
by rewrite unit_zero.
Qed.

Lemma dlog_exp (i: dlog_ord):
  dlog(qx ^+ i) = i.
Proof.
have->:qx ^+ i = qpow_map i by [].
have->: dlog (qpow_map i) = dlog_map (qpow_map i); 
  last by rewrite qpow_map_can.
rewrite /dlog; move: erefl.
case: {2 3}(qunit (qpow_map i)) => //.
move=> qpow_nunit.
have: qunit (qpow_map i) = true by apply qun.
by rewrite {1}qpow_nunit.
Qed.

(* From definition of primitive poly *)
Lemma qx_field_sz1: qx ^+ (#|F| ^ (size p).-1).-1 = 1.
Proof.
apply qpoly_inj =>/=; rewrite qx_exp.
case p_prim => [_ [p_div _]].
move: p_div.
rewrite /dvdp modpD modNp (@modp_small _ 1); 
  last by rewrite size_poly1 (ltn_trans _ p_notx).
by rewrite GRing.subr_eq0 => /eqP.
Qed.

Lemma qpoly_exp_modn (m n: nat) :
  m = n %[mod (#|F| ^ (size p).-1).-1] ->
  qx ^+ m = qx ^+ n.
Proof.
move=> mn_eqmod.
rewrite (divn_eq m (#|F| ^ (size p).-1).-1) 
  (divn_eq n (#|F| ^ (size p).-1).-1).
rewrite !GRing.exprD !(mulnC _ ((#|F| ^ (size p).-1).-1)).
rewrite !GRing.exprM !qx_field_sz1 !GRing.expr1n !GRing.mul1r.
by rewrite mn_eqmod.
Qed.

End Primitive.

End FieldConstr.