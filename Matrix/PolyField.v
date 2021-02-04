Require Import VST.floyd.functional_base.

From mathcomp Require Import all_ssreflect.

Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import PolyMod.
Require Import PrimitiveFacts.

Import Poly.WPoly.

Section PrimFieldClass.

(*We define a typeclass for a primitive polynomial and some additional properties which will be sufficient
  for it to be the modulus for a finite field. This allows us to bundle together the relevant conditions 
  and make more arguments implicit*)
Class PrimPoly (f: poly) : Type := {
  f_pos : (deg f > 0)%Z;
  f_prim : primitive f;
  f_notx : f <> x}.

Lemma f_irred: forall f `{PrimPoly f}, irreducible f.
Proof.
  intros f Hprim. destruct Hprim. unfold primitive in f_prim0.
  apply f_prim0.
Qed.

Lemma f_nonzero: forall f `{PrimPoly f}, f <> zero.
Proof.
  intros f Hprim. destruct Hprim. intro Hfz.
  assert (Hzpos: (deg zero > 0)%Z) by (rewrite <- Hfz; auto).
  assert (Hzneg : (deg zero < 0)%Z) by (rewrite deg_zero; reflexivity). lia.
Qed.

End PrimFieldClass.

(*Now we define the (mathcomp) field of polynomials modulo an irreducible polynomial*)

Section PolyField.

Import Poly.WPoly.

Variable f: poly.
Variable Hnontriv: (deg f > 0)%Z.
Variable Hired: irreducible f.

(*EqType*)

Definition eq_qpoly (a b: qpoly f) : bool :=
  if (poly_eq_dec (proj1_sig a) (proj1_sig b)) then true else false.

Lemma qpoly_eq_reflect: forall x y, reflect (x = y) (eq_qpoly x y).
Proof.
  move => x y. case Heq: (eq_qpoly x y).
  - move : Heq; rewrite /eq_qpoly. move : x y => [x Hx] [y Hy]. rewrite /=.
    case : (poly_eq_dec x y) =>[Heq H{H}/=|//]. subst. apply ReflectT. by apply exist_ext.
  - move : Heq; rewrite /eq_qpoly. move : x y => [x Hx] [y Hy]. rewrite /=.
    case: (poly_eq_dec x y) => [//|Hneq H{H}]. apply ReflectF. move => Hex. by case: Hex.
Qed.

Lemma poly_eq_axiom: Equality.axiom eq_qpoly.
Proof.
  rewrite /Equality.axiom.
  apply qpoly_eq_reflect.
Qed.

Definition qpoly_eq_mixin := EqMixin poly_eq_axiom.
Canonical qpoly_eqtype := EqType (qpoly f) qpoly_eq_mixin.

(*We need a [ChoiceType] structure. We will use the (more restrictive) finite and countable structures
  to help define this, which gives us these additional structures as well*)

(*FiniteType*)

Definition q0 := @r0 _ Hnontriv.
Definition qlist := (q0 :: map (fun x => proj1_sig x) (all_nonzero_qpolys f Hnontriv)).

(*TODO: move*)
(*Generalized version of lemma in ListMarix - TODO remove from there*)
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

Lemma uniq_qlist: uniq qlist.
Proof.
  rewrite /qlist /=. have Hnotin: ~In q0 [seq sval x0 | x0 <- all_nonzero_qpolys f Hnontriv].
  rewrite in_map_iff. move => [[x Hx] [Hzero Hin]]. move : Hzero; rewrite /q0 /r0 /= => Hz.
  apply Hx. by rewrite Hz.
  have {Hnotin} ->: (q0 \notin [seq sval x0 | x0 <- all_nonzero_qpolys f Hnontriv]).
  case Hin : (q0 \in [seq sval x0 | x0 <- all_nonzero_qpolys f Hnontriv]).
  have: (q0 \in [seq sval x0 | x0 <- all_nonzero_qpolys f Hnontriv]) by []. by rewrite in_mem_In =>{} Hin. by [].
  rewrite uniq_NoDup. apply FinFun.Injective_map_NoDup. move => [x Hx] [y Hy]. rewrite /=. move => Hxy. by
  apply exist_ext. apply all_nonzero_qpolys_NoDups.
Qed.

Lemma qpoly_finite: Finite.axiom qlist.
Proof.
  move => q. rewrite count_uniq_mem. 2: apply uniq_qlist. case Hz : (eq_qpoly q q0).
  - have ->: q = q0 by apply (elimT (qpoly_eq_reflect q q0)). by rewrite in_cons eq_refl.
  - rewrite /qlist in_cons. have->: (q \in [seq sval x0 | x0 <- all_nonzero_qpolys f Hnontriv]).
    rewrite in_mem_In. rewrite in_map_iff.
    have Hnz: q <> q0. move => Heq. subst. have: eq_qpoly q0 q0 by apply (introT (qpoly_eq_reflect _ _)).
    by rewrite Hz. have Hsv : sval q <> zero. move => Hs. apply Hnz. move : Hnz Hz Hs.
    rewrite /q0 /r0. case: q => [q Hq /= Hnonz H{H} Hz]. by apply exist_ext.
    exists (exist _ q Hsv). split. by []. apply all_nonzero_qpolys_in. by rewrite orbT.
Qed.

(*Countable Type*)

Definition qpoly_pickle (q: qpoly f) : nat :=
  find (fun x => x == q) qlist.

Definition qpoly_unpickle (n: nat) : option (qpoly f) :=
  if (n < size qlist)%N then Some (nth q0 qlist n) else None.

Lemma qpoly_pickleK : pcancel qpoly_pickle qpoly_unpickle.
Proof.
  move => x. rewrite /qpoly_unpickle /qpoly_pickle.
  have Hin: has (eq_op^~ x) qlist. have: Finite.axiom qlist by apply qpoly_finite. rewrite /Finite.axiom => /(_ x).
  rewrite has_count. by move ->.
  rewrite -has_find Hin. f_equal. have: nth q0 qlist (find (eq_op^~ x) qlist) == x by apply (nth_find q0 Hin).
  by move => /eqP Nnth.
Qed.

(* Choice Type*)

Definition choice_find (p: pred (qpoly f)) (n: nat) :=
  if p(nth q0 qlist n) then Some (nth q0 qlist n) else None.

Lemma qpoly_choice1: forall (P : pred (qpoly f)) (n : nat) x, choice_find P n = Some x -> P x.
Proof.
  move => P n x. rewrite /choice_find. case Hp: (P (nth q0 qlist n)).
  - move => H; case : H. by move <-.
  - by [].
Qed.

Lemma qpoly_choice2: forall P : pred (qpoly f), (exists x, P x) -> exists n : nat, choice_find P n.
Proof.
  move => P [x Hx]. have Hin: x \in qlist. have: Finite.axiom qlist by apply qpoly_finite. 
  rewrite /Finite.axiom => /(_ x). rewrite count_uniq_mem. by case : (x\in qlist). by apply uniq_qlist.
  exists (index x qlist). rewrite /choice_find. rewrite nth_index =>[|//]. by rewrite Hx.
Qed.

Lemma qpoly_choice3: forall P Q : pred (qpoly f), P =1 Q -> choice_find P =1 choice_find Q.
Proof.
  move => P Q. rewrite /eqfun =>[Hpq x]. rewrite /choice_find.
  by rewrite Hpq.
Qed.

(*All the above packed into their structures*)

Definition qpoly_choicemixin := Choice.Mixin qpoly_choice1 qpoly_choice2 qpoly_choice3.
Canonical qpoly_choicetype := ChoiceType (qpoly f) qpoly_choicemixin.

Definition qpoly_countmixin := PcanCountMixin qpoly_pickleK.
Canonical qpoly_counttype := CountType (qpoly f) qpoly_countmixin.

Definition qpoly_finitemixin := FinMixin qpoly_finite.
Canonical qpoly_finitetype := FinType (qpoly f) qpoly_finitemixin.

(*ZModType*)

(*TODO: some duplication with stuff in PolyMod, may remove that*)

Definition qadd := @r_add _ Hnontriv.

Definition q1 := @r1 _ Hnontriv.

Lemma qpoly_addA : associative qadd.
Proof.
  move => [x Hx] [y Hy] [z Hz]. rewrite /qadd /r_add /=. apply exist_ext. 
  rewrite /poly_add_mod pmod_add_reduce =>[|//]. rewrite -poly_add_assoc.
  rewrite (poly_add_comm ((x +~ y) %~ f)) pmod_add_reduce =>[|//]. by rewrite poly_add_comm.
Qed.

Lemma qpoly_addC: commutative qadd.
Proof.
  move => [x Hx] [y Hy]. rewrite /qadd /r_add /=. apply exist_ext.
  by rewrite /poly_add_mod poly_add_comm.
Qed.

Lemma qpoly_add0q : left_id q0 qadd.
Proof.
  move => [x Hx]. rewrite /qadd /q0 /r_add /r0 /=. apply exist_ext.
  by rewrite /poly_add_mod poly_add_0_l pmod_refl.
Qed.

(*Since our polynomials are over GF(2), they are their own inverse*)
Lemma qpoly_addNq: left_inverse q0 id qadd.
Proof.
  move => [x Hx]. rewrite /qadd /r_add /q0 /r0 /=. apply exist_ext.
  by rewrite /poly_add_mod poly_add_inv pmod_zero.
Qed.

Definition qpoly_zmodmixin := ZmodMixin qpoly_addA qpoly_addC qpoly_add0q qpoly_addNq.
Canonical qpoly_zmodtype := ZmodType _ qpoly_zmodmixin.

(*RingType*)
Definition qmul := @r_mul _ Hnontriv.

Lemma qpoly_mulA : associative qmul.
Proof.
  move => [x Hx] [y Hy] [z Hz]. rewrite /qmul /r_mul /=. apply exist_ext.
  rewrite /poly_mult_mod (poly_mult_comm ((x *~ y) %~ f)) pmod_mult_reduce  =>[|//].
  rewrite pmod_mult_reduce =>[|//]. by rewrite -poly_mult_assoc poly_mult_comm.
Qed.

Lemma qpoly_mulC: commutative qmul.
Proof.
  move => [x Hx] [y Hy]. rewrite /qmul /r_mul /=. apply exist_ext. 
  by rewrite /poly_mult_mod poly_mult_comm.
Qed.

Lemma qpoly_mul1q: left_id q1 qmul.
Proof.
  move => [x Hx]. rewrite /qmul /q1 /r_mul /r1 /=. apply exist_ext. 
  by rewrite /poly_mult_mod poly_mult_1_l pmod_refl.
Qed.

Lemma qpoly_mulD : left_distributive qmul qadd.
Proof.
  move => [x Hx] [y Hy] [z Hz]. rewrite /qadd /qmul /r_add /r_mul /=. apply exist_ext.
  rewrite /poly_mult_mod /poly_add_mod. rewrite -pmod_add_distr =>[|//].
  rewrite poly_mult_comm pmod_mult_reduce =>[|//]. by rewrite poly_mult_comm poly_mult_distr_r.
Qed.

Lemma qpoly_1not0: q1 != q0.
Proof.
  case Heq : (q1 == q0).
  - by move : Heq => /eqP Heq.
  - by [].
Qed. 

Definition qpoly_comringmixin := ComRingMixin qpoly_mulA qpoly_mulC qpoly_mul1q qpoly_mulD qpoly_1not0.
Canonical qpoly_ring := RingType (qpoly f) qpoly_comringmixin.
Canonical qpoly_comring := ComRingType (qpoly f) qpoly_mulC.

(*Unit Ring (ring with computable inverse)*)


Definition qpoly_unit : pred (qpoly f) :=
  fun x => x != q0.

Definition qpoly_inv := @find_inv _ Hnontriv.

Lemma qpoly_mulrV : {in qpoly_unit, right_inverse q1 qpoly_inv qmul}.
Proof.
  move => x Hin. rewrite /qmul /qpoly_inv /q1. apply find_inv_correct. by [].
  move : Hin. rewrite unfold_in /q0 => Hin Heq. by move: Hin; rewrite Heq eq_refl.
Qed.

Lemma qpoly_mulVr : {in qpoly_unit, left_inverse q1 qpoly_inv qmul}.
Proof.
  move => x Hin. by rewrite qpoly_mulC qpoly_mulrV.
Qed. 

Lemma qpoly_unitP : forall x y : (qpoly f), (y * x)%R = 1%R /\ (x * y)%R = 1%R -> qpoly_unit x.
Proof.
  move => x y [Hxy Hyx]. rewrite /qpoly_unit. case Heq : (x == q0) =>[|//]. move : Heq => /eqP Heq.
  subst. by rewrite GRing.Theory.mul0r in Hyx.
Qed. 

Lemma qpoly_inv0id : {in [predC qpoly_unit], qpoly_inv =1 id}.
Proof.
  move => x Hin. have Hnz: ~~ (x != q0) by []. have /eqP {} Hnz: x == q0 by move : Hnz; case: (x == q0).
  subst. by rewrite /qpoly_inv /q0 -find_inv_zero.
Qed.

Definition qpoly_unitringmixin := UnitRingMixin qpoly_mulVr qpoly_mulrV qpoly_unitP qpoly_inv0id.
Canonical qpoly_unitringtype := UnitRingType (qpoly f) qpoly_unitringmixin.

(*Integral Domain*)

Lemma qpoly_mulf_eq0 : forall x y : (qpoly f), (x * y)%R = 0%R -> (x == 0%R) || (y == 0%R).
Proof.
  move => x y Hxy. case Hx : (x == 0%R) =>[//|].
  have {}Hx: x != 0%R by rewrite Hx. have: (x^-1 * (x * y))%R = (x^-1 * 0%R)%R by rewrite Hxy.
  rewrite GRing.Theory.mulrA GRing.Theory.mulr0 GRing.mulVr =>[|//]. rewrite GRing.mul1r. move ->.
  by rewrite eq_refl orbT.
Qed.

(*Need the comUnitRing first*)
Canonical qpoly_comunitring := [comUnitRingType of (qpoly f)].
Canonical qpoly_idomaintype := IdomainType (qpoly f) qpoly_mulf_eq0.

(*Field*)

Lemma qpoly_mulVf : GRing.Field.axiom qpoly_inv.
Proof.
  move => x Hnz. by apply qpoly_mulVr.
Qed.

Lemma qpoly_inv0: qpoly_inv 0%R = 0%R.
Proof.
  apply qpoly_inv0id. rewrite unfold_in /=. case Hin : (0%R \in qpoly_unit).
  move : Hin. by rewrite unfold_in eq_refl. by [].
Qed. 

Definition qpoly_fieldmixin := FieldMixin qpoly_mulVf qpoly_inv0.
Canonical qpoly_fieldType := FieldType (qpoly f) qpoly_fieldmixin.

End PolyField.
