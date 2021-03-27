From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(*Field of booleans*)

Definition bool_zmodmixin := ZmodMixin addbA addbC addFb addbb.
Canonical bool_zmodtype := ZmodType _ bool_zmodmixin.

Lemma t_not_f: true != false.
Proof.
  by [].
Qed.

Definition bool_comringmixin := ComRingMixin andbA andbC andTb andb_addl t_not_f.
Canonical bool_ring := RingType bool bool_comringmixin.
Canonical bool_comring := ComRingType bool andbC.

Definition bool_unit : pred bool := id.
Definition bool_inv : bool -> bool := id.

Lemma bool_andbV : {in bool_unit, right_inverse true bool_inv andb}.
Proof.
  move => x. by case: x.
Qed. 

Lemma bool_andVb: {in bool_unit, left_inverse true bool_inv andb}.
Proof.
  move => x. by case : x.
Qed.
 
Lemma bool_unitP: forall x y : bool, (y * x)%R = 1%R /\ (x * y)%R = 1%R -> bool_unit x.
Proof.
  move => x y. case : x; case : y; rewrite //= // => [[H01 //  H01' //]].
Qed.

Lemma bool_inv0id: {in [predC bool_unit], bool_inv =1 id}.
Proof.
  by [].
Qed.

Definition bool_unitringmixin := UnitRingMixin bool_andVb bool_andbV bool_unitP bool_inv0id.
Canonical bool_unitringtype := UnitRingType bool bool_unitringmixin.

Lemma bool_mulf_eq0:  forall x y : bool, (x * y)%R = 0%R -> (x == 0%R) || (y == 0%R).
Proof.
  move => x y. by case : x; case : y.
Qed.

Canonical bool_comunitring := [comUnitRingType of bool].
Canonical bool_idomaintype := IdomainType bool bool_mulf_eq0.

Lemma bool_fieldMixin : GRing.Field.mixin_of bool_comunitring.
Proof.
  move => x. by case : x.
Qed.

Canonical bool_fieldType := FieldType bool bool_fieldMixin.