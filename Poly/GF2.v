Require Import VST.floyd.functional_base.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.setoid_ring.Field_theory.
(** The field GF(2), represented as bits *)

Inductive bit :=
  | Zero
  | One.

Notation "0" := Zero.
Notation "1" := One.

Ltac solve_bit :=
  repeat(match goal with
  | [x : bit |- _ ] => destruct x; try reflexivity
  end).

Instance bit_default : Inhabitant bit.
apply Zero.
Defined.

Definition bit_add (b1 b2 : bit) :=
  match (b1, b2) with
  | (1, 1) => 0
  | (0, 0) => 0
  | (_, _) => 1
  end.

Lemma bit_add_comm: forall b1 b2,
  bit_add b1 b2 = bit_add b2 b1.
Proof.
  intros. solve_bit.
Qed.

Lemma bit_add_assoc : forall b1 b2 b3,
  bit_add (bit_add b1 b2) b3 = bit_add b1 (bit_add b2 b3).
Proof.
  intros; solve_bit.
Qed.

Lemma bit_add_0_l: forall b,
  bit_add 0 b = b.
Proof.
  intros; solve_bit. 
Qed.

Lemma bit_add_0_r: forall b,
  bit_add b 0 = b.
Proof.
  intros; solve_bit.
Qed.

Definition eq_bit (b1 b2 : bit) :=
  match (b1, b2) with
  | (1, 1) => true
  | (0, 0) => true
  | (_, _) => false
  end.

Lemma eq_bit_eq: forall b1 b2,
  eq_bit b1 b2 = true <-> b1 = b2.
Proof.
  intros; split; intros; solve_bit; inversion H.
Qed.

Definition bit_mult (b1 b2 : bit) : bit :=
  match b1, b2 with
  | 1, 1 => 1
  | _, _ => 0
  end.

Lemma bit_mult_comm: forall b1 b2,
  bit_mult b1 b2 = bit_mult b2 b1.
Proof.
  intros; solve_bit. 
Qed.

Lemma bit_mult_assoc: forall b1 b2 b3,
  bit_mult (bit_mult b1 b2) b3 = bit_mult b1 (bit_mult b2 b3).
Proof.
  intros; solve_bit. 
Qed.

Lemma bit_mult_0_l: forall b,
  bit_mult 0 b = 0.
Proof.
  intros; solve_bit. 
Qed.

Lemma bit_mult_0_r: forall b,
  bit_mult b 0 = 0.
Proof.
  intros; solve_bit. 
Qed.

Lemma bit_mult_1_l:
  forall b,
  bit_mult 1 b = b.
Proof.
  intros; solve_bit.
Qed.

Lemma bit_mult_1_r:
  forall b,
  bit_mult b 1 = b.
Proof.
  intros; solve_bit. 
Qed.

Lemma bit_distr: forall b1 b2 b3,
  bit_mult (bit_add b1 b2) b3  = bit_add (bit_mult b1 b3) (bit_mult b2 b3).
Proof.
  intros; solve_bit. 
Qed.

Definition bit_ring: @ring_theory bit 0 1 bit_add bit_mult bit_add id eq.
Proof.
apply mk_rt.
- apply bit_add_0_l.
- apply bit_add_comm.
- intros; symmetry; apply bit_add_assoc.
- apply bit_mult_1_l.
- apply bit_mult_comm.
- intros; symmetry; apply bit_mult_assoc.
- apply bit_distr.
- reflexivity.
- intros. solve_bit.
Defined.

Definition bit_field: @field_theory bit 0 1 bit_add bit_mult bit_add id bit_mult id eq.
Proof.
apply mk_field.
- apply bit_ring.
- intro. inversion H.
- intros. solve_bit.
- intros. solve_bit. contradiction.
Defined.

Lemma bit_eq_dec: forall (b1 b2 : bit),
  {b1 = b2} + {b1 <> b2}.
Proof.
  intros. destruct (eq_bit b1 b2) eqn : E.
  - rewrite eq_bit_eq in E. left. assumption.
  - right. intro. subst. destruct b2; inversion E.
Qed.
