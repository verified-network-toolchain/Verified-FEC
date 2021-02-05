Require Import VST.floyd.functional_base.
Require Import Poly.
Require Import PolyMod.
(** * Concrete ireducible and primitive polynomials over GF(2) *)

(*note: we include in a different file bc proving primitive takes a long time - there are a lot of
  polynomials to check!*)
(** Concrete irreducible polynomials*)

(*1011*)
Definition p8 := from_list (1 :: 1 :: 0 :: 1 :: nil).

(*10011*)
Definition p16 := from_list (1 :: 1 :: 0 :: 0 :: 1 :: nil).

(*100101*)
Definition p32 := from_list (1 :: 0 :: 1 :: 0 :: 0 :: 1 :: nil).

(*1000011*)
Definition p64 := from_list (1 :: 1 :: 0 :: 0 :: 0 :: 0 :: 1 :: nil).

(*10001001*)
Definition p128:= from_list (1 :: 0 :: 0 :: 1 :: 0 :: 0 :: 0 :: 1 :: nil).

(*100011101*)
Definition p256 := from_list (1 :: 0 :: 1 :: 1 :: 1 :: 0 :: 0 :: 0 :: 1 :: nil).

Lemma p8_irred: irreducible p8.
Proof.
  apply (irreducible_test p8 2).
  - assert (deg p8 = 3). reflexivity. lia.
  - simpl. reflexivity.
Qed.

Lemma p16_irred: irreducible p16.
Proof.
  apply (irreducible_test p16 2).
  - assert (deg p16 = 4) by reflexivity. lia.
  - reflexivity.
Qed.

Lemma p32_irred: irreducible p32.
Proof.
  apply (irreducible_test p32 3).
  - assert (deg p32 = 5) by reflexivity. lia.
  - reflexivity.
Qed.

Lemma p64_irred: irreducible p64.
Proof.
  apply (irreducible_test p64 3).
  - assert (deg p64 = 6) by reflexivity. lia.
  - reflexivity.
Qed.

Lemma p128_irred: irreducible p128.
Proof.
  apply (irreducible_test p128 4).
  - assert (deg p128 = 7) by reflexivity. lia.
  - reflexivity.
Qed.

Lemma p256_irred: irreducible p256.
Proof.
  apply (irreducible_test p256 4).
  - assert (deg p256 = 8) by reflexivity. lia.
  - reflexivity.
Qed.

(** Concrete Primitive Polynomials*)

Ltac prim1 := unfold divides_pmod; compute; exist_eq; try reflexivity.
(* Ltac prim2 := unfold *)

Lemma p8_primitive : primitive p8.
Proof.
  apply test_primitive. assert (deg p8 = 3) by reflexivity.
  split. lia. split. apply p8_irred. split. simpl. prim1.
  compute. reflexivity.
Qed.

Lemma p16_primitive: primitive p16.
Proof.
  apply test_primitive. assert (deg p16 = 4) by reflexivity.
  split. lia. split. apply p16_irred. split. prim1. compute. reflexivity.
Qed.

Lemma p32_primitive: primitive p32.
Proof.
  apply test_primitive. assert (deg p32 = 5) by reflexivity.
  split. lia. split. apply p32_irred. split. prim1. compute. reflexivity.
Qed.

Lemma p64_primitive: primitive p64.
Proof.
  apply test_primitive. assert (deg p64 = 6) by reflexivity.
  split. lia. split. apply p64_irred. split. prim1. compute. reflexivity.
Qed.

(*starts taking a while*)
Lemma p128_primitive: primitive p128.
Proof.
  apply test_primitive. assert (deg p128 = 7) by reflexivity.
  split. lia. split. apply p128_irred. split. prim1. compute. reflexivity.
Qed.

Lemma p256_primitive: primitive p256.
Proof.
  apply test_primitive. assert (deg p256 = 8) by reflexivity.
  split. lia. split. apply p256_irred. split. prim1. compute. reflexivity.
Qed.