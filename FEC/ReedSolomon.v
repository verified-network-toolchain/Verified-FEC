From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section RS.

Variable F : fieldType.

Local Open Scope ring_scope.


(*The encoder takes the first h * k portion of the weight matrix and multiplies it by a k * c matrix *)
Definition encoder (h k c max_h max_n : nat) (Hh: h <= max_h) (Hk: k <= max_n) 
  (weights : 'M[F]_(max_h, max_n)) (input : 'M[F]_(k, c)) :=
    (mxsub (fun (x : 'I_h) => widen_ord Hh x) (fun (x : 'I_k) => widen_ord Hk x) weights) *m input.

End RS.