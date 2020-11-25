Require Import Coq.Lists.List.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.Arith.PeanoNat.
Require Import VST.floyd.functional_base.

Lemma lt_dec: forall (x y : nat),
  { (x < y)%nat} + {~(x < y) %nat}.
Proof.
intros.
eapply reflect_dec. apply Nat.ltb_spec0.
Qed.

(*pairwise operations over lists *)
Fixpoint combineWith {X Y Z: Type} (l1 : list X) (l2: list Y) (f: X -> Y -> Z) : list Z :=
  match (l1, l2) with
  | (h1 :: t1, h2 :: t2) => f h1 h2 :: combineWith t1 t2 f
  | (_, _) => nil
  end.

Lemma combineWithLength: forall {X Y Z} l1 l2 (f : X -> Y -> Z),
  Zlength l1 = Zlength l2 ->
  Zlength (combineWith l1 l2 f) = Zlength l1.
Proof.
  intros X Y Z l1. induction l1; intros.
  - list_solve.
  - rewrite Zlength_cons in H. destruct l2. list_solve. rewrite Zlength_cons in H.
    apply Z.succ_inj in H. simpl. rewrite Zlength_cons. rewrite IHl1. list_solve. assumption.
Qed.

Lemma combineWithZnth: forall {X Y Z} `{Inhabitant X} `{Inhabitant Y} `{Inhabitant Z} l1 l2 (f: X -> Y -> Z) z,
  Zlength l1 = Zlength l2 ->
  0 <= z < Zlength l1 ->
  Znth z (combineWith l1 l2 f) = f (Znth z l1) (Znth z l2).
Proof.
  intros X Y Z I1 I2 I3 l1. induction l1; intros.
  - list_solve.
  - destruct l2. list_solve. assert (Zlength l1 = Zlength l2) by list_solve. clear H.
    assert (z = 0 \/ 0 < z) by lia. destruct H.
    + subst. simpl. repeat (rewrite Znth_0_cons). reflexivity.
    + simpl. repeat (rewrite Znth_pos_cons). apply IHl1. assumption. rewrite Zlength_cons in H0. all: lia.
Qed.


Module Type RingMod.

Reserved Notation "x == y" (at level 70, no associativity).

Parameter A : Type.
Parameter plus : A -> A -> A.
Parameter mult: A -> A -> A.
Parameter sub: A -> A -> A.
Parameter opp: A -> A.
Parameter zero: A.
Parameter one: A.
Infix "==" := eq.
Infix "*" := mult.
Infix "+" := plus.
Infix "-" := sub.
Notation "0" := zero.
Notation "1" := one.
Notation "- x" := (opp x).

Axiom Rth: ring_theory zero one plus mult sub opp eq.

End RingMod.

Module Type Matrix(A: RingMod).

Definition A:= A.A.

Instance default : `{Inhabitant A}.
apply A.zero.
Defined.


(*row, columns *)
Parameter matrix : nat -> nat -> Type.

(*construct matrix from function *)
Parameter mk_matrix: forall m n: nat, (nat -> nat -> A) -> matrix m n.

(*get the (i,j)th entry*)
Parameter get: forall {m n : nat},  (matrix m n) -> nat -> nat ->  A.

(*matrix equivalence*)
Axiom matrix_equiv: forall {m n} (m1 m2: matrix m n),
  m1 = m2 <-> forall i j, (i<m)%nat -> (j<n)%nat -> @get m n m1 i j = @get m n m2 i j.

(*specification for mk_matrix - we dont care about matrices where 1 dimension is 0*)
Axiom mk_matrix_spec: forall m n f i j,
  (0<m)%nat ->
  (0<n)%nat ->
  (i< m)%nat ->
  (j< n)%nat ->
  get (mk_matrix m n f) i j = f i j.
(*

Parameter ith_row: forall {m n :nat}, (matrix m n) -> nat -> list A.

Parameter ith_col: forall {m n:nat}, (matrix m n) -> nat -> list A.

Axiom ith_row_spec: forall {m n} (mx: matrix m n) (i : nat),
  (i < m)%nat ->
  ith_row mx i = prop_list_nat (fun j => get mx i j) n.

Axiom ith_row_length: forall {m n} (mx: matrix m n) i,
  Zlength (ith_row mx i) = Z.of_nat n.




(*specification of ith_row and ith_col *)
Axiom ith_row_spec: forall {m n} (mx: matrix m n) i,
  ith_row mx
  (i < m)%nat ->
  (j < n)%nat ->
 get mx i j = Znth (Z.of_nat j) (ith_row mx i).



Axiom ith_col_spec: forall {m n} (mx: matrix m n) i j,
  (i < m)%nat ->
  (j < n)%nat ->
 get mx i j = Znth (Z.of_nat i) (ith_col mx j).

Axiom ith_col_length: forall {m n} (mx: matrix m n) i,
  Zlength (ith_col mx i) = Z.of_nat m.
*)


(*multiply the ith row by a scalar*)
Parameter scalar_mul_row: forall {m n : nat}, (matrix m n) -> nat -> A -> (matrix m n).
(*specification of scalar mult*)
Axiom scalar_mul_row_spec: forall {m n} (mx: matrix m n) i j k c,
  (i < m)%nat ->
  (j < n)%nat ->
  (k < m)%nat ->
  get (scalar_mul_row mx k c) i j =
    if (Nat.eq_dec i k) then  A.mult c (get mx i j) else get mx i j.

(*exchange rows i and j*)
Parameter swap_rows: forall {m n: nat}, (matrix m n) -> nat -> nat -> (matrix m n).

(*exchange rows spec *)
Axiom swap_rows_spec: forall {m n} (mx: matrix m n) i j r1 r2,
  (i < m)%nat ->
  (j < n)%nat ->
  (r1 < m)%nat ->
  (r2 < m)%nat ->
  get (swap_rows mx r1 r2) i j =
    if (Nat.eq_dec i r1) then get mx r2 j
    else if (Nat.eq_dec i r2) then get mx r1 j
    else get mx i j.

(*row r2 = k * row r1  + row r2 *)
Parameter add_multiple: forall {m n : nat}, (matrix m n) -> nat -> nat -> A -> (matrix m n).

Axiom add_multiple_spec: forall {m n} (mx: matrix m n) i j r1 r2 c,
  (i < m)%nat ->
  (j < n)%nat ->
  (r1 < m)%nat ->
  (r2 < m)%nat ->
  r1 <> r2 ->
  get (add_multiple mx r1 r2 c) i j =
    if (Nat.eq_dec i r2) then A.plus (A.mult c (get mx r1 j)) (get mx r2 j)
    else get mx i j. 





(*

(* row r1 = row r1 - row r2 *)
Parameter subtract_rows: forall {m n: nat}, (matrix m n) -> nat -> nat -> (matrix m n).

(*spec - note that you cannot subtract a row from itself - or else this breaks invariants of EROs*)
Axiom subtract_rows_spec: forall {m n} (mx: matrix m n) i j r1 r2,
  (i < m)%nat ->
  (j < n)%nat ->
  (r1 < m)%nat ->
  (r2 < m)%nat ->
  r1 <> r2 ->
  get (subtract_rows mx r1 r2) i j =
    if (Nat.eq_dec i r1) then A.sub (get mx r1 j) (get mx r2 j)
    else get mx i j.

*)

End Matrix.

(*TODO: redo maybe with new [add_multiple] 

Module FnMatrix(T: RingMod) <: Matrix T.

Definition A := T.A.

Program Instance test : `{Inhabitant A}.
Next Obligation.
apply T.zero.
Defined.

(*matrix is a function defined only on its valid arguments - need this for equality, we want to be able to say
  that a matrix is equal to another if it agrees on all valid entries*)
Definition matrix (m n : nat) := {f: nat -> nat -> A | forall i j, (i>=m)%nat \/ (j>=n)%nat -> f i j = T.zero}.

(*construct matrix from function *)
Program Definition mk_matrix m n (f: nat -> nat -> A) : matrix m n := exist _ (fun i j =>
   if (lt_dec i m) then if (lt_dec j n) then f i j else T.zero else T.zero) _.
Next Obligation.
if_tac. if_tac. lia. all: reflexivity.
Defined.

Definition get {m n} (mx: matrix m n) i j :=
  (proj1_sig mx) i j.

Lemma matrix_equiv: forall {m n} (m1 m2: matrix m n),
  m1 = m2 <-> forall i j, (i<m)%nat -> (j<n)%nat -> @get m n m1 i j = @get m n m2 i j.
Proof.
  intros. split; intros.
  - subst. reflexivity.
  - unfold get in H. destruct m1; destruct m2; simpl in *. apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
    apply functional_extensionality. intros. apply functional_extensionality. intros.
    destruct (lt_dec x1 m).
    + destruct (lt_dec x2 n).
      * apply H; auto.
      * rewrite e; try lia. rewrite e0; try lia. reflexivity.
    + rewrite e; try lia. rewrite e0; try lia. reflexivity.
Qed.

Lemma mk_matrix_spec: forall m n f i j,
  (0<m)%nat ->
  (0<n)%nat ->
  (i< m)%nat ->
  (j< n)%nat ->
  get (mk_matrix m n f) i j = f i j.
Proof.
  intros. unfold mk_matrix. unfold get. simpl. if_tac. if_tac. reflexivity. all: lia.
Qed.
(*

(* [ith_row] - we define a helper function to build the list *)

Fixpoint ith_row_help (mx: nat -> nat -> A) i j: list A :=
  match j with
  | O => (mx i j) :: nil
  | S(j') => (ith_row_help mx i j') ++ (mx i j) :: nil
  end.

Definition ith_row {m n} (mx: matrix m n) i : list A :=
  ith_row_help (proj1_sig mx) i (n-1).

Lemma ith_row_help_length: forall (mx: nat -> nat -> A)  i j,
  Zlength (ith_row_help mx i j) = Z.of_nat (j + 1).
Proof.
  intros. induction j.
  - simpl. apply Zlength_cons.
  - simpl. rewrite Zlength_app. rewrite Zlength_cons. rewrite IHj. simpl. lia.
Qed. 

Lemma ith_row_help_spec: forall (mx: nat -> nat -> A) i j k,
  (k <=j)%nat ->
  Znth (Z.of_nat k) (ith_row_help mx i j) = mx i k.
Proof.
  intros. induction j.
  - simpl. assert (k=0)%nat by lia. subst. simpl.
    apply Znth_0_cons.
  - simpl. assert (k = S j \/ (k <= j)%nat) by lia. destruct H0.
    + subst. rewrite Znth_app2. rewrite ith_row_help_length. 
      assert (Z.of_nat (S j) - Z.of_nat (j + 1) = 0) by lia. rewrite H0; clear H0.
      rewrite Znth_0_cons. reflexivity. rewrite ith_row_help_length. lia.
    + rewrite Znth_app1. apply IHj. lia. rewrite ith_row_help_length. lia.
Qed.

Lemma ith_row_spec: forall {m n} (mx: matrix m n) i j,
  (i < m)%nat ->
  (j < n)%nat ->
 get mx i j = Znth (Z.of_nat j) (ith_row mx i).
Proof.
  intros. unfold get. unfold ith_row. rewrite ith_row_help_spec. reflexivity. lia.
Qed.

Lemma ith_row_length: forall {m n} (mx: matrix m n) i,
  Zlength (ith_row mx i) = Z.of_nat n.
Proof.
  intros. unfold ith_row. rewrite ith_row_help_length.  lia. simpl. unfold ith_row_help.

(*basically same for ith col *)

Fixpoint ith_col_help (mx: nat -> nat -> A) i j: list A :=
  match i with
  | O => (mx i j) :: nil
  | S(i') => (ith_col_help mx i' j) ++ (mx i j) :: nil
  end.

Definition ith_col {m n} (mx: matrix m n) i: list A :=
  ith_col_help (proj1_sig mx) (m-1) i.

Lemma ith_col_help_length: forall (mx: nat -> nat -> A) i j,
  Zlength (ith_col_help mx i j) = Z.of_nat (i + 1).
Proof.
  intros. induction i.
  - simpl. apply Zlength_cons.
  - simpl. rewrite Zlength_app. rewrite Zlength_cons. rewrite IHi. simpl. lia.
Qed. 

Lemma ith_col_help_spec: forall (mx: nat -> nat -> A) i j k,
  (k <=i)%nat ->
  Znth (Z.of_nat k) (ith_col_help mx i j) = mx k j.
Proof.
  intros. induction i.
  - simpl. assert (k=0)%nat by lia. subst. simpl.
    apply Znth_0_cons.
  - simpl. assert (k = S i \/ (k <= i)%nat) by lia. destruct H0.
    + subst. rewrite Znth_app2. rewrite ith_col_help_length. 
      assert (Z.of_nat (S i) - Z.of_nat (i + 1) = 0) by lia. rewrite H0; clear H0.
      rewrite Znth_0_cons. reflexivity. rewrite ith_col_help_length. lia.
    + rewrite Znth_app1. apply IHi. lia. rewrite ith_col_help_length. lia.
Qed.

Lemma ith_col_spec: forall {m n} (mx: matrix m n) i j,
  (i < m)%nat ->
  (j < n)%nat ->
 get mx i j = Znth (Z.of_nat i) (ith_col mx j).
Proof.
  intros. unfold get. unfold ith_col. rewrite ith_col_help_spec. reflexivity. lia.
Qed.
*)

Add Ring test: T.Rth.

Lemma mul_0_1: forall (c: A),
  T.mult c (T.zero) = T.zero.
Proof.
intros.
ring. (*for some reason ring works here but not in the next proof *)
Qed.

(*scalar mult - this is very easy with functions *)
Program Definition scalar_mul_row {m n} (mx: matrix m n) i c : matrix m n :=
  exist _ (fun x y => if Nat.eq_dec x i then T.mult c (mx x y) else mx x y) _.
Next Obligation.
destruct mx; simpl. if_tac; try lia. subst. rewrite e. apply mul_0_1. lia. apply e. lia.
Defined. 

(*this definition makes the proof essentially free  *)
Lemma scalar_mul_row_spec: forall {m n} (mx: matrix m n) i j k c,
  (i < m)%nat ->
  (j < n)%nat ->
  (k < m)%nat ->
  get (scalar_mul_row mx k c) i j =
    if (Nat.eq_dec i k) then  T.mult c (get mx i j) else get mx i j.
Proof. reflexivity. Qed.

(*for swapping rows, we need bound info, so we encode the proof in the return type to be able to handle the
  proof obligations with Program *)
Program Definition swap_rows' {m n} (mx: matrix m n) r1 r2 : 
  {mret : matrix m n | (r1 < m)%nat -> (r2 < m)%nat -> forall i j,(i < m)%nat ->
  (j < n)%nat -> get mret i j =
    if (Nat.eq_dec i r1) then get mx r2 j
    else if (Nat.eq_dec i r2) then get mx r1 j
    else get mx i j} :=
  match (lt_dec r1 m) with
  | left H => match (lt_dec r2 m) with
              |left H' =>  exist _ (fun x y => if (Nat.eq_dec x r1) then mx r2 y 
                          else if (Nat.eq_dec x r2) then mx r1 y else mx x y) _
              |right H' => mx
              end
  |right H => mx
  end.
Next Obligation. 
destruct mx; simpl. destruct H0. if_tac. subst. lia. if_tac. subst. lia.
apply e. lia. if_tac. subst. apply e. lia. if_tac. subst. apply e. lia. apply e. lia.
Defined.
Next Obligation.
destruct mx; simpl. apply e. lia.
Defined.
Next Obligation.
lia.
Defined.
Next Obligation.
destruct mx; simpl. apply e; lia.
Defined.
Next Obligation.
lia.
Defined.

Definition swap_rows {m n} (mx: matrix m n) r1 r2 := proj1_sig (swap_rows' mx r1 r2).

(*exchange rows spec *)
Lemma swap_rows_spec: forall {m n} (mx: matrix m n) i j r1 r2,
  (i < m)%nat ->
  (j < n)%nat ->
  (r1 < m)%nat ->
  (r2 < m)%nat ->
  get (swap_rows mx r1 r2) i j =
    if (Nat.eq_dec i r1) then get mx r2 j
    else if (Nat.eq_dec i r2) then get mx r1 j
    else get mx i j.
Proof.
  intros. unfold swap_rows. destruct (swap_rows' mx r1 r2). simpl. apply e; lia.  
Qed.

(* subtracting rows is similar*)
Program Definition subtract_rows' {m n} (mx: matrix m n) r1 r2 : 
  {mret : matrix m n | (r1 < m)%nat -> (r2 < m)%nat -> forall i j,(i < m)%nat ->
  (j < n)%nat -> r1 <> r2 -> get mret i j =
    if (Nat.eq_dec i r1) then T.sub (get mx r1 j) (get mx r2 j)
    else get mx i j} :=
  match (lt_dec r1 m) with
  | left H => match (lt_dec r2 m) with
              |left H' =>  exist _ (fun x y => if (Nat.eq_dec x r1) then T.sub (mx r1 y) (mx r2 y) else mx x y) _
              |right H' => mx
              end
  |right H => mx
  end.
Next Obligation.
destruct mx; simpl. if_tac. subst. rewrite e; try lia. rewrite e; try lia.
assert (T.sub T.zero T.zero = T.zero) by ring. apply H1.
apply e. lia.
Defined.
Next Obligation.
destruct mx; simpl. rewrite e. reflexivity. lia.
Defined.
Next Obligation.
lia.
Defined.
Next Obligation. 
destruct mx; simpl. apply e. lia.
Defined.
Next Obligation.
lia.
Defined.

Definition subtract_rows {m n} (mx: matrix m n) r1 r2 := proj1_sig (subtract_rows' mx r1 r2).

Lemma subtract_rows_spec:  forall {m n} (mx: matrix m n) i j r1 r2,
  (i < m)%nat ->
  (j < n)%nat ->
  (r1 < m)%nat ->
  (r2 < m)%nat ->
  r1 <> r2 ->
  get (subtract_rows mx r1 r2) i j =
    if (Nat.eq_dec i r1) then T.sub (get mx r1 j) (get mx r2 j)
    else get mx i j.
Proof.
  intros. unfold subtract_rows. destruct (subtract_rows' mx r1 r2); simpl. apply e; lia. 
Qed.

End FnMatrix.


Module ListMatrix(A: RingMod) <: Matrix A.

Definition A := A.A.

Program Instance test : `{Inhabitant A}.
Next Obligation.
apply A.zero.
Defined.

(*trying alternate*)
Definition matrix_type := list (list A).

Definition matrix m n := {l: list(list A) | Zlength l = Z.of_nat m /\ forall row, In row l -> Zlength row = Z.of_nat n}.

Definition get {m n} (mx: matrix m n) i j : A :=
  Znth (Z.of_nat j) (Znth (Z.of_nat i) (proj1_sig mx)).

(* equality - we only define lists on valid locations *)
(*
(*two lists of equal length with the same elements in the same locations are equal*)
Lemma Znth_list_eq: forall {X: Type} `{Inhabitant X} (l1 l2: list X),
  Zlength l1 = Zlength l2 ->
  (forall i, 0 <= i < Zlength l1 -> Znth i l1 = Znth i l2) ->
  l1 = l2.
Proof.
  intros X H l1. induction l1; intros.
  - list_solve.
  - rewrite Zlength_cons in H0. destruct l2. list_solve. rewrite Zlength_cons in H0.
    apply Z.succ_inj in H0. assert (A:= H1). specialize (H1 0). repeat (rewrite Znth_0_cons in H1). rewrite H1.
    erewrite IHl1. reflexivity. assumption. intros. specialize (A (i+1)). 
    rewrite Znth_pos_cons in A. rewrite Znth_pos_cons in A. assert (i + 1 - 1 = i) by lia.
    rewrite H3 in A. apply A. list_solve. all: try lia. list_solve.
Qed.
*)

Lemma matrix_equiv: forall {m n} (m1 m2: matrix m n),
  m1 = m2 <-> forall i j, (i<m)%nat -> (j<n)%nat -> @get m n m1 i j = @get m n m2 i j.
Proof.
  intros. split; intros. subst. reflexivity. unfold get in *; destruct m1. destruct m2. simpl in *.
  apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.  apply Znth_eq_ext. list_solve.
  intros. apply Znth_eq_ext. destruct a. destruct a0. rewrite H2. rewrite H4. reflexivity.
  all: try (apply Znth_In; lia). intros.
  pose proof Z2Nat.id i.
  pose proof Z2Nat.id i0. 
  rewrite <- H2; try lia. rewrite <- H3; try lia. apply H. lia. destruct a. rewrite H5 in H1. lia. 
  apply Znth_In; lia.
Qed.


(*we build the matrix by building each row, then putting them together - similar to ith_row_help in function version *)
Fixpoint build_ith_row (f: nat -> nat -> A) j i : list A :=
  match j with
  | O => (f i j) :: nil
  | S(j') => (build_ith_row f j' i) ++ (f i j) :: nil
  end.

Lemma build_ith_row_length: forall f i j,
  Zlength (build_ith_row f j i) = Z.of_nat (j+1).
Proof.
  intros. induction j.
  - simpl. apply Zlength_cons.
  - simpl. rewrite Zlength_app. rewrite IHj. rewrite Zlength_cons. simpl. lia.
Qed.

Lemma build_ith_row_Znth: forall f i j k,
  (k<=j)%nat ->
  Znth (Z.of_nat k) (build_ith_row f j i) = f i k.
Proof.
  intros. induction j.
  - simpl. assert (k = 0)%nat by lia. subst. apply Znth_0_cons. 
  - simpl. assert (k = S j \/ (k <= j)%nat) by lia. destruct H0.
    + subst. rewrite Znth_app2. rewrite build_ith_row_length. 
      assert (Z.of_nat (S j) - Z.of_nat (j + 1) = 0) by lia. rewrite H0; clear H0.
      rewrite Znth_0_cons. reflexivity. rewrite build_ith_row_length. lia.
    + rewrite Znth_app1. apply IHj. lia. rewrite build_ith_row_length. lia.
Qed.

(*we make this generic - taking in a function that gives us the ith row  (NOTE: this is basically the
  same function, may be able to abstract *)
Fixpoint build_cols (f: nat -> list A) i :=
  match i with
  | O => f i :: nil
  | S (i') => (build_cols f i') ++ (f i :: nil)
  end.

Lemma build_cols_length: forall f i,
  Zlength (build_cols f i) = Z.of_nat (i+1).
Proof.
  intros. induction i.
  - simpl. apply Zlength_cons.
  - simpl. rewrite Zlength_app. rewrite IHi. rewrite Zlength_cons. simpl. lia.
Qed.

Lemma build_cols_Znth: forall f i k,
  (k<=i)%nat ->
  Znth (Z.of_nat k) (build_cols f i) = f k.
Proof.
  intros. induction i.
  - simpl. assert (k = 0)%nat by lia. subst. apply Znth_0_cons. 
  - simpl. assert (k = S i \/ (k <= i)%nat) by lia. destruct H0.
    + subst. rewrite Znth_app2. rewrite build_cols_length. 
      assert (Z.of_nat (S i) - Z.of_nat (i + 1) = 0) by lia. rewrite H0; clear H0.
      rewrite Znth_0_cons. reflexivity. rewrite build_cols_length. lia.
    + rewrite Znth_app1. apply IHi. lia. rewrite build_cols_length. lia.
Qed.

(* now we can define mk_matrix - we prove the spec here as well *)

Program Definition mk_matrix_full m n (f: nat -> nat -> A) (H1: (0<m)%nat) (H2: (0<n)%nat) : {mx: matrix m n |
  forall i j, (i< m)%nat -> (j< n)%nat -> get mx i j = f i j}
 :=
  exist _ (build_cols (build_ith_row f (n-1)%nat) (m-1)%nat) _.
Next Obligation.
split. rewrite build_cols_length. lia. intros. rewrite In_Znth_iff in H. destruct H as [i].
destruct H. rewrite <- H0. assert (i = Z.of_nat (Z.to_nat i)). lia. rewrite H3. rewrite build_cols_Znth.
rewrite build_ith_row_length. lia. rewrite build_cols_length in H. lia.
Defined.
Next Obligation.
unfold get. simpl. rewrite build_cols_Znth. rewrite build_ith_row_Znth. reflexivity. lia. lia.
Defined.


Local Obligation Tactic := unfold RelationClasses.complement, Equivalence.equiv; Tactics.program_simpl; try lia.
(*we do the pattern matching manually instead of using Program to remove the inequalities in the hypothesis *)
Program Definition mk_matrix_dep m n (f: nat -> nat -> A) : { mx: matrix m n | (0<m)%nat -> (0<n)%nat ->
  forall i j, (i< m)%nat -> (j< n)%nat -> get mx i j = f i j} :=
  match (lt_dec 0 m) with
  | left H => match (lt_dec 0 n) with
              |left H1 => proj1_sig (mk_matrix_full m n f H H1)
              |right H1 => exist _ (list_repeat m nil) _
              end
  | right H => exist _ nil _
  end.
Next Obligation.
apply mk_matrix_full_obligation_1; auto.
Defined.
Next Obligation.
apply mk_matrix_full_obligation_2; auto.
Defined.
Next Obligation.
split. apply Zlength_list_repeat'. intros. apply in_list_repeat in H0. subst.
assert (0 = n)%nat by lia. subst. simpl. apply Zlength_nil.
Defined.
Next Obligation.
assert (0 = m)%nat by lia. subst. split. simpl. apply Zlength_nil. intros. destruct H0.
Defined.

(*there has got to be a better way than all this indirection *)
Definition mk_matrix m n (f: nat -> nat -> A) : matrix m n := proj1_sig (mk_matrix_dep m n f).

(*finally, we can prove this *)
Lemma mk_matrix_spec: forall m n f i j,
  (0<m)%nat ->
  (0<n)%nat ->
  (i< m)%nat ->
  (j< n)%nat ->
  get (mk_matrix m n f) i j = f i j.
Proof.
  intros. unfold mk_matrix. destruct ((mk_matrix_dep m n f)). simpl.
apply e; assumption.
Qed.
(*
(*ith row - this is quite simple *)

Definition ith_row {m n} (mx: matrix m n) i : list A :=
  Znth (Z.of_nat i) (proj1_sig mx).

Lemma ith_row_spec: forall {m n} (mx: matrix m n) i j,
  (i < m)%nat ->
  (j < n)%nat ->
 get mx i j = Znth (Z.of_nat j) (ith_row mx i).
Proof.
  intros. unfold get. unfold ith_row. reflexivity.
Qed.

(*ith col - this is slightly more complicated, because we have to combine the elements from each list.
  But the proof is easy*)
Definition ith_col {m n} (mx: matrix m n) i : list A :=
  map (fun l => Znth (Z.of_nat i) l) (proj1_sig mx).

Lemma ith_col_spec: forall {m n} (mx: matrix m n) i j,
  (i < m)%nat ->
  (j < n)%nat ->
 get mx i j = Znth (Z.of_nat i) (ith_col mx j).
Proof.
  intros. unfold get. unfold ith_col. destruct mx. simpl. rewrite Znth_map. reflexivity. lia.
Qed.
*)

(* scalar multiplication - we get the ith row, map over it, then replace it *)
(*we first define over lists, then deal with the dependent types later *)
Definition scalar_mul_row_list (l: list (list A)) i c : list (list A) :=
  let row := Znth (Z.of_nat i) l in
  let new_row := map (fun x => A.mult c x) row in
  upd_Znth (Z.of_nat i) l new_row.

Program Definition scalar_mul {m n} (mx: matrix m n) k c : {mret : matrix m n | (k<m)%nat ->
  forall i j, (j<n)%nat -> (i<m)%nat -> get mret i j =
    if (Nat.eq_dec i k) then A.mult c (get mx i j) else get mx i j} :=
  match (lt_dec k m) with
  | left H =>  exist _ (scalar_mul_row_list (proj1_sig mx) k c) _
  | right H => mx
  end.
Next Obligation.
destruct mx; simpl.
split.
- unfold scalar_mul_row_list. rewrite Zlength_solver.Zlength_upd_Znth. apply a.
- intros. destruct a. unfold scalar_mul_row_list in H0.
  rewrite In_Znth_iff in H0. destruct H0 as [i]. destruct H0.
  destruct (Z.eq_dec i (Z.of_nat k)).
  + subst. rewrite  Zlength_solver.Zlength_upd_Znth in H0.
    rewrite upd_Znth_same. rewrite Zlength_map. apply H2. apply Znth_In. all: apply H0.
  + rewrite  Zlength_solver.Zlength_upd_Znth in H0. rewrite upd_Znth_diff in H3.
    apply H2. rewrite <- H3. apply Znth_In. all: try apply H0. lia.  lia.
Defined.
Next Obligation.
unfold get. simpl. unfold scalar_mul_row_list. destruct mx; simpl.
if_tac.
- subst.  rewrite upd_Znth_same. rewrite Znth_map. reflexivity. destruct a. rewrite H4. lia.
  apply Znth_In. lia. lia.
- rewrite upd_Znth_diff. reflexivity. all: lia.
Defined.
Next Obligation.
destruct mx; simpl. apply a.
Defined.

(*finally the definition *)
Definition scalar_mul_row {m n} (mx: matrix m n) k c : matrix m n :=
  proj1_sig (scalar_mul mx k c).

(*specification of scalar mult*)
Lemma scalar_mul_row_spec: forall {m n} (mx: matrix m n) i j k c,
  (i < m)%nat ->
  (j < n)%nat ->
  (k < m)%nat ->
  get (scalar_mul_row mx k c) i j =
    if (Nat.eq_dec i k) then  A.mult c (get mx i j) else get mx i j.
Proof.
  intros. unfold scalar_mul_row. destruct (scalar_mul mx k c). simpl.
  apply e; auto.
Qed.

(* interchange 2 rows - this is structured similarly to scalar multiplication*)
Definition swap_row_list (l: list (list A)) i j : list (list A) :=
  let rowI := Znth (Z.of_nat i) l in
  let rowJ := Znth (Z.of_nat j) l in
  upd_Znth (Z.of_nat i) (upd_Znth (Z.of_nat j) l rowI) rowJ.


Program Definition swap {m n} (mx: matrix m n) r1 r2 : {mret : matrix m n | (r1<m)%nat -> (r2<m)%nat ->
  forall i j, (j<n)%nat -> (i<m)%nat -> get mret i j =
    if (Nat.eq_dec i r1) then (get mx r2 j) 
    else if (Nat.eq_dec i r2) then (get mx r1 j) 
    else get mx i j} :=
  match (lt_dec r1 m) with
  | left H => match (lt_dec r2 m) with
              | left H' => exist _ (swap_row_list (proj1_sig mx) r1 r2) _
              | right H' => mx
              end
  | right H => mx
  end.
Next Obligation.
destruct mx; simpl. unfold swap_row_list. split.
- rewrite Zlength_solver.Zlength_upd_Znth. rewrite Zlength_solver.Zlength_upd_Znth. apply a.
- intros. rewrite In_Znth_iff in H0. destruct H0 as [i]. 
  rewrite Zlength_solver.Zlength_upd_Znth in H0. rewrite Zlength_solver.Zlength_upd_Znth in H0.
  destruct H0. destruct a. destruct (Z.eq_dec i (Z.of_nat r1)).
  + subst. rewrite upd_Znth_same. apply H3. apply Znth_In. lia. 
    rewrite Zlength_solver.Zlength_upd_Znth. assumption.
  + rewrite upd_Znth_diff in H1. destruct (Z.eq_dec i (Z.of_nat r2)).
    * subst. rewrite upd_Znth_same. apply H3. apply Znth_In. all: lia.
    * rewrite upd_Znth_diff in H1. apply H3. rewrite <- H1. apply Znth_In. all: try lia.
    * rewrite Zlength_solver.Zlength_upd_Znth. lia.
    * rewrite Zlength_solver.Zlength_upd_Znth. lia.
    * assumption.
Defined.
Next Obligation.
unfold get. simpl. destruct mx; simpl. unfold swap_row_list. 
destruct a. destruct (Nat.eq_dec i r1).
- subst. rewrite upd_Znth_same. reflexivity. rewrite Zlength_solver.Zlength_upd_Znth. lia.
- rewrite upd_Znth_diff; try (rewrite Zlength_solver.Zlength_upd_Znth); try lia.
  destruct (Nat.eq_dec i r2).
  + subst. rewrite upd_Znth_same. reflexivity. lia.
  + rewrite upd_Znth_diff; try(rewrite Zlength_solver.Zlength_upd_Znth); try lia. reflexivity.
Defined.
Next Obligation.
destruct mx; simpl. apply a.
Defined.
Next Obligation. 
destruct mx; simpl; apply a.
Defined.

(*similarly, the actual definition just discards the dependent type*)
Definition swap_rows {m n} (mx: matrix m n) r1 r2: matrix m n :=
  proj1_sig (swap mx r1 r2).

(*exchange rows spec *)
Lemma swap_rows_spec: forall {m n} (mx: matrix m n) i j r1 r2,
  (i < m)%nat ->
  (j < n)%nat ->
  (r1 < m)%nat ->
  (r2 < m)%nat ->
  get (swap_rows mx r1 r2) i j =
    if (Nat.eq_dec i r1) then get mx r2 j
    else if (Nat.eq_dec i r2) then get mx r1 j
    else get mx i j.
Proof.
  intros. unfold swap_rows. destruct (swap mx r1 r2). simpl. apply e; auto.
Qed.

(* subtract row by another *)

Definition sub_row_list (l: list (list A)) r1 r2 : list (list A) :=
  let rowI := Znth (Z.of_nat r1) l in
  let rowJ := Znth (Z.of_nat r2) l in
  let sub := combineWith rowI rowJ A.sub in
  upd_Znth (Z.of_nat r1) l sub.
  
Program Definition sub {m n} (mx: matrix m n) r1 r2 : {mret : matrix m n | (r1<m)%nat -> (r2<m)%nat -> r1 <> r2 ->
  forall i j,  (j<n)%nat -> (i<m)%nat -> get mret i j =
  if (Nat.eq_dec i r1) then A.sub (get mx r1 j) (get mx r2 j) else (get mx i j)} :=
  match (lt_dec r1 m) with
  | left H => match (lt_dec r2 m) with
              | left H' => exist _ (sub_row_list (proj1_sig mx) r1 r2) _
              | right H' => mx
              end
  | right H => mx
  end.
Next Obligation.
destruct mx; unfold sub_row_list; simpl. split.
- rewrite Zlength_solver.Zlength_upd_Znth. apply a.
- intros. rewrite In_Znth_iff in H0. rewrite Zlength_solver.Zlength_upd_Znth in H0.
  destruct a. destruct H0 as [i]. destruct H0. 
  destruct (Z.eq_dec i (Z.of_nat r1)).
  + subst. rewrite upd_Znth_same. rewrite combineWithLength. 
    apply H2. apply Znth_In. lia. rewrite H2. rewrite H2. reflexivity. apply Znth_In. lia. apply Znth_In; lia.
    assumption.
  + rewrite upd_Znth_diff in H3. apply H2. subst. apply Znth_In; lia. assumption. lia. assumption.
Defined.
Next Obligation.
unfold get. destruct mx; simpl. if_tac.
- subst. unfold sub_row_list. rewrite upd_Znth_same. 
  rewrite combineWithZnth. reflexivity.
  destruct a. rewrite H6. rewrite H6. reflexivity. all: try (apply Znth_In); try list_solve.
  destruct a. rewrite H6. lia. apply Znth_In; lia.
- unfold sub_row_list. rewrite upd_Znth_diff; try lia. reflexivity.
Defined.
Next Obligation.
destruct mx; simpl. apply a.
Defined.
Next Obligation.
destruct mx; simpl. apply a.
Defined.

(*similarly, the actual definition just discards the dependent type*)
Definition subtract_rows {m n} (mx: matrix m n) r1 r2 : matrix m n :=
  proj1_sig (sub mx r1 r2).

Lemma subtract_rows_spec:  forall {m n} (mx: matrix m n) i j r1 r2,
  (i < m)%nat ->
  (j < n)%nat ->
  (r1 < m)%nat ->
  (r2 < m)%nat ->
  r1 <> r2 ->
  get (subtract_rows mx r1 r2) i j =
    if (Nat.eq_dec i r1) then A.sub (get mx r1 j) (get mx r2 j)
    else get mx i j.
Proof.
  intros. unfold subtract_rows. destruct (sub mx r1 r2). simpl. apply e; auto.
Qed.


End ListMatrix.

(* note: this does not include subtracting one row from another - need to add, then gauss
specification should be pretty easy - similar to other EROs
- then define EROs in terms of these three operations
- may want to define as relation (determinstic) instead of fixpoint then prove equivalence, see
  essentially like the following: In each step
  1. find the largest in the current pivot position (maybe add to mx), swap
  2. multiply each row in pivot and below by unit (separate function)
  3. subtract each row below pivot from this

need some invariants - pivot contains a 1 in ith position, 0's in all columns below (also before pivot)
and row equiv - think about this a bit more
  -- find the largest in the current row (maybe add to mx), do a swap
  -- if largest is already at pivot, then multiply each row in pivot and below by unit (separate function)
     then subtrac *)
*)

