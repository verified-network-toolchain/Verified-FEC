Require Import MatrixDef.
Require Import VST.floyd.functional_base.
Require Import Coq.setoid_ring.Field_theory.

(*TODO: get rid of these once i merge with helper*)
Lemma Znth_seq: forall start len z,
  0 <= z < Z.of_nat len ->
  Znth z (seq start len) = Z.to_nat (Z.of_nat start + z).
Proof.
  intros. rewrite <- nth_Znth. rewrite seq_nth. lia. lia. 
  rewrite Zlength_correct. rewrite seq_length. lia.
Qed. 

Lemma Zlength_seq: forall start len,
  Zlength (seq start len) = Z.of_nat len.
Proof.
  intros. rewrite Zlength_correct. rewrite seq_length. reflexivity.
Qed. 


(*TODO: probably combine with prop_list*)
Definition prop_list_nat {B : Type} (f: nat -> B) (bound : nat) :=
  map f (seq 0 bound).

Lemma prop_list_nat_length: forall {A} (f: nat -> A) bound,
  Zlength (prop_list_nat f bound) = Z.of_nat bound.
Proof.
  intros. unfold prop_list_nat. rewrite? Zlength_map. 
  rewrite Zlength_seq. lia.
Qed.

Lemma prop_list_nat_Znth: forall {A} `{Inhabitant A} (f: nat -> A) bound i,
  0 <= i < Z.of_nat bound ->
  Znth i (prop_list_nat f bound) = f (Z.to_nat i).
Proof.
  intros. unfold prop_list_nat. rewrite Znth_map.
  rewrite Znth_seq. simpl. f_equal. lia.
  rewrite Zlength_seq. lia. 
Qed.

Lemma prop_list_nat_0: forall {A: Type} (f: nat -> A),
  prop_list_nat f 0 = nil.
Proof.
  intros. unfold prop_list_nat. simpl. reflexivity.
Qed.

(*Not everything requires a field, but the elementary matrices do*)

Module Type FieldMod <: RingMod.

Parameter A : Type.
Parameter plus : A -> A -> A.
Parameter mult: A -> A -> A.
Parameter sub: A -> A -> A.
Parameter opp: A -> A.
Parameter zero: A.
Parameter one: A.
Parameter div : A -> A -> A.
Parameter inv : A -> A.

Parameter Fth : field_theory zero one plus mult sub opp div inv eq.

Definition Rth := F_R Fth.

End FieldMod.

Module MatrixFacts(T: FieldMod)(M: Matrix T).

Definition A := T.A.

(*TODO: maybe move - generalized summations over fields*)
Definition summation_aux (f: nat -> A) (l: list nat) :=
  fold_right (fun n acc => T.plus (f n) acc) T.zero l.

Definition summation (f : nat -> A) (lb len : nat) : A :=
  summation_aux f (seq lb len).

Add Ring r : T.Rth.

Lemma summation_aux_scalar_mult: forall f l x,
  T.mult (summation_aux f l) x = summation_aux (fun y => T.mult (f y) x) l.
Proof.
  intros. induction l.
  - simpl. ring.
  - simpl. ring_simplify. rewrite IHl. reflexivity.
Qed.

Lemma summation_scalar_mult: forall f lb len x,
  T.mult (summation f lb len) x = summation (fun y => T.mult (f y) x) lb len.
Proof.
  intros. unfold summation. apply summation_aux_scalar_mult.
Qed.

(*sum a_i + b_i = sum a_i + sum b_i*)
Lemma summation_aux_distr_sum: forall f g l,
  summation_aux (fun i => T.plus (f i) (g i)) l =
  T.plus (summation_aux (fun i => f i) l)
        (summation_aux (fun i => g i) l).
Proof.
  intros. induction l. 
  - simpl. ring.
  - simpl. rewrite IHl. ring.
Qed.

(*sum_i sum_j a_{ij} = sum_j sum_i a_{ij} (for finite sums) *)
Lemma summation_aux_change_order: forall (f: nat -> nat -> A) l1 l2,
  summation_aux (fun i => summation_aux (fun j => f i j) l1) l2 = 
  summation_aux (fun j => summation_aux (fun i => f i j) l2) l1.
Proof.
  intros. revert l2. revert f. induction l1; intros.
  - simpl. induction l2. reflexivity. simpl. rewrite IHl2. ring.
  - simpl. rewrite summation_aux_distr_sum. rewrite IHl1. reflexivity.
Qed.

Import M.

Definition mx_mult {m n p} (mx : matrix m n ) (mx' : matrix n p) :=
  mk_matrix m p (fun i j => summation (fun k => T.mult (get mx i k) (get mx' k j)) 0 n).

Lemma mx_mult_spec: forall {m n p} (mx: matrix m n) (mx' : matrix n p) i j,
  (i < m)%nat ->
  (j < p)%nat ->
  get (mx_mult mx mx') i j = summation (fun k => T.mult (get mx i k) (get mx' k j)) 0 n.
Proof.
  intros. unfold mx_mult. rewrite mk_matrix_spec. reflexivity. all: lia.
Qed.

(*facts about matrix multiplication*)
Lemma mx_mult_assoc: forall {m n p l} (m1: matrix m n) (m2 : matrix n l) (m3: matrix l p),
  mx_mult (mx_mult m1 m2) m3 = mx_mult m1 (mx_mult m2 m3).
Proof.
  intros. rewrite matrix_equiv. intros.
  rewrite? mx_mult_spec; try lia. (*cannot expand inner automatically bc we need to know bounds*)
  unfold summation.
  assert(forall l1 : list nat,
    (forall x, In x l1 -> (x < l)%nat) ->
    summation_aux (fun k : nat => T.mult (get (mx_mult m1 m2) i k) (get m3 k j)) l1 =
    summation_aux (fun k : nat => T.mult (summation (fun y => T.mult (get m1 i y) (get m2 y k)) 0 n) (get m3 k j)) l1). {
  intros. induction l1. simpl. reflexivity. simpl. 
  rewrite mx_mult_spec. rewrite IHl1. reflexivity. intuition. lia. apply H1. left. reflexivity. }
  (*the same for the other side*)
  assert(forall l1: list nat,
    (forall x, In x l1 -> (x < n)%nat) ->
    summation_aux (fun k : nat => T.mult (get m1 i k) (get (mx_mult m2 m3) k j)) l1 =
    summation_aux (fun k : nat => T.mult (get m1 i k) ((summation (fun y => T.mult (get m2 k y) (get m3 y j)) 0 l))) l1). {
  intros. induction l1. reflexivity. simpl. rewrite mx_mult_spec. rewrite IHl1. reflexivity. 
  intuition. apply H2. left. reflexivity. lia. }
  rewrite H1. rewrite H2. 
  (*now rewrite the inner sum*)
  assert ((fun k : nat => T.mult (summation (fun y : nat => T.mult (get m1 i y) (get m2 y k)) 0 n) (get m3 k j)) =
  (fun k : nat => summation (fun y : nat => T.mult (T.mult (get m1 i y) (get m2 y k)) (get m3 k j)) 0 n)). {
  apply functional_extensionality. intros. rewrite summation_scalar_mult. reflexivity. }
  rewrite H3.
  assert ((fun k : nat => T.mult (get m1 i k) (summation (fun y : nat => T.mult (get m2 k y) (get m3 y j)) 0 l)) =
    (fun k : nat => (summation (fun y : nat => T.mult (T.mult (get m1 i k) (get m2 k y)) (get m3 y j)) 0 l))). {
  apply functional_extensionality. intros. assert (forall x y, T.mult x y = T.mult y x) by (intros; ring).
  rewrite H4. 
  rewrite summation_scalar_mult. 
  f_equal. apply functional_extensionality. intros. ring. } rewrite H4.
  unfold summation. rewrite (summation_aux_change_order 
  (fun k y => T.mult (T.mult (get m1 i y) (get m2 y k)) (get m3 k j))). reflexivity.
  intros. rewrite in_seq in H3. lia. intros. rewrite in_seq in H3. lia.
Qed.

(*The identity matrix*)
Definition identity (n: nat) : matrix n n :=
  mk_matrix n n (fun i j => if Nat.eq_dec i j then T.one else T.zero).

Lemma summation_identity_notin_r: forall f l j,
  ~In j l ->
   summation_aux (fun k => T.mult (f k) (if Nat.eq_dec k j then T.one else T.zero)) l = T.zero.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. if_tac. exfalso. apply H. left. assumption.
    rewrite IHl. ring. intuition.
Qed.

Lemma summation_identity_notin_l: forall f l j,
  ~In j l ->
   summation_aux (fun k => T.mult (if Nat.eq_dec j k then T.one else T.zero) (f k)) l = T.zero.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. if_tac. exfalso. apply H. left. auto. 
    rewrite IHl. ring. intuition.
Qed.

Lemma summation_identity_in_once_r: forall f l j,
  (exists l1 l2, l = l1 ++ j :: l2 /\ ~In j l1 /\ ~In j l2) ->
  summation_aux (fun k => T.mult (f k) (if Nat.eq_dec k j then T.one else T.zero)) l = f j.
Proof.
  intros. induction l.
  - simpl. destruct H. destruct H. destruct H. destruct x; inversion H.
  - destruct H as [l1]. destruct H as [l2]. destruct H. destruct H0.
    destruct l1. 
    + inversion H; subst. simpl. if_tac. 2: contradiction.
      rewrite summation_identity_notin_r. ring. assumption.
    + inversion H; subst. simpl. if_tac. exfalso. apply H0. left. assumption.
      rewrite IHl. ring. exists l1. exists l2. split. reflexivity. split. intuition. assumption.
Qed. 

Lemma summation_identity_in_once_l: forall f l j,
  (exists l1 l2, l = l1 ++ j :: l2 /\ ~In j l1 /\ ~In j l2) ->
  summation_aux (fun k => T.mult (if Nat.eq_dec j k then T.one else T.zero) (f k)) l = f j.
Proof.
  intros. induction l.
  - simpl. destruct H. destruct H. destruct H. destruct x; inversion H.
  - destruct H as [l1]. destruct H as [l2]. destruct H. destruct H0.
    destruct l1. 
    + inversion H; subst. simpl. if_tac. 2: contradiction.
      rewrite summation_identity_notin_l. ring. assumption.
    + inversion H; subst. simpl. if_tac. exfalso. apply H0. left. auto. 
      rewrite IHl. ring. exists l1. exists l2. split. reflexivity. split. intuition. assumption.
Qed. 

Lemma noDup_in_split: forall {A: Type} (l: list A) (x: A),
  In x l ->
  NoDup l ->
  exists l1 l2, l = l1 ++ x :: l2 /\ ~In x l1 /\ ~In x l2.
Proof.
  intros. induction l.
  - inversion H.
  - simpl in H. inversion H0; subst.
    destruct H. 
    + subst. exists nil. exists l. split. reflexivity. split. auto. assumption.
    + specialize (IHl H H4). destruct IHl as [l1]. destruct H1 as [l2].
      destruct H1. destruct H2. exists (a :: l1). exists l2.
      split. subst. reflexivity. split. intro. destruct H6; subst; contradiction.
      assumption.
Qed.

Lemma seq_bounds_split: forall lb len j,
  (lb <= j)%nat ->
  (j < lb + len)%nat ->
  exists l1 l2, seq lb len = l1 ++ j :: l2 /\ ~In j l1 /\ ~In j l2.
Proof.
  intros. apply noDup_in_split. rewrite in_seq. lia. apply seq_NoDup.
Qed.

Lemma mx_mult_I_r: forall {n} (m: matrix n n),
  mx_mult m (identity n) = m.
Proof.
  intros. rewrite matrix_equiv. intros.
  rewrite mx_mult_spec; try lia. unfold summation.
  assert(forall l,
    (forall x, In x l -> (x < n)%nat) ->
    summation_aux (fun k : nat => T.mult (get m i k) (get (identity n) k j)) l =
    summation_aux (fun k : nat => T.mult (get m i k) (if Nat.eq_dec k j then T.one else T.zero)) l). {
  intros. induction l. reflexivity. simpl. unfold identity at 1. rewrite mk_matrix_spec. rewrite IHl.
  reflexivity. intuition. all: try lia. apply H1. left. reflexivity. }
  rewrite H1. rewrite summation_identity_in_once_r. reflexivity.
  apply seq_bounds_split. lia. lia. intros. rewrite in_seq in H2. lia.
Qed.

Lemma mk_mult_I_l: forall {n} (m: matrix n n),
  mx_mult (identity n) m = m.
Proof.
  intros. rewrite matrix_equiv. intros.
  rewrite mx_mult_spec; try lia. unfold summation.
  assert(forall l,
    (forall x, In x l -> (x < n)%nat) ->
    summation_aux (fun k : nat => T.mult (get (identity n) i k) (get m k j)) l =
    summation_aux (fun k : nat => T.mult (if Nat.eq_dec i k then T.one else T.zero)  (get m k j)) l). {
  intros. induction l. reflexivity. simpl. unfold identity at 1. rewrite mk_matrix_spec. rewrite IHl.
  reflexivity. intuition. all: try lia. apply H1. left. reflexivity. }
  rewrite H1. rewrite summation_identity_in_once_l. reflexivity.
  apply seq_bounds_split. lia. lia. intros. rewrite in_seq in H2. lia.
Qed.

(** Elementary Matrices *)

(*m has left and right inverse m'*)
Definition inverse {n} (m: matrix n n) (m' : matrix n n) :=
  mx_mult m m' = identity n /\ mx_mult m' m = identity n.

Lemma identity_spec: forall n i j,
  (i < n)%nat ->
  (j < n)%nat ->
  get (identity n) i j = if Nat.eq_dec i j then T.one else T.zero.
Proof.
  intros. unfold identity. rewrite mk_matrix_spec; try lia.
  reflexivity.
Qed.


(*Row swapping - swap rows i and j*)
Definition row_swap_mx (n i j : nat) : matrix n n :=
  swap_rows (identity n) i j.

Lemma swap_rows_elem_mx: forall {m n} i j (mx: matrix m n),
  (i < m)%nat ->
  (j < m)%nat ->
  swap_rows mx i j = mx_mult (row_swap_mx m i j) mx.
Proof.
  intros. apply matrix_equiv. intros.
  rewrite swap_rows_spec; try lia.
  rewrite mx_mult_spec; try lia.
  unfold row_swap_mx. 
  unfold summation. assert (forall l,
    (forall x, In x l -> (x<m)%nat) ->
    summation_aux (fun k : nat => T.mult (get (swap_rows (identity m) i j) i0 k) (get mx k j0)) l =
    summation_aux (fun k : nat => T.mult (if Nat.eq_dec i0 i 
              then if Nat.eq_dec j k then T.one else T.zero
            else if Nat.eq_dec i0 j
              then if Nat.eq_dec i k then T.one else T.zero
            else if Nat.eq_dec i0 k then T.one else T.zero) (get mx k j0)) l). {
    intros. induction l. reflexivity.
    simpl. rewrite swap_rows_spec. rewrite? identity_spec. rewrite IHl. reflexivity. intuition.
    all: try lia. all: apply H3; left; reflexivity. } rewrite H3. clear H3.
    2 : { intros. rewrite in_seq in H4. lia. }
  if_tac.
  - subst. rewrite summation_identity_in_once_l. reflexivity.
    apply seq_bounds_split; lia.
  - if_tac.
    + rewrite summation_identity_in_once_l. reflexivity. apply seq_bounds_split; lia.
    + rewrite summation_identity_in_once_l. reflexivity. apply seq_bounds_split; lia.
Qed.

Lemma swap_sym: forall {m n} (mx: matrix m n) i j,
  (i < m)%nat ->
  (j < m)%nat ->
  swap_rows mx i j = swap_rows mx j i.
Proof.
  intros. rewrite matrix_equiv. intros.
  rewrite? swap_rows_spec; try lia. if_tac. subst. if_tac; subst; reflexivity.
  reflexivity.
Qed. 

Lemma swap_twice: forall {m n} (mx: matrix m n) r1 r2,
  (r1 < m)%nat ->
  (r2 < m)%nat ->
  swap_rows (swap_rows mx r1 r2) r2 r1 = mx.
Proof.
  intros. rewrite matrix_equiv. intros.
  rewrite swap_rows_spec; try lia. if_tac. 
  - subst. rewrite swap_rows_spec. if_tac. reflexivity. all: lia.
  - if_tac. subst. rewrite swap_rows_spec. if_tac. subst. reflexivity. if_tac. reflexivity. all: try lia.
    rewrite swap_rows_spec. if_tac. lia. if_tac.  lia. reflexivity. all: lia.
Qed.

(*The swap matrix is invertible, and, moreover, it is its own inverse*)
Lemma row_swap_mx_inv: forall n i j,
  (i < n)%nat ->
  (j < n)%nat ->
  inverse (row_swap_mx n i j) (row_swap_mx n i j).
Proof.
  intros. unfold inverse. rewrite <- swap_rows_elem_mx.
  unfold row_swap_mx. rewrite swap_sym. split; apply swap_twice. all: lia.
Qed.


(*Scalar multiplication*)
Definition scalar_mult_mx n i c :=
  scalar_mul_row (identity n) i c.

Lemma scalar_mult_elem: forall {m n} (mx: matrix m n) i c,
  (i < m)%nat ->
  scalar_mul_row mx i c = mx_mult (scalar_mult_mx m i c) mx.
Proof.
  intros. apply matrix_equiv. intros. rewrite scalar_mul_row_spec; try lia.
  rewrite mx_mult_spec; try lia. unfold scalar_mult_mx. unfold summation.
  assert (forall l,
    (forall x, In x l -> (x < m)%nat) ->
    summation_aux (fun k : nat => T.mult (get (scalar_mul_row (identity m) i c) i0 k) (get mx k j)) l =
    summation_aux (fun k : nat => T.mult (if Nat.eq_dec i0 i then if Nat.eq_dec k i then c else T.zero
                                            else if Nat.eq_dec i0 k then T.one else T.zero) (get mx k j)) l). {
  intros. induction l. reflexivity.
  simpl. rewrite scalar_mul_row_spec. rewrite identity_spec. rewrite IHl. f_equal.
  if_tac. subst. if_tac. subst. if_tac. ring. contradiction. if_tac. subst. contradiction.
  ring. reflexivity. intuition. all: try lia. all: apply H2; left; reflexivity. } rewrite H2. clear H2.
  if_tac.
  - subst. assert ((fun k : nat => T.mult (if Nat.eq_dec k i then c else T.zero) (get mx k j)) =
    (fun k : nat => T.mult (T.mult (if Nat.eq_dec i k then T.one else T.zero) (get mx k j)) c)). {
   apply functional_extensionality. intros. if_tac; try(if_tac); try(subst; contradiction); ring.  } 
   rewrite H2. clear H2.
   rewrite <- summation_aux_scalar_mult. 
   rewrite summation_identity_in_once_l. assert (forall x y, T.mult x y = T.mult y x) by (intros; ring).
   rewrite H2. reflexivity. apply seq_bounds_split; lia.
  - rewrite summation_identity_in_once_l. reflexivity. apply seq_bounds_split; lia.
  - intros. rewrite in_seq in H3. lia.
Qed.

Add Field field : T.Fth.

Import Field.

Lemma scalar_mult_inv: forall (n: nat) i c,
  (i < n)%nat ->
  (c <> T.zero) ->
  inverse (scalar_mult_mx n i c) (scalar_mult_mx n i (T.inv c)).
Proof.
  intros. unfold inverse.
  assert (forall x, x <> T.zero ->
  mx_mult (scalar_mult_mx n i x) (scalar_mult_mx n i (T.inv x)) = identity n). { intros.
  rewrite <- scalar_mult_elem. 2 : lia. unfold scalar_mult_mx. apply matrix_equiv.
  intros. rewrite scalar_mul_row_spec; try lia. rewrite scalar_mul_row_spec; try lia.
  if_tac. subst. remember (get (identity n) i j) as g.  
  assert(forall x y, x <> T.zero -> T.mult x (T.mult (T.inv x) y) = y). intros. field. assumption.
  apply H4. assumption. reflexivity. }
  split. rewrite H1. reflexivity. assumption.
  assert (forall x, x <> T.zero -> x = T.inv (T.inv x)). intros. field. split. assumption.
  apply (F_1_neq_0 (T.Fth)). rewrite (H2 c) at 2. 2 : assumption. apply H1.
  intro. assert (T.mult c  (T.inv c) = T.one) by (field; assumption). rewrite H3 in H4.
  assert (T.mult c T.zero = T.zero) by ring. rewrite H5 in H4. apply (F_1_neq_0 (T.Fth)). rewrite H4.
  reflexivity.
Qed.


(*subtract one row from another*)

(*TODO: subtract rows - maybe change to add scalar multiple?*)


End MatrixFacts.