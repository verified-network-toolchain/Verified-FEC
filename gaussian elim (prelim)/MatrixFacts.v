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

Lemma summation_aux_app: forall f l1 l2,
  summation_aux f (l1 ++ l2) =
  T.plus (summation_aux f l1) (summation_aux f l2).
Proof.
  intros. induction l1.
  - simpl. ring.
  - simpl. rewrite IHl1. ring.
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

Lemma mx_mult_I_r: forall {n m} (mx: matrix m n),
  mx_mult mx (identity n) = mx.
Proof.
  intros. rewrite matrix_equiv. intros.
  rewrite mx_mult_spec; try lia. unfold summation.
  assert(forall l,
    (forall x, In x l -> (x < n)%nat) ->
    summation_aux (fun k : nat => T.mult (get mx i k) (get (identity n) k j)) l =
    summation_aux (fun k : nat => T.mult (get mx i k) (if Nat.eq_dec k j then T.one else T.zero)) l). {
  intros. induction l. reflexivity. simpl. unfold identity at 1. rewrite mk_matrix_spec. rewrite IHl.
  reflexivity. intuition. all: try lia. apply H1. left. reflexivity. }
  rewrite H1. rewrite summation_identity_in_once_r. reflexivity.
  apply seq_bounds_split. lia. lia. intros. rewrite in_seq in H2. lia.
Qed.

Lemma mx_mult_I_l: forall {m n} (mx: matrix m n),
  mx_mult (identity m) mx = mx.
Proof.
  intros. rewrite matrix_equiv. intros.
  rewrite mx_mult_spec; try lia. unfold summation.
  assert(forall l,
    (forall x, In x l -> (x < m)%nat) ->
    summation_aux (fun k : nat => T.mult (get (identity m) i k) (get mx k j)) l =
    summation_aux (fun k : nat => T.mult (if Nat.eq_dec i k then T.one else T.zero)  (get mx k j)) l). {
  intros. induction l. reflexivity. simpl. unfold identity at 1. rewrite mk_matrix_spec. rewrite IHl.
  reflexivity. intuition. all: try lia. apply H1. left. reflexivity. }
  rewrite H1. rewrite summation_identity_in_once_l. reflexivity.
  apply seq_bounds_split. lia. lia. intros. rewrite in_seq in H2. lia.
Qed.

(** Elementary Matrices *)

(*m has left and right inverse m'*)
Definition inverse {n} (m: matrix n n) (m' : matrix n n) :=
  mx_mult m m' = identity n /\ mx_mult m' m = identity n.

Lemma inverse_unique: forall {n} (a : matrix n n) b c,
  inverse a b ->
  inverse a c ->
  b = c.
Proof.
  intros. unfold inverse in *. destruct H. destruct H0. 
  pose proof (mx_mult_I_r b). rewrite <- H0 in H3.
  rewrite <- mx_mult_assoc in H3. rewrite H1 in H3. rewrite mx_mult_I_l in H3.
  subst. reflexivity.
Qed.

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

(*Add a multiple of row to another *)
Definition add_multiple_mx n i j c :=
  mk_matrix n n (fun x y => if Nat.eq_dec x j then
                               if Nat.eq_dec y i then c
                               else (if Nat.eq_dec x y then T.one else T.zero)
                            else (if Nat.eq_dec x y then T.one else T.zero)).

(*Not sure how to avoid this repetition*)
Lemma NoDup_split_twice: forall {A: Type} r1 r2 (l: list A),
  In r1 l ->
  In r2 l ->
  r1 <> r2 ->
  NoDup l ->
  (exists l1 l2 l3, l = l1 ++ r1 :: l2 ++ r2 :: l3 /\ ~In r1 l1 /\ ~In r1 l2 /\ ~In r1 l3 /\
    ~In r2 l1 /\ ~In r2 l2 /\ ~In r2 l3) \/ 
  (exists l1 l2 l3, l = l1 ++ r2 :: l2 ++ r1 :: l3 /\ ~In r1 l1 /\ ~In r1 l2 /\ ~In r1 l3 /\
    ~In r2 l1 /\ ~In r2 l2 /\ ~In r2 l3).
Proof.
  intros. induction l.
  - inversion H.
  - inversion H2; subst.
    simpl in H. simpl in H0. destruct H.
    + destruct H0.
      * subst. contradiction.
      * subst. left. exists nil. 
        pose proof (noDup_in_split _ _ H0 H6). destruct H as [l']. destruct H as [l''].
        exists l'. exists l''. destruct H. destruct H3. split. rewrite H. reflexivity.
        repeat(split; try(intro C; inversion C); try(assumption)). 
        intro. apply H5. rewrite H. apply in_or_app. left. assumption.
        intro. apply H5. rewrite H. apply in_or_app. right. right. assumption.
    + destruct H0.
      * subst. right. exists nil. pose proof (noDup_in_split _ _ H H6). destruct H0 as [l'].
        destruct H0 as [l'']. destruct H0. destruct H3. exists l'. exists l''. split.
        rewrite H0. reflexivity. repeat(split; try(intro C; inversion C); try(assumption)). 
        intro. apply H5. rewrite H0. apply in_or_app. left. assumption. intro. apply H5.
        rewrite H0. apply in_or_app. right. right. assumption.
      * specialize (IHl H H0 H6). destruct IHl.
        -- destruct H3 as [l']. destruct H3 as [l'']. destruct H3 as [l'''].
           left. destruct H3 as [H3 D]. repeat(destruct D as [? D]).
           exists (a :: l'). exists l''. exists l'''. split. rewrite H3. reflexivity.
           repeat(split; try assumption). intro. destruct H11; subst; contradiction.
           intro. destruct H11; subst; contradiction.
        -- destruct H3 as [l']. destruct H3 as [l'']. destruct H3 as [l'''].
           right. destruct H3 as [H3 D]. repeat(destruct D as [? D]).
           exists (a :: l'). exists l''. exists l'''. split. rewrite H3. reflexivity.
           repeat(split; try assumption). intro. destruct H11; subst; contradiction.
           intro. destruct H11; subst; contradiction.
Qed.


Lemma summation_twice_notin_l: forall f l r1 r2 c1 c2,
  ~In r1 l ->
  ~In r2 l ->
  summation_aux
     (fun k : nat =>
      T.mult (if Nat.eq_dec k r1 then c1 else if Nat.eq_dec r2 k then c2 else T.zero) (f k)) l = T.zero.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. if_tac. subst. exfalso. apply H. left. reflexivity.
    if_tac. exfalso. apply H0. subst. left. reflexivity.
    rewrite IHl. ring. all: intuition.
Qed.

Lemma two_nonzero_entries_mult:
forall {m n : nat} r1 r2 (c1 c2: A) (mx: matrix m n) j l,
  In r1 l ->
  In r2 l ->
  NoDup l ->
  r1 <> r2 ->
  (forall x, In x l -> (x<m)%nat) ->
  (j < n)%nat ->
  summation_aux
  (fun k : nat =>
   T.mult (if Nat.eq_dec k r1 then c1 else if Nat.eq_dec r2 k then c2 else T.zero) (get mx k j)) l =
  T.plus (T.mult c1 (get mx r1 j)) (T.mult c2 (get mx r2 j)). 
Proof.
  intros. pose proof (NoDup_split_twice _ _ _ H H0 H2 H1). destruct H5.
  - destruct H5 as [l1]. destruct H5 as [l2]. destruct H5 as [l3].
    destruct H5 as [? D]. repeat(destruct D as [? D]).
    rewrite H5. rewrite summation_aux_app. rewrite summation_twice_notin_l; try assumption.
    simpl. rewrite summation_aux_app. rewrite summation_twice_notin_l; try assumption.
    simpl. rewrite summation_twice_notin_l; try assumption. if_tac. 2 : contradiction.
    if_tac. subst. contradiction. if_tac. 2 : contradiction. ring.
  - destruct H5 as [l1]. destruct H5 as [l2]. destruct H5 as [l3].
    destruct H5 as [? D]. repeat(destruct D as [? D]).
    rewrite H5. rewrite summation_aux_app. rewrite summation_twice_notin_l; try assumption.
    simpl. rewrite summation_aux_app. rewrite summation_twice_notin_l; try assumption.
    simpl. rewrite summation_twice_notin_l; try assumption. if_tac. subst. contradiction.
    if_tac. 2 : contradiction. if_tac. 2 : contradiction. ring.
Qed.

Lemma add_multiple_elem: forall {m n} (mx: matrix m n) r1 r2 c,
  (r1 < m)%nat ->
  (r2 < m)%nat ->
  r1 <> r2 ->
  add_multiple mx r1 r2 c = mx_mult (add_multiple_mx m r1 r2 c) mx.
Proof.
  intros. rewrite matrix_equiv. intros.
  unfold add_multiple_mx.
  rewrite add_multiple_spec; try lia.
  rewrite mx_mult_spec; try lia.
  unfold summation.
  assert (forall l, (forall x, In x l -> (x < m)%nat) ->
    summation_aux
  (fun k : nat =>
   T.mult
     (get
        (mk_matrix m m
           (fun x y : nat =>
            if Nat.eq_dec x r2
            then if Nat.eq_dec y r1 then c else if Nat.eq_dec x y then T.one else T.zero
            else if Nat.eq_dec x y then T.one else T.zero)) i k) (get mx k j)) l =
    summation_aux
  (fun k : nat =>
   T.mult   (if Nat.eq_dec i r2
            then if Nat.eq_dec k r1 then c else if Nat.eq_dec i k then T.one else T.zero
            else if Nat.eq_dec i k then T.one else T.zero) (get mx k j)) l). { intros.
  induction l. reflexivity. simpl. rewrite IHl. rewrite mk_matrix_spec; try lia.
  reflexivity. apply H4. left. reflexivity. intuition. } rewrite H4. clear H4.
  2 : { intros. rewrite in_seq in H5. lia. } if_tac.
  - subst. rewrite two_nonzero_entries_mult. f_equal. assert (forall x, x = T.mult T.one x) by(intros; ring).
    apply H4. rewrite in_seq; lia. rewrite in_seq; lia. apply seq_NoDup. assumption. intros.
    rewrite in_seq in H4; lia. assumption.
  - rewrite summation_identity_in_once_l. reflexivity. apply seq_bounds_split. lia.
    lia.
Qed.

Lemma add_multiple_inv: forall (n: nat) r1 r2 c,
  (r1 < n)%nat ->
  (r2 < n)%nat ->
  (r1 <> r2) ->
  inverse (add_multiple_mx n r1 r2 c) (add_multiple_mx n r1 r2 (T.opp c)).
Proof.
  intros. unfold inverse. assert (forall x, 
    mx_mult (add_multiple_mx n r1 r2 x) (add_multiple_mx n r1 r2 (T.opp x)) = identity n). {
  intros. rewrite <- add_multiple_elem; try lia. apply matrix_equiv. intros.
  rewrite add_multiple_spec; try lia. unfold add_multiple_mx.
  rewrite mk_matrix_spec; try lia. rewrite identity_spec; try lia.
  repeat(rewrite mk_matrix_spec; try lia).
  if_tac. 2 : reflexivity. subst. if_tac. subst. contradiction.
  if_tac. subst. if_tac. 2 : contradiction. if_tac. 2 : contradiction. if_tac. subst. contradiction.
  ring_simplify. reflexivity.
  if_tac. 2 : contradiction. if_tac. subst. contradiction. if_tac. subst.
  all: replace (T.mult x T.zero) with T.zero by ring. all: ring_simplify; reflexivity. }
  split. apply H2. replace c with (T.opp (T.opp c)) at 2 by ring. apply H2.
Qed.

(*Inverses of products*)

Definition invertible {n: nat} (m: matrix n n) :=
  exists mx, inverse m mx.

Lemma identity_inv: forall n,
  inverse (identity n) (identity n).
Proof.
  intros. unfold inverse. split. all: apply mx_mult_I_r.
Qed.

Lemma identity_invertible: forall n,
  invertible (identity n).
Proof.
  intros. unfold invertible. exists (identity n). apply identity_inv.
Qed.

(*(AB)^-1 = B^-1A^-1*)
Lemma inverse_of_product : forall {n : nat} (a a' b b' : matrix n n),
  inverse a a' ->
  inverse b b' ->
  inverse (mx_mult a b) (mx_mult b' a').
Proof.
  intros. unfold inverse in *. destruct H. destruct H0. 
  split. rewrite <- mx_mult_assoc. rewrite (mx_mult_assoc a). rewrite H0.
  rewrite mx_mult_I_r. assumption.
  rewrite <- mx_mult_assoc. rewrite (mx_mult_assoc b'). rewrite H1. 
  rewrite mx_mult_I_r. assumption.
Qed.

Lemma product_invertible: forall {n: nat} (a b: matrix n n),
  invertible a ->
  invertible b ->
  invertible (mx_mult a b).
Proof.
  intros. unfold invertible in *. destruct H as [a'].
  destruct H0 as [b']. exists (mx_mult b' a'). apply inverse_of_product; assumption.
Qed.

(*Finally, we can define products of elementary matrices *)
Section Elementary.

Variable m : nat.

Inductive elem_matrix: (matrix m m) -> Prop :=
  | e_swap: forall i j,
    (i<m)%nat ->
    (j<m)%nat ->
    elem_matrix (row_swap_mx m i j)
  | e_scalar: forall i c,
    (i<m)%nat ->
    c <> T.zero ->
    elem_matrix (scalar_mult_mx m i c)
  | e_add_multiple: forall i j c,
    (i<m)%nat ->
    (j<m)%nat ->
    i <> j -> (*this is invalid or just scalar mult anyway*)
    elem_matrix (add_multiple_mx m i j c).

Lemma elem_matrix_invertible: forall mx,
  elem_matrix mx -> invertible mx.
Proof.
  intros. unfold invertible. inversion H.
  - exists (row_swap_mx m i j). apply row_swap_mx_inv; assumption.
  - exists (scalar_mult_mx m i (T.inv c)).  apply scalar_mult_inv; assumption.
  - exists (add_multiple_mx m i j (T.opp c)). apply add_multiple_inv; try assumption.
Qed.

Lemma elem_matrix_inverse_elementary: forall mx mx',
  elem_matrix mx ->
  inverse mx mx' ->
  elem_matrix mx'.
Proof.
  intros. inversion H; subst.
  - pose proof (row_swap_mx_inv m i j H1 H2).
    assert (mx' = row_swap_mx m i j). eapply inverse_unique. apply H0. assumption.
    subst. constructor; assumption.
  - pose proof (scalar_mult_inv m i c H1 H2).
    assert (mx' = (scalar_mult_mx m i (T.inv c))). eapply inverse_unique. apply H0. assumption.
    subst. constructor; try assumption. intro. assert (T.mult c (T.inv c) = T.one) by (field; assumption).
    rewrite H4 in H5. assert (T.mult c T.zero = T.zero) by field. rewrite H5 in H6.
    pose proof (F_1_neq_0 (T.Fth)). contradiction.
  - pose proof (add_multiple_inv m i j c H1 H2 H3). 
    assert (mx' = (add_multiple_mx m i j (T.opp c))). eapply inverse_unique. apply H0. assumption.
    subst. constructor; assumption.
Qed.

(*A product of elementary matrices*)
Inductive elem_product: (matrix m m) -> Prop :=
  | p_id: elem_product (identity m)
  | p_multiple: forall m1 mx,
      elem_product m1 ->
      elem_matrix mx ->
      elem_product (mx_mult mx m1).

Lemma elem_mx_product: forall mx,
  elem_matrix mx ->
  elem_product mx.
Proof.
  intros. rewrite <- mx_mult_I_r. eapply p_multiple. constructor. assumption.
Qed.

Lemma elem_product_trans: forall m1 m2,
  elem_product m1 ->
  elem_product m2 ->
  elem_product (mx_mult m1 m2).
Proof.
  intros. induction H.
  - rewrite mx_mult_I_l. assumption.
  - rewrite mx_mult_assoc. apply p_multiple. apply IHelem_product. assumption.
Qed.

(*The other direction is true, but much harder*)
Lemma elem_product_invertible: forall mx,
  elem_product mx -> invertible mx.
Proof.
  intros. induction H.
  - apply identity_invertible.
  - apply product_invertible. apply elem_matrix_invertible. all: assumption.
Qed.

(*TODO: see*)
(*
Lemma elem_product_inverse_elem: forall mx mx',
  elem_product mx ->
  inverse mx mx' ->
  elem_product mx'.
Proof.
  intros. revert H0. revert mx'. induction H; intros.
  - assert (mx' = identity m). eapply inverse_unique. apply H0. apply identity_inv. subst. constructor.
  -  Search inverse. rewrite mx_mult_inverse in H0.
*)
(** Elemetary Row Operations *)
Variable n : nat.

Inductive ERO : matrix m n -> matrix m n -> Prop :=
  | ero_swap: forall mx r1 r2,
    (r1 < m)%nat ->
    (r2 < m)%nat ->
    ERO mx (swap_rows mx r1 r2)
  | ero_scalar: forall mx i c,
    (i < m)%nat ->
    c <> T.zero ->
    ERO mx (scalar_mul_row mx i c)
  | ero_add: forall mx r1 r2 c,
    (r1 < m)%nat ->
    (r2 < m)%nat ->
    r1 <> r2 ->
    ERO mx (add_multiple mx r1 r2 c).


(*two matrices are row equivalent if one can be transformed to another via a sequence of EROs*)
Inductive row_equivalent: matrix m n -> matrix m n -> Prop :=
  | row_same: forall mx,
    row_equivalent mx mx
  | row_ero: forall mx mx' mx'',
    ERO mx mx' ->
    row_equivalent mx' mx'' ->
    row_equivalent mx mx''.

(*
Lemma row_equivalent_refl: forall m1 m2,
  m1 = m2 ->
  row_equivalent m1 m2.
Proof.
  intros. subst. apply row_same.
Qed.
*)
Lemma row_equivalent_trans: forall m1 m2 m3,
  row_equivalent m1 m2 ->
  row_equivalent m2 m3 ->
  row_equivalent m1 m3.
Proof.
  intros. induction H.
  - assumption.
  - eapply row_ero. apply H. auto.
Qed.

Lemma row_equivalent_ero: forall m1 m2,
  ERO m1 m2 ->
  row_equivalent m1 m2.
Proof.
  intros. eapply row_ero. apply H. apply row_same.
Qed.


(*Equivalence between EROs and multiplication on left by elementary matrices*)
Lemma ero_elem_mx_iff: forall m1 m2,
  ERO m1 m2 <-> exists e, elem_matrix e /\ m2 = mx_mult e m1.
Proof.
  intros. split; intros.
  - inversion H; subst.
    + exists (row_swap_mx m r1 r2). split. constructor; assumption.
      apply swap_rows_elem_mx; assumption.
    + exists (scalar_mult_mx m i c). split. constructor; assumption.
      apply scalar_mult_elem; assumption.
    + exists (add_multiple_mx m r1 r2 c). split. constructor; assumption.
      apply (add_multiple_elem); assumption.
  - destruct H as [e]. destruct H. inversion H; subst.
    + rewrite <- swap_rows_elem_mx. constructor. all: assumption.
    + rewrite <- scalar_mult_elem. constructor. all: assumption.
    + rewrite <- add_multiple_elem. constructor. all: assumption.
Qed.
(*
Variable Mpos: (0<m)%nat.

Lemma identity_is_elem_mx: elem_matrix (identity m).
Proof.
  intros.
  assert (identity m = (scalar_mult_mx m 0 (T.one))). {
  apply matrix_equiv. intros.  
  unfold scalar_mult_mx. rewrite scalar_mul_row_spec; try assumption.
  repeat(rewrite identity_spec; try assumption).
  if_tac. subst. if_tac. ring_simplify. reflexivity. reflexivity.
  if_tac. ring_simplify. all: reflexivity. } rewrite H. constructor.
  assumption. intro. pose proof (F_1_neq_0 (T.Fth)). contradiction.
Qed.
*)
Lemma row_equiv_elem_product_iff: forall m1 m2,
  row_equivalent m1 m2 <-> exists e, elem_product e /\ m2 = mx_mult e m1.
Proof.
  intros. split; intros.
  - induction H.
    + exists (identity m). split. constructor.
      rewrite mx_mult_I_l. reflexivity.
    + destruct IHrow_equivalent. destruct H1.
      rewrite ero_elem_mx_iff in H. destruct H as [e]. destruct H. subst.
      exists (mx_mult x e). split. apply elem_product_trans. apply H1.
      apply elem_mx_product. assumption. rewrite mx_mult_assoc. reflexivity.
  - destruct H as [e]. destruct H. generalize dependent m2. generalize dependent m1. induction H; intros.
    + rewrite mx_mult_I_l in H0. subst. constructor. 
    + rewrite mx_mult_assoc in H1. specialize (IHelem_product m0 (mx_mult m1 m0)).
      eapply row_equivalent_trans. apply IHelem_product. reflexivity.
      rewrite H1. apply row_equivalent_ero. apply ero_elem_mx_iff.
      exists mx. split. assumption. reflexivity.
Qed.


Lemma ERO_sym: forall m1 m2,
  ERO m1 m2 ->
  ERO m2 m1.
Proof.
  intros. rewrite ero_elem_mx_iff in H. rewrite ero_elem_mx_iff.
  destruct H as [e]. destruct H.
  pose proof (elem_matrix_invertible e H). unfold invertible in H1.
  destruct H1 as [e']. exists e'. split. eapply elem_matrix_inverse_elementary. apply H.
  assumption. subst. rewrite <- mx_mult_assoc. unfold inverse in H1. destruct H1.
  rewrite H1. rewrite mx_mult_I_l. reflexivity.
Qed.

Lemma row_equivalent_sym: forall m1 m2,
  row_equivalent m1 m2 ->
  row_equivalent m2 m1.
Proof.
  intros. induction H.
  - constructor.
  - eapply row_equivalent_trans. apply IHrow_equivalent.
    apply row_equivalent_ero. apply ERO_sym. assumption.
Qed.

End Elementary.

(*A key property of row operations: they preserve invertibility*)
Lemma row_equiv_invertible_iff: forall {n} m1 m2,
  row_equivalent n n m1 m2 ->
  invertible m1 <-> invertible m2.
Proof.
  intros. assert (forall a b,
    row_equivalent n n a b ->
    invertible a -> invertible b). { intros.
    rewrite row_equiv_elem_product_iff in H0. destruct H0 as [e]. destruct H0.
    subst. apply product_invertible. apply elem_product_invertible. assumption. assumption. }
  split; intros. eapply H0. apply H. assumption. eapply H0.
    apply row_equivalent_sym. apply H. assumption.
Qed.

(*get rows and columns of a matrix*)
Definition get_row {m n} (mx: matrix m n) (i: nat) :=
  if (lt_dec i m) then
  prop_list_nat (fun x => get mx i x) n else nil.

Definition get_column {m n} (mx: matrix m n) (i: nat) :=
  if (lt_dec i n) then
  prop_list_nat (fun x => get mx x i) m else nil.

Section Gaussian.

Variable Aeq_dec: forall x y : A, {x = y } + { x <> y}.

(*beginning of gaussian elimination*)

(*Returns the leading coefficient of a row and the index of that coefficient, or None if the row is all zeroes*)
Definition leading_coefficient_aux (l: list A) (s : list nat) :=
  fold_right (fun x acc => let c := (Znth (Z.of_nat x) l) in
                             if Aeq_dec c T.zero then acc else Some (c, x)) None s.
(*
Fixpoint leading_coefficient_aux (l: list A) (n: nat) : option (A * nat) :=
  match l with
  | nil => None
  | x :: t => if Aeq_dec x T.zero then leading_coefficient_aux t (n+1)%nat else Some (x, n)
  end.
*)
Lemma leading_coeff_none_iff: forall l s,
  leading_coefficient_aux l s = None <-> forall x, In x s -> Znth (Z.of_nat x) l = T.zero.
Proof.
  intros. induction s; intros.
  - split; intros. inversion H0. reflexivity.
  - simpl. split; intros. destruct H0. subst. 
    destruct (Aeq_dec (Znth (Z.of_nat x) l) T.zero). apply e. inversion H.
    destruct (Aeq_dec (Znth (Z.of_nat a) l) T.zero). rewrite IHs in H. apply H. assumption.
    inversion H. if_tac. apply IHs. intros. apply H. right. assumption.
    exfalso. apply H0. apply H. left. reflexivity.
Qed. 

Lemma leading_coeff_some_iff: forall l s c' n',
  leading_coefficient_aux l s = Some (c', n') <-> exists s1 s2,
    s = s1 ++ n' :: s2 /\ c' <> T.zero /\ Znth (Z.of_nat n') l = c' /\ forall x, In x s1 -> Znth (Z.of_nat x) l = T.zero.
Proof.
  intros. revert c' n' l. induction s; intros; simpl; split; intros.
  - inversion H.
  - destruct H as [s1]. destruct H as [s2]. destruct H. destruct s1; inversion H.
  - destruct (Aeq_dec (Znth (Z.of_nat a) l) T.zero).
    + apply IHs in H. destruct H as [s1]. destruct H as [s2 E]. repeat(destruct E as [? E]).
      exists (a :: s1). exists s2. split. rewrite H. reflexivity.
      split. assumption. split. assumption. intros. destruct H2. subst. assumption.
      apply E. assumption.
    + inversion H; subst. exists nil. exists s. split. reflexivity. split. assumption.
      split. reflexivity. intros. inversion H0.
  - destruct H as [s1]. destruct H as [s2 E]. repeat(destruct E as [? E]).
    if_tac. apply IHs. destruct s1. inversion H; subst. contradiction.
    inversion H; subst. exists s1. exists s2. split. reflexivity. split. assumption.
    split. reflexivity. intros. apply E. right. assumption.
    destruct s1. inversion H; subst. reflexivity. inversion H; subst.
    exfalso. apply H2. apply E. left. reflexivity.
Qed. 
(*
Lemma leading_coeff_aux_bounds: forall l s m c' n',
  (forall x, In x s -> (x<m)%nat) ->
  leading_coefficient_aux l s = Some (c', n') ->
  (n' < m)%nat.
Proof.
  intros. generalize dependent H0.  revert n' c'. induction s; intros.
  - inversion H0.
  - simpl in H0. destruct (Aeq_dec (Znth (Z.of_nat a) l) T.zero).
    + apply IHs in H0. assumption. intuition.
    + inversion H0; subst. apply H. left. reflexivity.
Qed.
*)
Lemma seq_split: forall a b l1 c l2,
  seq a b = l1 ++ c :: l2 -> (forall x, (a <= x < c)%nat <-> In x l1) /\ (forall x, (c < x < a + b)%nat <-> In x l2).
Proof.
  intros. generalize dependent H. revert a l1 c l2. induction b; intros.
  - simpl in H. destruct l1; inversion H.
  - simpl in H. destruct l1. inversion H; subst.
    split; intros; split; intros. lia. inversion H0. rewrite in_seq. lia. rewrite in_seq in H0. lia.
    inversion H; subst. apply IHb in H2. destruct H2.
    split; intros; split; intros. assert (n = x \/ n < x)%nat by lia.
    destruct H3. subst. left. reflexivity. right. apply H0. lia.
    destruct H2. subst. inversion H; subst.
    assert (E: In c (seq (S x) b)). rewrite H3. apply in_or_app. right. left. reflexivity.
    rewrite in_seq in E. lia. apply H0 in H2. lia. apply H1. lia. apply H1 in H2. lia.
Qed. 

Definition leading_coefficient l m := leading_coefficient_aux l (seq 0 m).

Lemma leading_coefficient_some_iff: forall l m c' n',
  leading_coefficient l m = Some (c', n') <-> (n' < m)%nat /\ c' <> T.zero /\ Znth (Z.of_nat n') l = c' /\ 
    forall x, (x<n')%nat -> Znth (Z.of_nat x) l = T.zero.
Proof.
  intros. unfold leading_coefficient. rewrite leading_coeff_some_iff. split; intros.
  - destruct H as [s1]. destruct H as [s2]. destruct H. destruct H0. destruct H1.
    split. assert (In n' (seq 0 m)). rewrite H. apply in_or_app. right. left. reflexivity.
    rewrite in_seq in H3. lia.
    apply seq_split in H. split. assumption. split. assumption. destruct H. intros.
    apply H2. apply H. lia.
  - destruct H. destruct H0. destruct H1. 
    assert (In n' (seq 0 m)). rewrite in_seq. lia. apply in_split in H3.
    destruct H3 as [l1]. destruct H3 as [l2]. exists l1. exists l2. split. assumption.
    apply seq_split in H3. destruct H3. split. assumption. split. assumption.
    intros. apply H2. apply H3 in H5. lia.
Qed.

(*We define row echelon form on a particular subset of a matrix, to make it easier to use in inavariants.
  Here, we define row echelon form in the first r-1 rows of the matrix*)

Inductive gaussian_invariant: forall m n, matrix m n -> nat -> nat -> Prop :=
  | r_inv {m n : nat} (mx: matrix m n) ( r c : nat) :
    (*all rows of all zeroes are below the first r rows*)
    (forall x : nat, leading_coefficient (get_row mx x) n = None <-> (r<x)%nat) ->
    (*leading coefficients are strictly to the right of those in rows above*)
    (forall i j n1 n2 c1 c2, (i<j)%nat -> (j <= r)%nat ->
      leading_coefficient (get_row mx i) n = Some (c1, n1) ->
      leading_coefficient (get_row mx j) n = Some (c2, n2) ->
      (n1 < n2)%nat) ->
    (*for rows < r, leading coefficient occurs before column c*)
    (forall r' n1 c1, (r' < r)%nat ->
      leading_coefficient (get_row mx r') n = Some (c1, n1) ->
       (n1 < c)%nat) ->
    (*for the first c - 1 columns, each column with a leading coefficient has all other entries 0 *)
    (forall i c' n', leading_coefficient (get_row mx i) n = Some (c', n') ->
      (n' < c)%nat ->
      forall x, x <> i -> get mx x n' = T.zero) ->
    (*all rows >= r have zeroes in the first c-1 entries*)
    (forall r' c', (r' <= r)%nat -> (c' < c)%nat -> get mx r' c' = T.zero) ->
    gaussian_invariant m n mx r c.

   (* (

Inductive row_echelon_form_partial: forall m n, matrix m n -> nat -> Prop :=
  | r_ref: forall {m n} (mx: matrix m n) (r: nat),
    (*all rows of all zeroes are below the first r rows*)
    (forall x : nat, leading_coefficient (get_row mx x) = None <-> (r < x)%nat) ->
    (forall i j n1 n2 c1 c2, (i< j)%nat ->
      (j < r)%nat ->
      leading_coefficient (get_row mx i) = Some (c1, n1) ->
      leading_coefficient (get_row mx j) = Some (c2, n2) ->
      (n1 < n2)%nat) -> (*leading coefficients are strictly to the right of rows above*)
    row_echelon_form_partial m n mx r.

(*reduced row echelon form (without the leading coeff being one) - up to row r and column c*)
Inductive reduced_row_echelon_form_partial: forall m n, matrix m n -> nat -> nat -> Prop :=
  | r_rref: forall {m n} (mx: matrix m n) r c,
      row_echelon_form_partial m n mx r ->
     (* (forall i c n, (i<r)%nat -> leading_coefficient (get_row mx i) = Some (c, n) -> c = T.one) ->*) (*leading coeffs are 1*)
      (forall i c' n', leading_coefficient (get_row mx i) = Some (c', n') ->
          (n <c)%nat ->
          forall x, x <> i -> get mx x n = T.zero) -> (*column with leading coeff has all other entries o*)
      (forall r' c', (r <= r')%nat -> (c' < c)%nat -> get mx r' c' = T.zero) -> (*all rows >= r have zeroes
          in the first c-1 entries*)
      reduced_row_echelon_form_partial m n mx r c.*)

(*steps in gaussian elimination - have current row r, column c
  - all previous rows have leading coefficient at position < c (so not all zero)
  - r has leading coefficient at position c
  - all previous rows have zero entries in all positions <= c except at leading coeffs
  - all previous rows have leading coeffs in strictly increasing positions
  - all rows > r has zeroes in first c positions
  - These invariants will be preserved in the next iteration of the loop*)

(*steps: find row among r, r+1, ..., m with nonzero entry in column c
  - if no such row exists, then set c = c + 1 and continue
  - otherwise, let k be that row, swap rows k and r
    then, for every row that has a nonzero entry in column c, multiply the column by the inverse of entry at c
    then, subtract all rows with nonzero entry in column c from row r
    then, set r = r + 1 and c = c + 1, continue*)

(*TODO: go back and use this*)
Lemma inv_nonzero: forall a : A,
  a <> T.zero ->
  T.inv a <> T.zero.
Proof.
  intros. intro. assert (T.mult a (T.inv a) = T.one) by (field; assumption). 
  rewrite H0 in H1. assert (T.mult a T.zero = T.zero) by ring. rewrite H1 in H2.
  pose proof (F_1_neq_0 (T.Fth)). contradiction. 
Qed. 

(*wrong definition*)
(*
Definition find_nonzero_row {m n} (mx: matrix m n) (c: nat) : option nat :=
  match (leading_coefficient (get_column mx c) m) with
  | None => None
  | Some (c', n') => Some n'
  end.
*)

(*look for first nonzero entry in column c, starting at row r*)
Definition find_nonzero_row {m n} (mx: matrix m n) (c r: nat) : option nat :=
  match (leading_coefficient (sublist (Z.of_nat r) (Z.of_nat m) (get_column mx c)) (m-r)%nat) with
  | None => None
  | Some (c', n') => Some (n' + r)%nat
  end.


Definition  all_columns_one_aux {m n} (mx: matrix m n) (c: nat) (l: list nat) : matrix m n :=
  fold_right (fun x acc => let f := (get mx x c) in 
                             if (Aeq_dec f T.zero) then acc else (scalar_mul_row acc x (T.inv f))) mx l. 

Lemma all_columns_one_aux_row_equiv: forall {m n} (mx: matrix m n) c l,
  (forall x, In x l -> (x<m)%nat) ->
  row_equivalent m n mx (all_columns_one_aux mx c l).
Proof.
  intros. induction l. simpl. constructor. simpl.
  if_tac.
  - apply IHl. intuition.
  - eapply row_equivalent_trans. apply IHl. intuition. apply row_equivalent_ero.
    constructor. apply H. left. reflexivity. apply inv_nonzero. assumption.
Qed. 

Definition all_columns_one {m n} (mx: matrix m n) (c: nat) : matrix m n :=
  all_columns_one_aux mx c (seq 0 m).

Lemma all_columns_one_row_equiv: forall {m n} (mx: matrix m n) c,
  row_equivalent m n mx (all_columns_one mx c).
Proof.
  intros. unfold all_columns_one. apply all_columns_one_aux_row_equiv. intros.
  rewrite in_seq in H. lia.
Qed.

Definition subtract_all_rows_aux {m n} (mx: matrix m n) (r: nat) (c: nat) (l: list nat) :=
  fold_right (fun x acc => if (Nat.eq_dec x r) then acc else let f := (get mx x c) in
                            if (Aeq_dec f T.zero) then acc else (add_multiple acc r x T.one)) mx l.

Lemma subtract_all_rows_aux_row_equiv: forall {m n} (mx: matrix m n) r c l,
  (r<m)%nat ->
  (forall x, In x l -> (x<m)%nat) ->
  row_equivalent m n mx (subtract_all_rows_aux mx r c l).
Proof.
  intros. induction l.
  - simpl. constructor.
  - simpl. if_tac.
    + apply IHl. intuition.
    + if_tac.
      * apply IHl. intuition.
      * eapply row_equivalent_trans. apply IHl. intuition. apply row_equivalent_ero.
        constructor. assumption. apply H0. left. reflexivity. auto.
Qed.  

Definition subtract_all_rows {m n} (mx : matrix m n) (r c: nat) : matrix m n :=
  subtract_all_rows_aux mx r c (seq 0 m).

Lemma subtract_all_rows_row_equiv: forall {m n} (mx: matrix m n) r c,
  (r<m)%nat ->
  row_equivalent m n mx (subtract_all_rows mx r c).
Proof.
  intros. unfold subtract_all_rows. apply subtract_all_rows_aux_row_equiv.
  assumption. intros. rewrite in_seq in H0; lia.
Qed.

Definition gauss_one_step {m n} (mx: matrix m n) (r c : nat) : (matrix m n * nat * nat) :=
  match (find_nonzero_row mx c r) with
        | Some k =>
            let mx1 := swap_rows mx k r in
            let mx2 := all_columns_one mx1 c in
            let mx3 := subtract_all_rows mx2 k c in
            (mx3, (r+1)%nat, (c+1)%nat)
        | None => (mx, r, (c+1)%nat)
      end.

Definition get_matrix {m n} (t: matrix m n * nat * nat) : matrix m n :=
  match t with
  | (x, _, _) => x
  end.

Lemma gauss_one_step_row_equiv: forall {m n} (mx: matrix m n) r c,
  (r<m)%nat ->
  row_equivalent m n mx (get_matrix (gauss_one_step mx r c)).
Proof.
  intros. unfold gauss_one_step. destruct (find_nonzero_row mx c r) eqn : E.
  - simpl. eapply row_equivalent_trans. 2 : { apply subtract_all_rows_row_equiv.
    unfold find_nonzero_row in E. 
    destruct (leading_coefficient (sublist (Z.of_nat r) (Z.of_nat m) (get_column mx c)) (m - r)) eqn : F.
    destruct p. inversion E; subst. rewrite leading_coefficient_some_iff in F. destruct F.  lia.
    inversion E. }
    eapply row_equivalent_trans. 2 : { apply all_columns_one_row_equiv. }
    apply row_equivalent_ero. constructor. unfold find_nonzero_row in E.
    destruct (leading_coefficient (sublist (Z.of_nat r) (Z.of_nat m) (get_column mx c)) (m - r)) eqn : F.
    destruct p; inversion E; subst. rewrite leading_coefficient_some_iff in F.
    lia. inversion E. assumption.
  - simpl. constructor.
Qed.

Lemma gauss_one_step_invariant_preserved: forall {m n} (mx: matrix m n) r c,
  gaussian_invariant m n mx r c ->
   match (gauss_one_step mx r c) with
    |(m', r', c') => gaussian_invariant m n m' r' c'
   end.
Proof.
  intros. destruct (gauss_one_step mx r c) as [p c'] eqn : E.
  destruct p as [m' r']. unfold gauss_one_step in E.
  destruct (find_nonzero_row mx c) eqn : F.
  - admit.
  - unfold find_nonzero_row in F. inversion E; subst. inversion H; subst. 
    apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H0.
    apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H0. subst.
    constructor. apply H1.  apply H2. intros. eapply H3 in H5. lia. lia.
    intros.
    (*need to show that if n' = c, then leading coefficient has to appear in row >=r - by H3
      thus, we know that get m' i c = c' <> Zero, by r <= i < m, so appears in sublist, 
      contradicts fact that column gives none - do tomorrow*)
 clear H1. clear H2. clear H3. (* clear H7.*) (* H4*) assert (n' < c \/ n' = c)%nat by lia.
    destruct H1. eapply H4. apply H0. lia. assumption. 
    subst. rewrite leading_coefficient_some_iff in H0. destruct H0. destruct H1.
    destruct H2. unfold get_row in H2. destruct (lt_dec i m). 2 : {
    rewrite Znth_overflow in H2. unfold default in H2. subst. contradiction. list_solve. }
    rewrite prop_list_nat_Znth in H2. 2: lia. replace (Z.to_nat (Z.of_nat c)) with c in H2 by lia.
    (*now we know that get m; i c = c' and c' <> zero. By H7, i > r'. but then this contradicts 
      the fact that rows r' to m of column c are empty*)
    assert (i > r')%nat. 


  Search get_row.
    apply H3. 
    apply H1.

 unfold gaussian_invariant in *. 
Admitted.

Program Fixpoint gaussian_elim_aux {m n} (mx: matrix m n) (r: nat) (c: nat) {measure ((m- r) + (n-c))} : matrix m n :=
  if (lt_dec r m) then 
    if (lt_dec c n) then
      match (find_nonzero_row mx r c) with
        | Some k =>
            let mx1 := swap_rows mx k r in
            let mx2 := all_columns_one mx c in
            let mx3 := subtract_all_rows mx k in
            gaussian_elim_aux mx3 (r+1)%nat (c+1)%nat
        | None => gaussian_elim_aux mx r (c+1)%nat
      end
    else mx
  else mx.

 
  
  fold_right (fun x acc => if Aeq_dec x T.zero then acc else Some


End MatrixFacts.