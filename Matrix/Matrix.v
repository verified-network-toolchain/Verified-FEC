Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.setoid_ring.Field_theory.
Require Import VST.floyd.functional_base.
Require Import PropList.
Require Import Field.

(*pairwise operations over lists - TODO maybe move*)
Fixpoint combine {X Y Z: Type} (l1 : list X) (l2: list Y) (f: X -> Y -> Z) : list Z :=
  match (l1, l2) with
  | (h1 :: t1, h2 :: t2) => f h1 h2 :: combine t1 t2 f
  | (_, _) => nil
  end.

Lemma combine_Zlength: forall {X Y Z} l1 l2 (f : X -> Y -> Z),
  Zlength l1 = Zlength l2 ->
  Zlength (combine l1 l2 f) = Zlength l1.
Proof.
  intros X Y Z l1. induction l1; intros.
  - list_solve.
  - rewrite Zlength_cons in H. destruct l2. list_solve. rewrite Zlength_cons in H.
    apply Z.succ_inj in H. simpl. rewrite Zlength_cons. rewrite IHl1. list_solve. assumption.
Qed.

Lemma combine_Znth: forall {X Y Z} `{Inhabitant X} `{Inhabitant Y} `{Inhabitant Z} l1 l2 (f: X -> Y -> Z) z,
  Zlength l1 = Zlength l2 ->
  0 <= z < Zlength l1 ->
  Znth z (combine l1 l2 f) = f (Znth z l1) (Znth z l2).
Proof.
  intros X Y Z I1 I2 I3 l1. induction l1; intros.
  - list_solve.
  - destruct l2. list_solve. assert (Zlength l1 = Zlength l2) by list_solve. clear H.
    assert (z = 0 \/ 0 < z) by lia. destruct H.
    + subst. simpl. repeat (rewrite Znth_0_cons). reflexivity.
    + simpl. repeat (rewrite Znth_pos_cons). apply IHl1. assumption. rewrite Zlength_cons in H0. all: lia.
Qed.

(*Sequences of positive integers - TODO: move to separate file*)
Definition Zseq (x len : Z) :=
  map (fun y => Z.of_nat y) (seq (Z.to_nat x) (Z.to_nat len)).

Lemma Zseq_Zlength: forall x len,
  (0<=x) ->
  (0<= len) ->
  Zlength (Zseq x len) = len.
Proof.
  intros. unfold Zseq. rewrite Zlength_map. rewrite Helper.Zlength_seq. lia.
Qed.

Lemma Zseq_In: forall x len z,
  (0 <= x) ->
  (0 <= len) ->
  In z (Zseq x len) <-> (x <= z < x + len).
Proof.
  intros. unfold Zseq. split; intros. rewrite in_map_iff in H1.
  destruct H1. destruct H1. rewrite in_seq in H2. lia.
  rewrite in_map_iff. exists (Z.to_nat z). split. lia.
  rewrite in_seq. lia.
Qed.

(*TODO move: We only know that if f is injective and NoDup l, then NoDup (map f l). But this is too strong,
  we only want to require that f is injective on elements of l*)
Lemma NoDup_map_restricted: forall {A B: Type} (f: A -> B) (l: list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l ->
  NoDup (map f l).
Proof.
  intros. induction H0.
  - simpl. constructor.
  - simpl. constructor. intro. rewrite in_map_iff in H2.
    destruct H2. destruct H2. assert ( x = x0). apply H. left. reflexivity.
    right. assumption. rewrite H2. reflexivity. subst. contradiction.
    apply IHNoDup. intros. apply H. right. assumption. right. assumption. assumption.
Qed.

Lemma Zseq_NoDup: forall x len,
  (0 <= x) ->
  (0 <= len) ->
  NoDup (Zseq x len).
Proof.
  intros. unfold Zseq. apply NoDup_map_restricted. intros.
  rewrite in_seq in H1. rewrite in_seq in H2. lia.
  apply seq_NoDup.
Qed.

(*Result about NoDup - TODO: Move*)
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

(*A similar lemma for when we have 2 elements in a list with no duplicates. Not sure how to avoid this repetition*)
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

(*Matrices*)

Section MatrixDef.

(*matrices are defined over arbitrary rings*)
Context {A: Type} {plus : A -> A -> A} {mult: A -> A -> A} {sub: A -> A -> A} {opp: A -> A} {zero: A} {one: A}
  (Rth: @ring_theory A zero one plus mult sub opp eq).
(*
Variable {A : Type}.
Variable plus : A -> A -> A.
Variable mult: A -> A -> A.
Variable sub: A -> A -> A.
Variable opp: A -> A.
Variable zero: A.
Variable one: A.
Variable Rth: 
*)
Add Ring r : Rth.

Instance default : `{Inhabitant A}.
apply zero.
Defined.

Definition matrix := list (list A).

Definition wf_matrix (mx: matrix) (m n : Z) :=
  Zlength mx = m /\ forall x, In x mx -> Zlength x = n.

(*get the (i,j)th entry of a matrix*)
Definition get (mx: matrix) (i j : Z) :=
  let row := Znth i mx in
  Znth j row.

Lemma matrix_equiv: forall (m1 m2: matrix) (m n: Z),
  wf_matrix m1 m n ->
  wf_matrix m2 m n ->
  m1 = m2 <-> forall i j, (0 <= i<m) -> (0 <= j<n) -> get m1 i j = get m2 i j.
Proof.
  intros. unfold wf_matrix in *. destruct H. destruct H0. split; intros.
  - subst. reflexivity.
  - apply Znth_eq_ext. subst. rewrite H0. reflexivity.
    intros. apply Znth_eq_ext. rewrite H1. rewrite H2. reflexivity.
    all: try (apply Znth_In; list_solve). intros.
    unfold get in H3. apply H3. list_solve. rewrite H1 in H5. list_solve.
    apply Znth_In; list_solve.
Qed.

(*create a m x n matrix with entries given by a function*)
Definition mk_matrix (m n : Z) (f: Z -> Z -> A) :=
  prop_list (fun i => (prop_list (fun j => f i j) n)) m.

Lemma mk_matrix_wf: forall m n f, (0 <= m) -> (0<= n) -> wf_matrix (mk_matrix m n f) m n.
Proof.
  intros. unfold wf_matrix. unfold mk_matrix. split. rewrite prop_list_length. reflexivity. assumption.
  intros. rewrite In_Znth_iff in H1. destruct H1. destruct H1.
  rewrite prop_list_Znth in H2. subst. rewrite prop_list_length. reflexivity. assumption.
  rewrite prop_list_length in H1. lia. assumption.
Qed.

Lemma mk_matrix_spec: forall m n f i j,
  (0 <= i< m) ->
  (0 <= j< n) ->
  get (mk_matrix m n f) i j = f i j.
Proof.
  intros. unfold mk_matrix. unfold get. rewrite prop_list_Znth. 2 : assumption.
  rewrite prop_list_Znth. reflexivity. assumption.
Qed.

(*because we have [mk_matrix] and [matrix_equiv], we can define all matrix operations in terms of mk_matrix; any 
  other implementatoin must then be equal*)

(*row operations*)

(*1. multiply row r by scalar k *)
Definition scalar_mul_row (mx: matrix) (r: Z) (k: A) : matrix :=
  let old_row := Znth r mx in
  let new_row := map (fun x => mult k x) old_row in
  upd_Znth r mx new_row. 

Lemma scalar_mul_row_wf: forall mx m n r k,
  (0 <= m) ->
  (0 <= n) ->
  wf_matrix mx m n ->
  wf_matrix (scalar_mul_row mx r k) m n.
Proof.
  intros. unfold scalar_mul_row. unfold wf_matrix in *. destruct H1.
  split. list_solve. intros. rewrite In_Znth_iff in H3. destruct H3 as [i].
  destruct H3. 
  assert ((( 0 > r) \/ r >= m) \/ (0 <= r < m)) by lia. destruct H5.
  - rewrite upd_Znth_out_of_range in H4. 2 : list_solve. subst. apply H2.
    apply Znth_In. list_solve.
  - erewrite upd_Znth_lookup' in H4. 2 : apply H1. destruct (zeq i r).
    subst. rewrite Zlength_map. apply H2. apply Znth_In. list_solve.
    subst. apply H2. apply Znth_In. list_solve. list_solve.  lia.
Qed. 

Lemma scalar_mul_row_spec: forall mx m n r k i j,
  wf_matrix mx m n ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  (0 <= r < m) ->
  get (scalar_mul_row mx r k) i j =
    if (Z.eq_dec i r) then  mult k (get mx i j) else get mx i j.
Proof.
  intros. unfold scalar_mul_row. unfold get. destruct (Z.eq_dec i r).
  - subst. rewrite upd_Znth_same. rewrite Znth_map. reflexivity. unfold wf_matrix in H. destruct H.
    rewrite H3. assumption. apply Znth_In. list_solve. unfold wf_matrix in H. list_solve.
  - unfold wf_matrix in H. destruct H. rewrite upd_Znth_diff. reflexivity. list_solve. list_solve. assumption.
Qed.

(*2. swap rows r1 and r2*)
Definition swap_rows (mx: matrix) (r1 r2 : Z) : matrix :=
  let old1 := Znth r1 mx in
  let old2 := Znth r2 mx in
  upd_Znth r2 (upd_Znth r1 mx old2) old1.

Lemma swap_rows_wf: forall mx m n r1 r2,
  (0 <= n) ->
  (0 <= r1 < m) ->
  (0 <= r2 < m) ->
  wf_matrix mx m n ->
  wf_matrix (swap_rows mx r1 r2) m n.
Proof.
  intros. unfold wf_matrix in *. destruct H2. unfold swap_rows.
  split. list_solve. intros.
  rewrite In_Znth_iff in H4. destruct H4 as [i].
  destruct H4.
  erewrite upd_Znth_lookup' in H5. 4 : apply H1.
  2 : list_solve. 2 : list_solve. destruct (zeq i r2).
  - subst. apply H3. apply Znth_In. assumption.
  - erewrite upd_Znth_lookup' in H5. 2 : apply H2.
    2 : list_solve. 2 : assumption. destruct (zeq i r1).
    + subst. apply H3. apply Znth_In. assumption.
    + subst. apply H3. apply Znth_In. list_solve.
Qed.

Lemma swap_rows_spec: forall (mx: matrix) m n r1 r2 i j,
  wf_matrix mx m n ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  (0 <= r1 < m) ->
  (0 <= r2 < m) ->
  get (swap_rows mx r1 r2) i j =
    if (Z.eq_dec i r1) then get mx r2 j
    else if (Z.eq_dec i r2) then get mx r1 j
    else get mx i j.
Proof.
  intros. unfold wf_matrix in H. destruct H. unfold swap_rows. unfold get. destruct (Z.eq_dec i r2).
  - subst. rewrite upd_Znth_same.  2: list_solve. if_tac. subst. reflexivity. reflexivity.
  - rewrite upd_Znth_diff. 2 : list_solve. 2 : list_solve. 2 : assumption.
    destruct (Z.eq_dec i r1).
    + subst. list_solve.
    + list_solve.
Qed.

(*3. row r2 = row r2 + k * row r1*)
Definition add_multiple (mx: matrix) (r1 r2 : Z) (k : A) : matrix :=
  upd_Znth r2 mx (combine (Znth r2 mx) (Znth r1 mx) (fun x y => plus x (mult k y))).

Lemma add_multiple_wf: forall mx m n r1 r2 k,
  wf_matrix mx m n ->
  (0 <= n) ->
  (0 <= r1 < m) ->
  (0 <= r2 < m) ->
  wf_matrix (add_multiple mx r1 r2 k) m n.
Proof.
  intros. unfold wf_matrix in *. unfold add_multiple.
  split. list_solve. intros. rewrite In_Znth_iff in H3. destruct H3 as [i].
  destruct H3. destruct (Z.eq_dec i r2).
  - subst. rewrite upd_Znth_same. rewrite combine_Zlength. apply H. apply Znth_In.
    list_solve. destruct H. rewrite H4. rewrite H4. reflexivity.
    all: try(apply Znth_In; list_solve). list_solve.
  - subst. rewrite upd_Znth_diff. destruct H. rewrite H4. reflexivity. apply Znth_In.
    4 : assumption. all: list_solve.
Qed.

Lemma add_multiple_spec: forall (mx: matrix) m n r1 r2 k i j,
  wf_matrix mx m n ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  (0 <= r1 < m) ->
  (0 <= r2 < m) ->
  get (add_multiple mx r1 r2 k) i j =
    if (Z.eq_dec i r2) then plus (get mx r2 j) (mult k (get mx r1 j))
    else get mx i j.
Proof.
  intros. unfold get. unfold add_multiple. unfold wf_matrix in H.
  destruct H. destruct (zeq i r2).
  - subst. rewrite upd_Znth_same. 2: assumption. rewrite combine_Znth.
    if_tac. reflexivity. contradiction. rewrite H4. rewrite H4. reflexivity.
    3: rewrite H4. 3 : assumption. all: apply Znth_In; list_solve.
  - rewrite upd_Znth_diff. if_tac. contradiction. reflexivity. list_solve.
    list_solve. assumption.
Qed.


(*Generalized summations over rings - TODO: maybe move*)
Section Sum.

Definition summation_aux (f: Z -> A) (l: list Z) :=
  fold_right (fun n acc => plus (f n) acc) zero l.

Definition summation (f : Z -> A) (lb len : Z) : A :=
  summation_aux f (Zseq lb len).



Lemma summation_aux_scalar_mult: forall f l x,
  mult (summation_aux f l) x = summation_aux (fun y => mult (f y) x) l.
Proof.
  intros. induction l.
  - simpl. ring.
  - simpl. ring_simplify. rewrite IHl. reflexivity.
Qed.

Lemma summation_scalar_mult: forall f lb len x,
  mult (summation f lb len) x = summation (fun y => mult (f y) x) lb len.
Proof.
  intros. unfold summation. apply summation_aux_scalar_mult.
Qed.

(*sum a_i + b_i = sum a_i + sum b_i*)
Lemma summation_aux_distr_sum: forall f g l,
  summation_aux (fun i => plus (f i) (g i)) l =
  plus (summation_aux (fun i => f i) l)
        (summation_aux (fun i => g i) l).
Proof.
  intros. induction l. 
  - simpl. ring.
  - simpl. rewrite IHl. ring.
Qed.

(*sum_i sum_j a_{ij} = sum_j sum_i a_{ij} (for finite sums) *)
Lemma summation_aux_change_order: forall (f: Z -> Z -> A) l1 l2,
  summation_aux (fun i => summation_aux (fun j => f i j) l1) l2 = 
  summation_aux (fun j => summation_aux (fun i => f i j) l2) l1.
Proof.
  intros. revert l2. revert f. induction l1; intros.
  - simpl. induction l2. reflexivity. simpl. rewrite IHl2. ring.
  - simpl. rewrite summation_aux_distr_sum. rewrite IHl1. reflexivity.
Qed.

Lemma summation_aux_app: forall f l1 l2,
  summation_aux f (l1 ++ l2) =
  plus (summation_aux f l1) (summation_aux f l2).
Proof.
  intros. induction l1.
  - simpl. ring.
  - simpl. rewrite IHl1. ring.
Qed.

End Sum.

(*Matrix Multiplication*)
Section MatrixMult.

Definition mx_mult (mx : matrix) (mx' : matrix) m n p :=
  mk_matrix m p (fun i j => summation (fun k => mult (get mx i k) (get mx' k j)) 0 n).

Lemma mx_mult_wf: forall mx mx' m n p,
  (0<= m) ->
  (0 <= p) ->
  wf_matrix (mx_mult mx mx' m n p) m p.
Proof.
  intros. apply mk_matrix_wf; assumption.
Qed.

Lemma mx_mult_spec: forall mx mx' m n p i j,
  (0 <= i < m) ->
  (0 <= j < p) ->
  get (mx_mult mx mx' m n p) i j = summation (fun k => mult (get mx i k) (get mx' k j)) 0 n.
Proof.
  intros. unfold mx_mult. rewrite mk_matrix_spec. reflexivity. all: lia.
Qed.

(*key property - matrix multiplication is associative*)
Lemma mx_mult_assoc: forall m1 m2 m3 m n p l,
  wf_matrix m1 m n ->
  wf_matrix m2 n l ->
  wf_matrix m3 l p ->
  (0 <= m) ->
  (0 <= n) ->
  (0 <= p) ->
  (0 <= l) ->
  mx_mult (mx_mult m1 m2 m n l) m3 m l p = mx_mult m1 (mx_mult m2 m3 n l p) m n p.
Proof.
  intros. rewrite matrix_equiv. 2 : apply mx_mult_wf. 4 : apply mx_mult_wf. all: try assumption. intros.
  rewrite? mx_mult_spec; try lia. (*cannot expand inner automatically bc we need to know bounds*)
  unfold summation.
  assert(forall l1 : list Z,
    (forall x, In x l1 -> (0 <= x < l)) ->
    summation_aux (fun k : Z => mult (get (mx_mult m1 m2 m n l) i k) (get m3 k j)) l1 =
    summation_aux (fun k : Z => mult (summation (fun y => mult (get m1 i y) (get m2 y k)) 0 n) (get m3 k j)) l1). {
  intros. induction l1. simpl. reflexivity. simpl. 
  rewrite mx_mult_spec. rewrite IHl1. reflexivity. intros. apply H8. right. assumption.  lia.
  apply H8. left. reflexivity.  }
  (*the same for the other side*)
  assert(forall l1: list Z,
    (forall x, In x l1 -> (0 <= x < n)) ->
    summation_aux (fun k : Z => mult (get m1 i k) (get (mx_mult m2 m3 n l p) k j)) l1 =
    summation_aux (fun k : Z => mult (get m1 i k) ((summation (fun y => mult (get m2 k y) (get m3 y j)) 0 l))) l1). {
  intros. induction l1. reflexivity. simpl. rewrite mx_mult_spec. rewrite IHl1. reflexivity.
  intros. apply H9. right. assumption. apply H9. left. reflexivity. lia.  }
  rewrite H8. rewrite H9. 
  (*now rewrite the inner sum*)
  assert ((fun k : Z => mult (summation (fun y : Z => mult (get m1 i y) (get m2 y k)) 0 n) (get m3 k j)) =
  (fun k : Z => summation (fun y : Z => mult (mult (get m1 i y) (get m2 y k)) (get m3 k j)) 0 n)). {
  apply functional_extensionality. intros. rewrite summation_scalar_mult. reflexivity. }
  rewrite H10.
  assert ((fun k : Z => mult (get m1 i k) (summation (fun y : Z => mult (get m2 k y) (get m3 y j)) 0 l)) =
    (fun k : Z => (summation (fun y : Z => mult (mult (get m1 i k) (get m2 k y)) (get m3 y j)) 0 l))). {
  apply functional_extensionality. intros.  assert (forall x y, mult x y = mult y x) by (intros; ring).
  rewrite H11. 
  rewrite summation_scalar_mult. 
  f_equal. apply functional_extensionality. intros. ring. } rewrite H11.
  unfold summation. rewrite (summation_aux_change_order 
  (fun k y => mult (mult (get m1 i y) (get m2 y k)) (get m3 k j))). reflexivity.
  intros. rewrite Zseq_In in H10. lia. lia. lia. intros. rewrite Zseq_In in H10.
  lia. lia. lia.
Qed.

End MatrixMult.


(*The identity matrix and proofs*)
Section Identity.

(*The identity matrix*)
Definition identity (n: Z) : matrix :=
  mk_matrix n n (fun i j => if Z.eq_dec i j then one else zero).

Lemma identity_wf: forall n,
  (0<=n) ->
  wf_matrix (identity n) n n.
Proof.
  intros. unfold identity. apply mk_matrix_wf; assumption. 
Qed.

Lemma identity_spec: forall n i j,
  (0 <= i < n) ->
  (0 <= j < n) ->
  get (identity n) i j = if Z.eq_dec i j then one else zero.
Proof.
  intros. unfold identity. rewrite mk_matrix_spec; try lia.
  reflexivity.
Qed.

Lemma summation_identity_notin_r: forall f l j,
  ~In j l ->
   summation_aux (fun k => mult (f k) (if Z.eq_dec k j then one else zero)) l = zero.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. if_tac. exfalso. apply H. left. assumption.
    rewrite IHl. ring. intuition.
Qed.

Lemma summation_identity_notin_l: forall f l j,
  ~In j l ->
   summation_aux (fun k => mult (if Z.eq_dec j k then one else zero) (f k)) l = zero.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. if_tac. exfalso. apply H. left. auto. 
    rewrite IHl. ring. intuition.
Qed.

Lemma summation_identity_in_once_r: forall f l j,
  (exists l1 l2, l = l1 ++ j :: l2 /\ ~In j l1 /\ ~In j l2) ->
  summation_aux (fun k => mult (f k) (if Z.eq_dec k j then one else zero)) l = f j.
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
  summation_aux (fun k => mult (if Z.eq_dec j k then one else zero) (f k)) l = f j.
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

Lemma Zseq_bounds_split: forall lb len j,
  (0 <= lb) ->
  (0 <= len) ->
  (lb <= j) ->
  (j < lb + len) ->
  exists l1 l2, Zseq lb len = l1 ++ j :: l2 /\ ~In j l1 /\ ~In j l2.
Proof.
  intros. apply noDup_in_split. rewrite Zseq_In; lia. apply Zseq_NoDup; lia.
Qed.

(*The most important property of identity matrices*)
Lemma mx_mult_I_r: forall mx m n,
  wf_matrix mx m n ->
  (0<= m) ->
  (0 <= n) ->
  mx_mult mx (identity n) m n n = mx.
Proof.
  intros. rewrite matrix_equiv. 3 : apply H. 2 : { apply mx_mult_wf; assumption. } intros.
  rewrite mx_mult_spec; try lia. unfold summation.
  assert(forall l,
    (forall x, In x l -> (0 <= x < n)) ->
    summation_aux (fun k : Z => mult (get mx i k) (get (identity n) k j)) l =
    summation_aux (fun k : Z => mult (get mx i k) (if Z.eq_dec k j then one else zero)) l). {
  intros. induction l. reflexivity. simpl. unfold identity at 1. rewrite mk_matrix_spec. rewrite IHl.
  reflexivity. intros. apply H4. right. assumption. 2 : lia.  apply H4. left. reflexivity. }
  rewrite H4. rewrite summation_identity_in_once_r. reflexivity.
  apply Zseq_bounds_split. all: try lia. intros. rewrite Zseq_In in H5; lia.
Qed.

Lemma mx_mult_I_l: forall mx m n,
  wf_matrix mx m n ->
  (0 <= m) ->
  (0 <= n) ->
  mx_mult (identity m) mx m m n = mx.
Proof.
  intros. rewrite matrix_equiv. 3: apply H. 2 : apply mx_mult_wf; assumption. intros.
  rewrite mx_mult_spec; try lia. unfold summation.
  assert(forall l,
    (forall x, In x l -> (0 <= x < m)) ->
    summation_aux (fun k : Z => mult (get (identity m) i k) (get mx k j)) l =
    summation_aux (fun k : Z => mult (if Z.eq_dec i k then one else zero)  (get mx k j)) l). {
  intros. induction l. reflexivity. simpl. unfold identity at 1. rewrite mk_matrix_spec. rewrite IHl.
  reflexivity. intros. apply H4. right. assumption. assumption. apply H4. left. reflexivity.  }
  rewrite H4. rewrite summation_identity_in_once_l. reflexivity.
  apply Zseq_bounds_split; try lia. intros. rewrite Zseq_In in H5; lia.
Qed.

End Identity.

(*Inverses and invertibility (basic definitions)*)

Section Inverse.

(* (square matrix ) m has left and right inverse m'*)
Definition inverse (m m' : matrix) n :=
  mx_mult m m' n n n = identity n /\ mx_mult m' m n n n = identity n.

Definition invertible (mx: matrix) n :=
  exists mx', wf_matrix mx' n n /\ inverse mx mx' n.

Lemma inverse_unique: forall (a b c : matrix) n,
  wf_matrix a n n ->
  wf_matrix b n n ->
  wf_matrix c n n ->  
  (0<= n) ->
  inverse a b n ->
  inverse a c n ->
  b = c.
Proof.
  intros. unfold inverse in *. destruct H3. destruct H4. 
  pose proof (mx_mult_I_r b _ _ H0 H2 H2). rewrite <- H4 in H7.
  rewrite <- mx_mult_assoc in H7; try assumption. rewrite H5 in H7. rewrite mx_mult_I_l in H7; try assumption.
  subst. reflexivity.
Qed.

Lemma identity_inv: forall n,
  (0<= n) ->
  inverse (identity n) (identity n) n.
Proof.
  intros. unfold inverse. split. all: apply mx_mult_I_r. all: try assumption.
  all: apply identity_wf; assumption.
Qed.

Lemma identity_invertible: forall n,
  (0<= n) ->
  invertible (identity n) n.
Proof.
  intros. unfold invertible. exists (identity n). split. apply identity_wf. assumption. apply identity_inv. assumption.
Qed.

(*(AB)^-1 = B^-1A^-1*)
Lemma inverse_of_product : forall (a a' b b' : matrix) n,
  wf_matrix a n n ->
  wf_matrix b n n ->
  wf_matrix a' n n ->
  wf_matrix b' n n ->
  (0<= n) ->
  inverse a a' n ->
  inverse b b' n ->
  inverse (mx_mult a b n n n) (mx_mult b' a' n n n) n.
Proof.
  intros. unfold inverse in *. destruct H4. destruct H5. 
  split. rewrite <- mx_mult_assoc; try assumption. rewrite (mx_mult_assoc a); try assumption. rewrite H5.
  rewrite mx_mult_I_r. assumption. all: try assumption.
  apply mx_mult_wf; assumption.
  rewrite <- mx_mult_assoc; try assumption. rewrite (mx_mult_assoc b'); try assumption. rewrite H6. 
  rewrite mx_mult_I_r. assumption. all: try assumption. apply mx_mult_wf; assumption.
Qed.

Lemma product_invertible: forall a b n,
  wf_matrix a n n ->
  wf_matrix b n n ->
  (0<= n) ->
  invertible a n ->
  invertible b n ->
  invertible (mx_mult a b n n n) n.
Proof.
  intros. unfold invertible in *. destruct H2 as [a'].
  destruct H3 as [b']. exists (mx_mult b' a' n n n). split. apply mx_mult_wf; assumption.
  destruct H2. destruct H3.
  apply inverse_of_product; assumption.
Qed.

End Inverse.

(*Elementary Matrices*)

(*We require the underlying type to be a field (needed to show existence of inverse for
  scalar multiplication) *)
Context {div : A -> A -> A} {inv: A -> A} (Fth: field_theory zero one plus mult sub opp div inv eq).

Add Field fld : Fth.

Lemma inv_nonzero: forall a : A,
  a <> zero ->
  inv a <> zero.
Proof.
  intros. intro. assert (mult a (inv a) = one) by (field; assumption). 
  rewrite H0 in H1. assert (mult a zero = zero) by ring. rewrite H1 in H2.
  pose proof (F_1_neq_0 (Fth)). contradiction. 
Qed. 

Section ElemMx.

(*1. Row swap matrix - swap rows i and j*)
Definition row_swap_mx n i j : matrix :=
  swap_rows (identity n) i j.

Lemma row_swap_mx_wf: forall n i j,
  (0 <= i < n) ->
  (0 <= j < n) ->
  wf_matrix (row_swap_mx n i j) n n.
Proof.
  intros. unfold row_swap_mx. apply swap_rows_wf; try lia. apply identity_wf; lia.
Qed.

(*Prove the row operation [swap_rows] is equivalent to multiplying by elementary matrix*)
Lemma swap_rows_elem_mx: forall mx m n i j,
  wf_matrix mx m n ->
  (0 <= n) ->
  (0 <= i < m) ->
  (0 <= j < m) ->
  swap_rows mx i j = mx_mult (row_swap_mx m i j) mx m m n.
Proof.
  intros. rewrite matrix_equiv. 2 : { apply swap_rows_wf. 4 : apply H. all: lia. }
  2 : { apply mx_mult_wf; try assumption. lia. } intros.
  erewrite swap_rows_spec; try lia. 2 : apply H. all: try lia.
  rewrite mx_mult_spec; try lia.
  unfold row_swap_mx. 
  unfold summation. assert (forall l,
    (forall x, In x l -> (0 <= x<m)) ->
    summation_aux (fun k : Z => mult (get (swap_rows (identity m) i j) i0 k) (get mx k j0)) l =
    summation_aux (fun k : Z => mult (if Z.eq_dec i0 i 
              then if Z.eq_dec j k then one else zero
            else if Z.eq_dec i0 j
              then if Z.eq_dec i k then one else zero
            else if Z.eq_dec i0 k then one else zero) (get mx k j0)) l). {
    intros. induction l. reflexivity.
    simpl. erewrite swap_rows_spec. 2 : apply identity_wf. rewrite? identity_spec. rewrite IHl. reflexivity.
    intros. apply H5. right. assumption.
    all: try lia. all: apply H5; left; reflexivity. } rewrite H5. clear H5.
    2 : { intros. rewrite Zseq_In in H6; lia. }
  if_tac.
  - subst. rewrite summation_identity_in_once_l. reflexivity.
    apply Zseq_bounds_split; lia.
  - if_tac.
    + rewrite summation_identity_in_once_l. reflexivity. apply Zseq_bounds_split; lia.
    + rewrite summation_identity_in_once_l. reflexivity. apply Zseq_bounds_split; lia.
Qed.

Lemma swap_sym: forall mx m n i j,
  wf_matrix mx m n ->
  (0<= n) ->
  (0 <= i < m) ->
  (0 <= j < m) ->
  swap_rows mx i j = swap_rows mx j i.
Proof.
  intros. rewrite matrix_equiv. 2 : apply swap_rows_wf. 5 : apply H. all: try lia.
  2 : apply swap_rows_wf; try assumption. intros.
  erewrite swap_rows_spec. 2 : apply H. all: try assumption.
  erewrite swap_rows_spec. 2 : apply H. all: try assumption.
  if_tac. subst.  if_tac; subst; try reflexivity.
  reflexivity.
Qed. 

Lemma swap_twice: forall (mx: matrix) m n r1 r2,
  wf_matrix mx m n ->
  (0 <= n) ->
  (0 <= r1 < m) ->
  (0 <= r2 < m) ->
  swap_rows (swap_rows mx r1 r2) r2 r1 = mx.
Proof.
  intros. rewrite matrix_equiv. 3 : apply H. 2 : apply swap_rows_wf; try assumption.
  2 : apply swap_rows_wf; assumption. intros.
  rewrite? (swap_rows_spec _ m n); try lia. all: try apply H. if_tac.
  - subst. if_tac. reflexivity. contradiction. 
  - if_tac. subst. if_tac. subst. contradiction. if_tac. reflexivity. contradiction. reflexivity.
  - apply swap_rows_wf; assumption.
Qed. 

(*The swap matrix is invertible, and, moreover, it is its own inverse*)
Lemma row_swap_mx_inv: forall n i j,
  (0 <= i < n) ->
  (0 <= j < n) ->
  inverse (row_swap_mx n i j) (row_swap_mx n i j) n.
Proof.
  intros. unfold inverse. rewrite <- swap_rows_elem_mx.
  unfold row_swap_mx. rewrite (swap_sym _ n n). split; apply (swap_twice _ n n). all: try lia.
  all: try (apply identity_wf; lia). apply swap_rows_wf; try assumption.
  lia. apply identity_wf; lia. apply row_swap_mx_wf; lia.
Qed.

(*2. scalar multiplication*)
Definition scalar_mult_mx n i k :=
  scalar_mul_row (identity n) i k.

Lemma scalar_mult_mx_wf: forall n i k,
  (0 <=n) ->
  wf_matrix (scalar_mult_mx n i k) n n.
Proof.
  intros. unfold scalar_mult_mx. apply scalar_mul_row_wf; try assumption.
  apply identity_wf; assumption.
Qed.

(*equivalence between row operation and multiplication by elementary matrix*)
Lemma scalar_mult_elem: forall (mx: matrix) m n i k,
  wf_matrix mx m n ->
  (0 <= n) ->
  (0 <= i < m) ->
  scalar_mul_row mx i k = mx_mult (scalar_mult_mx m i k) mx m m n.
Proof.
  intros. rewrite (matrix_equiv _ _ m n). 2 : apply scalar_mul_row_wf; try lia; assumption.
  2 : apply mx_mult_wf; lia. intros. rewrite (scalar_mul_row_spec _ m n); try lia.
  rewrite (mx_mult_spec); try lia. unfold scalar_mult_mx. unfold summation.
  assert (forall l,
    (forall x, In x l -> (0 <= x < m)) ->
    summation_aux (fun y : Z => mult (get (scalar_mul_row (identity m) i k) i0 y) (get mx y j)) l =
    summation_aux (fun y : Z => mult (if Z.eq_dec i0 i then if Z.eq_dec y i then k else zero
                                            else if Z.eq_dec i0 y then one else zero) (get mx y j)) l). {
  intros. induction l. reflexivity.
  simpl. rewrite (scalar_mul_row_spec _ m m). rewrite identity_spec. rewrite IHl. f_equal.
  if_tac. subst. if_tac. subst. if_tac. ring. contradiction. if_tac. subst. contradiction.
  ring. reflexivity. intros. apply H4. right. assumption. all: try lia. 2 : apply identity_wf; lia.
  all: apply H4; left; reflexivity. } rewrite H4. clear H4.
  if_tac.
  - subst. assert ((fun y : Z => mult (if Z.eq_dec y i then k else zero) (get mx y j)) =
    (fun y : Z => mult (mult (if Z.eq_dec i y then one else zero) (get mx y j)) k)). {
   apply functional_extensionality. intros. if_tac; try(if_tac); try(subst; contradiction); ring.  } 
   rewrite H4. clear H4.
   rewrite <- summation_aux_scalar_mult. 
   rewrite summation_identity_in_once_l. ring. apply Zseq_bounds_split; lia.
  - rewrite summation_identity_in_once_l. reflexivity. apply Zseq_bounds_split; lia.
  - intros. rewrite Zseq_In in H5; lia.
  - assumption.
Qed.

(*inverse of scalar mult matrix is just scalar mult matrix for 1/c*)
Lemma scalar_mult_inv: forall n i c,
  (0 <= i < n) ->
  (c <> zero) ->
  inverse (scalar_mult_mx n i c) (scalar_mult_mx n i (inv c)) n.
Proof.
  intros. unfold inverse.
  assert (forall x, x <> zero ->
  mx_mult (scalar_mult_mx n i x) (scalar_mult_mx n i (inv x)) n n n = identity n). { intros.
  rewrite <- scalar_mult_elem. unfold scalar_mult_mx. rewrite (matrix_equiv _ _ n n).
  intros. rewrite (scalar_mul_row_spec _ n n); try lia. rewrite (scalar_mul_row_spec _ n n); try lia.
  if_tac. subst. field. assumption. reflexivity. 2 : apply scalar_mul_row_wf; try lia.
  all: try (apply identity_wf; lia). apply scalar_mul_row_wf; try lia. apply scalar_mul_row_wf; try lia.
  apply identity_wf; try lia. apply scalar_mult_mx_wf; lia. all: lia. }
  split. rewrite H1. reflexivity. assumption.
  assert (c = inv (inv c)). field. split. assumption. apply (F_1_neq_0 (Fth)).
  rewrite H2 at 2. apply H1. apply inv_nonzero. assumption.
Qed.

(*3. add multiple of row to another row*)

(*this one is harder, since in the multiplication we have exactly 2 nonzero entries, so we need lemmas
  to reason about this*)

Definition add_multiple_mx n r1 r2 c :=
  add_multiple (identity n) r1 r2 c.

Lemma add_multiple_mx_wf: forall n r1 r2 c,
  (0 <= r1 < n) ->
  (0 <= r2 < n) ->
  wf_matrix (add_multiple_mx n r1 r2 c) n n.
Proof.
  intros. unfold add_multiple_mx. apply add_multiple_wf; try lia.
  apply identity_wf; lia.
Qed.

Lemma add_multiple_mx_spec: forall n r1 r2 c i j,
  (0 <= r1 < n) ->
  (0 <= r2 < n) ->
  (0 <= i < n) ->
  (0 <= j < n) ->
  r1 <> r2 ->
  get (add_multiple_mx n r1 r2 c) i j =
                            if Z.eq_dec i r2 then
                               if Z.eq_dec j r1 then c
                               else (if Z.eq_dec i j then one else zero)
                            else (if Z.eq_dec i j then one else zero).
Proof.
  intros. unfold add_multiple_mx. rewrite (add_multiple_spec _ n n); try lia.
  rewrite? identity_spec; try lia.
  repeat(if_tac; subst; try contradiction; try ring).
  apply identity_wf; lia.
Qed.


Lemma summation_twice_notin_l: forall f l r1 r2 c1 c2,
  ~In r1 l ->
  ~In r2 l ->
  summation_aux
     (fun k : Z =>
      mult (if Z.eq_dec k r1 then c1 else if Z.eq_dec r2 k then c2 else zero) (f k)) l = zero.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. if_tac. subst. exfalso. apply H. left. reflexivity.
    if_tac. exfalso. apply H0. subst. left. reflexivity.
    rewrite IHl. ring. all: intuition.
Qed.

(*how matrix multiplication works when we have exactly 2 nonzero entries*)
Lemma two_nonzero_entries_mult:
forall (mx: matrix) m n r1 r2 (c1 c2: A) j l,
  wf_matrix mx m n ->
  (0 <= m) ->
  In r1 l ->
  In r2 l ->
  NoDup l ->
  r1 <> r2 ->
  (forall x, In x l -> (0 <= x<m)) ->
  (0 <= j < n) ->
  summation_aux
  (fun k : Z =>
   mult (if Z.eq_dec k r1 then c1 else if Z.eq_dec r2 k then c2 else zero) (get mx k j)) l =
  plus (mult c1 (get mx r1 j)) (mult c2 (get mx r2 j)). 
Proof.
  intros. pose proof (NoDup_split_twice _ _ _ H1 H2 H4 H3). destruct H7.
  - destruct H7 as [l1]. destruct H7 as [l2]. destruct H7 as [l3].
    destruct H7 as [? D]. repeat(destruct D as [? D]).
    rewrite H7. rewrite summation_aux_app. rewrite summation_twice_notin_l; try assumption.
    simpl. rewrite summation_aux_app. rewrite summation_twice_notin_l; try assumption.
    simpl. rewrite summation_twice_notin_l; try assumption. if_tac. 2 : contradiction.
    if_tac. subst. contradiction. if_tac. 2 : contradiction. ring.
  - destruct H7 as [l1]. destruct H7 as [l2]. destruct H7 as [l3].
    destruct H7 as [? D]. repeat(destruct D as [? D]).
    rewrite H7. rewrite summation_aux_app. rewrite summation_twice_notin_l; try assumption.
    simpl. rewrite summation_aux_app. rewrite summation_twice_notin_l; try assumption.
    simpl. rewrite summation_twice_notin_l; try assumption. if_tac. subst. contradiction.
    if_tac. 2 : contradiction. if_tac. 2 : contradiction. ring.
Qed.

(*finally, we have the row operation - multiplication equivalence*)
Lemma add_multiple_elem: forall mx m n r1 r2 c,
  wf_matrix mx m n ->
  (0 <= n) ->
  (0 <= r1 < m) ->
  (0 <= r2 < m) ->
  r1 <> r2 ->
  add_multiple mx r1 r2 c = mx_mult (add_multiple_mx m r1 r2 c) mx m m n.
Proof.
  intros. rewrite (matrix_equiv _ _ m n). intros. 2 : apply add_multiple_wf; try lia; try assumption.
  2 : apply mx_mult_wf; lia.
  (*rewrite add_multiple_mx_spec; try lia.
  unfold add_multiple_mx. *)
  rewrite (add_multiple_spec _ m n); try lia. 2 : assumption.
  rewrite mx_mult_spec; try lia.
  unfold summation.
  assert (forall l, (forall x, In x l -> (0 <= x < m)) ->
    summation_aux (fun k : Z => mult (get (add_multiple_mx m r1 r2 c) i k) (get mx k j)) l =
    summation_aux
  (fun k : Z =>
   mult   (if Z.eq_dec i r2
            then if Z.eq_dec k r1 then c else if Z.eq_dec i k then one else zero
            else if Z.eq_dec i k then one else zero) (get mx k j)) l). { intros.
  induction l. reflexivity. simpl. rewrite IHl. rewrite add_multiple_mx_spec; try lia. reflexivity. 
  apply H6; left; reflexivity. intros. apply H6; right; assumption. } rewrite H6. clear H6.
  2 : { intros. rewrite Zseq_In in H7; lia. } if_tac.
  - subst. rewrite (two_nonzero_entries_mult _ m n). ring. all: try assumption.
    all: try lia. all: try(rewrite Zseq_In; lia). apply Zseq_NoDup; lia. intros.
    rewrite Zseq_In in H6; lia.
  - rewrite summation_identity_in_once_l. reflexivity. apply Zseq_bounds_split; lia.
Qed.

(*Inverse of add multiple mx is just add multiple mx with -c *)
Lemma add_multiple_inv: forall n r1 r2 c,
  (0 <= r1 < n) ->
  (0 <= r2 < n) ->
  (r1 <> r2) ->
  inverse (add_multiple_mx n r1 r2 c) (add_multiple_mx n r1 r2 (opp c)) n.
Proof.
  intros. unfold inverse. assert (forall x, 
    mx_mult (add_multiple_mx n r1 r2 x) (add_multiple_mx n r1 r2 (opp x)) n n n = identity n). {
  intros. rewrite <- add_multiple_elem; try lia. rewrite (matrix_equiv _ _ n n). intros.
  rewrite (add_multiple_spec _ n n); try lia. repeat(rewrite add_multiple_mx_spec; try lia). 
  rewrite identity_spec; try lia.
  repeat(if_tac; subst; try(contradiction); try(ring)). 
  2: apply add_multiple_wf; try lia. 3 : apply identity_wf; lia. all: apply add_multiple_mx_wf; try lia. } 
  split. apply H2. replace c with (opp (opp c)) at 2 by ring. apply H2.
Qed.

End ElemMx.

(*Products of Elementary Matrices and Elementary Row Operations*)
Section ERO.

Variable m : Z. 

Inductive elem_matrix: (matrix) -> Prop :=
  | e_swap: forall i j,
    (0 <= i<m) ->
    (0 <= j<m) ->
    elem_matrix (row_swap_mx m i j)
  | e_scalar: forall i c,
    (0 <= i<m) ->
    c <> zero ->
    elem_matrix (scalar_mult_mx m i c)
  | e_add_multiple: forall i j c,
    (0 <= i<m) ->
    (0 <= j<m) ->
    i <> j -> (*this is invalid or just scalar mult anyway*)
    elem_matrix (add_multiple_mx m i j c).

Lemma elem_matrix_wf: forall mx,
  elem_matrix mx -> wf_matrix mx m m.
Proof.
  intros. inversion H; subst.
  - apply row_swap_mx_wf; lia.
  - apply scalar_mult_mx_wf; lia.
  - apply add_multiple_mx_wf; lia.
Qed.

Lemma elem_matrix_invertible: forall mx,
  elem_matrix mx -> invertible mx m.
Proof.
  intros. unfold invertible. inversion H.
  - exists (row_swap_mx m i j). split. apply row_swap_mx_wf; lia. apply row_swap_mx_inv; assumption.
  - exists (scalar_mult_mx m i (inv c)). split. apply scalar_mult_mx_wf; lia.  apply scalar_mult_inv; assumption.
  - exists (add_multiple_mx m i j (opp c)). split. apply add_multiple_mx_wf; lia. apply add_multiple_inv; try assumption.
Qed.

Lemma elem_matrix_inverse_elementary: forall mx mx',
  elem_matrix mx ->
  wf_matrix mx' m m ->
  inverse mx mx' m ->
  elem_matrix mx'.
Proof.
  intros. inversion H; subst.
  - pose proof (row_swap_mx_inv m i j H2 H3).
    assert (mx' = row_swap_mx m i j). eapply inverse_unique. 5: apply H1. apply row_swap_mx_wf; lia.
    assumption. apply row_swap_mx_wf; lia. lia. assumption.
    subst. constructor; assumption.
  - pose proof (scalar_mult_inv m i c H2 H3).
    assert (mx' = (scalar_mult_mx m i (inv c))). eapply inverse_unique. 6 : apply H4.
    apply scalar_mult_mx_wf; lia. assumption. apply scalar_mult_mx_wf; lia. lia. assumption.
    subst. constructor. lia. apply inv_nonzero. assumption. 
  - pose proof (add_multiple_inv m i j c H2 H3 H4). 
    assert (mx' = (add_multiple_mx m i j (opp c))). eapply inverse_unique. 6 : apply H5.
    all: try (apply add_multiple_mx_wf; lia). assumption. lia. assumption. subst. constructor; assumption.
Qed. 

(*A product of elementary matrices*)
Inductive elem_product: matrix -> Prop :=
  | p_id: elem_product (identity m)
  | p_multiple: forall m1 mx,
      elem_product m1 ->
      elem_matrix mx ->
      elem_product (mx_mult mx m1 m m m).

Variable Mnonneg: 0 <= m.

Lemma elem_product_wf: forall mx,
  elem_product mx ->
  wf_matrix mx m m.
Proof.
  intros. inversion H.
  - apply identity_wf; lia.
  - apply mx_mult_wf; lia.
Qed.

Lemma elem_mx_product: forall mx,
  elem_matrix mx ->
  elem_product mx.
Proof.
  intros. rewrite <- (mx_mult_I_r _ m m). eapply p_multiple. constructor. assumption.
  apply elem_matrix_wf. all: assumption. 
Qed.

Lemma elem_product_trans: forall m1 m2,
  elem_product m1 ->
  elem_product m2 ->
  elem_product (mx_mult m1 m2 m m m).
Proof.
  intros. induction H.
  - rewrite mx_mult_I_l. assumption. apply elem_product_wf. all: assumption.
  - rewrite mx_mult_assoc; try assumption. apply p_multiple. apply IHelem_product. assumption.
    apply elem_matrix_wf; assumption. all: apply elem_product_wf; assumption.
Qed.

(*The other direction is true, but much harder*)
Lemma elem_product_invertible: forall mx,
  elem_product mx -> invertible mx m.
Proof.
  intros. induction H.
  - apply identity_invertible. assumption.
  - apply product_invertible. apply elem_matrix_wf; assumption.
    apply elem_product_wf; assumption. assumption. apply elem_matrix_invertible. all: assumption.
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
Variable n : Z.
Variable Nnonneg: (0<= n).

Inductive ERO : matrix -> matrix -> Prop :=
  | ero_swap: forall mx r1 r2,
    (0 <= r1 < m) ->
    (0 <= r2 < m) ->
    ERO mx (swap_rows mx r1 r2)
  | ero_scalar: forall mx i c,
    (0 <= i < m) ->
    c <> zero ->
    ERO mx (scalar_mul_row mx i c)
  | ero_add: forall mx r1 r2 c,
    (0 <= r1 < m) ->
    (0 <= r2 < m) ->
    r1 <> r2 ->
    ERO mx (add_multiple mx r1 r2 c).


(*two matrices are row equivalent if one can be transformed to another via a sequence of EROs*)
Inductive row_equivalent: matrix -> matrix -> Prop :=
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

Lemma ERO_wf: forall m1 m2,
  wf_matrix m1 m n ->
  ERO m1 m2 ->
  wf_matrix m2 m n.
Proof.
  intros. inversion H0; subst.
  - apply swap_rows_wf; try lia. assumption.
  - apply scalar_mul_row_wf; try lia. assumption.
  - apply add_multiple_wf; try lia. assumption.
Qed.

Lemma row_equivalent_wf: forall m1 m2,
  wf_matrix m1 m n ->
  row_equivalent m1 m2 ->
  wf_matrix m2 m n.
Proof.
  intros. induction H0.
  - assumption.
  - apply IHrow_equivalent. apply (ERO_wf _ _ H H0).
Qed.

(*Equivalence between EROs and multiplication on left by elementary matrices*)
Lemma ero_elem_mx_iff: forall m1 m2,
  wf_matrix m1 m n ->
  wf_matrix m2 m n ->
  ERO m1 m2 <-> exists e, elem_matrix e /\ m2 = mx_mult e m1 m m n.
Proof.
  intros. split; intros.
  - inversion H1; subst.
    + exists (row_swap_mx m r1 r2). split. constructor; assumption.
      apply swap_rows_elem_mx; assumption.
    + exists (scalar_mult_mx m i c). split. constructor; assumption.
      apply scalar_mult_elem; assumption.
    + exists (add_multiple_mx m r1 r2 c). split. constructor; assumption.
      apply (add_multiple_elem); assumption.
  - destruct H1 as [e]. destruct H1. inversion H1; subst.
    + rewrite <- swap_rows_elem_mx. constructor. all: assumption.
    + rewrite <- scalar_mult_elem. constructor. all: assumption.
    + rewrite <- add_multiple_elem. constructor. all: assumption.
Qed.

Lemma row_equiv_elem_product_iff: forall m1 m2,
  wf_matrix m1 m n ->
  wf_matrix m2 m n ->
  row_equivalent m1 m2 <-> exists e, elem_product e /\ m2 = mx_mult e m1 m m n.
Proof.
  intros. split; intros.
  - induction H1.
    + exists (identity m). split. constructor.
      rewrite mx_mult_I_l. reflexivity. all: assumption.
    + assert (wf_matrix mx' m n). eapply ERO_wf. apply H. apply H1.
      specialize (IHrow_equivalent H3 H0). clear H3.  destruct IHrow_equivalent. destruct H3.
      rewrite ero_elem_mx_iff in H1. destruct H1 as [e]. destruct H1. subst.
      exists (mx_mult x e m m m). split. apply elem_product_trans. apply H3.
      apply elem_mx_product. assumption. rewrite mx_mult_assoc. reflexivity. all: try assumption.
      apply elem_product_wf; assumption. apply elem_matrix_wf; assumption.
      eapply ERO_wf. apply H. apply H1.
  - destruct H1 as [e]. destruct H1. generalize dependent m2. generalize dependent m1. induction H1; intros.
    + rewrite mx_mult_I_l in H2. subst. constructor. all: assumption. 
    + rewrite mx_mult_assoc in H3. specialize (IHelem_product m0 H0 (mx_mult m1 m0 m m n)).
      eapply row_equivalent_trans. apply IHelem_product. apply mx_mult_wf; lia. reflexivity.
      rewrite H3. apply row_equivalent_ero. apply ero_elem_mx_iff. all: try(apply mx_mult_wf; lia).
      exists mx. split. assumption. reflexivity. all: try assumption.
      apply elem_matrix_wf; assumption. apply elem_product_wf; assumption.
Qed.

Lemma ERO_sym: forall m1 m2,
  wf_matrix m1 m n ->
  ERO m1 m2 ->
  ERO m2 m1.
Proof.
  intros. assert (E:= H0). rewrite ero_elem_mx_iff in H0. rewrite ero_elem_mx_iff.
  destruct H0 as [e]. destruct H0. 
  pose proof (elem_matrix_invertible e H0). unfold invertible in H2.
  destruct H2 as [e']. exists e'. split. eapply elem_matrix_inverse_elementary. apply H0.
  apply H2. apply H2. subst. rewrite <- mx_mult_assoc. unfold inverse in H2. destruct H2.
  destruct H2. rewrite H3. rewrite mx_mult_I_l. reflexivity. all: try assumption. destruct H2; assumption.
  apply elem_matrix_wf; assumption. all: eapply ERO_wf; try (apply H); try (apply E).
Qed.

Lemma row_equivalent_sym: forall m1 m2,
  wf_matrix m1 m n ->
  row_equivalent m1 m2 ->
  row_equivalent m2 m1.
Proof.
  intros. induction H0.
  - constructor.
  - eapply row_equivalent_trans. apply IHrow_equivalent. eapply ERO_wf. apply H. assumption.
    apply row_equivalent_ero. apply ERO_sym. assumption. assumption.
Qed.

End ERO.

(*A key property of row operations: they preserve invertibility*)
Lemma row_equiv_invertible_iff: forall m1 m2 m,
  wf_matrix m1 m m ->
  (0 <= m) ->
  row_equivalent m m1 m2 ->
  invertible m1 m <-> invertible m2 m.
Proof.
  intros. assert (forall a b,
    wf_matrix a m m ->
    row_equivalent m a b ->
    invertible a m -> invertible b m). { intros.
    rewrite row_equiv_elem_product_iff in H3. 4 : apply H2. destruct H3 as [e]. destruct H3. subst. 
    apply product_invertible. apply elem_product_wf. lia. all: try assumption.
    apply elem_product_invertible; assumption. eapply row_equivalent_wf; try lia.
    apply H2. assumption.  }
  split; intros. eapply H2. apply H. assumption. assumption. eapply H2. 
  eapply row_equivalent_wf; try lia. apply H. apply H1. 
    eapply row_equivalent_sym. 3 : apply H. all: try lia. all: assumption.
Qed.


End MatrixDef.

 
  
