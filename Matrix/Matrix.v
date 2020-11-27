Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.setoid_ring.Field_theory.
Require Import VST.floyd.functional_base.
Require Import PropList.
Require Import Field.

(*since the lemma is super long*)
Ltac exist_eq := apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.

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

Lemma all_list: forall {A: Type} (a : A) (l: list A) (p: A -> Prop),
  (forall x, In x (a :: l) -> p x) ->
  forall x, In x l -> p x.
Proof.
  intros. apply H. right. assumption.
Qed.

Lemma fst_list: forall {A: Type} (a : A) (l: list A) (p: A -> Prop),
  (forall x, In x (a :: l) -> p x) ->
  p a.
Proof.
  intros. apply H. left. reflexivity.
Qed.

(*We work over an arbitrary field, and pack the operations and proofs into a single typeclass.
  Some of the basic definitions only require rings, but it is more convenient to avoid having different ring
  structures*) 
(*
Record ring_type (A: Type) := 
  {r_plus : A -> A -> A ;
  r_mult : A -> A -> A;
  r_sub : A -> A -> A;
  r_opp: A -> A ;
  r_zero : A;
  r_one : A;
  r_Rth : @ring_theory A r_zero r_one r_plus r_mult r_sub r_opp eq}.
*)
Record field_type (A: Type) :=
  { f_plus : A -> A -> A ;
    f_mult : A -> A -> A;
    f_sub : A -> A -> A;
    f_opp: A -> A ;
    f_zero : A;
    f_one : A;
    f_div : A -> A -> A;
    f_inv : A -> A;
    f_Fth: field_theory f_zero f_one f_plus f_mult f_sub f_opp f_div f_inv eq;
     }.

(*Matrices*)

Section MatrixDef.

(*matrices are defined over arbitrary rings*)
Context {A: Type} (F: field_type A).

(*So we don't have to pass F around everywhere*)

Definition plus := f_plus A F.
Definition mult := f_mult A F.
Definition sub := f_sub A F.
Definition opp := f_opp A F.
Definition zero := f_zero A F.
Definition one := f_one A F.
Definition div := f_div A F.
Definition inv := f_inv A F.
Definition Rth := F_R (f_Fth A F).
Definition Fth := f_Fth A F. 

Ltac ring_unfold H := unfold plus in H; unfold mult in H; unfold sub in H; unfold opp in H; unfold zero in H;
  unfold one in H.
Ltac field_unfold H := ring_unfold H; unfold div in H; unfold inv in H.
Ltac ring' := unfold plus; unfold mult; unfold sub; unfold opp; unfold zero; unfold one; ring.
Ltac ring_simplify' := unfold plus; unfold mult; unfold sub; unfold opp; unfold zero; unfold one; ring_simplify.
Ltac field' := unfold plus; unfold mult; unfold sub; unfold opp; unfold zero; unfold one; unfold div; unfold inv; field.
Ltac field_simplify' := unfold plus; unfold mult; unfold sub; unfold opp; unfold zero; unfold one; unfold div; 
  unfold inv; field_simplify.

Add Field f : Fth.

Instance default : `{Inhabitant A}.
apply zero.
Defined.

Section MatrixList.

Definition matrix_type := list (list A).

Definition wf_matrix (mx: matrix_type) (m n : Z) :=
  Zlength mx = m /\ forall x, In x mx -> Zlength x = n.

(*get the (i,j)th entry of a matrix*)
Definition get_aux (mx: matrix_type) (i j : Z) :=
  let row := Znth i mx in
  Znth j row.

Lemma matrix_equiv_aux: forall (m1 m2: matrix_type) (m n: Z),
  wf_matrix m1 m n ->
  wf_matrix m2 m n ->
  m1 = m2 <-> forall i j, (0 <= i<m) -> (0 <= j<n) -> get_aux m1 i j = get_aux m2 i j.
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
Definition mk_matrix_aux (m n : Z) (f: Z -> Z -> A) : matrix_type :=
  prop_list (fun i => (prop_list (fun j => f i j) n)) m.

Lemma mk_matrix_aux_wf: forall m n f, (0 <= m) -> (0<= n) -> wf_matrix (mk_matrix_aux m n f) m n.
Proof.
  intros. unfold wf_matrix. unfold mk_matrix_aux. split. rewrite prop_list_length. reflexivity. assumption.
  intros. rewrite In_Znth_iff in H1. destruct H1. destruct H1.
  rewrite prop_list_Znth in H2. subst. rewrite prop_list_length. reflexivity. assumption.
  rewrite prop_list_length in H1. lia. assumption.
Qed.

Lemma mk_matrix_aux_spec: forall m n f i j,
  (0 <= i< m) ->
  (0 <= j< n) ->
  get_aux (mk_matrix_aux m n f) i j = f i j.
Proof.
  intros. unfold mk_matrix_aux. unfold get_aux. rewrite prop_list_Znth. 2 : assumption.
  rewrite prop_list_Znth. reflexivity. assumption.
Qed.

(*row operations*)

(*1. multiply row r by scalar k *)
Definition scalar_mul_row_aux (mx: matrix_type) (r: Z) (k: A) : matrix_type :=
  let old_row := Znth r mx in
  let new_row := map (fun x => mult k x) old_row in
  upd_Znth r mx new_row. 

Lemma scalar_mul_row_aux_wf: forall mx m n r k,
  (0 <= m) ->
  (0 <= n) ->
  wf_matrix mx m n ->
  wf_matrix (scalar_mul_row_aux mx r k) m n.
Proof.
  intros. unfold scalar_mul_row_aux. unfold wf_matrix in *. destruct H1.
  split. list_solve. intros. rewrite In_Znth_iff in H3. destruct H3 as [i].
  destruct H3. 
  assert ((( 0 > r) \/ r >= m) \/ (0 <= r < m)) by lia. destruct H5.
  - rewrite upd_Znth_out_of_range in H4. 2 : list_solve. subst. apply H2.
    apply Znth_In. list_solve.
  - erewrite upd_Znth_lookup' in H4. 2 : apply H1. destruct (zeq i r).
    subst. rewrite Zlength_map. apply H2. apply Znth_In. list_solve.
    subst. apply H2. apply Znth_In. list_solve. list_solve.  lia.
Qed. 

Lemma scalar_mul_row_aux_spec: forall mx m n r k i j,
  wf_matrix mx m n ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  (0 <= r < m) ->
  get_aux (scalar_mul_row_aux mx r k) i j =
    if (Z.eq_dec i r) then  mult k (get_aux mx i j) else get_aux mx i j.
Proof.
  intros. unfold scalar_mul_row_aux. unfold get_aux. destruct (Z.eq_dec i r).
  - subst. rewrite upd_Znth_same. rewrite Znth_map. reflexivity. unfold wf_matrix in H. destruct H.
    rewrite H3. assumption. apply Znth_In. list_solve. unfold wf_matrix in H. list_solve.
  - unfold wf_matrix in H. destruct H. rewrite upd_Znth_diff. reflexivity. list_solve. list_solve. assumption.
Qed.

(*2. swap rows r1 and r2*)
Definition swap_rows_aux (mx: matrix_type) (r1 r2 : Z) : matrix_type :=
  let old1 := Znth r1 mx in
  let old2 := Znth r2 mx in
  upd_Znth r2 (upd_Znth r1 mx old2) old1.

Lemma swap_rows_aux_wf: forall mx m n r1 r2,
  (0 <= n) ->
  (0 <= r1 < m) ->
  (0 <= r2 < m) ->
  wf_matrix mx m n ->
  wf_matrix (swap_rows_aux mx r1 r2) m n.
Proof.
  intros. unfold wf_matrix in *. destruct H2. unfold swap_rows_aux.
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

Lemma swap_rows_aux_spec: forall (mx: matrix_type) m n r1 r2 i j,
  wf_matrix mx m n ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  (0 <= r1 < m) ->
  (0 <= r2 < m) ->
  get_aux (swap_rows_aux mx r1 r2) i j =
    if (Z.eq_dec i r1) then get_aux mx r2 j
    else if (Z.eq_dec i r2) then get_aux mx r1 j
    else get_aux mx i j.
Proof.
  intros. unfold wf_matrix in H. destruct H. unfold swap_rows_aux. unfold get_aux. destruct (Z.eq_dec i r2).
  - subst. rewrite upd_Znth_same.  2: list_solve. if_tac. subst. reflexivity. reflexivity.
  - rewrite upd_Znth_diff. 2 : list_solve. 2 : list_solve. 2 : assumption.
    destruct (Z.eq_dec i r1).
    + subst. list_solve.
    + list_solve.
Qed.

(*3. row r2 = row r2 + k * row r1*)
Definition add_multiple_aux (mx: matrix_type) (r1 r2 : Z) (k : A) : matrix_type :=
  upd_Znth r2 mx (combine (Znth r2 mx) (Znth r1 mx) (fun x y => plus x (mult k y))).

Lemma add_multiple_aux_wf: forall mx m n r1 r2 k,
  wf_matrix mx m n ->
  (0 <= n) ->
  (0 <= r1 < m) ->
  (0 <= r2 < m) ->
  wf_matrix (add_multiple_aux mx r1 r2 k) m n.
Proof.
  intros. unfold wf_matrix in *. unfold add_multiple_aux.
  split. list_solve. intros. rewrite In_Znth_iff in H3. destruct H3 as [i].
  destruct H3. destruct (Z.eq_dec i r2).
  - subst. rewrite upd_Znth_same. rewrite combine_Zlength. apply H. apply Znth_In.
    list_solve. destruct H. rewrite H4. rewrite H4. reflexivity.
    all: try(apply Znth_In; list_solve). list_solve.
  - subst. rewrite upd_Znth_diff. destruct H. rewrite H4. reflexivity. apply Znth_In.
    4 : assumption. all: list_solve.
Qed.

Lemma add_multiple_aux_spec: forall (mx: matrix_type) m n r1 r2 k i j,
  wf_matrix mx m n ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  (0 <= r1 < m) ->
  (0 <= r2 < m) ->
  get_aux (add_multiple_aux mx r1 r2 k) i j =
    if (Z.eq_dec i r2) then plus (get_aux mx r2 j) (mult k (get_aux mx r1 j))
    else get_aux mx i j.
Proof.
  intros. unfold get_aux. unfold add_multiple_aux. unfold wf_matrix in H.
  destruct H. destruct (zeq i r2).
  - subst. rewrite upd_Znth_same. 2: assumption. rewrite combine_Znth.
    if_tac. reflexivity. contradiction. rewrite H4. rewrite H4. reflexivity.
    3: rewrite H4. 3 : assumption. all: apply Znth_In; list_solve.
  - rewrite upd_Znth_diff. if_tac. contradiction. reflexivity. list_solve.
    list_solve. assumption.
Qed.

End MatrixList.

Section DepMatrix.

(* We wrap the matrix operations in a dependent type for all outside operations, so we don't have
  to carry around the wf_matrix predicate everywhere*)
Definition matrix m n := {mx : matrix_type | wf_matrix mx m n}.

Definition get {m n} (mx: matrix m n) (i j : Z) :=
  get_aux (proj1_sig mx) i j.

Lemma matrix_equiv: forall {m n} (m1 m2 : matrix m n),
  m1 = m2 <-> forall i j, (0 <= i<m) -> (0 <= j<n) -> get m1 i j = get m2 i j.
Proof.
  intros. destruct m1. destruct m2. unfold get. simpl. rewrite <- matrix_equiv_aux; try assumption. 
  split; intros. inversion H. reflexivity.  exist_eq. assumption.
Qed.

Definition mk_matrix (m n : Z) (M: 0 <= m) (N : 0 <= n) (f: Z -> Z -> A) : matrix m n :=
  exist _ (mk_matrix_aux m n f) (mk_matrix_aux_wf m n f M N).

Lemma mk_matrix_spec: forall m n f i j (M: 0 <= m) (N : 0 <= n),
  (0 <= i< m) ->
  (0 <= j< n) ->
  get (mk_matrix m n M N f) i j = f i j.
Proof.
  intros. unfold mk_matrix. unfold get. simpl. apply mk_matrix_aux_spec; assumption.
Qed.

(*Row operations*)

(*1. scalar mult*)
Definition scalar_mul_row {m n} (mx: matrix m n) (r: Z) (k: A) (M: 0 <= m) (N: 0 <= n) : matrix m n :=
  exist _ (scalar_mul_row_aux (proj1_sig mx) r k) (scalar_mul_row_aux_wf (proj1_sig mx) m n r k M N (proj2_sig mx)).

Lemma scalar_mul_row_spec: forall {m n} (mx: matrix m n) r k i j (M: 0 <= m) (N: 0 <= n),
  (0 <= i < m) ->
  (0 <= j < n) ->
  (0 <= r < m) ->
  get (scalar_mul_row mx r k M N) i j =
    if (Z.eq_dec i r) then  mult k (get mx i j) else get mx i j.
Proof.
  intros. unfold get. unfold scalar_mul_row. simpl.
  destruct mx. simpl. eapply scalar_mul_row_aux_spec. apply w. all: assumption.
Qed.


(*2. swap rows*)

Definition swap_rows {m n} (mx: matrix m n) (r1 r2 : Z) (N: 0 <= n) (R1 : 0 <= r1 < m) (R2: 0 <= r2 < m) : matrix m n :=
  exist _ (swap_rows_aux (proj1_sig mx) r1 r2) (swap_rows_aux_wf (proj1_sig mx) m n r1 r2 N R1 R2 (proj2_sig mx)).

Lemma swap_rows_spec: forall {m n} (mx: matrix m n) r1 r2 i j (N: 0 <= n) (R1: 0 <= r1 < m) (R2: 0 <= r2 < m),
  (0 <= i < m) ->
  (0 <= j < n) ->
  get (swap_rows mx r1 r2 N R1 R2) i j =
    if (Z.eq_dec i r1) then get mx r2 j
    else if (Z.eq_dec i r2) then get mx r1 j
    else get mx i j.
Proof.
  intros. unfold get. unfold swap_rows. simpl. destruct mx; simpl.
  apply (swap_rows_aux_spec _ m n); assumption.
Qed.

(*3. add multiple of row one to another*)

Definition add_multiple {m n} (mx: matrix m n) (r1 r2 : Z) (k: A) (N: 0 <= n) (R1: 0 <= r1 < m) (R2: 0 <= r2 < m) : matrix m n :=
  exist _ (add_multiple_aux (proj1_sig mx) r1 r2 k) (add_multiple_aux_wf (proj1_sig mx) m n r1 r2 k (proj2_sig mx)
    N R1 R2).

Lemma add_multiple_spec: forall {m n} (mx: matrix m n) r1 r2 k i j (N: 0 <= n) (R1: 0 <= r1 < m) (R2: 0 <= r2 < m),
  (0 <= i < m) ->
  (0 <= j < n) ->
  get (add_multiple mx r1 r2 k N R1 R2) i j =
    if (Z.eq_dec i r2) then plus (get mx r2 j) (mult k (get mx r1 j))
    else get mx i j.
Proof.
  intros. unfold get. unfold add_multiple. simpl. destruct mx; simpl.
  apply (add_multiple_aux_spec _ m n); assumption.
Qed.

End DepMatrix.

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
  - simpl. ring'.
  - simpl. ring_simplify'. ring_unfold IHl. rewrite IHl. reflexivity.
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
  - simpl. ring'.
  - simpl. rewrite IHl. ring'.
Qed.

(*sum_i sum_j a_{ij} = sum_j sum_i a_{ij} (for finite sums) *)
Lemma summation_aux_change_order: forall (f: Z -> Z -> A) l1 l2,
  summation_aux (fun i => summation_aux (fun j => f i j) l1) l2 = 
  summation_aux (fun j => summation_aux (fun i => f i j) l2) l1.
Proof.
  intros. revert l2. revert f. induction l1; intros.
  - simpl. induction l2. reflexivity. simpl. rewrite IHl2. ring'.
  - simpl. rewrite summation_aux_distr_sum. rewrite IHl1. reflexivity.
Qed.

Lemma summation_aux_app: forall f l1 l2,
  summation_aux f (l1 ++ l2) =
  plus (summation_aux f l1) (summation_aux f l2).
Proof.
  intros. induction l1.
  - simpl. ring'.
  - simpl. rewrite IHl1. ring'.
Qed.

End Sum.


(*Matrix Multiplication*)
Section MatrixMult.

Definition mx_mult {m n p} (mx : matrix m n ) (mx' : matrix n p) (M: 0 <= m) (P : 0 <= p) :=
  mk_matrix m p M P (fun i j => summation (fun k => mult (get mx i k) (get mx' k j)) 0 n).

Lemma mx_mult_spec: forall {m n p} (mx: matrix m n) (mx' : matrix n p) (M: 0 <= m) (P: 0 <= p) i j,
  (0 <= i < m) ->
  (0 <= j < p) ->
  get (mx_mult mx mx' M P) i j = summation (fun k => mult (get mx i k) (get mx' k j)) 0 n.
Proof.
  intros. unfold mx_mult. rewrite mk_matrix_spec; try assumption. reflexivity.
Qed.

(*key property - matrix multiplication is associative*)
Lemma mx_mult_assoc: forall {m n l p} (m1 : matrix m n) (m2: matrix n l) (m3 : matrix l p)
  (M : 0 <= m) (N : 0 <= n) (P : 0 <= p) (L : 0 <= l),
  mx_mult (mx_mult m1 m2 M L) m3 M P = mx_mult m1 (mx_mult m2 m3 N P) M P.
Proof.
  intros. rewrite matrix_equiv. intros.
  rewrite? mx_mult_spec; try lia. (*cannot expand inner automatically bc we need to know bounds*)
  unfold summation.
  assert(forall l1 : list Z,
    (forall x, In x l1 -> (0 <= x < l)) ->
    summation_aux (fun k : Z => mult (get (mx_mult m1 m2 M L) i k) (get m3 k j)) l1 =
    summation_aux (fun k : Z => mult (summation (fun y => mult (get m1 i y) (get m2 y k)) 0 n) (get m3 k j)) l1). {
  intros. induction l1. simpl. reflexivity. simpl. 
  rewrite mx_mult_spec. rewrite IHl1. reflexivity. apply (all_list _ _ _ H1). assumption.
  apply (fst_list _ _ _ H1).   }
  (*the same for the other side*)
  assert(forall l1: list Z,
    (forall x, In x l1 -> (0 <= x < n)) ->
    summation_aux (fun k : Z => mult (get m1 i k) (get (mx_mult m2 m3 N P) k j)) l1 =
    summation_aux (fun k : Z => mult (get m1 i k) ((summation (fun y => mult (get m2 k y) (get m3 y j)) 0 l))) l1). {
  intros. induction l1. reflexivity. simpl. rewrite mx_mult_spec. rewrite IHl1. reflexivity.
  apply (all_list _ _ _ H2). apply (fst_list _ _ _ H2). assumption.  }
  rewrite H1. rewrite H2. 
  (*now rewrite the inner sum*)
  assert ((fun k : Z => mult (summation (fun y : Z => mult (get m1 i y) (get m2 y k)) 0 n) (get m3 k j)) =
  (fun k : Z => summation (fun y : Z => mult (mult (get m1 i y) (get m2 y k)) (get m3 k j)) 0 n)). {
  apply functional_extensionality. intros. rewrite summation_scalar_mult. reflexivity. }
  rewrite H3.
  assert ((fun k : Z => mult (get m1 i k) (summation (fun y : Z => mult (get m2 k y) (get m3 y j)) 0 l)) =
    (fun k : Z => (summation (fun y : Z => mult (mult (get m1 i k) (get m2 k y)) (get m3 y j)) 0 l))). {
  apply functional_extensionality. intros.  assert (forall x y, mult x y = mult y x) by (intros; ring').
  rewrite H4. rewrite summation_scalar_mult. 
  f_equal. apply functional_extensionality. intros. ring'. } rewrite H4.
  unfold summation. rewrite (summation_aux_change_order 
  (fun k y => mult (mult (get m1 i y) (get m2 y k)) (get m3 k j))). reflexivity.
  intros. rewrite Zseq_In in H3; lia. intros. rewrite Zseq_In in H3; lia.
Qed.

End MatrixMult.

(*The identity matrix and proofs*)
Section Identity.

(*The identity matrix*)
Definition identity (n: Z) (N: 0 <= n) : matrix n n :=
  mk_matrix n n N N (fun i j => if Z.eq_dec i j then one else zero).

Lemma identity_spec: forall n i j (N: 0 <= n),
  (0 <= i < n) ->
  (0 <= j < n) ->
  get (identity n N) i j = if Z.eq_dec i j then one else zero.
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
    rewrite IHl. ring'. intuition.
Qed.

Lemma summation_identity_notin_l: forall f l j,
  ~In j l ->
   summation_aux (fun k => mult (if Z.eq_dec j k then one else zero) (f k)) l = zero.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. if_tac. exfalso. apply H. left. auto. 
    rewrite IHl. ring'. intuition.
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
      rewrite summation_identity_notin_r. ring'. assumption.
    + inversion H; subst. simpl. if_tac. exfalso. apply H0. left. assumption.
      rewrite IHl. ring'. exists l1. exists l2. split. reflexivity. split. intuition. assumption.
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
      rewrite summation_identity_notin_l. ring'. assumption.
    + inversion H; subst. simpl. if_tac. exfalso. apply H0. left. auto. 
      rewrite IHl. ring'. exists l1. exists l2. split. reflexivity. split. intuition. assumption.
Qed. 

(*TODO move*)
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
Lemma mx_mult_I_r: forall {n m} (mx: matrix m n) (M: 0 <= m) (N: 0 <= n),
  mx_mult mx (identity n N) M N = mx.
Proof.
  intros. rewrite matrix_equiv. intros.
  rewrite mx_mult_spec; try lia. unfold summation.
  assert(forall l,
    (forall x, In x l -> (0 <= x < n)) ->
    summation_aux (fun k : Z => mult (get mx i k) (get (identity n N) k j)) l =
    summation_aux (fun k : Z => mult (get mx i k) (if Z.eq_dec k j then one else zero)) l). {
  intros. induction l. reflexivity. simpl. unfold identity at 1. rewrite mk_matrix_spec. rewrite IHl.
  reflexivity. apply (all_list _ _ _ H1). apply (fst_list _ _ _ H1). assumption. }
  rewrite H1. rewrite summation_identity_in_once_r. reflexivity.
  apply Zseq_bounds_split. all: try lia. intros. rewrite Zseq_In in H2; lia.
Qed.

Lemma mx_mult_I_l: forall {m n} (mx: matrix m n) (M: 0 <= m) (N: 0 <= n),
  mx_mult (identity m M) mx M N = mx.
Proof.
  intros. rewrite matrix_equiv. intros.
  rewrite mx_mult_spec; try lia. unfold summation.
  assert(forall l,
    (forall x, In x l -> (0 <= x < m)) ->
    summation_aux (fun k : Z => mult (get (identity m M) i k) (get mx k j)) l =
    summation_aux (fun k : Z => mult (if Z.eq_dec i k then one else zero)  (get mx k j)) l). {
  intros. induction l. reflexivity. simpl. unfold identity at 1. rewrite mk_matrix_spec. rewrite IHl.
  reflexivity. apply (all_list _ _ _ H1). assumption. apply (fst_list _ _ _ H1).  }
  rewrite H1. rewrite summation_identity_in_once_l. reflexivity.
  apply Zseq_bounds_split; try lia. intros. rewrite Zseq_In in H2; lia.
Qed.

End Identity.

(*Inverses and invertibility (basic definitions)*)

Section Inverse.

(* (square matrix ) m has left and right inverse m'*)
Definition inverse {n} (m m' : matrix n n) (N: 0 <= n) :=
  mx_mult m m' N N = identity n N /\ mx_mult m' m N N = identity n N.

Definition invertible {n} (mx: matrix n n) (N: 0 <= n) :=
  exists mx', inverse mx mx' N.

Lemma inverse_unique: forall {n} (a b c : matrix n n) (N: 0 <= n),
  inverse a b N ->
  inverse a c N ->
  b = c.
Proof.
  intros. unfold inverse in *. destruct H. destruct H0. 
  pose proof (mx_mult_I_r b N N). rewrite <- H0 in H3.
  rewrite <- (mx_mult_assoc _ _ _ N N N N) in H3. rewrite H1 in H3. rewrite mx_mult_I_l in H3.
  subst. reflexivity.
Qed.

Lemma identity_inv: forall n (N: 0 <= n),
  inverse (identity n N) (identity n N) N.
Proof.
  intros. unfold inverse. split. all: apply mx_mult_I_r. 
Qed.

Lemma identity_invertible: forall n (N: 0 <= n),
  invertible (identity n N) N.
Proof.
  intros. unfold invertible. exists (identity n N). split. all: apply identity_inv. 
Qed.

(*(AB)^-1 = B^-1A^-1*)
Lemma inverse_of_product : forall {n} (a a' b b' : matrix n n) (N: 0 <= n),
  inverse a a' N ->
  inverse b b' N ->
  inverse (mx_mult a b N N) (mx_mult b' a' N N) N.
Proof.
  intros. unfold inverse in *. destruct H. destruct H0. 
  split. rewrite <- (mx_mult_assoc _ _ _ N N N N). rewrite (mx_mult_assoc a _ _ N N N N). rewrite H0.
  rewrite mx_mult_I_r. assumption.
  rewrite <- (mx_mult_assoc _ _ _ N N N N). rewrite (mx_mult_assoc b' _ _ N N N N). rewrite H1. 
  rewrite mx_mult_I_r. assumption.
Qed.

Lemma inverse_sym: forall {n} (a b : matrix n n) (N: 0 <= n),
  inverse a b N ->
  inverse b a N.
Proof.
  intros. unfold inverse in *. destruct H. split; assumption.
Qed.

Lemma product_invertible: forall {n} (a b : matrix n n) (N: 0 <= n),
  invertible a N ->
  invertible b N ->
  invertible (mx_mult a b N N) N.
Proof.
  intros. unfold invertible in *. destruct H as [a'].
  destruct H0 as [b']. exists (mx_mult b' a' N N). split.
  apply inverse_of_product. all: try(apply inverse_sym; assumption).
  apply inverse_of_product; assumption.
Qed.

End Inverse.

(*Elementary Matrices*)

Lemma inv_nonzero: forall a : A,
  a <> zero ->
  inv a <> zero.
Proof.
  intros. intro. assert (mult a (inv a) = one) by (field'; assumption). 
  rewrite H0 in H1. assert (mult a zero = zero) by ring'. rewrite H1 in H2.
  pose proof (F_1_neq_0 (Fth)). contradiction. 
Qed. 

Section ElemMx.

(*1. Row swap matrix - swap rows i and j*)
Definition row_swap_mx n i j (N: 0 <= n) (I1 : 0 <= i < n) (J1 : 0 <= j < n) : matrix n n :=
  swap_rows (identity n N) i j N I1 J1.

(*Prove the row operation [swap_rows] is equivalent to multiplying by elementary matrix*)
Lemma swap_rows_elem_mx: forall {m n} (mx: matrix m n) i j (N: 0 <= n) (M: 0 <= m) (I1: 0 <= i < m) (J1 : 0 <= j < m),
  swap_rows mx i j N I1 J1 = mx_mult (row_swap_mx m i j M I1 J1) mx M N.
Proof.
  intros. rewrite matrix_equiv.  intros.
  rewrite swap_rows_spec; try lia. rewrite mx_mult_spec; try lia.
  unfold row_swap_mx. 
  unfold summation. assert (forall l,
    (forall x, In x l -> (0 <= x<m)) ->
    summation_aux (fun k : Z => mult (get (swap_rows (identity m M) i j M I1 J1) i0 k) (get mx k j0)) l =
    summation_aux (fun k : Z => mult (if Z.eq_dec i0 i 
              then if Z.eq_dec j k then one else zero
            else if Z.eq_dec i0 j
              then if Z.eq_dec i k then one else zero
            else if Z.eq_dec i0 k then one else zero) (get mx k j0)) l). {
    intros. induction l. reflexivity.
    simpl. rewrite swap_rows_spec. rewrite? identity_spec. rewrite IHl. reflexivity.
    apply (all_list _ _ _ H1). all: try assumption.
    all: apply (fst_list _ _ _ H1). } rewrite H1. clear H1.
    2 : { intros. rewrite Zseq_In in H2; lia. }
  if_tac.
  - subst. rewrite summation_identity_in_once_l. reflexivity.
    apply Zseq_bounds_split; lia.
  - if_tac.
    + rewrite summation_identity_in_once_l. reflexivity. apply Zseq_bounds_split; lia.
    + rewrite summation_identity_in_once_l. reflexivity. apply Zseq_bounds_split; lia.
Qed.

Lemma swap_sym: forall {m n} (mx: matrix m n) i j (N: 0 <= n) (I1: 0 <= i < m) (J1: 0 <= j < m),
  swap_rows mx i j N I1 J1 = swap_rows mx j i N J1 I1.
Proof.
  intros. rewrite matrix_equiv. intros.
  repeat(rewrite swap_rows_spec; try assumption). 
  if_tac. subst.  if_tac; subst; try reflexivity.
  reflexivity.
Qed. 

Lemma swap_twice: forall {m n} (mx: matrix m n) r1 r2 (N: 0 <= n) (R1: 0 <= r1 < m) (R2: 0 <= r2 < m),
  swap_rows (swap_rows mx r1 r2 N R1 R2) r2 r1 N R2 R1 = mx.
Proof.
  intros. rewrite matrix_equiv.  intros.
  repeat(rewrite swap_rows_spec; try assumption).
  repeat(if_tac; subst; try reflexivity; try contradiction).
Qed. 

(*The swap matrix is invertible, and, moreover, it is its own inverse*)
Lemma row_swap_mx_inv: forall n i j (N: 0 <= n) (I1 : 0 <= i < n) (J1: 0 <= j < n),
  inverse (row_swap_mx n i j N I1 J1) (row_swap_mx n i j N I1 J1) N.
Proof.
  intros. unfold inverse. rewrite <- swap_rows_elem_mx.
  unfold row_swap_mx. rewrite swap_sym. split; apply (swap_twice).
Qed. 

(*2. scalar multiplication*)
Definition scalar_mult_mx n i k (N: 0 <= n) :=
  scalar_mul_row (identity n N) i k N N.

(*equivalence between row operation and multiplication by elementary matrix*)
Lemma scalar_mult_elem: forall {m n} (mx: matrix m n) i k (N: 0 <= n) (M: 0 <= m),
  (0 <= i < m) ->
  scalar_mul_row mx i k M N = mx_mult (scalar_mult_mx m i k M) mx M N .
Proof.
  intros. rewrite (matrix_equiv). intros. rewrite scalar_mul_row_spec; try assumption.
  rewrite (mx_mult_spec); try lia. unfold scalar_mult_mx. unfold summation.
  assert (forall l,
    (forall x, In x l -> (0 <= x < m)) ->
    summation_aux (fun y : Z => mult (get (scalar_mul_row (identity m M) i k M M) i0 y) (get mx y j)) l =
    summation_aux (fun y : Z => mult (if Z.eq_dec i0 i then if Z.eq_dec y i then k else zero
                                            else if Z.eq_dec i0 y then one else zero) (get mx y j)) l). {
  intros. induction l. reflexivity.
  simpl. rewrite scalar_mul_row_spec. rewrite identity_spec. rewrite IHl. f_equal.
  repeat(if_tac; subst; try (ring'); try(contradiction); try(reflexivity)).
  apply (all_list _ _ _ H2). all: try assumption. all: apply (fst_list _ _ _ H2). }
  rewrite H2. clear H2.
  if_tac.
  - subst. assert ((fun y : Z => mult (if Z.eq_dec y i then k else zero) (get mx y j)) =
    (fun y : Z => mult (mult (if Z.eq_dec i y then one else zero) (get mx y j)) k)). {
   apply functional_extensionality. intros. if_tac; try(if_tac); try(subst; contradiction); ring'.  } 
   rewrite H2. clear H2.
   rewrite <- summation_aux_scalar_mult. 
   rewrite summation_identity_in_once_l. ring'. apply Zseq_bounds_split; lia.
  - rewrite summation_identity_in_once_l. reflexivity. apply Zseq_bounds_split; lia.
  - intros. rewrite Zseq_In in H3; lia.
Qed.

(*inverse of scalar mult matrix is just scalar mult matrix for 1/c*)
Lemma scalar_mult_inv: forall n i c (N: 0 <= n),
  (0 <= i < n) ->
  (c <> zero) ->
  inverse (scalar_mult_mx n i c N) (scalar_mult_mx n i (inv c) N) N.
Proof.
  intros. unfold inverse.
  assert (forall x, x <> zero ->
  mx_mult (scalar_mult_mx n i x N) (scalar_mult_mx n i (inv x) N) N N = identity n N). { intros.
  rewrite <- scalar_mult_elem. unfold scalar_mult_mx. rewrite matrix_equiv.
  intros. rewrite scalar_mul_row_spec; try assumption. 2: assumption. rewrite scalar_mul_row_spec; try assumption.
  if_tac. subst. field'. assumption. reflexivity. }
  split. apply H1. assumption. assert (c = inv (inv c)). field'. split. assumption. apply (F_1_neq_0 (Fth)).
  rewrite H2 at 2. apply H1. apply inv_nonzero. assumption.
Qed.

(*3. add multiple of row to another row*)

(*this one is harder, since in the multiplication we have exactly 2 nonzero entries, so we need lemmas
  to reason about this*)

Definition add_multiple_mx n r1 r2 c (N: 0 <= n) (R1: 0 <= r1 < n) (R2: 0 <= r2 < n) :=
  add_multiple (identity n N) r1 r2 c N R1 R2.

Lemma add_multiple_mx_spec: forall n r1 r2 c i j (N: 0 <= n) (R1: 0 <= r1 < n) (R2: 0 <= r2 < n),
  (0 <= i < n) ->
  (0 <= j < n) ->
  r1 <> r2 ->
  get (add_multiple_mx n r1 r2 c N R1 R2) i j =
                            if Z.eq_dec i r2 then
                               if Z.eq_dec j r1 then c
                               else (if Z.eq_dec i j then one else zero)
                            else (if Z.eq_dec i j then one else zero).
Proof.
  intros. unfold add_multiple_mx. rewrite add_multiple_spec; try assumption.
  rewrite? identity_spec; try lia.
  repeat(if_tac; subst; try contradiction; try ring').
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
    rewrite IHl. ring'. all: intuition.
Qed.

(*how matrix multiplication works when we have exactly 2 nonzero entries*)
Lemma two_nonzero_entries_mult:
forall {m n} (mx: matrix m n) r1 r2 (c1 c2: A) j l,
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
  intros. pose proof (NoDup_split_twice _ _ _ H0 H1 H3 H2). destruct H6.
  - destruct H6 as [l1]. destruct H6 as [l2]. destruct H6 as [l3].
    destruct H6 as [? D]. repeat(destruct D as [? D]).
    rewrite H6. rewrite summation_aux_app. rewrite summation_twice_notin_l; try assumption.
    simpl. rewrite summation_aux_app. rewrite summation_twice_notin_l; try assumption.
    simpl. rewrite summation_twice_notin_l; try assumption. if_tac. 2 : contradiction.
    if_tac. subst. contradiction. if_tac. 2 : contradiction. ring'.
  - destruct H6 as [l1]. destruct H6 as [l2]. destruct H6 as [l3].
    destruct H6 as [? D]. repeat(destruct D as [? D]).
    rewrite H6. rewrite summation_aux_app. rewrite summation_twice_notin_l; try assumption.
    simpl. rewrite summation_aux_app. rewrite summation_twice_notin_l; try assumption.
    simpl. rewrite summation_twice_notin_l; try assumption. if_tac. subst. contradiction.
    if_tac. 2 : contradiction. if_tac. 2 : contradiction. ring'.
Qed.

(*finally, we have the row operation - multiplication equivalence*)
Lemma add_multiple_elem: forall {m n} (mx : matrix m n) r1 r2 c (N: 0 <= n) (M: 0 <= m) (R1: 0 <= r1 < m) (R2: 0 <= r2 < m),
  (0 <= n) ->
  r1 <> r2 ->
  add_multiple mx r1 r2 c N R1 R2 = mx_mult (add_multiple_mx m r1 r2 c M R1 R2) mx M N.
Proof.
  intros. rewrite matrix_equiv. intros.
  rewrite add_multiple_spec; try assumption. rewrite mx_mult_spec; try lia.
  unfold summation.
  assert (forall l, (forall x, In x l -> (0 <= x < m)) ->
    summation_aux (fun k : Z => mult (get (add_multiple_mx m r1 r2 c M R1 R2) i k) (get mx k j)) l =
    summation_aux
  (fun k : Z =>
   mult   (if Z.eq_dec i r2
            then if Z.eq_dec k r1 then c else if Z.eq_dec i k then one else zero
            else if Z.eq_dec i k then one else zero) (get mx k j)) l). { intros.
  induction l. reflexivity. simpl. rewrite IHl. rewrite add_multiple_mx_spec; try lia. reflexivity.
  apply (fst_list _ _ _ H3). apply (all_list _ _ _ H3). } rewrite H3. clear H3.
  2 : { intros. rewrite Zseq_In in H4; lia. } if_tac.
  - subst. rewrite two_nonzero_entries_mult. ring'. all: try assumption.
    all: try(rewrite Zseq_In; lia). apply Zseq_NoDup; lia. intros.
    rewrite Zseq_In in H3; lia.
  - rewrite summation_identity_in_once_l. reflexivity. apply Zseq_bounds_split; lia.
Qed.

(*Inverse of add multiple mx is just add multiple mx with -c *)
Lemma add_multiple_inv: forall n r1 r2 c (N: 0 <= n) (R1: 0 <= r1 < n) (R2: 0 <= r2 < n),
  (r1 <> r2) ->
  inverse (add_multiple_mx n r1 r2 c N R1 R2) (add_multiple_mx n r1 r2 (opp c) N R1 R2) N.
Proof.
  intros. unfold inverse. assert (forall x, 
    mx_mult (add_multiple_mx n r1 r2 x N R1 R2) (add_multiple_mx n r1 r2 (opp x) N R1 R2) N N = identity n N). {
  intros. rewrite <- add_multiple_elem; try lia. rewrite matrix_equiv. intros.
  rewrite add_multiple_spec; try lia. repeat(rewrite add_multiple_mx_spec; try lia). 
  rewrite identity_spec; try lia.
  repeat(if_tac; subst; try(contradiction); try(ring')). } 
  split. apply H0. replace c with (opp (opp c)) at 2 by ring'. apply H0.
Qed.

End ElemMx.

(*Products of Elementary Matrices and Elementary Row Operations*)
Section ERO.

Variable m : Z. 
Variable M : 0 <= m.

Inductive elem_matrix: matrix m m -> Prop :=
  | e_swap: forall i j (I1: 0 <= i < m) (J1: 0 <= j < m),
    elem_matrix (row_swap_mx m i j M I1 J1)
  | e_scalar: forall i c,
    0 <= i < m ->
    c <> zero ->
    elem_matrix (scalar_mult_mx m i c M)
  | e_add_multiple: forall i j c (I1: 0 <= i < m) (J1: 0 <= j < m),
    i <> j -> (*this is invalid or just scalar mult anyway*)
    elem_matrix (add_multiple_mx m i j c M I1 J1).

Lemma elem_matrix_invertible: forall mx,
  elem_matrix mx -> invertible mx M.
Proof.
  intros. unfold invertible. inversion H.
  - exists (row_swap_mx m i j M I1 J1). apply row_swap_mx_inv; assumption.
  - exists (scalar_mult_mx m i (inv c) M). apply scalar_mult_inv; assumption.
  - exists (add_multiple_mx m i j (opp c) M I1 J1). apply add_multiple_inv; try assumption.
Qed.

Lemma elem_matrix_inverse_elementary: forall mx mx',
  elem_matrix mx ->
  inverse mx mx' M ->
  elem_matrix mx'.
Proof.
  intros. inversion H; subst.
  - pose proof (row_swap_mx_inv m i j M I1 J1).
    assert (mx' = row_swap_mx m i j M I1 J1). eapply inverse_unique. 2 : apply H1. assumption.
    subst. assumption.
  - pose proof (scalar_mult_inv m i c M H1 H2).
    assert (mx' = (scalar_mult_mx m i (inv c) M)). eapply inverse_unique. 2 : apply H3. assumption.
    subst. constructor. assumption. apply inv_nonzero; assumption.
  - pose proof (add_multiple_inv m i j c M I1 J1 H1). 
    assert (mx' = (add_multiple_mx m i j (opp c) M I1 J1)). eapply inverse_unique. 2 : apply H2.
    assumption. subst. constructor. assumption.
Qed. 

(*A product of elementary matrices*)
Inductive elem_product: (matrix m m) -> Prop :=
  | p_id: elem_product (identity m M)
  | p_multiple: forall m1 mx,
      elem_product m1 ->
      elem_matrix mx ->
      elem_product (mx_mult mx m1 M M).

Lemma elem_mx_product: forall mx,
  elem_matrix mx ->
  elem_product mx.
Proof.
  intros. rewrite <- (mx_mult_I_r mx M M). eapply p_multiple. constructor. assumption.
Qed.

Lemma elem_product_trans: forall m1 m2,
  elem_product m1 ->
  elem_product m2 ->
  elem_product (mx_mult m1 m2 M M).
Proof.
  intros. induction H.
  - rewrite mx_mult_I_l. assumption.
  - rewrite (mx_mult_assoc _ _ _ M M M M); try assumption. apply p_multiple. apply IHelem_product.
    assumption.
Qed.

(*The other direction is true, but much harder*)
Lemma elem_product_invertible: forall mx,
  elem_product mx -> invertible mx M.
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
Variable n : Z.
Variable N: (0<= n).

Inductive ERO : (matrix m n) -> (matrix m n) -> Prop :=
  | ero_swap: forall mx r1 r2 (R1: 0 <= r1 < m) (R2: 0 <= r2 < m),
    ERO mx (swap_rows mx r1 r2 N R1 R2)
  | ero_scalar: forall mx i c,
    (0 <= i < m) ->
    c <> zero ->
    ERO mx (scalar_mul_row mx i c M N)
  | ero_add: forall mx r1 r2 c (R1: 0 <= r1 < m) (R2: 0 <= r2 < m),
    r1 <> r2 ->
    ERO mx (add_multiple mx r1 r2 c N R1 R2).


(*two matrices are row equivalent if one can be transformed to another via a sequence of EROs*)
Inductive row_equivalent: (matrix m n) -> (matrix m n) -> Prop :=
  | row_same: forall mx,
    row_equivalent mx mx
  | row_ero: forall mx mx' mx'',
    ERO mx mx' ->
    row_equivalent mx' mx'' ->
    row_equivalent mx mx''.

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
  ERO m1 m2 <-> exists e, elem_matrix e /\ m2 = mx_mult e m1 M N.
Proof.
  intros. split; intros.
  - inversion H; subst.
    + exists (row_swap_mx m r1 r2 M R1 R2). split. constructor; assumption.
      apply swap_rows_elem_mx; assumption.
    + exists (scalar_mult_mx m i c M). split. constructor; assumption.
      apply scalar_mult_elem; assumption.
    + exists (add_multiple_mx m r1 r2 c M R1 R2). split. constructor; assumption.
      apply (add_multiple_elem); assumption.
  - destruct H as [e]. destruct H. inversion H; subst.
    + rewrite <- swap_rows_elem_mx. constructor. all: assumption.
    + rewrite <- scalar_mult_elem. constructor. all: assumption.
    + rewrite <- add_multiple_elem. constructor. all: assumption.
Qed.

Lemma row_equiv_elem_product_iff: forall m1 m2,
  row_equivalent m1 m2 <-> exists e, elem_product e /\ m2 = mx_mult e m1 M N.
Proof.
  intros. split; intros.
  - induction H.
    + exists (identity m M). split. constructor.
      rewrite mx_mult_I_l. reflexivity.
    + destruct IHrow_equivalent. destruct H1.
      rewrite ero_elem_mx_iff in H. destruct H as [e]. destruct H. subst.
      exists (mx_mult x e M M). split. apply elem_product_trans. assumption.
      apply elem_mx_product. assumption. erewrite mx_mult_assoc. reflexivity. 
  - destruct H as [e]. destruct H. generalize dependent m2. generalize dependent m1. induction H; intros.
    + rewrite mx_mult_I_l in H0. subst. constructor. 
    + rewrite (mx_mult_assoc _ _ _ M M N) in H1. specialize (IHelem_product m0 (mx_mult m1 m0 M N)).
      eapply row_equivalent_trans. apply IHelem_product. reflexivity.
      rewrite H1. apply row_equivalent_ero. apply ero_elem_mx_iff.
      exists mx. split. assumption. reflexivity.
Qed.

Lemma ERO_sym: forall m1 m2,
  ERO m1 m2 ->
  ERO m2 m1.
Proof.
  intros. assert (E:= H). rewrite ero_elem_mx_iff in H. rewrite ero_elem_mx_iff.
  destruct H as [e]. destruct H. 
  pose proof (elem_matrix_invertible e H). unfold invertible in H1.
  destruct H1 as [e']. exists e'. split. eapply elem_matrix_inverse_elementary. apply H. assumption.
  subst. erewrite <- mx_mult_assoc. unfold inverse in H1. destruct H1.
  rewrite e1. rewrite mx_mult_I_l. reflexivity.
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

End ERO.

(*A key property of row operations: they preserve invertibility*)
Lemma row_equiv_invertible_iff: forall {m} (m1 m2 : matrix m m) (M: 0 <= m),
  (0 <= m) ->
  row_equivalent m M m M m1 m2 ->
  invertible m1 M <-> invertible m2 M.
Proof.
  intros. assert (forall a b,
    row_equivalent m M m M a b ->
    invertible a M -> invertible b M). { intros.
    rewrite row_equiv_elem_product_iff in H1. destruct H1 as [e]. destruct H1. subst. 
    apply product_invertible. apply elem_product_invertible; assumption. assumption. }
  split; intros. eapply H1. apply H0. assumption. eapply H1.
  apply row_equivalent_sym. apply H0. assumption. 
Qed.


End MatrixDef.

 
  
