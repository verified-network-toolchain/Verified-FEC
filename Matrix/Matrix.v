Require Import Coq.setoid_ring.Ring_theory.
Require Import VST.floyd.functional_base.
Require Import PropList.

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


Section MatrixDef.

(*matrices are defined over arbitrary rings*)
Variable A : Type.
Variable plus : A -> A -> A.
Variable mult: A -> A -> A.
Variable sub: A -> A -> A.
Variable opp: A -> A.
Variable zero: A.
Variable one: A.
Variable Rth: ring_theory zero one plus mult sub opp eq.

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
  m1 = m2 <-> forall i j, (i<m) -> (j<n) -> get m1 i j = get m2 i j.
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

End MatrixDef.


 
  
