Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.setoid_ring.Field_theory.
Require Import VST.floyd.functional_base.
Require Import PropList.
Require Import Field.

(*since the lemma is super long*)
Ltac exist_eq := apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.

Ltac destruct_all :=
  repeat(match goal with
  | [H : exists x, _ |- _] => first [destruct H as [?x] | destruct H as [?x'] | destruct H]
  | [H: ?P /\ ?Q |- _] => destruct H
  end).

Ltac solve_in :=
  subst;
  match goal with
  | [ H : _ |- In ?x (?y :: ?z)] => simpl; first [ left; subst; auto; reflexivity | right; solve_in ] 
  | [ H : _ |- In ?x (?l1 ++ ?l2)] => apply in_or_app; first [left; solve_in | right; solve_in]
  | [ H : _ |- In ?x ?l] => assumption
  end.

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

(*Check for bounds so we don't need to carry around hypotheses everywhere*)
Lemma zeq_in_dec : forall z1 z2 z3 : Z, {z1 <= z2 < z3} + {~(z1 <= z2 < z3)}.
Proof.
  intros. destruct (Z_le_gt_dec z1 z2).
  destruct (Z_lt_le_dec z2 z3). left. lia. right. lia. right. lia.
Qed.

(*2. swap rows r1 and r2*)
Definition swap_rows_aux (mx: matrix_type) (r1 r2 : Z) : matrix_type :=
  if (zeq_in_dec 0 r1 (Zlength mx)) then if (zeq_in_dec 0 r2 (Zlength mx)) then
  let old1 := Znth r1 mx in
  let old2 := Znth r2 mx in
  upd_Znth r2 (upd_Znth r1 mx old2) old1 else mx else mx.

Lemma swap_rows_aux_wf: forall mx m n r1 r2,
  (0 <= n) ->
  wf_matrix mx m n ->
  wf_matrix (swap_rows_aux mx r1 r2) m n.
Proof.
  intros. unfold wf_matrix in *. unfold swap_rows_aux.
  repeat(if_tac; try assumption). destruct H0.
  split. list_solve. intros.
  rewrite In_Znth_iff in H4. destruct H4 as [i].
  destruct H4.
  erewrite upd_Znth_lookup' in H5. 4 : apply H2.
  2 : list_solve. 2 : list_solve. destruct (zeq i r2).
  - subst. apply H3. apply Znth_In. assumption.
  - erewrite upd_Znth_lookup' in H5. 2 : apply H0.
    2 : list_solve. 2 : list_solve. destruct (zeq i r1).
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
  intros. unfold wf_matrix in H. destruct H. unfold swap_rows_aux. if_tac. if_tac. 2 : list_solve.
  2: list_solve. unfold get_aux. destruct (Z.eq_dec i r2).
  - subst. rewrite upd_Znth_same.  2: list_solve. if_tac. subst. reflexivity. reflexivity.
  - rewrite upd_Znth_diff. 2 : list_solve. 2 : list_solve. 2 : assumption.
    destruct (Z.eq_dec i r1).
    + subst. list_solve.
    + list_solve.
Qed.


(*3. row r2 = row r2 + k * row r1*)
Definition add_multiple_aux (mx: matrix_type) (r1 r2 : Z) (k : A) : matrix_type :=
  if (zeq_in_dec 0 r1 (Zlength mx)) then if (zeq_in_dec 0 r2 (Zlength mx)) then
  upd_Znth r2 mx (combine (Znth r2 mx) (Znth r1 mx) (fun x y => plus x (mult k y)))
  else mx else mx.

Lemma add_multiple_aux_wf: forall mx m n r1 r2 k,
  wf_matrix mx m n ->
  (0 <= n) ->
  wf_matrix (add_multiple_aux mx r1 r2 k) m n.
Proof.
  intros. unfold wf_matrix in *. unfold add_multiple_aux.
  if_tac. if_tac. all: try assumption.
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
  if_tac. if_tac. 2 : list_solve. 2 : list_solve.
  destruct H. destruct (zeq i r2).
  - subst. rewrite upd_Znth_same. 2: assumption. rewrite combine_Znth.
    if_tac. reflexivity. contradiction. rewrite H6. rewrite H6. reflexivity.
    3 : rewrite H6. 3 : assumption. all: apply Znth_In; list_solve.
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

Definition swap_rows {m n} (mx: matrix m n) (r1 r2 : Z) (N: 0 <= n) : matrix m n :=
  exist _ (swap_rows_aux (proj1_sig mx) r1 r2) (swap_rows_aux_wf (proj1_sig mx) m n r1 r2 N (proj2_sig mx)).

Lemma swap_rows_spec: forall {m n} (mx: matrix m n) r1 r2 i j (N: 0 <= n) (R1: 0 <= r1 < m) (R2: 0 <= r2 < m),
  (0 <= i < m) ->
  (0 <= j < n) ->
  get (swap_rows mx r1 r2 N) i j =
    if (Z.eq_dec i r1) then get mx r2 j
    else if (Z.eq_dec i r2) then get mx r1 j
    else get mx i j.
Proof.
  intros. unfold get. unfold swap_rows. simpl. destruct mx; simpl.
  apply (swap_rows_aux_spec _ m n); assumption.
Qed.

(*3. add multiple of row one to another*)

Definition add_multiple {m n} (mx: matrix m n) (r1 r2 : Z) (k: A) (N: 0 <= n) : matrix m n :=
  exist _ (add_multiple_aux (proj1_sig mx) r1 r2 k) (add_multiple_aux_wf (proj1_sig mx) m n r1 r2 k (proj2_sig mx) N).

Lemma add_multiple_spec: forall {m n} (mx: matrix m n) r1 r2 k i j (N: 0 <= n) (R1: 0 <= r1 < m) (R2: 0 <= r2 < m),
  (0 <= i < m) ->
  (0 <= j < n) ->
  get (add_multiple mx r1 r2 k N) i j =
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
Definition row_swap_mx n i j (N: 0 <= n): matrix n n :=
  swap_rows (identity n N) i j N.

(*Prove the row operation [swap_rows] is equivalent to multiplying by elementary matrix*)
Lemma swap_rows_elem_mx: forall {m n} (mx: matrix m n) i j (N: 0 <= n) (M: 0 <= m)(I1: 0 <= i < m) (J1 : 0 <= j < m),
  swap_rows mx i j N = mx_mult (row_swap_mx m i j M) mx M N.
Proof.
  intros. rewrite matrix_equiv.  intros.
  rewrite swap_rows_spec; try lia. rewrite mx_mult_spec; try lia.
  unfold row_swap_mx. 
  unfold summation. assert (forall l,
    (forall x, In x l -> (0 <= x<m)) ->
    summation_aux (fun k : Z => mult (get (swap_rows (identity m M) i j M) i0 k) (get mx k j0)) l =
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
  swap_rows mx i j N = swap_rows mx j i N.
Proof.
  intros. rewrite matrix_equiv. intros.
  repeat(rewrite swap_rows_spec; try assumption). 
  if_tac. subst.  if_tac; subst; try reflexivity.
  reflexivity.
Qed. 

Lemma swap_twice: forall {m n} (mx: matrix m n) r1 r2 (N: 0 <= n) (R1: 0 <= r1 < m) (R2: 0 <= r2 < m),
  swap_rows (swap_rows mx r1 r2 N) r2 r1 N = mx.
Proof.
  intros. rewrite matrix_equiv.  intros.
  repeat(rewrite swap_rows_spec; try assumption).
  repeat(if_tac; subst; try reflexivity; try contradiction).
Qed. 

(*The swap matrix is invertible, and, moreover, it is its own inverse*)
Lemma row_swap_mx_inv: forall n i j (N: 0 <= n) (I1 : 0 <= i < n) (J1: 0 <= j < n),
  inverse (row_swap_mx n i j N) (row_swap_mx n i j N) N.
Proof.
  intros. unfold inverse. rewrite <- swap_rows_elem_mx.
  unfold row_swap_mx. rewrite swap_sym. split; apply (swap_twice). all: assumption.
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

Definition add_multiple_mx n r1 r2 c (N: 0 <= n) :=
  add_multiple (identity n N) r1 r2 c N.

Lemma add_multiple_mx_spec: forall n r1 r2 c i j (N: 0 <= n) (R1: 0 <= r1 < n) (R2: 0 <= r2 < n),
  (0 <= i < n) ->
  (0 <= j < n) ->
  r1 <> r2 ->
  get (add_multiple_mx n r1 r2 c N) i j =
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
  add_multiple mx r1 r2 c N = mx_mult (add_multiple_mx m r1 r2 c M) mx M N.
Proof.
  intros. rewrite matrix_equiv. intros.
  rewrite add_multiple_spec; try assumption. rewrite mx_mult_spec; try lia.
  unfold summation.
  assert (forall l, (forall x, In x l -> (0 <= x < m)) ->
    summation_aux (fun k : Z => mult (get (add_multiple_mx m r1 r2 c M) i k) (get mx k j)) l =
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
  inverse (add_multiple_mx n r1 r2 c N) (add_multiple_mx n r1 r2 (opp c) N) N.
Proof.
  intros. unfold inverse. assert (forall x, 
    mx_mult (add_multiple_mx n r1 r2 x N) (add_multiple_mx n r1 r2 (opp x) N) N N = identity n N). {
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
    elem_matrix (row_swap_mx m i j M)
  | e_scalar: forall i c,
    0 <= i < m ->
    c <> zero ->
    elem_matrix (scalar_mult_mx m i c M)
  | e_add_multiple: forall i j c (I1: 0 <= i < m) (J1: 0 <= j < m),
    i <> j -> (*this is invalid or just scalar mult anyway*)
    elem_matrix (add_multiple_mx m i j c M).

Lemma elem_matrix_invertible: forall mx,
  elem_matrix mx -> invertible mx M.
Proof.
  intros. unfold invertible. inversion H.
  - exists (row_swap_mx m i j M). apply row_swap_mx_inv; assumption.
  - exists (scalar_mult_mx m i (inv c) M). apply scalar_mult_inv; assumption.
  - exists (add_multiple_mx m i j (opp c) M). apply add_multiple_inv; try assumption.
Qed.

Lemma elem_matrix_inverse_elementary: forall mx mx',
  elem_matrix mx ->
  inverse mx mx' M ->
  elem_matrix mx'.
Proof.
  intros. inversion H; subst.
  - pose proof (row_swap_mx_inv m i j M I1 J1).
    assert (mx' = row_swap_mx m i j M). eapply inverse_unique. 2 : apply H1. assumption.
    subst. assumption.
  - pose proof (scalar_mult_inv m i c M H1 H2).
    assert (mx' = (scalar_mult_mx m i (inv c) M)). eapply inverse_unique. 2 : apply H3. assumption.
    subst. constructor. assumption. apply inv_nonzero; assumption.
  - pose proof (add_multiple_inv m i j c M I1 J1 H1). 
    assert (mx' = (add_multiple_mx m i j (opp c) M)). eapply inverse_unique. 2 : apply H2.
    assumption. subst. constructor. all: assumption.
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
    ERO mx (swap_rows mx r1 r2 N)
  | ero_scalar: forall mx i c,
    (0 <= i < m) ->
    c <> zero ->
    ERO mx (scalar_mul_row mx i c M N)
  | ero_add: forall mx r1 r2 c (R1: 0 <= r1 < m) (R2: 0 <= r2 < m),
    r1 <> r2 ->
    ERO mx (add_multiple mx r1 r2 c N).


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
    + exists (row_swap_mx m r1 r2 M). split. constructor; assumption.
      apply swap_rows_elem_mx; assumption.
    + exists (scalar_mult_mx m i c M). split. constructor; assumption.
      apply scalar_mult_elem; assumption.
    + exists (add_multiple_mx m r1 r2 c M). split. constructor; assumption.
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


(** Gaussian Elimination *)

Section Gaussian.

Variable Aeq_dec: forall x y : A, {x = y } + { x <> y}.
Variable n : Z.
Variable N : 0 <= n.
Variable m : Z.
Variable M : 0 <= m.

(*Gaussian elimination helpers*)
Section GaussHelp.

(*return the first element and value in list l that is nonzero*)
Definition get_fst (l: list Z) (f: Z -> A) : option (A * Z) :=
  fold_right (fun x acc => if Aeq_dec (f x) zero then acc else Some (f x, x)) None l.

Lemma get_fst_none_iff: forall l f,
  get_fst l f = None <-> forall x, In x l -> f x = zero.
Proof.
  intros. induction l; intros; split; intros.
  - inversion H0.
  - reflexivity.
  - simpl in H0. simpl in H. destruct (Aeq_dec (f a) zero).
    destruct H0. subst. assumption. apply IHl; assumption. inversion H.
  - simpl. if_tac. apply IHl. apply (all_list _ _ _ H). rewrite H in H0. contradiction.
    left. reflexivity.
Qed.


Lemma get_fst_some_iff: forall l f a' z',
  get_fst l f = Some (a', z') <-> exists l1 l2, l = l1 ++ z' :: l2 /\
    f z' = a' /\ a' <> zero /\ forall x, In x l1 -> f x = zero.
Proof.
  intros. induction l; split; intros.
  - inversion H.
  - destruct_all. destruct l1; inversion H.
  - simpl in H. destruct (Aeq_dec (f a) zero). 
    apply IHl in H. destruct_all. exists (a :: l1). exists l2. split. subst. reflexivity.
    repeat(split; try assumption).
    intros. destruct H3. subst. assumption. apply H2. assumption.
    inversion H; subst. exists nil. exists l. split. reflexivity. split. reflexivity.
    split. assumption. intros. inversion H0.
  - simpl. if_tac. apply IHl. destruct_all.
    destruct l1. inversion H; subst. contradiction. inversion H; subst. 
    exists l1. exists l2. split. reflexivity. split. reflexivity. split. assumption.
    apply (all_list _ _ _ H3). destruct_all.
    subst. destruct l1. inversion H; subst. reflexivity. inversion H; subst. 
    rewrite H3 in H0. contradiction. left. reflexivity.
Qed.

(*The leading coefficient of a row, if one exists*)
Definition leading_coefficient (mx: matrix m n) (row : Z) : option (A * Z) :=
  get_fst (Zseq 0 n) (fun col => get mx row col).

(*TODO: move*)
Lemma seq_split: forall a b l1 c l2,
  seq a b = l1 ++ c :: l2 -> (forall x, (a <= x < c)%nat <-> In x l1) /\ (forall x, (c < x < a + b)%nat <-> In x l2).
Proof.
  intros. generalize dependent H. revert a l1 c l2. induction b; intros.
  - simpl in H. destruct l1; inversion H.
  - simpl in H. destruct l1. inversion H; subst.
    split; intros; split; intros. lia. inversion H0. rewrite in_seq. lia. rewrite in_seq in H0. lia.
    inversion H; subst. apply IHb in H2. destruct H2.
    split; intros; split; intros. assert (n0 = x \/ n0 < x)%nat by lia.
    destruct H3. subst. left. reflexivity. right. apply H0. lia.
    destruct H2. subst. inversion H; subst.
    assert (E: In c (seq (S x) b)). rewrite H3. apply in_or_app. right. left. reflexivity.
    rewrite in_seq in E. lia. apply H0 in H2. lia. apply H1. lia. apply H1 in H2. lia.
Qed. 

Lemma map_split: forall {A B} (f: A -> B) l l1 l2,
  map f l = l1 ++ l2 ->
  exists l1' l2', l = l1' ++ l2' /\ map f l1' = l1 /\ map f l2' = l2.
Proof.
  intros. generalize dependent l1. generalize dependent l2. induction l; intros.
  - simpl in H. destruct l1. destruct l2. exists nil. exists nil. split3; reflexivity. inversion H. inversion H.
  - simpl in H. destruct l1. 
    + destruct l2; inversion H; subst. exists nil. exists (a :: l). split. reflexivity. split. reflexivity.
      reflexivity.
    + inversion H; subst. apply IHl in H2. destruct_all. subst. exists (a :: l1'). exists l2'.
      split3; reflexivity.
Qed.

Lemma Zseq_split: forall a b l1 c l2,
  (0 <= a) ->
  (0 <= b) ->
  Zseq a b = l1 ++ c :: l2 -> (forall x, (a <= x < c) <-> In x l1) /\ (forall x, (c < x < a + b) <-> In x l2).
Proof.
  intros. unfold Zseq in H1. apply map_split in H1. destruct_all. destruct l2'. inversion H3.
  apply seq_split in H1. inversion H3; subst. destruct H1. split.
  intros. split; intros. rewrite in_map_iff. exists (Z.to_nat x). split. lia.
  apply H1. lia. rewrite in_map_iff in H4. destruct_all. subst. apply H1 in H5. lia.
  intros; split; intros. rewrite in_map_iff. exists (Z.to_nat x). split. lia. apply H2. lia.
  rewrite in_map_iff in H4. destruct_all. subst. apply H2 in H5. lia.
Qed. 


Lemma leading_coefficient_some_iff: forall mx row k col,
  0 <= row < m ->
  leading_coefficient mx row = Some (k, col) <-> (0 <= col < n) /\ k <> zero /\ get mx row col = k /\
    forall x, (0 <= x < col) -> get mx row x = zero.
Proof.
  intros. unfold leading_coefficient. rewrite get_fst_some_iff. split; intros.
  - destruct_all. assert (In col (Zseq 0 n)). rewrite H0. solve_in. split. rewrite Zseq_In in H5; lia.
    split. assumption. split. assumption. 
     apply Zseq_split in H0. intros. apply H3. apply H0. lia. lia. assumption.
  - destruct_all. assert (In col (Zseq 0 n)). rewrite Zseq_In; lia.
    apply In_split in H6. destruct_all. assert (ZS:= H6). apply Zseq_split in H6; try lia.
    exists l1. exists l2. split. assumption. split. assumption. split. assumption. intros. apply H3.
    apply H6 in H7. lia.
Qed.

Lemma leading_coefficient_none_iff: forall mx row,
  0 <= row < m ->
  leading_coefficient mx row = None <-> (forall x, (0 <= x < n) -> get mx row x = zero).
Proof.
  intros. unfold leading_coefficient. rewrite get_fst_none_iff. split; intros. apply H0.
  rewrite Zseq_In; lia. apply H0. rewrite Zseq_In in H1; lia.
Qed.

(*look for first nonzero entry in column c, starting at row r*)
Definition find_nonzero_row (mx: matrix m n) (c r: Z) : option Z :=
  match (get_fst (Zseq r (m - r)) (fun row => get mx row c)) with
    | None => None
    | Some (c', n') => Some n'
  end.

Lemma find_nonzero_row_some: forall mx c r n',
  (0 <= r < m) ->
  find_nonzero_row mx c r = Some n' ->
  (r <= n' < m) /\ get mx n' c <> zero.
Proof.
  intros. unfold find_nonzero_row in H0. destruct (get_fst (Zseq r (m - r)) (fun row : Z => get mx row c)) eqn : G.
  - destruct p. inversion H0; subst. rewrite get_fst_some_iff in G. destruct_all.
    split. assert (In n' (Zseq r (m - r))). rewrite H1. apply in_or_app. right. left. reflexivity.
    rewrite Zseq_In in H6; try lia. subst. assumption.
  - inversion H0.
Qed.

Lemma find_nonzero_row_none: forall mx c r,
  (0 <= r < m) ->
  find_nonzero_row mx c r = None ->
  (forall n', r <= n' < m -> get mx n' c = zero).
Proof.
  intros. unfold find_nonzero_row in H0. destruct (get_fst (Zseq r (m - r)) (fun row : Z => get mx row c)) eqn : G.
  destruct p. inversion H0. rewrite get_fst_none_iff in G. apply G.
  rewrite Zseq_In; lia.
Qed.

(*Make all nonzeroes in column c = one*)
Definition  all_columns_one_aux (mx: matrix m n) (c: Z) (l: list Z): matrix m n :=
  fold_right (fun x acc => let f := (get mx x c) in 
                             if (Aeq_dec f zero) then acc else (scalar_mul_row acc x (inv f) M N)) mx l.

Definition all_columns_one (mx: matrix m n) (c: Z) : matrix m n :=
  all_columns_one_aux mx c (Zseq 0 m).

Lemma all_columns_one_aux_row_equiv: forall (mx: matrix m n) c l,
  (forall x, In x l -> (0 <= x < m)) ->
  row_equivalent m M n N mx (all_columns_one_aux mx c l).
Proof.
  intros. induction l. simpl. constructor. simpl.
  if_tac.
  - apply IHl. apply (all_list _ _ _ H).
  - eapply row_equivalent_trans. apply IHl. apply (all_list _ _ _ H). apply row_equivalent_ero.
    constructor. apply (fst_list _ _ _ H). apply inv_nonzero. assumption.
Qed. 

Lemma all_columns_one_row_equiv: forall (mx: matrix m n) c,
  row_equivalent m M n N mx (all_columns_one mx c).
Proof.
  intros. unfold all_columns_one. apply all_columns_one_aux_row_equiv. intros.
  rewrite Zseq_In in H; lia.
Qed.

(*Specification of matrix resulting from [all_columns_one]*)
Lemma all_columns_one_aux_notin: forall mx c l x y,
  (0 <= c < n) ->
  (0 <= x < m) ->
  (0 <= y < n) ->
  (forall z, In z l -> 0 <= z < m) ->
  ~In x l ->
  get (all_columns_one_aux mx c l) x y = get mx x y.
Proof.
  intros. induction l.
  - reflexivity.
  - specialize (IHl (all_list _ _ _ H2)). assert (~In x l). intro. apply H3; solve_in.
    specialize (IHl H4). clear H4. simpl. if_tac. assumption.
    rewrite scalar_mul_row_spec; try lia. if_tac. subst. exfalso. apply H3. solve_in.
    assumption. apply (fst_list _ _ _ H2).
Qed. 

Lemma all_columns_one_aux_spec: forall mx c l x y,
  (0 <= c < n) ->
  (0 <= x < m) ->
  (0 <= y < n) ->
  (forall z, In z l -> 0 <= z < m) ->
  In x l ->
  NoDup l ->
  get (all_columns_one_aux mx c l) x y = if (Aeq_dec (get mx x c) zero) then get mx x y else mult (inv (get mx x c)) (get mx x y).
Proof.
  intros. induction l; simpl.
  - inversion H3.
  - specialize (IHl (all_list _ _ _ H2)). pose proof (all_list _ _ _ H2). simpl in H5.
    pose proof (fst_list _ _ _ H2). simpl in H6. inversion H4; subst. destruct H3.
    + subst. if_tac. apply all_columns_one_aux_notin; assumption.
      rewrite scalar_mul_row_spec; try lia. if_tac; try contradiction.
      rewrite all_columns_one_aux_notin; try assumption. reflexivity.
    + specialize (IHl H3 H10). if_tac. assumption. rewrite scalar_mul_row_spec; try lia.
      if_tac. subst. contradiction. assumption.
Qed.

Lemma all_columns_one_spec: forall mx c x y,
  (0 <= c < n) ->
  (0 <= x < m) ->
  (0 <= y < n) ->
  (0 <= x < m) ->
  get (all_columns_one mx c) x y = if (Aeq_dec (get mx x c) zero) then get mx x y else mult (inv (get mx x c)) (get mx x y).
Proof.
  intros. unfold all_columns_one. apply all_columns_one_aux_spec; try assumption. intros. rewrite Zseq_In in H3; lia.
  rewrite Zseq_In; lia. apply Zseq_NoDup; lia.
Qed.

Definition negone := opp one.

(*subtract all rows with a nonzero entry in column c from row r, except for row r itself*)
Definition subtract_all_rows_aux (mx: matrix m n) (r c: Z) (l: list Z) : matrix m n :=
  fold_right (fun x acc => if (Z.eq_dec x r) then acc else let f := (get mx x c) in
                            if (Aeq_dec f zero) then acc else (add_multiple acc r x negone N)) mx l.

Definition subtract_all_rows (mx : matrix m n) (r c: Z) : matrix m n :=
  subtract_all_rows_aux mx r c (Zseq 0 m). 

Lemma subtract_all_rows_aux_row_equiv: forall (mx: matrix m n) r c l,
  (0 <= r < m) ->
  (forall x, In x l -> (0 <= x < m)) ->
  row_equivalent m M n N mx (subtract_all_rows_aux mx r c l).
Proof.
  intros. induction l.
  - simpl. constructor.
  - simpl. if_tac.
    + apply IHl. apply (all_list _ _ _ H0).
    + if_tac.
      * apply IHl. apply (all_list _ _ _ H0).
      * eapply row_equivalent_trans. apply IHl. apply (all_list _ _ _ H0). apply row_equivalent_ero.
        constructor. assumption. apply (fst_list _ _ _ H0). auto.
Qed.

Lemma subtract_all_rows_row_equiv: forall (mx: matrix m n) r c,
  (0 <= r < m) ->
  row_equivalent m M n N mx (subtract_all_rows mx r c).
Proof.
  intros. unfold subtract_all_rows. apply subtract_all_rows_aux_row_equiv.
  assumption. intros. rewrite Zseq_In in H0; lia.
Qed.  
(*
Lemma subtract_all_rows_aux_split: forall mx r c x y l l1 l2,
  l = l1 
*)

(*Specification of matrix from [subtract_all_rows]*)
Lemma subtract_all_rows_aux_same: forall mx r c y l,
  (0 <= r < m) ->
  (0 <= y < n) ->
  (forall x, In x l -> 0 <= x < m) ->
  get (subtract_all_rows_aux mx r c l) r y = get mx r y.
Proof.
  intros. induction l; simpl.
  - reflexivity.
  - specialize (IHl (all_list _ _ _ H1)). pose proof (fst_list _ _ _ H1). simpl in H2.
    if_tac. subst. assumption. if_tac. assumption.
    rewrite add_multiple_spec; try assumption. if_tac. subst. contradiction. assumption.
Qed. 

Lemma subtract_all_rows_aux_notin: forall mx r c x y l,
  (0 <= r < m) ->
  (0 <= c < n) ->
  (0 <= x < m) ->
  (0 <= y < n) ->
  (forall x, In x l -> 0 <= x < m) ->
  ~In x l ->
  get (subtract_all_rows_aux mx r c l) x y = get mx x y.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. specialize (IHl (all_list _ _ _ H3)). pose proof (fst_list _ _ _ H3). simpl in H5.
    if_tac. subst. apply IHl. intro. apply H4. solve_in.
    if_tac. apply IHl. intro. apply H4; solve_in.
    rewrite add_multiple_spec; try lia.
    if_tac. subst. exfalso. apply H4. solve_in. apply IHl. intro. apply H4; solve_in.
Qed. 
(*
Lemma mult_negone: forall x,
  mult negone x = sub zero x.
Proof.
  intros. u  ring_simplify'. unfold negone. ring'. ring'.

Lemma mult_negone: forall x y,
  plus x (mult negone y) = sub x y.
Proof.
  intros. ring_simplify'. Search f_mult. field'. ring'.
*)
Lemma subtract_all_rows_aux_diff: forall (mx: matrix m n) r c x y l,
  (forall x, In x l -> 0 <= x < m) ->
  (0 <= r < m) ->
  (0 <= c < n) ->
  (0 <= y < n) ->
  (0 <= x < m) ->
  x <> r ->
  In x l ->
  NoDup l ->
  get (subtract_all_rows_aux mx r c l) x y = if (Aeq_dec (get mx x c) zero) then get mx x y else (sub (get mx x y) (get mx r y)). 
Proof.
  intros. induction l. inversion H5.
  specialize (IHl (all_list _ _ _ H)). pose proof (fst_list _ _ _ H). simpl in H7. simpl in H5.
  inversion H6; subst. simpl. destruct H5. subst.
  if_tac. contradiction. if_tac.
  apply subtract_all_rows_aux_notin; try assumption. apply (all_list _ _ _ H).
  rewrite add_multiple_spec; try lia. if_tac; try contradiction. rewrite subtract_all_rows_aux_notin; try assumption.
  rewrite subtract_all_rows_aux_same; try assumption. unfold negone; ring'. 
  all: try (apply (all_list _ _ _ H)).
  if_tac. subst. apply IHl; assumption. if_tac. apply IHl; assumption.
  rewrite add_multiple_spec; try assumption. if_tac. subst. contradiction.
  apply IHl; assumption.
Qed.

Lemma subtract_all_rows_same: forall mx r c y,
  (0 <= r < m) ->
  (0 <= y < n) ->
  get (subtract_all_rows mx r c ) r y = get mx r y.
Proof.
  intros. unfold subtract_all_rows. apply subtract_all_rows_aux_same; try assumption.
  intros. rewrite Zseq_In in H1; lia.
Qed.

Lemma subtract_all_rows_diff: forall mx r c x y,
  (0 <= r < m) ->
  (0 <= c < n) ->
  (0 <= y < n) ->
  (0 <= x < m) ->
  x <> r ->
  get (subtract_all_rows mx r c) x y = if (Aeq_dec (get mx x c) zero) then get mx x y else (sub (get mx x y) (get mx r y)).
Proof.
  intros. unfold subtract_all_rows. apply subtract_all_rows_aux_diff; try assumption.
  intros. rewrite Zseq_In in H4; lia. rewrite Zseq_In; lia. apply Zseq_NoDup; lia.
Qed. 


End GaussHelp.


(** Gaussian Elimination *)
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
Section GaussianElim.

(*reduced row echelon form without the requirement that all coefficients are leading ones*)
Inductive reduced_row_echelon_no1 : matrix m n -> Prop :=
  | r_rref' (mx: matrix m n) :
      (*all rows of zeroes are at the bottom*)
     (exists r : Z, 0 <= r <= m /\ forall x, (0 <= x < m) -> leading_coefficient mx x = None <-> (r <= x)) ->
      (*all leading coefficients appear in order*)
      (forall i j n1 n2 c1 c2, (0 <= i < j) -> (0 <= j < m) ->
      leading_coefficient mx i = Some (c1, n1) ->
      leading_coefficient mx j = Some (c2, n2) ->
      n1 < n2) ->
      (*each column with a leading coefficient has zeroes in all other columns*)
      (forall i c' n', (0 <= i < m) -> leading_coefficient mx i = Some (c', n') ->
        (forall x, 0 <= x < m -> x <> i -> get mx x n' = zero)) ->
      reduced_row_echelon_no1 mx.

Inductive reduced_row_echelon : matrix m n -> Prop :=
  | r_rref (mx: matrix m n) :
      reduced_row_echelon_no1 mx ->
      (*all leading coefficients are 1*)
      (forall i n c, (0 <= i < m) -> leading_coefficient mx i = Some (c, n) -> c = one) ->
      reduced_row_echelon mx.

(*To prove that Gaussian elimination results in a matrix in reduced row echelon form, we use the following
  invariant, representing a matrix that has been partially row reduced - up to row r and column c*)
Inductive gaussian_invariant: matrix m n -> Z -> Z -> Prop :=
  | r_inv (mx: matrix m n) ( r c : Z) :
    (*(*all rows of all zeroes are below the first r rows*)
    (forall x : nat, leading_coefficient (get_row mx x) n = None <-> (r<x)%nat) ->*)
    (*leading coefficients are strictly to the right of those in rows above*)
    (forall i j n1 n2 c1 c2, (0 <= i<j) -> (0 <= j < r) ->
      leading_coefficient mx i = Some (c1, n1) ->
      leading_coefficient mx j = Some (c2, n2) ->
      (n1 < n2)) ->
    (*for rows < r, leading coefficient exists and occurs before column c*)
    (forall r', (0 <= r' < r) -> exists n1 c1,
      leading_coefficient mx r' = Some (c1, n1) /\ (0 <= n1 < c)) ->
    (*for the first c - 1 columns, each column with a leading coefficient has all other entries 0 *)
    (forall i c' n', (0 <= i < m) -> leading_coefficient mx i = Some (c', n') ->
      (0 <= n' < c) ->
      forall x, (0 <= x < m) -> x <> i -> get mx x n' = zero) ->
    (*all rows >= r have zeroes in the first c-1 entries*)
    (forall r' c', (r <= r' < m) -> (0 <= c' < c) -> get mx r' c' = zero) ->
    gaussian_invariant mx r c.

(*A single step of Gaussian elimination - given a matrix satisfying the invariant for (r, c), returns a matrix
  and (r', c') such that mx' satisfies invariant up to (r', c') and (r' + c' > r + c)*)
Definition gauss_one_step (mx: matrix m n) (r c : Z) : (matrix m n * Z * Z) :=
  match (find_nonzero_row mx c r) with
        | Some k =>
            let mx1 := swap_rows mx k r N in
            let mx2 := all_columns_one mx1 c in
            let mx3 := subtract_all_rows mx2 r c in
            (mx3, (r+1), (c+1))
        | None => (mx, r, (c+1))
      end.

Definition get_matrix {m n} (t: matrix m n * Z * Z) : matrix m n :=
  match t with
  | (x, _, _) => x
  end.

(*Gaussian Elimination Proof of Correctness*)

(*First, we prove that after each step, the resulting matrix is still row equivalent*)
Lemma gauss_one_step_row_equiv: forall mx r c,
  (0 <= r < m) ->
  row_equivalent m M n N mx (get_matrix (gauss_one_step mx r c)).
Proof.
  intros. unfold gauss_one_step. destruct (find_nonzero_row mx c r) eqn : F1.
  - assert (B: 0 <= z < m). { apply find_nonzero_row_some in F1. lia. assumption. }
    simpl. eapply row_equivalent_trans. 2 : apply subtract_all_rows_row_equiv.
    eapply row_equivalent_trans. 2 : apply all_columns_one_row_equiv. apply row_equivalent_ero.
    constructor. all: assumption.
  - simpl. constructor.
Qed.

Definition some_snd {A B : Type} (o : option (A * B)) : option B :=
  match o with
  | None => None
  | Some (a,b) => Some b
  end.

(*TODO: move*)
Lemma field_integral_domain: forall r1 r2, mult r1 r2 = zero -> r1 = zero \/ r2 = zero.
Proof.
  intros. destruct (Aeq_dec r1 zero).
  - subst. left. reflexivity.
  - assert (inv r1 <> zero) by (apply inv_nonzero; assumption). 
    assert (mult (inv r1) (mult r1 r2) = zero). rewrite H. ring'.
    assert (mult (inv r1) (mult r1 r2) = r2). field'; assumption.
    rewrite H2 in H1. subst. right. reflexivity.
Qed.

(*Now, we show that the invariant is preserved*)
Lemma gauss_one_step_invar: forall mx r c,
  (0 <= r < m) ->
  (0 <= c < n) ->
  gaussian_invariant mx r c ->
  match (gauss_one_step mx r c) with
  | (mx', r', c') => gaussian_invariant mx' r' c'
  end.
Proof.
  intros. destruct (gauss_one_step mx r c) eqn : G. rename z into c'. destruct p as [mx' r'].
  unfold gauss_one_step in G. inversion H1; subst. destruct (find_nonzero_row mx c r) eqn : FN.
  inversion G; subst. clear G.
  - apply find_nonzero_row_some in FN. destruct FN. 2: assumption.
    (*structure of the resulting matrix - the beginning part does not change (except for the leading coefficient values*)
    assert (S1: forall x y, 0 <= x < r -> 0 <= y < c ->
      get mx x y = zero <-> get (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) x y = zero). {
    intros. rewrite subtract_all_rows_diff; try lia. split; intros.
    - assert (get (swap_rows mx z r N) x y = zero). rewrite swap_rows_spec; try lia. if_tac; try lia.
      if_tac; try lia. assumption.
      assert (get (all_columns_one (swap_rows mx z r N) c) x y = zero). rewrite all_columns_one_spec; try lia.
      if_tac. assumption. rewrite H11. ring'. 
      if_tac. assumption. (*since y < c, get (mx z y) = zero*)
      rewrite H12.
      assert (get (swap_rows mx z r N) r y = zero). rewrite swap_rows_spec; try lia. if_tac; try lia.
      subst. apply H5; lia. if_tac; try contradiction. apply H5; lia. 
      rewrite all_columns_one_spec; try lia. if_tac. rewrite H14. ring'.
      rewrite H14. ring'.
    - destruct (Aeq_dec (get (all_columns_one (swap_rows mx z r N) c) x c) zero).
      rewrite all_columns_one_spec in H10; try lia. 
      rewrite all_columns_one_spec in e; try lia.
      destruct (Aeq_dec (get (swap_rows mx z r N) x c) zero).
      rewrite swap_rows_spec in H10; try lia.
      destruct (Z.eq_dec x z); try lia. destruct (Z.eq_dec x r); try lia. assumption.
      apply field_integral_domain in e. destruct e. pose proof (inv_nonzero _ n0). contradiction.
      contradiction.
      assert (get (swap_rows mx z r N) r y = zero). rewrite swap_rows_spec; try lia.
      repeat(if_tac; try lia; try (apply H5; lia)).
      assert (get (all_columns_one (swap_rows mx z r N) c) r y = zero). 
      rewrite all_columns_one_spec; try lia. if_tac. assumption. rewrite H11. ring'.
      rewrite H12 in H10.
      assert (forall x, sub x zero = x) by (intros; ring'). rewrite H13 in H10.
      clear H13. 
      rewrite all_columns_one_spec in H10; try lia.
      destruct (Aeq_dec (get (swap_rows mx z r N) x c) zero).
      rewrite swap_rows_spec in H10; try lia. destruct (Z.eq_dec x z); try lia.
      destruct (Z.eq_dec x r); try lia. assumption.
      assert ((get (swap_rows mx z r N) x c) <> zero). {
      rewrite all_columns_one_spec in n0; try lia. destruct (Aeq_dec (get (swap_rows mx z r N) x c) zero).
      contradiction. assumption. } 
      apply field_integral_domain in H10. destruct H10. pose proof (inv_nonzero _ H13). contradiction.
      rewrite swap_rows_spec in H10; try lia. destruct (Z.eq_dec x z); try lia. destruct (Z.eq_dec x r); try lia.
      assumption. }
      (*second structure result: all entries with col = c and row <> r are zero *)
      assert (S2: forall x, 0 <= x < m -> r <> x -> get (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) x c = zero). {
      intros. rewrite subtract_all_rows_diff; try lia. if_tac.
      - assumption.
      - rewrite? all_columns_one_spec; try lia. if_tac.
        + rewrite H11. if_tac. rewrite H12. ring'. 
          rewrite all_columns_one_spec in H10; try lia. rewrite H11 in H10.
          destruct (Aeq_dec zero zero); try contradiction.
        + if_tac. rewrite swap_rows_spec in H12; try lia.
          destruct (Z.eq_dec r z); try lia. subst. contradiction. destruct (Z.eq_dec r r); try contradiction. field'.
          split; assumption. }
      (*third structure result: all entries with row >= r and col < c are still zero*)
      assert (S3 : forall x y, r <= x < m -> 0 <= y < c ->
        get (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) x y = zero). { intros.
      assert (x = r \/ r < x < m) by lia. destruct H10.
      - subst. rewrite subtract_all_rows_same; try lia. rewrite all_columns_one_spec; try lia.
        if_tac. rewrite swap_rows_spec; try lia. if_tac; try lia. subst. apply H5; lia.
        if_tac; apply H5; lia. assert ((get (swap_rows mx z r N) r y) = zero).
        rewrite swap_rows_spec; try lia. if_tac; try lia. apply H5; lia. if_tac; try contradiction.
        apply H5; lia. rewrite H11. ring'.
      - rewrite subtract_all_rows_diff; try lia. if_tac.
        + rewrite all_columns_one_spec; try lia. if_tac. rewrite swap_rows_spec; try lia.
          repeat(if_tac; try lia; try(apply H5; lia)). 
          assert ((get (swap_rows mx z r N) x y) = zero). rewrite swap_rows_spec; try lia.
          repeat(if_tac; try lia; try(apply H5; lia)). rewrite H13. ring'.
        + assert ((get (swap_rows mx z r N) x y) = zero). rewrite swap_rows_spec; try lia.
          repeat(if_tac; try lia; try (apply H5; lia)). rewrite? all_columns_one_spec; try lia. rewrite H12.
          assert (get (swap_rows mx z r N) r y = zero). rewrite swap_rows_spec; try lia.
          repeat(if_tac; try lia; subst; try(apply H5; lia)). rewrite H13.
          if_tac. if_tac. ring'. ring'. if_tac. ring'. ring'. }
      (*4th structure theorem: the entry (r, c) is one*)
      assert (S4: get (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) r c = one). { 
      rewrite subtract_all_rows_same; try lia. rewrite all_columns_one_spec; try lia. if_tac.
      rewrite swap_rows_spec in H8; try lia. destruct (Z.eq_dec r z); try lia. subst. contradiction.
      destruct (Z.eq_dec r r); try contradiction. field'. apply H8. }
      (* 5 (follows from others): for rows < r, leading coefficient position is same*)
      assert (S5: forall x, 0 <= x < r ->
      some_snd (leading_coefficient mx x) = 
        some_snd (leading_coefficient (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) x)). {
      intros. specialize (H3 x H8). destruct H3 as [n']. destruct H3 as [a]. destruct H3. rewrite H3. simpl.
      destruct (leading_coefficient (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) x) eqn : L.
      destruct p. apply leading_coefficient_some_iff in L. destruct_all.
      simpl. apply leading_coefficient_some_iff in H3. destruct_all. assert (n' = z0 \/ n' < z0 \/ n' > z0) by lia.
      destruct H24. subst. reflexivity. destruct H24. 
      assert (get (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) x n' = zero).
      apply H13; lia. rewrite <- S1 in H25; try lia. subst. contradiction.
      assert (get mx x z0 = zero). apply H22; lia. rewrite S1 in H25; try lia.
      subst. contradiction. lia. lia. rewrite leading_coefficient_none_iff in L.
      rewrite leading_coefficient_some_iff in H3; try lia. destruct_all. subst.
      specialize (L n').  assert (get (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) x n' = zero).
      apply L; lia. rewrite <- S1 in H13. subst. contradiction. lia. lia. lia. }
      (* 6: again follows, the leading coefficient of row r is (one, c)*)
      assert (S6: leading_coefficient (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) r = Some (one, c)). {
      rewrite leading_coefficient_some_iff. split. lia. split. apply ((F_1_neq_0 (Fth))).
      split. apply S4. intros. apply S3. lia. assumption. lia. }
      (*Now, we prove that each invariant is preserved*)
      (*we prove the first invariant separately because we need it later*)
      assert (I1: forall (i j n1 n2 : Z) (c1 c2 : A),
        0 <= i < j ->
        0 <= j < r + 1 ->
        leading_coefficient (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) i = Some (c1, n1) ->
        leading_coefficient (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) j = Some (c2, n2) ->
        n1 < n2). {
          intros. assert (0 <= j < r \/ j = r) by lia. destruct H12.
        * assert (L1 := S5 i). assert (0 <= i < r) by lia. specialize (L1 H13); clear H13.
          rewrite H10 in L1. simpl in L1. destruct (leading_coefficient mx i) eqn : L1'. destruct p.
          inversion L1; subst. 2 : inversion L1. 
          specialize (S5 j H12). rewrite H11 in S5. simpl in S5.
          destruct (leading_coefficient mx j) eqn : L2'. destruct p.
          inversion S5; subst. eapply H2. 3 : apply L1'. 3 : apply L2'. all: try assumption. inversion S5.
        * subst. rewrite S6 in H11. symmetry in H11. inversion H11; subst. specialize (H3 i H8). specialize (S5 i H8). destruct_all.
          rewrite H3 in S5. rewrite H10 in S5. inversion S5; subst. lia. }
      (*We also want invariant 2 separately*)
      (*assert (I2: forall r' : Z,
        0 <= r' < r + 1 ->
        exists (n1 : Z) (c1 : A),
          leading_coefficient (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) r' =
          Some (c1, n1) /\ n1 < c + 1). { 
           }*)
      constructor.
      + apply I1.
      + intros. assert (0 <= r' < r \/ r' = r) by lia. destruct H9.
        * specialize (H3 r' H9). specialize (S5 r' H9). destruct_all.
          rewrite H3 in S5. destruct (leading_coefficient (subtract_all_rows (all_columns_one (swap_rows mx z r N) c) r c) r') eqn : L.
          destruct p; inversion S5; subst. exists z0. exists a. split. reflexivity. lia. inversion S5. 
        * exists c. exists one. split. subst. apply S6. lia.
      + intros. assert (i <= r). { assert (i <= r \/ i > r) by lia. destruct H13. assumption.
        rewrite leading_coefficient_some_iff in H9; try lia. destruct_all.
        assert (n' < c \/ n' = c) by lia. destruct H24. subst. 
        exfalso. apply H16. apply S3; try lia. subst. exfalso. apply H16. apply S2; try assumption. lia.
        lia. } assert (n' < c \/ n' = c) by lia. destruct H14.
        * assert (x < r \/ x >= r) by lia. destruct H15.
          -- assert (i < r \/ i = r) by lia. destruct H16.
             ++ rewrite <- S1; try lia. specialize (S5 i). assert (0 <= i < r) by lia. specialize (S5 H17). clear H17.
                rewrite H9 in S5. simpl in S5. destruct (leading_coefficient mx i) eqn : L. destruct p. inversion S5; subst.
                2 : inversion S5. eapply H4; try assumption. 2 : apply L. lia. lia. assumption.
             ++ subst. rewrite S6 in H9. symmetry in H9. inversion H9; subst. apply S2; try lia.
          -- apply S3; try lia.
        * subst. assert (i < r \/ i = r) by lia. destruct H14.
          -- assert (c < c). eapply I1. 3 : apply H9. 3 : apply S6. lia. lia. lia.
          -- subst. eapply S2; try lia.
      + intros. assert (c' < c \/ c' = c) by lia. destruct H10.
        * apply S3; try lia.
        * subst. apply S2; lia.
  - pose proof (find_nonzero_row_none _ _ _ H FN) as FN'. inversion G; subst. clear G.
    inversion H1. constructor.
    + apply H2.
    + subst. intros. specialize (H3 r'0 H10). destruct_all. exists n1. exists c1. split. assumption. lia.
    + intros. assert (0 <= n' < c \/ n' = c) by lia. destruct H18.
      * eapply H8. 2: apply H14. all: try lia.
      * subst. (*cant have leading coeff here because smaller ones occur before, larger ones and r have zeroes*)
        assert (0 <= i < r' \/ i >= r') by lia. destruct H10.
        -- specialize (H3 i H10). destruct_all. rewrite H3 in H14. inversion H14; lia.
        -- rewrite leading_coefficient_some_iff in H14. destruct_all.
           subst. exfalso. apply H16. apply FN'. lia. lia.
    + intros. assert (0 <= c' < c \/ c' = c) by lia. destruct H15.
      * apply H9; lia.
      * subst. apply FN'; lia.
Qed.

Lemma gaussian_invariant_init: forall mx, gaussian_invariant mx 0 0.
Proof.
  intros. constructor; intros; lia.
Qed.

Definition fst' {A B C} (x: A * B * C) : A :=
  match x with
  | (a, _, _) => a
  end.

Definition snd' {A B C} (x: A * B * C) : B :=
  match x with
  | (_, b, _) => b
  end.

Definition trd' {A B C} (x: A * B * C) : C :=
  match x with
  | (_, _, c) => c
  end.

Lemma gauss_one_step_bounds: forall mx r c,
  (0 <= r < m) ->
  (0 <= c < n) ->
  match (gauss_one_step mx r c) with
  | (mx', r', c') => (Z.to_nat ((m-r') + (n-c')) < Z.to_nat ((m-r) + (n-c)))%nat
  end.
Proof.
  intros. destruct (gauss_one_step mx r c) eqn : G. destruct p. 
  unfold gauss_one_step in G. destruct (find_nonzero_row mx c r); inversion G; subst; lia.
Qed.

(*This is more complicated than it should be because of termination and the need to mantain the invariant at each step*)
Program Fixpoint gauss_all_steps_aux (r c : Z) (mx : {x : matrix m n | gaussian_invariant x r c}) {measure (Z.to_nat ((m - r) + (n-c)))} :
  { x : matrix m n * Z * Z |  row_equivalent m M n N mx (fst' x) /\ (0 <= r < m -> 0 <= c < n ->
    (((snd' x) = m /\ 0 <= (trd' x) <= n) \/ ( 0 <= (snd' x) <= m /\ (trd' x) = n))) /\ (~((0 <= r < m) /\ (0 <= c < n)) -> (snd' x) = r /\ (trd' x) = c) /\
    gaussian_invariant (fst' x) (snd' x) (trd' x)}   :=
  if (zeq_in_dec 0 r m) then
    if (zeq_in_dec 0 c n) then
      match (gauss_one_step mx r c) with
        | (mx', r', c') => gauss_all_steps_aux r' c' (exist _ mx' _)
      end
    else ((proj1_sig mx), r, c)
  else ((proj1_sig mx), r, c).
Next Obligation.
pose proof (gauss_one_step_invar mx r c).
assert (0 <= r < m) by (split; assumption).
assert (0 <= c < n) by (split; assumption).
specialize (H4 H5 H6 H3). rewrite <- Heq_anonymous in H4. assumption.
Defined.
Next Obligation.
assert (0 <= r < m). split; assumption.
assert (0 <= c < n). split; assumption.
pose proof (gauss_one_step_bounds mx r c H4 H5). rewrite <- Heq_anonymous in H6. apply H6. 
(*using lia causes awful proof term that appears everywhere*)
Defined.
Next Obligation.
remember ((gauss_all_steps_aux r' c'
           (exist (fun x : matrix m n => gaussian_invariant x r' c') mx'
              (eq_ind_r
                 (fun p : matrix m n * Z * Z =>
                  let (p0, c'0) := p in let (mx'0, r'0) := p0 in gaussian_invariant mx'0 r'0 c'0)
                 (gauss_one_step_invar mx r c (conj l1 l2) (conj l l0) H) Heq_anonymous))
           (eq_ind_r
              (fun p : matrix m n * Z * Z =>
               let (p0, c'0) := p in
               let (_, r'0) := p0 in (Z.to_nat (m - r'0 + (n - c'0)) < Z.to_nat (m - r + (n - c)))%nat)
              (gauss_one_step_bounds mx r c (conj l1 l2) (conj l l0)) Heq_anonymous))) as R. destruct R.
 simpl in HeqR. simpl in *. clear HeqR. 
destruct a.
split. (*row equivalence*)
- eapply row_equivalent_trans. apply gauss_one_step_row_equiv. 2 : { rewrite <- Heq_anonymous.
  simpl. assumption. } split; assumption.
- destruct H1. destruct H2. split.
  + intros. assert (0 <= r' < m \/ r' = m). { unfold gauss_one_step in Heq_anonymous. 
  destruct (find_nonzero_row mx c r); inversion Heq_anonymous; lia. }
  assert (0 <= c' < n \/ c' = n). { unfold gauss_one_step in Heq_anonymous. 
  destruct (find_nonzero_row mx c r); inversion Heq_anonymous; lia. }
  destruct H6. destruct H7. apply H1; assumption.
  assert (snd' x = r' /\ trd' x = c') by (apply H2; lia).
  destruct H8. right. split; lia. destruct H7. left. split; lia. 
  assert (snd' x = r' /\ trd' x = c') by (apply H2; lia).
  destruct H8. left. split; lia. 
  + split.
    * intros. lia.
    * assumption.
Defined.
Next Obligation.
split. constructor. split. intros. lia. split. intros. split; reflexivity. assumption.
Defined.
Next Obligation.
split. constructor. split. intros. lia. split. intros. split; reflexivity. assumption.
Defined.

(*still not sure if this definition will be usable - may need to redo with Equations*)

(*ending invariant implies rref without ones*)
Lemma invar_implies_rref: forall mx,
  (exists r, 0 <= r <= m /\ gaussian_invariant mx r n) \/ (exists c, 0 <= c <= n /\ gaussian_invariant mx m c) ->
  reduced_row_echelon_no1 mx.
Proof.
  intros. destruct H.
  - destruct H as [r]. destruct H. inversion H0; subst.
    (*need this in multiple places*)
    assert (S1: (forall x : Z, 0 <= x < m -> leading_coefficient mx x = None <-> r <= x)). { intros.
    split; intros. assert (x < r \/ r <= x) by lia. destruct H7. 2 : assumption.
    specialize (H2 x). assert (0 <= x < r) by lia. specialize (H2 H8). destruct_all.
    rewrite H2 in H6. inversion H6.
    rewrite leading_coefficient_none_iff. intros. apply H4; lia. lia. }
    constructor.
    + exists r. split; try lia; assumption.
    + intros. assert (0 <= j < r \/ r <= j) by lia. destruct H9.
      * eapply H1. apply H5. assumption. apply H7. apply H8.
      * rewrite <- S1 in H9. rewrite H9 in H8. inversion H8. lia.
    + intros. eapply H3. apply H5. apply H6. rewrite leading_coefficient_some_iff in H6.
      destruct H6. all: assumption.
  - destruct H as [c]. destruct H. inversion H0; subst. constructor.
    + exists m. split. lia. intros. split; intros. 
      specialize (H2 _ H5). destruct_all. rewrite H2 in H6. inversion H6. lia.
    + apply H1.
    + intros. eapply H3. apply H5. apply H6. specialize (H2 _ H5). destruct_all. rewrite H2 in H6. inversion H6; subst. lia.
      assumption. assumption.
Qed.

(*Last step: make all leading coefficients 1*)
Definition all_leading_coeffs_one_aux mx l :=
  fold_right (fun x acc => 
    match (leading_coefficient mx x) with
      | None => acc
      | Some (a, _) => scalar_mul_row acc x (inv a) M N 
    end) mx l.

Lemma leading_coeff_scalar_mul_row_diff: forall mx i j c,
  (0 <= i < m) ->
  (0 <= j < m) ->
  i <> j ->
  leading_coefficient mx i = leading_coefficient (scalar_mul_row mx j c M N) i.
Proof.
  intros. destruct (leading_coefficient mx i) eqn : L.
  - destruct p. rewrite leading_coefficient_some_iff in L; try assumption.
    symmetry. rewrite leading_coefficient_some_iff; try assumption. split. apply L. split. apply L.
    split. rewrite scalar_mul_row_spec; try lia. if_tac. contradiction. apply L.
    intros. rewrite scalar_mul_row_spec; try lia. if_tac. contradiction. apply L. assumption.
  - rewrite leading_coefficient_none_iff in L; try assumption. symmetry.
    rewrite leading_coefficient_none_iff; try assumption. intros. rewrite scalar_mul_row_spec; try lia.
    if_tac. contradiction. apply L. assumption.
Qed.

(*TODO: MOVE*)
Lemma field_cancellation: forall a b c,
  a <> zero ->
  mult a b = mult a c ->
  b = c.
Proof.
  intros. assert (mult (inv a) (mult a b) = mult (inv a) (mult a c)) by (rewrite H0; reflexivity).
  assert (mult (inv a) (mult a b) = b). field'. apply H.  
  assert (mult (inv a) (mult a c) = c). field'. apply H. rewrite H2 in H1. rewrite H3 in H1. assumption.
Qed. 

Lemma leading_coeff_scalar_mul_row_none: forall mx i j c,
  (0 <= i < m) ->
  (0 <= j < m) ->
  c <> zero ->
  leading_coefficient mx i = None <-> leading_coefficient (scalar_mul_row mx j c M N) i = None.
Proof.
  intros. split; intros. rewrite leading_coefficient_none_iff in H2; try lia.
  rewrite leading_coefficient_none_iff; try lia. intros. rewrite scalar_mul_row_spec; try lia.
  if_tac; try lia. subst. rewrite H2. ring'. lia.
  apply H2. lia.
  rewrite leading_coefficient_none_iff; try lia. rewrite leading_coefficient_none_iff in H2; try lia.
  intros. specialize (H2 _ H3). rewrite scalar_mul_row_spec in H2; try lia.
  destruct (Z.eq_dec i j). apply field_integral_domain in H2. destruct H2. contradiction. assumption.
  assumption.
Qed.

Lemma leading_coeff_scalar_mul_row_same: forall mx i c n' c',
  (0 <= i < m) ->
  c <> zero ->
  leading_coefficient mx i = Some (c', n') <-> 
  leading_coefficient (scalar_mul_row mx i c M N) i = Some ( mult c c', n').
Proof.
  intros. split; intros.
  - rewrite leading_coefficient_some_iff in H1; try assumption.
    destruct_all. rewrite leading_coefficient_some_iff; try lia.
    repeat(split; try lia). intro. apply field_integral_domain in H7. destruct H7; contradiction.
    rewrite scalar_mul_row_spec; try lia. if_tac; try contradiction. subst. reflexivity.
    intros. rewrite scalar_mul_row_spec; try lia. if_tac; try contradiction. subst. rewrite H4.
    ring'. assumption.
  - rewrite leading_coefficient_some_iff in H1; try lia. rewrite leading_coefficient_some_iff; try lia.
    destruct_all. repeat(split; try lia; try assumption). intro. subst.
    apply H2. ring'. rewrite scalar_mul_row_spec in H3; try lia. destruct (Z.eq_dec i i); try contradiction.
    apply field_cancellation in H3. assumption. assumption.
    intros. specialize (H4 _ H7). rewrite scalar_mul_row_spec in H4; try lia. destruct (Z.eq_dec i i); try lia.
    apply field_integral_domain in H4. destruct H4. contradiction. assumption.
Qed.

Lemma all_leading_coeffs_one_aux_leading_notin: forall mx l i,
  (0 <= i < m) ->
  (forall x, In x l -> (0 <= x < m)) ->
  ~In i l ->
  leading_coefficient mx i = leading_coefficient (all_leading_coeffs_one_aux mx l) i.
Proof.
  intros. induction l; simpl.
  - reflexivity.
  - specialize (IHl (all_list _ _ _ H0)). pose proof (fst_list _ _ _ H0). simpl in H2.
    pose proof (all_list _ _ _ H0). destruct (leading_coefficient mx a) eqn : L.
    + destruct p. rewrite <- leading_coeff_scalar_mul_row_diff. apply IHl. all: try assumption.
      intro. apply H1. solve_in. intro. subst. apply H1. solve_in.
    + apply IHl. intro. apply H1. solve_in.
Qed. 

Lemma all_leading_coeffs_one_aux_leading_none: forall mx l i,
  (forall x, In x l -> (0 <= x < m)) ->
  (0 <= i < m) ->  
  leading_coefficient mx i = None <-> leading_coefficient (all_leading_coeffs_one_aux mx l) i = None.
Proof.
  intros. generalize dependent i. induction l; split; intros.
  - simpl. assumption.
  - simpl in H1. assumption.
  - specialize (IHl (all_list _ _ _ H)). pose proof (all_list _ _ _ H). simpl in H2.
    pose proof (fst_list _ _ _ H). simpl in H3. simpl. destruct (leading_coefficient mx a) eqn : L.
    + destruct p. rewrite IHl in H1. rewrite (leading_coeff_scalar_mul_row_none _ _ a (inv a0)) in H1. apply H1.
      all: try lia. apply inv_nonzero. rewrite leading_coefficient_some_iff in L; try lia.
      apply L.
    + apply IHl. lia. assumption.
  - simpl in H1. specialize (IHl (all_list _ _ _ H)). pose proof (all_list _ _ _ H). simpl in H2.
    pose proof (fst_list _ _ _ H). simpl in H3. destruct (leading_coefficient mx a) eqn : L.
    + destruct p. rewrite <- leading_coeff_scalar_mul_row_none in H1; try lia. 
      apply IHl. lia. assumption. apply inv_nonzero. rewrite leading_coefficient_some_iff in L; try lia. apply L.
    + apply IHl. lia. assumption.
Qed. 

(*what we really want to know: leading coefficients are the same and in the same position, they are just one*)
Lemma all_leading_coeffs_one_aux_leading_coeffs: forall mx l i n,
  (0 <= i < m) ->
  (forall x, In x l -> (0 <= x < m)) ->
  In i l ->
  NoDup l ->
  (exists a, leading_coefficient mx i = Some(a,n)) <-> leading_coefficient (all_leading_coeffs_one_aux mx l) i = Some (one, n).
Proof.
  intros. induction l; simpl; split; intros.
  - inversion H1.
  - inversion H1.
  - specialize (IHl (all_list _ _ _ H0)). pose proof (all_list _ _ _ H0). simpl in H4.
    pose proof (fst_list _ _ _ H0). simpl in H5. inversion H2; subst. destruct H1.
    + subst. destruct_all. rewrite H1. assert (K := H1).
      assert (leading_coefficient (all_leading_coeffs_one_aux mx l) i = Some (a, n0)).
      rewrite <- all_leading_coeffs_one_aux_leading_notin; try assumption; try lia.
      rewrite (leading_coeff_scalar_mul_row_same _ _ (inv a)) in H7.
      assert (mult (inv a) a = one). rewrite leading_coefficient_some_iff in H1. destruct_all. field'. assumption.
      all: try lia. rewrite H10 in H7. apply H7. 
      apply inv_nonzero. rewrite leading_coefficient_some_iff in H1; destruct_all. assumption. lia.
    + specialize (IHl H1 H9). rewrite IHl in H3. 
      destruct (leading_coefficient mx a) eqn : L.
      * destruct p. rewrite (leading_coeff_scalar_mul_row_diff _ _ a (inv a0)) in H3. apply H3.
        lia. lia. intro. subst. contradiction.
      * assumption.
  - specialize (IHl (all_list _ _ _ H0)). pose proof (all_list _ _ _ H0). simpl in H4.
    pose proof (fst_list _ _ _ H0). simpl in H5. inversion H2; subst. destruct H1.
    + subst. destruct (leading_coefficient mx i) eqn : L.
      * destruct p. rewrite (all_leading_coeffs_one_aux_leading_notin _ l) in L.
        rewrite leading_coeff_scalar_mul_row_same in L. rewrite L in H3. inversion H3; subst.
        exists a. reflexivity. all: try lia. apply inv_nonzero. rewrite leading_coefficient_some_iff in L; try lia.
        apply L. assumption. assumption.
      * rewrite all_leading_coeffs_one_aux_leading_none in L. rewrite L in H3. inversion H3. assumption. lia.
    + specialize (IHl H1 H9). destruct (leading_coefficient mx a) eqn : L.
      * destruct p. rewrite <- (leading_coeff_scalar_mul_row_diff _ _ a (inv a0)) in H3; try lia.
        apply IHl. assumption. intro. subst. contradiction.
      * apply IHl; assumption.
Qed.

Lemma all_leading_coeffs_one_aux_get_zero: forall mx i j l,
  (0 <= i < m) ->
  (0 <= j < n) ->
  (forall x, In x l -> (0 <= x < m)) ->
  get mx i j = zero <-> get (all_leading_coeffs_one_aux mx l) i j = zero.
Proof.
  intros. induction l; simpl. reflexivity. specialize (IHl (all_list _ _ _ H1)).
  pose proof (fst_list _ _ _ H1). simpl in H2. split; intros.
  - destruct (leading_coefficient mx a) eqn : L.
    + destruct p. rewrite scalar_mul_row_spec; try lia. if_tac.
      * subst. rewrite IHl in H3. rewrite H3. ring'.
      * apply IHl. assumption.
    + apply IHl; assumption.
  - destruct (leading_coefficient mx a) eqn : L.
    + destruct p. rewrite scalar_mul_row_spec in H3; try lia.
      destruct (Z.eq_dec i a). subst. apply field_integral_domain in H3.
      destruct H3. rewrite leading_coefficient_some_iff in L; try lia. destruct_all.
      apply inv_nonzero in H5. contradiction. apply IHl. assumption. apply IHl; assumption.
    + apply IHl; assumption.
Qed. 

Lemma all_leading_coeffs_aux_row_equiv: forall mx l,
  (forall x, In x l -> (0 <= x < m)) ->
  row_equivalent m M n N mx (all_leading_coeffs_one_aux mx l).
Proof.
  intros. induction l. simpl. constructor.
  specialize (IHl (all_list _ _ _ H)). pose proof (fst_list _ _ _ H). simpl in H0.
  simpl. destruct (leading_coefficient mx a) eqn : D.
  destruct p. eapply row_equivalent_trans. apply IHl. apply row_equivalent_ero. constructor. lia.
  apply inv_nonzero. apply leading_coefficient_some_iff in D; try lia. apply D.
  apply IHl.
Qed. 

(*the full definition*)
Definition all_leading_coeffs_one mx :=
  all_leading_coeffs_one_aux mx (Zseq 0 m).

Lemma all_leading_coeffs_one_leading_coeffs_some: forall mx i n,
  (0 <= i < m) ->
  (exists a, leading_coefficient mx i = Some(a,n)) <-> leading_coefficient (all_leading_coeffs_one mx) i = Some (one, n).
Proof.
  intros. unfold all_leading_coeffs_one. apply all_leading_coeffs_one_aux_leading_coeffs. lia.
  intros. rewrite Zseq_In in H0; lia. rewrite Zseq_In; lia. apply Zseq_NoDup; lia.
Qed.

Lemma all_leading_coeffs_one_leading_coeffs_none: forall mx i,
  (0 <= i < m) ->
  leading_coefficient mx i = None <-> leading_coefficient (all_leading_coeffs_one mx) i = None.
Proof.
  intros. unfold all_leading_coeffs_one. apply all_leading_coeffs_one_aux_leading_none; try assumption.
  intros. rewrite Zseq_In in H0; lia.
Qed.

Lemma all_leading_coeffs_one_get_zero: forall mx i j,
  (0 <= i < m) ->
  (0 <= j < n) ->
  get mx i j = zero <-> get (all_leading_coeffs_one mx) i j = zero.
Proof.
  intros. unfold all_leading_coeffs_one. apply all_leading_coeffs_one_aux_get_zero; try assumption.
  intros. rewrite Zseq_In in H1; lia.
Qed.

Lemma all_leading_coeffs_row_equiv: forall mx,
  row_equivalent m M n N mx (all_leading_coeffs_one mx).
Proof.
  intros. unfold all_leading_coeffs_one. apply all_leading_coeffs_aux_row_equiv. intros.
  rewrite Zseq_In in H; lia.
Qed.

(*our final step puts the matrix into row echelon form*)
Lemma rref_all_leading_coeffs: forall mx,
  reduced_row_echelon_no1 mx ->
  reduced_row_echelon (all_leading_coeffs_one mx).
Proof.
  intros. inversion H; subst. constructor.
  - constructor.
    + destruct_all. exists r. split. lia. intros. rewrite <- H3.
      rewrite <- all_leading_coeffs_one_leading_coeffs_none. reflexivity. all: assumption.
    + intros. destruct (leading_coefficient mx i) eqn : L1.
      destruct p. 2 : { rewrite all_leading_coeffs_one_leading_coeffs_none in L1. rewrite L1 in H5. inversion H5.
      lia. } destruct (leading_coefficient mx j) eqn : L2. destruct p. 2 : { 
      rewrite all_leading_coeffs_one_leading_coeffs_none in L2. rewrite L2 in H6. inversion H6. lia. }
      assert (exists a, leading_coefficient mx i = Some (a, z)). exists a. assumption.
      rewrite all_leading_coeffs_one_leading_coeffs_some in H7; try lia.
      assert (exists a, leading_coefficient mx j = Some (a, z0)). exists a0. assumption.
      rewrite all_leading_coeffs_one_leading_coeffs_some in H8; try lia.
      rewrite H5 in H7. inversion H7; subst. rewrite H6 in H8. inversion H8; subst.
      eapply H1. apply H3. assumption. apply L1. apply L2.
    + intros. destruct (leading_coefficient mx i) eqn : L. 2 : { 
      rewrite all_leading_coeffs_one_leading_coeffs_none in L. rewrite L in H4; inversion H4. lia. }
      destruct p. assert (exists a, leading_coefficient mx i = Some (a, z)). exists a. assumption.
      rewrite all_leading_coeffs_one_leading_coeffs_some in H7; try lia. rewrite H4 in H7; inversion H7; subst.
       rewrite <- all_leading_coeffs_one_get_zero. eapply H2. apply H3. apply L. all: try assumption.
      rewrite leading_coefficient_some_iff in H4. apply H4. lia.
  - intros. destruct (leading_coefficient mx i) eqn : L.
    + destruct p. assert (exists a, leading_coefficient mx i = Some (a, z)) by (exists a; assumption).
      rewrite all_leading_coeffs_one_leading_coeffs_some in H5; try lia. rewrite H5 in H4. inversion H4; subst.
      reflexivity.
    + rewrite all_leading_coeffs_one_leading_coeffs_none in L. rewrite L in H4; inversion H4. lia.
Qed.




(*The final Gaussian elimination function*)
Definition gaussian_elimination (mx: matrix m n) : matrix m n :=
  all_leading_coeffs_one (fst' (proj1_sig (gauss_all_steps_aux 0 0 (exist _ mx (gaussian_invariant_init mx))))).

Lemma gaussian_row_equiv: forall mx,
  row_equivalent m M n N mx (gaussian_elimination mx).
Proof.
  intros. unfold gaussian_elimination. eapply row_equivalent_trans.
  2: apply all_leading_coeffs_row_equiv. destruct (
  (gauss_all_steps_aux 0 0
           (exist (fun x : matrix m n => gaussian_invariant x 0 0) mx (gaussian_invariant_init mx)))). simpl.
   simpl in a. destruct_all. assumption.
Qed.

(*later - maybe try to remove assumption*)
(*Proof that the matrix resuling from gaussian elimination is row reduced*)
Lemma gaussian_rref: forall mx,
  (0 < n) ->
  (0 < m) ->
  reduced_row_echelon (gaussian_elimination mx).
Proof.
  intros. unfold gaussian_elimination. apply rref_all_leading_coeffs. 
  destruct (
        (gauss_all_steps_aux 0 0
           (exist (fun x : matrix m n => gaussian_invariant x 0 0) mx (gaussian_invariant_init mx)))).
  simpl in *. destruct_all. clear H3. 
  apply invar_implies_rref. assert (snd' x = m /\ 0 <= trd' x <= n \/ 0 <= snd' x <= m /\ trd' x = n) by (apply H2; lia).
  destruct H3.
  - right. exists (trd' x). split. apply H3. destruct H3. rewrite H3 in H4. apply H4.
  - left. exists (snd' x). split. apply H3. destruct H3. rewrite H5 in H4. apply H4.
Qed.


(*TODO: 
  x prove that invariants initially satisfied
  x full gaussian elim (repeat steps)
  x invariants at end imply row echelon form
  - split/concat matrices
  - mult over split/concat matrices
  - from REF - if first part of matrix is invertible, get I_n | M after gaussian elim (ie, leading coeff of row i is i
  - corollary - if we take m * 2m mx with identity in second part, second is inverse after gaussian elim
  - then begin proving our special conditions
*)

End GaussianElim.

End Gaussian.
End MatrixDef.

 
  
