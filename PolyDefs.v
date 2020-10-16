Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import VST.floyd.functional_base.
Require Import GF2.
Require Import Helper.
Require Import Coq.setoid_ring.Ring_theory.
(** Computable Polynomials over GF(2) - here we provide executable definitions of polynomial addition and multiplication
  and prove that GF(2)\[x\] is a ring *)

Ltac solve_neq := intro C; inversion C.

Module P.

(** * Definitions *)

(* We represent a polynomial as a list of bits, representing the coefficients a_0,...a_n. The last element in
  the list must be 1*)
Definition poly := list bit.

Definition wf_poly p := p <> nil -> last p 0 = 1.

(* The degre of a polynomial is just the length - 1, except that the zero polynomial is a special case *)
Definition deg (p: poly) : Z :=
  match p with
  | nil => -1
  | _ => Zlength p - 1
end.

(* The coefficient a_i of x^i in poly p. Gives 0 for all inputs not in range *)
Definition ith (p: poly) (i: Z) : bit := Znth i p.

(* Transform a list into a polynomial by cutting off any trailing zeroes *)
Definition removeTrailingZeroes p := dropWhileEnd (eq_bit 0) p.

(** * General Results *)

(** [removeTrailingZeroes] *)

Lemma removeTrailingZeroes_wf: forall p, wf_poly (removeTrailingZeroes p).
Proof.
  intros. unfold wf_poly. intros. pose proof (dropWhileEnd_spec (eq_bit 0) p 0 (dropWhileEnd (eq_bit 0) p)).
  destruct H0. clear H1.
  unfold removeTrailingZeroes in *. destruct H0. reflexivity. destruct H0.
  destruct (last (dropWhileEnd (eq_bit 0) p) 0) eqn : Q.
  - apply H1 in H. inversion H.
  - reflexivity.
Qed.

(* removeTrailingZeroes actually removes a list of trailing zeroes *)
Lemma removeTrailingZeroes_app_zeroes: forall l1 l2,
  (forall x, In x l2 -> eq_bit x 0 = true) ->
  removeTrailingZeroes (l1 ++ l2) = removeTrailingZeroes l1.
Proof.
  intros. unfold removeTrailingZeroes. unfold dropWhileEnd. rewrite fold_right_app.
  assert ((fold_right (fun (x : bit) (acc : list bit) => if null acc && eq_bit 0 x then nil else x :: acc) nil
     l2) = removeTrailingZeroes l2) by reflexivity. rewrite H0; clear H0.
  assert (removeTrailingZeroes l2 = nil). unfold removeTrailingZeroes. apply dropWhileEnd_nil. apply H. rewrite H0.
  reflexivity.
Qed.

Lemma wf_no_trailing_zeroes: forall f,
   wf_poly f ->
  removeTrailingZeroes f = f.
Proof.
  intros. unfold wf_poly in H. unfold removeTrailingZeroes. pose proof (dropWhileEnd_spec (eq_bit 0) f 0 f).
  apply H0. split. exists nil. split. rewrite app_nil_r. reflexivity. intros.
  inversion H1. intros. rewrite <- eq_bit_eq in H. apply H in H1. rewrite eq_bit_eq in H1. rewrite H1. reflexivity.
Qed. 

(*note: we use length, since degree is meant to refer to well formed polynomials*)
Lemma removeTrailingZeroes_length: forall l1,
  Zlength(removeTrailingZeroes l1) <= Zlength l1.
Proof.
  intros. induction l1.
  - simpl. lia.
  - simpl.  destruct (null (removeTrailingZeroes l1) && eq_bit 0 a ). list_solve.
    list_solve.
Qed.

(** [wf_poly] *)

Lemma wf_poly_cons: forall x l1,
  l1 <> nil ->
  wf_poly (x :: l1) <-> wf_poly l1.
Proof.
  intros. destruct l1.
  - contradiction.
  - destruct l1. unfold wf_poly. simpl. split; intros.
    apply H0. intro C; inversion C. apply H0. intro C; inversion C.
    unfold wf_poly. simpl. split; intros. apply H0. intro C; inversion C. 
    apply H0. intro C; inversion C.
Qed.

Lemma wf_bad: wf_poly (0 :: nil) -> False.
Proof.
  intros. unfold wf_poly in H. simpl in H. assert (0=1) by (apply H; solve_neq). inversion H0.
Qed.

(** [deg] *)

Lemma deg_cons: forall x l,
  deg (x :: l) = 1 + deg l.
Proof.
  intros. unfold deg. rewrite Zlength_cons. destruct l. simpl. reflexivity. list_solve.
Qed. 

(** [ith] *)

Lemma ith_zero: forall i,
  ith nil i = 0.
Proof.
  intros. unfold ith. apply Znth_nil.
Qed.

Lemma ith_in: forall p x,
  In x p ->
  exists i, ith p i = x /\ 0 <= i < Zlength p.
Proof.
  intros. rewrite In_Znth_iff in H.
  unfold ith. destruct H. exists x0. split; apply H.
Qed. 

(* every polynomial of degree nth has a nonzero nth coefficient *)
Lemma ith_deg: forall p,
  p <> nil ->
  wf_poly p ->
  ith p (deg p) = 1.
Proof.
  intros. unfold deg. unfold ith. destruct p. contradiction.
  unfold wf_poly in H0.  erewrite Znth_last. apply H0.
  all: solve_neq.
Qed.

Lemma ith_unbounded: forall f i,
  i < 0 \/ i > deg f ->
  ith f i = 0.
Proof.
  intros. unfold ith. unfold deg in H. destruct f. apply ith_zero.
  destruct H. apply Znth_underflow. assumption. apply Znth_overflow. lia.
Qed.

(*For well formed polynomials, we can exactly determine polynomials by looking at their coefficients at
  each location. This is useful for proving properties of multiplication*)
Lemma ith_eq: forall p1 p2,
  wf_poly p1 ->
  wf_poly p2 ->
  p1 = p2 <-> (forall i, ith p1 i = ith p2 i).
Proof.
  intros. split; intros. subst. reflexivity.
  generalize dependent p2. induction p1; intros.
  - destruct p2. reflexivity. unfold wf_poly in H0. 
    assert (last (b :: p2) 0 = 1) by (apply H0; solve_neq). 
    remember (b :: p2) as p.
    assert (ith p (deg p) = 1). apply ith_deg. subst. solve_neq. unfold wf_poly.
    apply H0. rewrite <- H1 in H3. rewrite ith_zero in H3. inversion H3.
  - destruct p2. 
    assert (ith (a :: p1) (deg (a :: p1)) = 1). apply ith_deg.
    solve_neq. apply H. rewrite H1 in H2. rewrite ith_zero in H2. inversion H2.
    f_equal.
    + specialize (H1 0%Z). unfold ith in H1. rewrite? Znth_0_cons in H1. subst. reflexivity.
    + apply IHp1. unfold wf_poly in *. intros. simpl in H. destruct p1. contradiction. apply H.
      solve_neq. unfold wf_poly in *. intros. simpl in H0. destruct p2. contradiction.
      apply H0. solve_neq. intros. specialize (H1 (i+1)%Z).
      unfold ith. unfold ith in H1.
      assert (i <0 \/ i >= 0) by lia. destruct H2. rewrite? Znth_underflow; try lia. reflexivity.
      rewrite? Znth_pos_cons in H1; try lia. list_solve.
Qed.

(** * Addition *)

(** Definitions and Ring Properties *)

(* We use an intermediate function to add two polynomials. The result is correct, but may not be well-formed,
  since it may have trailing zeroes*)
Fixpoint poly_add_inter (f g: poly) :=
  match f, g with
  | nil, nil => nil
  | x1 :: t1, x2 :: t2 => bit_add x1 x2 :: poly_add_inter t1 t2
  | nil, l => l
  | l, _ => l
  end.

(* begin hide *)
Lemma poly_add_inter_nil: forall l1 l2,
  poly_add_inter l1 l2 = nil <-> l1 = nil /\ l2 = nil.
Proof.
  intros. split; intros. destruct l1; destruct l2; try auto; try inversion H.
  destruct H; subst; reflexivity.
Qed.

(*first, we prove that removing trailing zeroes does not affect addition - this turns out to be more complicated
  than it seems *)

(*poly_add_inter distributes over appending lists of same length*)
Lemma poly_add_inter_app: forall l1 l2 l3 l4,
  Zlength l1 = Zlength l3 ->
  poly_add_inter (l1 ++ l2) (l3 ++ l4) = 
  poly_add_inter l1 l3 ++ poly_add_inter l2 l4.
Proof.
  intros l1; induction l1; intros.
  - simpl. assert (Zlength l3 = 0%Z) by list_solve. 
    destruct l3. simpl. reflexivity. list_solve.
  - destruct l3. list_solve. assert (Zlength l1 = Zlength l3) by list_solve.
    simpl. rewrite IHl1. reflexivity. apply H0.
Qed. 

Lemma poly_add_inter_nil_r: forall l,
  poly_add_inter l nil = l.
Proof.
  intros. destruct l; reflexivity.
Qed.

Lemma poly_add_inter_nil_l: forall l,
  poly_add_inter nil l = l.
Proof.
  intros. destruct l; reflexivity.
Qed.

(*If we add a polynomial l2 with a poly (list) containing all zeroes, we get back l2 plus possibly
  some trailing zeroes*)
Lemma poly_add_inter_zeroes: forall l1 l2,
  (forall x, In x l1 -> eq_bit x 0 = true) ->
  exists l3,
  poly_add_inter l1 l2 = l2 ++ l3 /\ forall x, In x l3 -> eq_bit x 0 = true.
Proof.
  intros l1. induction l1; intros.
  - exists nil. simpl. split. rewrite app_nil_r. destruct l2; reflexivity. auto.
  - simpl. destruct l2. exists (a :: l1). split. reflexivity. apply H.
    specialize (IHl1 l2). destruct IHl1 as [l3]. intros. apply H. right. assumption.
    exists l3. destruct H0. split. rewrite H0. assert (eq_bit a 0 = true). apply H. left. reflexivity.
    assert (a = 0) by (destruct a; try reflexivity; inversion H2). subst.
    assert (forall b, bit_add 0 b = b). intros; destruct b0; reflexivity. rewrite H3. reflexivity.
    apply H1.
Qed.

(*the result we want: we can just remove trailing zeroes at the end when doing polynomial addition*)
Lemma poly_add_inter_removezero: forall p1 p2,
  removeTrailingZeroes (poly_add_inter p1 p2) = removeTrailingZeroes (poly_add_inter (removeTrailingZeroes p1) p2).
Proof.
  intros. unfold removeTrailingZeroes at 3. 
  pose proof (dropWhileEnd_spec (eq_bit 0) p1 0 (dropWhileEnd (eq_bit 0) p1)).
  destruct H. clear H0. destruct H. reflexivity.
  destruct H as [l1]. destruct H. rewrite H at 1.
  remember (dropWhileEnd (eq_bit 0) p1) as l.
  remember (Zlength l) as n1.
  remember (Zlength p2) as n2.
  assert (n2 <= n1 \/ n2 > n1) by lia.
  destruct H2.
  - (*if deg p2 smaller than deg p1, then trailing 1 comes from p1*)
    rewrite <- (sublist_same 0 n1 l); try lia.
    rewrite (sublist_split 0 n2 n1 l); try lia. 2 : list_solve.
    rewrite <- app_assoc. assert (p2 = p2 ++ nil) by (rewrite app_nil_r; reflexivity). rewrite H3.
    clear H3. rewrite poly_add_inter_app. rewrite poly_add_inter_app. rewrite poly_add_inter_nil_r.
    rewrite poly_add_inter_nil_r.
    (*now have list of all zeroes at end - clearly removezeroes will remove this list*)
    rewrite app_assoc.
    apply removeTrailingZeroes_app_zeroes. apply H1. all: list_solve.
  - (*if deg p2 is larger, then it will determine the result of add by itself*)
    rewrite <- (sublist_same 0 n2 p2); try lia. rewrite (sublist_split 0 n1 n2 p2); try lia.
    rewrite poly_add_inter_app.
    (*now have list of all zeroes + poly p2 -> result is poly p2 (plus maybe some trailing zeroes*)
    assert (A:= H1). apply poly_add_inter_zeroes with (l2:=(sublist n1 n2 p2)) in A.
    destruct A as [l3]. destruct H3. rewrite H3.
    assert (l = l ++ nil) by (rewrite app_nil_r; reflexivity). rewrite H5 at 2.
    rewrite poly_add_inter_app. rewrite poly_add_inter_nil_l. rewrite app_assoc.
    apply removeTrailingZeroes_app_zeroes. apply H4. all: list_solve.
Qed. 

(*Commutativity - this is easy, since we can reason bitwise*)
Lemma poly_add_inter_comm: forall p1 p2, poly_add_inter p1 p2 = poly_add_inter p2 p1.
Proof.
  intros p1. induction p1; intros.
  - simpl. destruct p2; reflexivity.
  - simpl. destruct p2. reflexivity. simpl. rewrite IHp1. rewrite bit_add_comm. reflexivity.
Qed.

(*Associativity - requires [poly_add_inter_removezero], so we can "push" the removeTrailingZeroes to the end*)
Lemma poly_add_inter_assoc: forall p1 p2 p3, poly_add_inter (poly_add_inter p1 p2) p3 =
  poly_add_inter p1 (poly_add_inter p2 p3).
Proof.
  intros p1; induction p1; intros.
  - rewrite poly_add_inter_nil_l. rewrite poly_add_inter_nil_l. reflexivity.
  - simpl. destruct p2.
    + rewrite poly_add_inter_nil_l. destruct p3.
      * reflexivity.
      * simpl. reflexivity.
    + destruct (poly_add_inter (b :: p2) p3) eqn : P.
      * rewrite poly_add_inter_nil in P. destruct P. inversion H.
      * simpl. simpl in P. destruct p3.
        -- inversion P; subst. reflexivity.
        -- inversion P; subst. rewrite bit_add_assoc. rewrite IHp1. reflexivity.
Qed.

(*inverses - every polynomial is its own inverse*)
Lemma poly_add_inter_same: forall l,
  forall x, In x (poly_add_inter l l) -> eq_bit x 0 = true.
Proof.
  intros. induction l.
  - inversion H.
  - simpl in H. destruct H. destruct a; simpl in H; subst; try reflexivity. apply IHl. apply H.
Qed.

(* end hide *)

Definition poly_add p1 p2 := removeTrailingZeroes (poly_add_inter p1 p2).

Lemma wf_poly_add : forall p1 p2, wf_poly (poly_add p1 p2).
Proof.
  intros. unfold poly_add. apply removeTrailingZeroes_wf.
Qed.

Lemma poly_add_comm: forall p1 p2, poly_add p1 p2 = poly_add p2 p1.
Proof.
  intros. unfold poly_add. rewrite poly_add_inter_comm. reflexivity.
Qed.

Lemma poly_add_assoc: forall p1 p2 p3, poly_add (poly_add p1 p2) p3 = poly_add p1 (poly_add p2 p3).
Proof.
  intros. unfold poly_add. rewrite <- poly_add_inter_removezero.
  assert ((poly_add_inter p1 (removeTrailingZeroes (poly_add_inter p2 p3))) =
  (poly_add_inter (removeTrailingZeroes (poly_add_inter p2 p3)) p1)) by (apply poly_add_inter_comm).
  rewrite H; clear H.
  rewrite <- poly_add_inter_removezero.
  assert ((poly_add_inter (poly_add_inter p2 p3) p1) = (poly_add_inter p1 (poly_add_inter p2 p3)))
  by (apply poly_add_inter_comm). rewrite H; clear H. rewrite poly_add_inter_assoc. reflexivity.
Qed.

Lemma poly_add_id: forall l,
  wf_poly l ->
  poly_add nil l = l.
Proof.
  intros. unfold poly_add. rewrite poly_add_inter_nil_l. apply wf_no_trailing_zeroes. apply H.
Qed.

Lemma poly_add_inv: forall l,
  poly_add l l = nil.
Proof.
  intros. unfold poly_add. unfold removeTrailingZeroes. apply dropWhileEnd_nil.
  apply poly_add_inter_same.
Qed.

(*begin hide*)

Lemma poly_add_inter_zeroes_eq: forall f g,
  wf_poly f ->
  wf_poly g ->
  (forall x, In x (poly_add_inter f g) -> eq_bit x 0 = true) ->
  f = g.
Proof.
  intros f; induction f; intros.
  - simpl in H1. destruct g. reflexivity. 
    unfold wf_poly in H0. specialize (H1 (last (b :: g) 0)). rewrite H0 in H1 at 2.
    unfold eq_bit in H1. assert (false = true). apply H1. apply last_in. solve_neq.
    inversion H2. solve_neq.
  - destruct g. specialize (H1 (last (a :: f) 0)). 
    unfold wf_poly in H. rewrite H in H1 at 2. assert (false = true).
    apply H1. unfold poly_add_inter. apply last_in. all: try solve_neq. inversion H2.
    simpl in H1. assert (a = b). assert (eq_bit (bit_add a b) 0 = true).
    apply H1. left. reflexivity. solve_bit. inversion H2. inversion H2. subst.
    destruct f. destruct g. reflexivity.
    unfold wf_poly in H0. specialize (H1 (last (b :: b0 :: g) 0)).
    assert ( eq_bit (last (b :: b0 :: g) 0) 0 = true). apply H1.
    right. unfold poly_add_inter.
    replace (last (b :: b0 :: g)) with (last (b0 :: g)) by reflexivity.
    apply last_in. solve_neq. rewrite H0 in H2. inversion H2. solve_neq.
    destruct g. unfold wf_poly in H. specialize (H1 (last (b :: b0 :: f) 0)).
    assert (eq_bit (last (b :: b0 :: f) 0) 0 = true). apply H1. right.
    unfold poly_add_inter. replace (last (b :: b0 :: f) 0) with (last (b0 :: f) 0) by reflexivity.
    apply last_in. solve_neq. rewrite H in H2. inversion H2. solve_neq. rewrite (IHf (b1 :: g)).
    reflexivity. rewrite wf_poly_cons in H. assumption. solve_neq. rewrite wf_poly_cons in H0.
    assumption. solve_neq. intuition.
Qed.

(*end hide*)

Lemma poly_add_inv_iff: forall f g,
  wf_poly f ->
  wf_poly g ->
  poly_add f g = nil <-> f = g.
Proof.
  intros. split; intros. unfold poly_add in H1. apply poly_add_inter_zeroes_eq; try assumption.
  unfold removeTrailingZeroes in H1. rewrite dropWhileEnd_nil in H1. intros. 
  rewrite eq_bit_eq. symmetry. rewrite <- eq_bit_eq. apply H1; assumption. 
  subst. apply poly_add_inv.
Qed.

Lemma poly_add_cancel_1: forall f g h,
  wf_poly f ->
  wf_poly h ->
  poly_add f g = h <-> f = poly_add g h.
Proof.
  intros. split; intros.
  - subst. rewrite poly_add_comm. rewrite poly_add_assoc. rewrite poly_add_inv.
    rewrite poly_add_comm. symmetry. apply poly_add_id. assumption.
  - subst. rewrite poly_add_assoc. rewrite poly_add_comm. rewrite poly_add_assoc. 
    rewrite poly_add_inv. rewrite poly_add_comm. apply poly_add_id. assumption.
Qed.

(*begin hide*)
Lemma poly_add_zero_same: forall f g,
  wf_poly f ->
  wf_poly g ->
  poly_add f g = f -> g = nil.
Proof.
  intros. rewrite poly_add_comm in H1. rewrite poly_add_cancel_1 in H1.
  rewrite poly_add_inv in H1. all: assumption. 
Qed.
(*end hide*)

Lemma poly_add_cancel_2: forall f g h,
  wf_poly f ->
  wf_poly g ->
  wf_poly h ->
  poly_add f g = poly_add f h -> g = h.
Proof.
  intros. rewrite poly_add_cancel_1 in H2; try assumption.
  rewrite poly_add_comm in H2. rewrite poly_add_assoc in H2. symmetry in H2. apply poly_add_zero_same in H2.
  rewrite poly_add_inv_iff in H2. auto. all: try assumption.
  all: apply wf_poly_add.
Qed.

(** Degrees of sums *)

(* begin hide *)
(*First, some helper lemmas about the structure of the sum*)

(*if we add two nonzero polynomials of the same degree, the resulting sum has a nonempty list of zeroes
  at the end (ie, the degree is reduced*)
Lemma poly_add_inter_degree_same: forall l1 l2,
  wf_poly l1 ->
  wf_poly l2 ->
  deg l1 = deg l2 ->
  (0 <= (deg l1)) ->
  exists l3 l4, l4 <> nil /\ (poly_add_inter l1 l2) = l3 ++ l4 /\ (forall x, In x l4 -> eq_bit x 0 = true).
Proof.
  intros l1; induction l1; intros. 
  - unfold deg in H2. lia. 
  - destruct l2. simpl in H1; list_solve.
    simpl.
    destruct l1. simpl in H1. destruct l2. simpl.
    unfold wf_poly in H. unfold wf_poly in H0. simpl in H. simpl in H0. rewrite H. rewrite H0.
    unfold bit_add. exists nil. exists (0 :: nil). split. solve_neq. split. reflexivity.
    intros. destruct H3. subst. reflexivity. inversion H3. solve_neq. solve_neq.
    list_solve. destruct l2. simpl in H1. list_solve.
    rewrite wf_poly_cons in H. rewrite wf_poly_cons in H0. specialize (IHl1 (b1 :: l2)).
    destruct IHl1 as [l3]; try assumption. simpl in H1. simpl. list_solve. simpl. list_solve.
    destruct H3 as [l4]. destruct H3. destruct H4. exists (bit_add a b :: l3). exists l4.
    split. assumption. split. rewrite H4. reflexivity. apply H5. all: solve_neq.
Qed.

(*No matter what, the degree is bounded by the degree of the larger one*)
Lemma poly_add_inter_degree_max: forall f g,
  (deg (poly_add_inter f g) <= Z.max (deg f) (deg g)).
Proof.
  intros f; induction f; intros.
  - simpl. destruct g; lia.
  - simpl. destruct g; simpl.
    + lia.
    + specialize (IHf g). unfold deg in IHf.
      destruct (poly_add_inter f g) eqn : P. simpl. list_solve.
      destruct f eqn : F. simpl. destruct g eqn : G. list_solve. list_solve.
      destruct g eqn : G; list_solve.
Qed. 

(* end hide *)

(*deg(f+g) <= max(deg f, deg g)*)
Lemma poly_add_degree_max: forall f g,
  deg (poly_add f g) <= Z.max (deg f) (deg g).
Proof.
  intros. unfold poly_add. pose proof (poly_add_inter_degree_max f g).
  pose proof (removeTrailingZeroes_length (poly_add_inter f g)).
  assert (deg (removeTrailingZeroes (poly_add_inter f g)) <= deg (poly_add_inter f g)). {
  unfold deg. destruct (poly_add_inter f g) eqn : E.
  - simpl. lia.
  - destruct (removeTrailingZeroes (b :: l)). list_solve. list_solve. }
  lia. 
Qed.

(* If deg f = deg g, then deg (f + g) < deg f - this will be important for Euclidean division
  and computing the mod operation *)
Lemma poly_add_degree_same: forall f g,
  wf_poly f ->
  wf_poly g ->
  deg f = deg g ->
  0 <= (deg f) ->
  deg (poly_add f g) < deg f.
Proof.
  intros. pose proof (poly_add_inter_degree_same _ _ H H0 H1 H2).
  unfold poly_add. destruct H3 as [l]. destruct H3 as [l']. destruct H3. destruct H4.
  rewrite H4. rewrite removeTrailingZeroes_app_zeroes. 
  2 : { apply H5. } pose proof removeTrailingZeroes_length l. 
  pose proof (poly_add_inter_degree_max f g).  rewrite H4 in H7.
  unfold deg at 1 in H7. destruct (l ++ l') eqn : L.
  destruct l. simpl in L. contradiction. inversion L. 
  rewrite <- L in H7. rewrite <- L in H4.  clear L. clear b. clear l0.
  rewrite Zlength_app in H7. assert (0 <= Zlength l') by list_solve.
  assert (0%Z = Zlength l' \/ 0%Z < Zlength l') by lia. destruct H9. symmetry in H9.
  apply Zlength_nil_inv in H9. contradiction. unfold deg at 1.
  rewrite <- H1 in H7. 
  rewrite Z.max_id in H7. destruct (removeTrailingZeroes l); lia.
Qed.

(* begin hide *)

Lemma poly_add_inter_degree_diff: forall l1 l2,
  wf_poly l2 ->  
  deg l1 < deg l2 ->
  exists l3 l4,
  poly_add_inter l1 l2 = l3 ++ l4 /\ l3 <> nil /\ (forall x, In x l4 -> eq_bit x 0 = true) /\
  last l3 0 = 1 /\ Zlength l3 = Zlength l2.
Proof.
  intro l1; induction l1; intros.
  - simpl. destruct l2. simpl in H0. lia.
    exists (b :: l2). exists nil. split. rewrite app_nil_r. reflexivity. split. solve_neq. 
    split. intros. inversion H1. unfold wf_poly in H. split. apply H. solve_neq. reflexivity.
  - destruct l2. simpl in H0. list_solve. specialize (IHl1 l2).
    assert (exists l3 l4 : list bit,
         poly_add_inter l1 l2 = l3 ++ l4 /\
         l3 <> nil /\ (forall x : bit, In x l4 -> eq_bit x 0 = true) /\ last l3 0 = 1 /\ Zlength l3 = Zlength l2). apply IHl1.
    unfold wf_poly in H. unfold wf_poly. intros. destruct l2. contradiction. simpl in H. simpl. apply H.
    solve_neq. rewrite? deg_cons in H0. lia. destruct H1 as [l3]. destruct H1 as [l4]. destruct H1.
    destruct H2. destruct H3. simpl. rewrite H1. exists ((bit_add a b) :: l3). exists l4. split.
    reflexivity. split. solve_neq. split. apply H3. split. simpl. destruct l3. contradiction. destruct H4. assumption.
    list_solve.
Qed. 

(*do this separately so we dont need to repeat the proof*)
Lemma poly_add_degree_diff_one: forall f g,
  wf_poly g ->
  deg f < deg g ->
  deg (poly_add f g) = Z.max(deg f) (deg g).
Proof.
  intros. unfold poly_add. unfold removeTrailingZeroes.
  pose proof (dropWhileEnd_spec (eq_bit 0) (poly_add_inter f g) 0).
  pose proof (poly_add_inter_degree_diff f g H H0). destruct H2 as [l]. destruct H2 as [l'].
  destruct H2. destruct H3. destruct H4. destruct H5.
  specialize (H1 l). destruct H1. clear H1. rewrite H7.
  unfold deg at 1. destruct l. contradiction. assert (Z.max (deg f) (deg g) = deg g) by lia.
  rewrite H1. unfold deg. destruct g. simpl in H0. unfold deg in H0. destruct f; list_solve.
  lia. split. exists l'. split; assumption. intros. rewrite H5. reflexivity.
Qed.

(* end hide *)

(* If the degrees are different, the inequality in [poly_add_degree_max] is an equality*)
Lemma poly_add_degree_diff: forall f g,
  wf_poly f ->
  wf_poly g ->
  deg f <> deg g ->
  deg(poly_add f g) = Z.max (deg f) (deg g).
Proof.
  intros.
  assert (deg f < deg g \/ deg g < deg f) by lia.
  destruct H2. apply poly_add_degree_diff_one; assumption.
  rewrite Z.max_comm. rewrite poly_add_comm. apply poly_add_degree_diff_one; assumption.
Qed.

(** [ith] elements of sums *)


(*zero polynomial results in zeroes for ith*)


(* begin hide *)
Lemma ith_poly_add_inter: forall p1 p2 i,
  ith (poly_add_inter p1 p2) i = bit_add (ith p1 i) (ith p2 i).
Proof.
  intros p1. induction p1; intros.
  - simpl. destruct p2.
    + simpl. rewrite ith_zero. reflexivity.
    + rewrite ith_zero. rewrite bit_add_0_l. reflexivity.
  - destruct p2.
    + simpl. rewrite ith_zero. rewrite bit_add_0_r. reflexivity.
    + simpl. assert (i = 0%Z \/ (i > 0) \/ i < 0) by lia.
      destruct H.
      * subst. unfold ith. simpl. rewrite? Znth_0_cons. reflexivity.
      * destruct H.
        -- unfold ith. unfold ith in IHp1. rewrite? Znth_pos_cons; try lia.
           apply IHp1.
        -- unfold ith. rewrite? Znth_underflow; try lia. reflexivity.
Qed.

(*removing the trailing zeroes does not change coefficients*)
Lemma ith_removeTrailingZeroes: forall l i,
  ith l i = ith (removeTrailingZeroes l) i.
Proof.
  intros l. induction l; intros.
  - simpl. reflexivity.
  - simpl. destruct (removeTrailingZeroes l) eqn : L.
    + simpl. destruct (eq_bit 0 a) eqn : E.
      * rewrite ith_zero. unfold ith. assert (i = 0%Z \/ i>0 \/ i < 0) by lia. destruct H.
        -- subst. rewrite Znth_0_cons. rewrite eq_bit_eq in E. auto.
        -- destruct H.
           ++ rewrite Znth_pos_cons; try lia. unfold ith in IHl. rewrite IHl. apply Znth_nil.
           ++ rewrite Znth_underflow; try lia. reflexivity.
      * assert (i=0%Z \/ i>0 \/ i < 0) by lia. destruct H.
        -- subst. unfold ith. rewrite? Znth_0_cons. reflexivity.
        -- destruct H.
           ++ unfold ith. rewrite? Znth_pos_cons; try lia. apply IHl.
           ++ unfold ith in *. rewrite? Znth_underflow; try lia. reflexivity.
    + simpl.  assert (i=0%Z \/ (i>0) \/ i < 0) by lia. destruct H.
      * subst. unfold ith. rewrite? Znth_0_cons. reflexivity.
      * destruct H.
        -- unfold ith in *. rewrite Znth_pos_cons; try lia. rewrite Znth_pos_cons; try lia. apply IHl.
        -- unfold ith. rewrite? Znth_underflow; try lia. reflexivity.
Qed.
(* end hide *)
Lemma ith_poly_add: forall p1 p2 i,
  ith (poly_add p1 p2) i = bit_add (ith p1 i) (ith p2 i).
Proof.
  intros. unfold poly_add. rewrite <- ith_removeTrailingZeroes. apply ith_poly_add_inter.
Qed.

(** * Shift *)

(*shift f n = x^n*f*)
Definition shift (f: poly) (n: nat) : poly := list_repeat n 0 ++ f.

Lemma ith_shift : forall f n i,
  ith (shift f n) i = ith f (i - Z.of_nat n).
Proof.
  intros.
  assert ((i < Z.of_nat n)%Z \/ (i>= Z.of_nat n )%Z) by lia.
  destruct H.
  - unfold shift. unfold ith. rewrite Znth_app1. 
    assert (i < 0%Z \/ i >= 0%Z) by lia.
    destruct H0.
    + rewrite? Znth_underflow. reflexivity. all: lia.
    + assert (n = Z.to_nat (Z.of_nat n)) by lia. rewrite H1 at 1.  rewrite Znth_list_repeat_inrange; try lia.
      rewrite Znth_underflow. reflexivity. lia.
    + rewrite Zlength_list_repeat'. assumption.
  - unfold ith. unfold shift. pose proof (Zlength_list_repeat' n 0). rewrite Znth_app2. rewrite H0.
    reflexivity. lia.
Qed. 

Lemma deg_shift: forall f n,
  deg (shift f n) = deg f + Z.of_nat n.
Proof.
  intros. unfold deg. destruct (shift f n) eqn : L.
  - unfold shift in L. destruct n; simpl in L. subst. lia. inversion L.
  - destruct f. unfold shift in L. rewrite app_nil_r in L. rewrite <- L.
    rewrite Zlength_list_repeat'. lia.  unfold shift in L. rewrite <- L.
    rewrite Zlength_app. rewrite Zlength_list_repeat'. lia.
Qed. 

Lemma wf_shift: forall f n,
  f <> nil ->
  wf_poly f ->
  wf_poly (shift f n).
Proof.
  intros. unfold wf_poly in *. unfold shift. intros.
  destruct f. contradiction.  
  rewrite last_nonempty. apply H0. all: solve_neq.
Qed.



(** * Multiplication *)
(* We want to define a (relatively) efficient algorithm to compute polynomial multiplication. We use the
  standard grade school algorithm. To prove properties, we relate this to the standard mathematical definition - 
  the ith coefficient is \sum_{j=0}^{i} a_j*b_{i-j} *)


(* Again we use a helper function which is correct for nonzero polynomials but may result in a list
  of zeroes if g is nil*)
Fixpoint mult_help (f g : poly) : poly :=
  match f with
  | nil => nil
  | 0 :: nil => (*cannot happen in well formed poly*) nil
  | 1 :: nil => g
  | 1 :: f' => poly_add g (shift (mult_help f' g) 1)
  | 0 :: f' => shift (mult_help f' g) 1
  end.

Definition poly_mult f g :=
  match g with
  | nil => nil
  | _ => mult_help f g
  end.

(* begin hide *)

(*specification of [mult_help]*)

(*this was intended to just include the info about the degrees, but it turns out we need the other results as 
  induction hypotheses. All of them need each other to be proved*)
Lemma mult_help_facts: forall f g,
  wf_poly f ->
  wf_poly g ->
  f <> nil ->
  g <> nil ->
  deg (mult_help f g) = deg g + deg f /\ wf_poly (mult_help f g) /\ mult_help f g <> nil.
Proof.
  intros f. induction f; intros.
  - contradiction.
  - simpl. destruct a. destruct f.
    unfold wf_poly in H; simpl in H. assert (0 = 1) by (apply H; solve_neq). inversion H3.
    rewrite deg_shift.
    specialize (IHf g). assert (A : deg (mult_help (b :: f) g) = deg g + deg (b :: f) /\ wf_poly (mult_help (b :: f) g)
    /\ mult_help (b :: f) g <> nil).
    apply IHf. rewrite wf_poly_cons in H. assumption. solve_neq. assumption. solve_neq. assumption. 
    destruct A. destruct H4. rewrite H3. split. unfold deg. destruct g; list_solve. split. apply wf_shift.
    assumption. assumption. unfold shift. simpl. solve_neq.
   split.
    + destruct f. simpl. lia.
      specialize (IHf g). assert (deg (mult_help (b :: f) g) = deg g + deg (b :: f) /\
      wf_poly (mult_help (b :: f) g) /\ mult_help (b :: f) g <> nil). apply IHf. 
      rewrite wf_poly_cons in H. assumption. solve_neq. assumption. solve_neq. assumption.
      destruct H3. destruct H4. 
      assert (deg g < deg (shift (mult_help (b :: f) g) 1)). rewrite deg_shift. rewrite H3.
      simpl. list_solve.  rewrite poly_add_degree_diff_one. 
      replace (Z.max (deg g) (deg (shift (mult_help (b :: f) g) 1))) with
      (deg (shift (mult_help (b :: f) g) 1)) by lia. rewrite deg_shift. rewrite H3. simpl. list_solve.
      apply wf_shift; assumption. assumption.
    + split.
      * destruct f. assumption. apply wf_poly_add.
      * destruct f. assumption. intro. 
        (*to prove this need, to prove degrees again - this is why we need strong IH*)
        assert (deg (mult_help (b :: f) g) = deg g + deg (b :: f) /\
      wf_poly (mult_help (b :: f) g) /\ mult_help (b :: f) g <> nil). apply IHf.
      rewrite wf_poly_cons in H. assumption. solve_neq. assumption. solve_neq. assumption.
      destruct H4. destruct H5. 
      assert (deg (poly_add g (shift (mult_help (b :: f) g) 1)) = deg nil). rewrite H3.
      reflexivity.
      assert (deg g < deg (shift (mult_help (b :: f) g) 1)). rewrite deg_shift. rewrite H4.
      simpl. list_solve.  rewrite poly_add_degree_diff_one in H7.
      assert (Z.max (deg g) (deg (shift (mult_help (b :: f) g) 1)) = deg (shift (mult_help (b :: f) g) 1)) by lia.
      rewrite H9 in H7; clear H9. unfold shift in H7. simpl list_repeat in H7. simpl deg in H7. list_solve.
      apply wf_shift. assumption. assumption. assumption.
Qed.

(* for convinience, use 3 different lemmas *)
Lemma mult_help_deg: forall f g,
  wf_poly f ->
  wf_poly g ->
  f <> nil ->
  g <> nil ->
  deg (mult_help f g) = deg g + deg f.
Proof.
  intros. apply mult_help_facts; assumption.
Qed.

Eval compute in  mult_help (0 :: 0 :: 1 :: nil) nil.
(*this example shows - we need to reduce at the end*)

(*after reduction, true in general*)
Lemma wf_mult_help_nonzero: forall f g,
  wf_poly f ->
  wf_poly g ->
  f <> nil ->
  g <> nil ->
  wf_poly (mult_help f g).
Proof.
  intros. apply mult_help_facts; assumption.
Qed.

(*proves integral domain (once we have ring properties )*)
Lemma mult_help_nonzero: forall f g,
  wf_poly f ->
  wf_poly g ->
  f <> nil ->
  g <> nil ->
  (mult_help f g) <> nil.
Proof.
  intros.  apply mult_help_facts; assumption.
Qed.

(*use integer bounds so we allow for invalid summations - will just get 0*)

(* end hide *)

(** Summations *)

(* If f(x) = a_0 + ...+a_nx^n and g(x) = b_0 + ... + b_mx^m, then the ith coefficient of f(x)g(x) is
  sum_{j=0}^{i} a_{ijb_{i-j}. We represent this with the following summation function, which is
  generic to make some of the induction easier. We allow integer bounds but a summation with a negative
  upper bound returns 0 *)

Definition summation_aux (u : Z) f g l' base :=
  fold_right (fun x acc => bit_add (bit_mult (ith f (u - (Z.of_nat x))%Z) (ith g (Z.of_nat x))) acc) base l'.

Definition summation_gen (u: Z) (f g : poly) lower :=
  if zlt u 0%Z then 0 else
  summation_aux u f g (seq 0%nat (Z.to_nat u + 1)) lower.

Definition summation (u: Z) (f g : poly) :=
  summation_gen u f g 0.
(* begin hide *)
(*TODO: move*)
Lemma summation_nil_aux_l: forall u g l',
  summation_aux u nil g l' 0 = 0.
Proof.
  intros. revert u g. induction l'; intros; simpl.
  - reflexivity.
  - rewrite IHl'. rewrite ith_zero. rewrite bit_mult_0_l. reflexivity.
Qed.

Lemma summation_nil_l: forall u g,
  summation u nil g = 0.
Proof.
  intros. unfold summation. unfold summation_gen. if_tac. reflexivity. apply summation_nil_aux_l.
Qed.

Lemma summation_nil_aux_r: forall u f l',
  summation_aux u f nil l' 0 = 0.
Proof.
  intros. revert u f. induction l'; intros; simpl.
  - reflexivity.
  - rewrite IHl'. rewrite ith_zero. rewrite bit_mult_0_r. reflexivity.
Qed.

Lemma summation_nil_r: forall u f,
  summation u f nil = 0.
Proof.
  intros. unfold summation. unfold summation_gen. if_tac. reflexivity. apply summation_nil_aux_r.
Qed.

(*TODO: maybe go back and use this for other summation proofs*)
Lemma summation_aux_app: forall i f g base l l',
  summation_aux i f g (l ++ l') base = (summation_aux i f g l (summation_aux i f g l' base)).
Proof.
  intros. unfold summation_aux. rewrite fold_right_app. reflexivity.
Qed.

Lemma summation_aux_add_base: forall i g f l base b,
  bit_add (summation_aux i f g l base) b = summation_aux i f g l (bit_add base b).
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. rewrite bit_add_assoc. reflexivity.
Qed. 




(*A very annoying lemma to prove - we have to reason about both ends of the list at once. We do this by proving
  a stronger claim: if our list has the property that the ith and (length l - i - 1)st elements add up to i,
  then, we can prove the claim for (sublist 0 i) and sublist (length l - i) (length l) and unroll elements 
  from each side of the list*)

(* end hide *)

Lemma summation_comm: forall f g i,
  summation i f g = summation i g f.
Proof.
  intros. unfold summation. unfold summation_gen.
  if_tac. reflexivity.
  assert (forall l base,
    (forall z, 0<= z < Zlength l -> (Z.of_nat (Znth z l) + Z.of_nat ((Znth (Zlength l - z -1) l)%nat) = i)) ->
    (forall n, 0 <= Z.of_nat n <= Zlength l -> summation_aux i f g (sublist 0%Z (Z.of_nat n) l) base = 
      summation_aux i g f (sublist (Zlength l - (Z.of_nat n)) (Zlength l) l) base)). { intros.
    generalize dependent base. induction n; intros.
    - simpl. replace (Zlength l - 0) with (Zlength l) by lia. rewrite sublist_nil. reflexivity.
    - assert (Z.of_nat n <= Zlength l) by lia.
      rewrite (sublist_split 0 (Z.of_nat n) (Z.of_nat (S n)) l); try lia.
      rewrite (sublist_split ((Zlength l - Z.of_nat (S n))) (Zlength l - Z.of_nat n) (Zlength l) l); try lia.
      rewrite? summation_aux_app.
      replace ( Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
      rewrite sublist_len_1; try lia. replace (Zlength l - Z.of_nat n) with
      ((Zlength l - (Z.of_nat n + 1)) + 1) by lia. rewrite sublist_len_1; try lia.
      simpl. unfold ith.
      specialize (H0 (Z.of_nat n)).
      assert (Z.of_nat (Znth (Z.of_nat n) l) + Z.of_nat (Znth (Zlength l - Z.of_nat n - 1) l) = i) by (apply H0; lia).
      clear H0. 
      (*prove that the f's are equal*)
      assert ((i - Z.of_nat (Znth (Z.of_nat n) l)) = ((Z.of_nat (Znth (Zlength l - (Z.of_nat n + 1)) l)))). {
      rewrite <- H3.  rewrite Z.add_comm.
      assert (Z.of_nat (Znth (Z.of_nat n) l) - Z.of_nat (Znth (Z.of_nat n) l) = 0%Z) by lia.
      remember (Z.of_nat (Znth (Zlength l - Z.of_nat n - 1) l)) as temp.
      unfold Z.sub. rewrite <- Z.add_assoc. unfold Z.sub in H0. rewrite H0. replace (temp + 0) with temp by lia.
      subst. f_equal. f_equal. lia. } rewrite <- H0. (* now need to do the g's - can just use lia this time*)
      replace ((i - (i - Z.of_nat (Znth (Z.of_nat n) l)))) with ((Z.of_nat (Znth (Z.of_nat n) l))) by lia.
      remember ((Znth (i - Z.of_nat (Znth (Z.of_nat n) l)) f)) as n1.
      remember ((Znth (Z.of_nat (Znth (Z.of_nat n) l)) g)) as n2. symmetry. rewrite bit_add_comm.
      rewrite summation_aux_add_base. symmetry. replace (Zlength l - (Z.of_nat n + 1) + 1) with
      (Zlength l - Z.of_nat n) by lia. rewrite bit_mult_comm. rewrite bit_add_comm. apply IHn.
      lia. }
      remember (seq 0 (Z.to_nat i + 1)) as l. rewrite <- (sublist_same 0 (Zlength l) l); try lia.
      pose proof Zlength_nonneg l.
      replace (Zlength l) with (Z.of_nat (Z.to_nat (Zlength l))) at 1 by lia.
      rewrite H0.
      - replace (Zlength l - Z.of_nat (Z.to_nat (Zlength l))) with 0%Z by lia. reflexivity.
      - intros. rewrite Heql.
        assert (A: z <= i). rewrite Heql in H2. rewrite Zlength_seq in H2. lia.
        rewrite Znth_seq. rewrite Zlength_seq. 
        replace (Z.of_nat (Z.to_nat i + 1) - z - 1) with (i -z) by lia. 
        replace (Z.of_nat (Z.to_nat (Z.of_nat 0 + z))) with z by lia.
        rewrite Znth_seq. lia. lia. lia.
      -  lia.
Qed.

Lemma summation_distr: forall f g h i,
  summation i (poly_add f g) h = bit_add (summation i f h) (summation i g h).
Proof.
  intros. unfold summation. unfold summation_gen. if_tac. reflexivity.
  remember (seq 0 (Z.to_nat i + 1)) as l. clear Heql. induction l.
  - simpl. reflexivity.
  - simpl. rewrite ith_poly_add. rewrite IHl.
    remember (ith f (i - Z.of_nat a)) as n1. 
    remember (ith g (i - Z.of_nat a)) as n2.
    remember (ith h (Z.of_nat a)) as n3. 
    remember (summation_aux i f h l 0) as n4.
    remember (summation_aux i g h l 0) as n5.
    rewrite bit_distr. symmetry. rewrite bit_add_assoc.
    replace ((bit_add n4 (bit_add (bit_mult n2 n3) n5))) with (bit_add  (bit_add (bit_mult n2 n3) n5) n4) by
    (apply bit_add_comm). 
    replace (bit_add (bit_add (bit_mult n2 n3) n5) n4) with (bit_add (bit_mult n2 n3) (bit_add n5 n4))
    by (rewrite bit_add_assoc; reflexivity). rewrite bit_add_assoc. f_equal. f_equal. apply bit_add_comm.
Qed.

(* begin hide *)

(*lemma for 1st case of [mult_help_ith] - when the ones digit in f is 0*)
(*this is really annoying to prove - since the bounds change, the function inside fold_right changes too*)
Lemma summation_leading_zero: forall f g i base,
  (0 <= i) ->
  summation_gen i f g base = summation_gen (i + 1) (0 :: f) g base.
Proof.
  intros. unfold summation_gen. unfold summation_aux.
  if_tac. lia. if_tac. lia.
  replace ((Z.to_nat (i + 1) + 1))%nat with (S(S(Z.to_nat i))) by lia. symmetry. rewrite seq_S.
  rewrite fold_right_app. 
  assert ((fold_right
     (fun (x : nat) (acc : bit) =>
      bit_add (bit_mult (ith (0 :: f) (i + 1 - Z.of_nat x)) (ith g (Z.of_nat x))) acc) base
     ((0 + S (Z.to_nat i))%nat :: nil)) = base). { unfold fold_right.
      replace ( (i + 1 - Z.of_nat (0 + S (Z.to_nat i)))) with 0%Z by lia. simpl. apply bit_add_0_l. }
  rewrite H2. clear H2. symmetry.
    assert (forall l, 
    (forall x, In x l -> (x <= Z.to_nat i)%nat) ->
  fold_right
  (fun (x : nat) (acc : bit) =>
   bit_add (bit_mult (ith f (i - Z.of_nat x)) (ith g (Z.of_nat x))) acc) base l =
fold_right
  (fun (x : nat) (acc : bit) =>
   bit_add (bit_mult (ith (0 :: f) (i+1 - Z.of_nat x)) (ith g (Z.of_nat x))) acc) base l). {
  intros. induction l.
  - simpl. reflexivity.
  - simpl. remember (i - Z.of_nat a) as k. 
    replace (i + 1 - Z.of_nat a) with (k+1) by lia. unfold ith at 1. unfold ith at 4.
    rewrite Znth_pos_cons. replace (k + 1 -1) with k by lia. rewrite IHl. reflexivity. intros.
    apply H2. right. assumption. assert (Z.of_nat a <= i). assert (a <= Z.to_nat i)%nat. apply H2.
    left. reflexivity. lia. lia. } rewrite H2. 
    replace ((Z.to_nat i + 1)%nat) with (S(Z.to_nat i)) by lia. reflexivity.
    intros. rewrite in_seq in H3. lia.
Qed. 

(*summation when f = 1*)
Lemma summation_by_one:  forall g i,
  0 <= i ->
  ith g i = summation_gen i (1 :: nil) g 0.
Proof.
  intros. unfold summation_gen. if_tac. lia. replace (Z.to_nat i + 1)%nat with (S(Z.to_nat i)) by lia.
  rewrite seq_S. simpl. unfold summation_aux. rewrite fold_right_app. simpl.
  replace (i - Z.of_nat (Z.to_nat i)) with 0%Z by lia.
  unfold ith at 4. rewrite Znth_0_cons. rewrite bit_mult_1_l. 
  replace ((Z.of_nat (Z.to_nat i))) with i by lia. rewrite bit_add_0_r.
  (*we need to generalize seq and prove a separate lemma - since i - x > 0 for all x in l,
    we add 0 each time*)
  assert (forall l base, (forall x, In x l -> (x < (Z.to_nat i))%nat) ->
    fold_right
    (fun (x : nat) (acc : bit) =>
   bit_add (bit_mult (ith (1 :: nil) (i - Z.of_nat x)) (ith g (Z.of_nat x))) acc)  
    base l = base). { intros l; induction l; intros.
    - reflexivity.
    - simpl. assert (a < Z.to_nat i)%nat. apply H1. left. reflexivity.
      unfold ith at 1. rewrite Znth_overflow. simpl. rewrite bit_add_0_l. apply IHl.
      intros. apply H1. right. assumption. list_solve. }
    rewrite H1. reflexivity. intros. rewrite in_seq in H2. lia.
Qed. 

(*third case: f = 1 + f'*)
Lemma summation_split: forall f g i,
  f <> nil ->
   (0 <= i) ->
  bit_add (ith g i) (summation (i - Z.of_nat 1) f g) = summation i (1 :: f) g.
Proof.
  intros. unfold summation. unfold summation_gen.
  if_tac. assert (i = 0%Z) by lia. subst. if_tac. lia. 
  simpl. destruct (ith g 0); reflexivity.
  assert (i > 0) by lia.
  if_tac. lia. (*now we have handled the i=0 case*)
  unfold summation_aux. 
  (*why we need to use integers, not nats, for summation: *)
  replace (Z.to_nat (i - Z.of_nat 1) + 1)%nat with (Z.to_nat i) by lia.
  replace (Z.to_nat i + 1)%nat with (S(Z.to_nat i)) by lia.
  rewrite seq_S. rewrite fold_right_app. 
  assert ((fold_right
     (fun (x : nat) (acc : bit) =>
      bit_add (bit_mult (ith (1 :: f) (i - Z.of_nat x)) (ith g (Z.of_nat x))) acc) 0
     ((0 + Z.to_nat i)%nat :: nil)) = (ith g i)). { simpl.
   replace ((i - Z.of_nat (Z.to_nat i))) with 0%Z by lia.
   unfold ith at 1. rewrite Znth_0_cons. rewrite bit_mult_1_l.
   unfold ith. rewrite bit_add_0_r. replace (Z.of_nat (Z.to_nat i)) with i by lia. reflexivity. }
  rewrite H4; clear H4.
  (*now we need to know a + fold_right ... (base =0) = fold_right ... (base = a) - ie, we can add to beginning or end*)
  assert (forall l base,
  (forall x, In x l -> Z.of_nat x < i) ->
  bit_add base (fold_right
     (fun (x : nat) (acc : bit) =>
      bit_add (bit_mult (ith f (i - Z.of_nat 1 - Z.of_nat x)) (ith g (Z.of_nat x))) acc) 0 l) =
   fold_right
  (fun (x : nat) (acc : bit) =>
   bit_add (bit_mult (ith (1 :: f) (i - Z.of_nat x)) (ith g (Z.of_nat x))) acc) 
  base l). { intros l; induction l; intros.
  - simpl. rewrite bit_add_0_r. reflexivity.
  - simpl. remember (i - Z.of_nat a) as k. replace (i - 1 - Z.of_nat a) with (k-1) by lia.
    unfold ith at 1. unfold ith at 4. rewrite Znth_pos_cons. rewrite <- IHl.
    (*now it is just using asoc and comm to simplify - TODO: maybe use ring once i have a ring*)
  rewrite <- bit_add_assoc.
    simpl.
    remember (fold_right
        (fun (x : nat) (acc : bit) =>
         bit_add (bit_mult (ith f (i - 1 - Z.of_nat x)) (ith g (Z.of_nat x))) acc) 0 l) as y.
    assert ((bit_add base (bit_mult (Znth (k - 1) f) (ith g (Z.of_nat a))) =
    (bit_add (bit_mult (Znth (k - 1) f) (ith g (Z.of_nat a))) base))). apply bit_add_comm. 
    rewrite H5; clear H5. rewrite bit_add_assoc. reflexivity. intros. apply H4. right. assumption.
    assert (Z.of_nat a < i). apply H4. left. reflexivity. lia. } rewrite H4. reflexivity.
    intros. rewrite in_seq in H5. lia.
Qed.


(*if the second value is nil, mult_help does not give nil necessarily, but the resulting list has all 0s*)
(*One last lemma about mult_help -for the annoying case when g is nil and we may end up with a list of zeroes*)
Lemma mult_help_nil_r: forall f,
  forall x, In x (mult_help f nil) -> x = 0.
Proof.
  intros. generalize dependent x; induction f; intros.
  - simpl in H. destruct H.
  - simpl in H. destruct a. destruct f. inversion H.
    remember (b :: f) as f'. simpl in H. destruct H. auto. apply IHf. assumption.
    destruct f. inversion H. remember (b :: f) as f'. unfold shift in H. simpl in H.
    unfold poly_add in H. rewrite poly_add_inter_nil_l in H. simpl in H.
    unfold eq_bit in H. rewrite andb_true_r in H. 
    destruct (removeTrailingZeroes (mult_help f' nil)) eqn : R.
    simpl in H. inversion H.
    unfold removeTrailingZeroes in R. rewrite dropWhileEnd_spec with(y:=0) in R.
    destruct R. destruct H0 as [l1]. destruct H0.
    assert (In (last (b0 :: l) 0) (mult_help f' nil)).
    rewrite H0. apply in_or_app. left. rewrite <- Znth_last.
    apply Znth_In. list_solve. solve_neq.
    apply IHf in H3. rewrite H3 in H1. assert (true = false). unfold eq_bit in H1. apply H1. solve_neq.
    inversion H4.
Qed.

(*if we are outside the range of indices, summation gives 0*)
Lemma summation_overflow: forall f g i,
  0 <= i ->
  i > deg f + deg g ->
  summation i f g = 0.
Proof.
  intros. unfold summation. unfold summation_gen.
  if_tac. reflexivity. 
  assert (forall l, (forall x, In x l -> (x <= Z.to_nat i)%nat) -> 
   summation_aux i f g l 0 = 0). { intros l; induction l; intros.
  - reflexivity.
  - simpl. assert (a <= Z.to_nat i)%nat. apply H2. left. reflexivity.
    (*since i > 2*min(deg f, deg g), at least one of i-a and a are out of bounds*)
    assert (i > 2 * Z.min (deg f) (deg g)) by lia.
    assert (((i - Z.of_nat a) <= Z.min (deg f) (deg g) /\ (Z.of_nat a) <= Z.min (deg f) (deg g))
     \/ (i - Z.of_nat a) > Z.min (deg f) (deg g) \/ Z.of_nat a > Z.min (deg f) (deg g)) by lia.
    destruct H5. lia.
    (*lots of annoying cases, we have to know if deg f or deg g is the min, even though it is essneitally the same
      either way*)
    assert (Z.min (deg f) (deg g) = deg f \/ Z.min (deg f) (deg g) = deg g) by lia. destruct H6; subst.
    destruct H5. rewrite H6 in H5. destruct f. rewrite ith_zero. 
    rewrite bit_mult_0_l. rewrite IHl. reflexivity. intuition.
    rewrite ith_unbounded; try lia. simpl.  rewrite IHl. reflexivity. intuition.
    (* even if Z.of_nat a is in bounds, i -a cannot be then*)
    assert (Z.of_nat a <= deg g \/ Z.of_nat a > deg g) by lia. destruct H7.
    assert (i - Z.of_nat a > deg f) by lia. (*same case as before - maybe a better way to automate*)
    rewrite ith_unbounded; try lia. simpl. rewrite IHl. reflexivity. intuition.
    assert (ith g (Z.of_nat a ) = 0). apply ith_unbounded. lia. rewrite H8. clear H8.
    rewrite bit_mult_0_r. rewrite IHl. reflexivity. intuition.
    (*now have to do the same things for when deg g is the max *)
    destruct H5. rewrite H6 in H5. assert (i - Z.of_nat a <= deg f \/ i - Z.of_nat a > deg f) by lia.
    destruct H7. assert (Z.of_nat a > deg g) by lia. 
    assert (ith g (Z.of_nat a) = 0). apply ith_unbounded; lia. rewrite H9.
    rewrite bit_mult_0_r. rewrite IHl. reflexivity. intuition. 
    rewrite ith_unbounded; try lia. simpl. rewrite IHl. reflexivity. intuition.
    assert (ith g (Z.of_nat a) = 0). apply ith_unbounded; lia. rewrite H7.
    rewrite bit_mult_0_r. rewrite IHl. reflexivity. intuition. } (*finally*)
    apply H2. intros. rewrite in_seq in H3. lia.
Qed.

(*now we can try to prove the key fact about ith*)
Lemma mult_help_ith: forall f g i,
  wf_poly f ->
  wf_poly g ->
  ith (mult_help f g) i = summation i f g.
Proof.
  intros. assert (A: i < 0 \/ i >= 0) by lia. destruct A as [A | A].
  unfold ith. rewrite Znth_underflow. unfold summation. unfold summation_gen. if_tac. reflexivity.
  lia. assumption.
  generalize dependent g. generalize dependent i.
  induction f; intros.
  - simpl. unfold summation. rewrite ith_zero. symmetry. apply  summation_nil_l.
  - destruct g. rewrite summation_nil_r. unfold ith.
    assert (i < Zlength ((mult_help (a :: f) nil)) \/ i >= Zlength ((mult_help (a :: f) nil))) by lia.
    destruct H1.
    eapply mult_help_nil_r.
    apply Znth_In. lia. rewrite Znth_overflow. reflexivity. lia.
    (*case on whether i is larger than the degree or not*)
    assert (B: i > deg (a :: f) + deg (b :: g) \/ i <= deg (a :: f) + deg (b :: g)) by lia. destruct B as [B | B].
     rewrite ith_unbounded. symmetry. apply summation_overflow. lia. lia. rewrite mult_help_deg; try assumption.
    lia. solve_neq. solve_neq. 
     (*now we are within bounds*)
    simpl. destruct a. destruct f. unfold wf_poly in H. simpl in H. assert (0 =1) by (apply H; solve_neq).
    inversion H1. assert (i = 0%Z \/ i > 0) by lia. destruct H1.
    + subst. unfold shift. unfold ith. unfold list_repeat. apply Znth_0_cons.
    + rewrite ith_shift. rewrite IHf.  unfold summation. 
      rewrite summation_leading_zero. f_equal. lia. lia. rewrite wf_poly_cons in H. assumption. solve_neq. lia.
      assumption.
    + destruct f.
      * unfold summation. apply summation_by_one. lia.
      * (*first, if i=0, we cannot use IH*)
        assert (i = 0%Z \/ i > 0) by lia. destruct H1.
        -- subst. rewrite ith_poly_add. rewrite ith_shift.
           unfold ith at 2. rewrite Znth_underflow. unfold summation. unfold summation_gen.
          if_tac. lia. simpl. destruct (ith (b :: g) 0); reflexivity. lia.
        -- rewrite ith_poly_add. rewrite ith_shift. rewrite IHf. apply summation_split. solve_neq. lia.
           rewrite wf_poly_cons in H. assumption. solve_neq. lia. assumption. 
Qed.

(* end hide *)

(** Properties of [poly_mult *)

Lemma poly_mult_zero_iff: forall f g,
  wf_poly f ->
  wf_poly g ->
  poly_mult f g = nil <-> f = nil \/ g = nil.
Proof.
  intros. split; intros.
  - destruct f eqn : F. left. reflexivity. 
    destruct g eqn : G. right. reflexivity.
    unfold poly_mult in H1. pose proof (mult_help_nonzero (b :: l) (b0 :: l0)). 
    exfalso. apply H2; try assumption; try solve_neq.
  - destruct H1. subst. unfold poly_mult. simpl. destruct g; reflexivity.
    subst. reflexivity. 
Qed.

(*For the zero case, see previous lemma*)
Lemma poly_mult_deg: forall f g,
  wf_poly f ->
  wf_poly g ->
  f <> nil ->
  g <> nil ->
  deg (poly_mult f g) = deg f + deg g.
Proof.
  intros. unfold poly_mult. destruct g. contradiction. remember (b :: g) as g'. rewrite mult_help_deg. lia.
  all: try assumption.
Qed.

Lemma wf_poly_mult: forall f g,
  wf_poly f ->
  wf_poly g ->
  wf_poly (poly_mult f g).
Proof.
  intros. unfold poly_mult. destruct g. assumption.
  destruct f. simpl. assumption. apply mult_help_facts; try assumption; try solve_neq.
Qed.

(*key property of multiplication - the coefficient of x^i is sum_{j=0}^i f_j g_{i-j}*)
Lemma ith_poly_mult: forall f g i,
  wf_poly f ->
  wf_poly g ->
  ith (poly_mult f g) i = summation i f g.
Proof.
  intros. destruct g. simpl.  rewrite summation_nil_r. apply ith_zero.
  destruct f. simpl. rewrite summation_nil_l. apply ith_zero.
  unfold poly_mult. apply mult_help_ith; try assumption. 
Qed.

(*begin hide *)
(*With these in mind, we now want to start proving that polynomials form a ring - we need
  commutativity, associativity, and distributivity - we will prove these by proving that the summations
  are equal. Then, by [ith_eq], we can conclude that the resulting polynomials are equal*)

Lemma mult_help_comm: forall f g,
  wf_poly f ->
  wf_poly g ->
  f <> nil ->
  g <> nil ->
  mult_help f g = mult_help g f.
Proof.
  intros. rewrite ith_eq.
  - intros. rewrite? mult_help_ith; try assumption; try lia. apply summation_comm.
  - apply wf_mult_help_nonzero; assumption.
  - apply wf_mult_help_nonzero; assumption.
Qed.

(* end hide*)
Lemma poly_mult_comm: forall f g,
  wf_poly f ->
  wf_poly g ->
  poly_mult f g = poly_mult g f.
Proof.
  intros. rewrite ith_eq. intros. rewrite? ith_poly_mult; try assumption. apply summation_comm.
  all: apply wf_poly_mult; assumption.
Qed.


Lemma poly_mult_distr_r: forall f g h,
  wf_poly f ->
  wf_poly g ->
  wf_poly h ->
  poly_mult (poly_add f g) h = poly_add (poly_mult f h) (poly_mult g h).
Proof.
  intros. rewrite ith_eq.
  - intros. rewrite ith_poly_add. rewrite? ith_poly_mult; try assumption.
    apply summation_distr. apply wf_poly_add; assumption.
  - apply wf_poly_mult. apply wf_poly_add. assumption.
  - apply wf_poly_add.
Qed.

Lemma poly_mult_distr_l: forall f g h,
  wf_poly f ->
  wf_poly g ->
  wf_poly h ->
  poly_mult f (poly_add g h) = poly_add (poly_mult f g) (poly_mult f h).
Proof.
  intros. rewrite poly_mult_comm. rewrite poly_mult_distr_r; try assumption.
  f_equal; apply poly_mult_comm. all: try assumption. apply wf_poly_add.
Qed.

(*begin hide*)


(* For associativity, we cannot go element by element, since the corresponding terms are not equal
  (and the structure is much less nice than commutativity). But we can prove by induction on
  f, as long as we have the result for the polynomial x, which is easy. We also use distributivity in the proof.*)
Lemma mult_help_assoc_x: forall f g,
  wf_poly f ->
  wf_poly g ->
  f <> nil ->
  g <> nil ->
  shift (mult_help f g) 1 = mult_help (shift f 1) g.
Proof.
  intros. destruct f.
  - contradiction.
  - simpl. destruct b. 
    + destruct f.
      * apply wf_bad in H. destruct H.
      * reflexivity.
    + destruct f.
      * reflexivity.
      * reflexivity.
Qed. 

(*follows easily from real distributivity*)
Lemma mult_help_distr: forall f g h,
  wf_poly f ->
  wf_poly g ->
  wf_poly h ->
  f <> nil ->
  g <> nil ->
  h <> nil ->
  mult_help (poly_add f g) h = poly_add (mult_help f h) (mult_help g h).
Proof.
  intros. pose proof poly_mult_distr_r f g h H H0 H1. unfold poly_mult in H5.
  destruct h; try contradiction. apply H5.
Qed.


Lemma mult_help_assoc: forall f g h,
  wf_poly f ->
  wf_poly g ->
  wf_poly h ->
  f <> nil ->
  g <> nil ->
  h <> nil ->
  mult_help (mult_help f g) h = mult_help f (mult_help g h).
Proof.
  intros. induction f.
  - reflexivity.
  - simpl. destruct a.
    + destruct f.
      * apply wf_bad in H. destruct H.
      * rewrite <- mult_help_assoc_x. rewrite IHf. reflexivity. apply wf_poly_cons in H. assumption.
        solve_neq. solve_neq. apply wf_mult_help_nonzero. apply wf_poly_cons in H. all: try assumption.
        solve_neq. solve_neq. apply mult_help_nonzero; try assumption; try solve_neq. apply wf_poly_cons in H.
        assumption. solve_neq.
    + destruct f.
      * reflexivity.
      * assert (wf_poly (b :: f)). rewrite wf_poly_cons in H. apply H. solve_neq.
        rewrite mult_help_distr; try assumption. rewrite <- mult_help_assoc_x; try assumption.
        rewrite IHf; try assumption. reflexivity. solve_neq.
        apply wf_mult_help_nonzero; try assumption. solve_neq.
        apply mult_help_nonzero; try assumption; try solve_neq.
        apply wf_shift.
        apply mult_help_nonzero; try assumption; try solve_neq.
        apply wf_mult_help_nonzero; try assumption; try solve_neq.
        unfold shift. intro. simpl in H6; inversion H6.
Qed.

(*end hide *)

Lemma poly_mult_0_l: forall f,
  poly_mult nil f = nil.
Proof.
  intros. unfold poly_mult; destruct f; reflexivity.
Qed.

Lemma poly_mult_0_r: forall f,
  poly_mult f nil = nil.
Proof.
  intros. reflexivity.
Qed.

Lemma poly_mult_assoc: forall f g h,
  wf_poly f ->
  wf_poly g ->
  wf_poly h ->
  poly_mult (poly_mult f g) h = poly_mult f (poly_mult g h).
Proof.
  intros. destruct f.
  - rewrite? poly_mult_0_l. reflexivity.
  - destruct g. rewrite poly_mult_0_r. rewrite? poly_mult_0_l.
    rewrite poly_mult_0_r. reflexivity. destruct h.
    + rewrite? poly_mult_0_r. reflexivity.
    + unfold poly_mult. rewrite mult_help_assoc; try assumption; try solve_neq.
      destruct (mult_help (b0 :: g) (b1 :: h)) eqn : D.
      pose proof mult_help_nonzero. exfalso. apply (H2 (b0 :: g) (b1 :: h)); try assumption; try solve_neq.
      reflexivity.
Qed.

(*begin hide*)

Eval compute in (poly_mult (0 :: 1 :: 1 :: nil) (1 :: 1 :: nil)).
(*end hide*)

(*special shorthand for monomials - will help in Euclidean division *)
Definition monomial (n: nat) :=
  if Nat.eq_dec n 0%nat then (1 :: nil) else shift (1 :: nil) n.

Lemma monomial_deg: forall n,
  deg (monomial n) = Z.of_nat n.
Proof.
  intros. unfold monomial. if_tac. subst. simpl. reflexivity. rewrite deg_shift. unfold deg. list_solve.
Qed.

Lemma wf_monomial: forall n,
  wf_poly (monomial n).
Proof.
  intros. unfold monomial. if_tac. unfold wf_poly; intros. reflexivity.
  unfold shift. unfold wf_poly. intros. rewrite last_last. reflexivity.
Qed.

Lemma monomial_not_0: forall n,
  monomial n <> nil.
Proof.
  intros. intro. unfold monomial in H. destruct (Nat.eq_dec n 0). inversion H.
  unfold shift in H. destruct (list_repeat n 0); inversion H.
Qed.

Lemma shift_monomial: forall f n,
  f <> nil ->
  shift f n = poly_mult (monomial n) f.
Proof.
  intros. unfold shift. unfold monomial. if_tac.
  subst. simpl. unfold poly_mult. destruct f. reflexivity. reflexivity.
  unfold shift. clear H0. induction n.
  - simpl. destruct f; reflexivity.
  - simpl. rewrite IHn. unfold poly_mult. destruct f. contradiction.
    simpl. destruct (list_repeat n 0 ++ 1 :: nil) eqn : L.
    + destruct (list_repeat n 0); inversion L.
    + rewrite <- L. unfold shift. simpl. reflexivity.
Qed.

End P.
  