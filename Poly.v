Require Import PolyDefs.
Require Import PolyDiv.
Require Import Coq.Lists.List.
Require Import VST.floyd.functional_base.
Require Export GF2.
(** Computable Polynomials over GF2 - wraps the definitions in PolyDefs.v into 
  dependent types for clean interface *)

Module WPoly.

Ltac exist_eq := apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.

(*This definition should not need to be unwrapped outside this file *)
Definition poly := {p : P.poly | P.wf_poly p}.

(*begin hide*)
Lemma wf_zero: P.wf_poly nil.
Proof.
  unfold P.wf_poly. intros. contradiction.
Qed.
(*end hide*)
Definition zero : poly := exist _ nil wf_zero.

(*begin hide*)
Lemma wf_one: P.wf_poly (1 :: nil).
Proof.
  unfold P.wf_poly. intros. reflexivity.
Qed.
(*end hide*)
Definition one : poly := exist _ (1 :: nil) wf_one.

Definition deg (p : poly) := P.deg (proj1_sig p).

Definition ith (p: poly) := P.ith (proj1_sig p).

Definition from_list (l: list bit) : poly :=
  exist _ (P.removeTrailingZeroes l) (P.removeTrailingZeroes_wf _).

Definition to_list (p: poly) : list bit := proj1_sig p.

(* Use this instead of destructing underlying list*)
Lemma destruct_poly: forall p,
  { p = zero } + { p <> zero }.
Proof.
  intros. destruct p. destruct x.
  - left. unfold zero; exist_eq; reflexivity.
  - right. intro. unfold zero; inversion H.
Qed.

Lemma poly_eq_dec: forall (p q : poly),
  {p = q} + {p <> q}.
Proof.
  intros. destruct p. destruct q. pose proof (list_eq_dec bit_eq_dec x x0).
  destruct H. left. subst. exist_eq. reflexivity. right. intro. inversion H. contradiction.
Qed. 

(** Results about [ith] *)
Lemma ith_zero: forall i,
  ith zero i = 0.
Proof.
  intros. unfold zero. unfold ith. simpl. apply P.ith_zero.
Qed.

(*begin hide*)
(*helper lemma to destruct list *)
Lemma nonzero_not_nil: forall p,
  p <> zero <-> proj1_sig p <> nil.
Proof.
  intros; split; intros. destruct p. intro.
  simpl in H0. subst. apply H. unfold zero. exist_eq. reflexivity.
  intro. subst. simpl in H. contradiction.
Qed.
(*end hide*)
Lemma ith_deg: forall p,
  p <> zero ->
  ith p (deg p) = 1.
Proof.
  intros. unfold deg. unfold ith. rewrite nonzero_not_nil in H.
  destruct p. simpl in *. apply P.ith_deg; assumption.
Qed.

Lemma ith_unbounded: forall f i,
  i < 0 \/ i > deg f ->
  ith f i = 0.
Proof.
  intros. unfold ith. unfold deg in H. destruct f. simpl in *.
  apply P.ith_unbounded; assumption.
Qed. 

Lemma ith_eq: forall p1 p2,
  p1 = p2 <-> (forall i, ith p1 i = ith p2 i).
Proof.
  intros. destruct p1; destruct p2; unfold ith; simpl in *.
  split; intros. inversion H. subst. reflexivity. exist_eq. apply P.ith_eq; assumption.
Qed. 

(** Results about [deg] *)

Lemma deg_zero: forall p,
  deg p < 0 <-> p = zero.
Proof.
  intros. destruct p; unfold zero; unfold deg; simpl. split; intros.
  exist_eq. destruct x. reflexivity. unfold P.deg in H. list_solve.
  inversion H. simpl. lia.
Qed.

Lemma deg_nonzero: forall p,
  0 <= deg p <-> p <> zero.
Proof.
  intros. rewrite nonzero_not_nil. destruct p; unfold deg; simpl. split; intros.
  - intro. subst. simpl in H. lia.
  - destruct x. contradiction. unfold P.deg. list_solve.
Qed.

Lemma deg_one: forall p,
  0%Z = deg p <-> p = one.
Proof.
  intros. unfold deg; unfold one; destruct p; simpl. split; intros.
  - exist_eq. unfold P.deg in H. destruct x. inversion H. destruct x. 2 :  list_solve.
    destruct b. unfold P.wf_poly in w. simpl in w. assert (0=1). apply w. solve_neq. inversion H0.
    reflexivity.
  - inversion H. simpl. reflexivity.
Qed.

Lemma deg_lower_bound: forall p,
  deg p >= -1.
Proof.
  intros. destruct p. unfold deg. simpl. destruct x; unfold PolyDefs.P.deg; list_solve.
Qed.

(** Polynomial addition **)

Definition poly_add (p1 p2 : poly) := exist _ (P.poly_add (proj1_sig p1) (proj1_sig p2)) (P.wf_poly_add _ _).
Infix "+~" := poly_add (at level 50).

Lemma poly_add_comm: forall p1 p2, p1 +~ p2 = p2 +~ p1.
Proof.
  intros. unfold poly_add. exist_eq. destruct p1; destruct p2; simpl.
  apply P.poly_add_comm.
Qed.

Lemma poly_add_assoc: forall p1 p2 p3, (p1 +~ p2) +~ p3 = p1 +~ (p2 +~ p3).
Proof.
  intros. unfold poly_add. exist_eq. simpl. destruct p1; destruct p2; destruct p3; simpl.
  apply P.poly_add_assoc.
Qed.

Lemma poly_add_0_l: forall p, zero +~ p = p.
Proof.
  intros. unfold poly_add. unfold zero; simpl. destruct p; simpl. exist_eq.
  apply P.poly_add_id; assumption.
Qed.

Lemma poly_add_0_r: forall p, p +~ zero = p.
Proof.
  intros. rewrite poly_add_comm. apply poly_add_0_l.
Qed.

Lemma poly_add_inv: forall p, p +~ p = zero.
Proof.
  intros. unfold poly_add. unfold zero. exist_eq. destruct p; simpl.
  apply P.poly_add_inv.
Qed.

Lemma poly_add_inv_iff: forall p1 p2, p1 +~ p2 = zero <-> p1 = p2.
Proof.
  intros. unfold poly_add; unfold zero; destruct p1; destruct p2; simpl. split; intros.
  - inversion H. exist_eq. apply P.poly_add_inv_iff; assumption.
  - exist_eq. inversion H. subst. apply P.poly_add_inv.
Qed.

Lemma poly_add_cancel_1: forall (f g h: poly), f +~ g = h <-> f = g +~ h.
Proof.
  intros. unfold poly_add; destruct f; destruct g; destruct h; simpl. split; intros H; inversion H; exist_eq;
  apply P.poly_add_cancel_1; try assumption; try reflexivity.
  all: apply P.wf_poly_add.
Qed.

Lemma poly_add_cancel_2: forall (f g h: poly), f +~ g = f +~ h -> g = h.
Proof.
  unfold poly_add; intros; destruct f; destruct g; destruct h. inversion H. exist_eq.
  apply P.poly_add_cancel_2 with (f := x); assumption.
Qed.

Lemma poly_add_deg_max: forall f g,
  deg (f +~ g) <= Z.max (deg f) (deg g).
Proof.
  intros. unfold poly_add; unfold deg. simpl. destruct f; destruct g; simpl.
  apply P.poly_add_degree_max.
Qed.

Lemma poly_add_deg_same: forall f g,
  deg f = deg g ->
  f <> zero ->
  deg (f +~ g) < deg f.
Proof.
  intros. rewrite nonzero_not_nil in H0.
  unfold deg in *; unfold poly_add; unfold zero in H0; destruct f; destruct g; simpl in *.
  apply P.poly_add_degree_same; try assumption. destruct x. contradiction. unfold P.deg; list_solve.
Qed.

Lemma poly_add_deg_diff: forall f g,
  deg f <> deg g ->
  deg (f +~ g) = Z.max (deg f) (deg g).
Proof.
  intros. unfold poly_add; unfold deg in *; destruct f; destruct g; simpl in *; apply P.poly_add_degree_diff;
  assumption.
Qed.

Lemma ith_poly_add: forall f g i,
  ith (f +~ g) i = bit_add (ith f i) (ith g i).
Proof.
  intros; unfold poly_add; unfold ith; destruct f; destruct g; simpl in *; apply P.ith_poly_add.
Qed.

(** Monomials *)
Definition monomial n : poly := exist _ (P.monomial n) (P.wf_monomial n).

Lemma monomial_deg: forall n,
  deg (monomial n) = Z.of_nat n.
Proof.
  intros. unfold deg; unfold monomial; simpl. apply P.monomial_deg.
Qed.

Lemma monomial_nonzero: forall n,
  monomial n <> zero.
Proof.
  intros. unfold monomial; unfold zero; intro; inversion H.
  apply (P.monomial_not_0 _ H1).
Qed.

(** Shift (ie, multiply by x^n) *)

Lemma nonzero_not_nil': forall f,
  f <> zero -> proj1_sig f <> nil.
Proof.
  apply nonzero_not_nil.
Qed.

Definition shift f n :=
  match (destruct_poly f) with
  | left H => zero
  | right H => exist _ (P.shift (proj1_sig f) n) (P.wf_shift (proj1_sig f) n (nonzero_not_nil' f H) (proj2_sig f))
  end.

Lemma shift_zero_iff: forall f n,
  shift f n = zero <-> f = zero.
Proof.
  intros. unfold shift. split; intros.
  - destruct (destruct_poly f). assumption.
    unfold zero in H. inversion H. destruct f; simpl in *. unfold P.shift in H1.
    unfold zero in n0. destruct (list_repeat n 0). exfalso. apply n0. exist_eq. auto.
    inversion H1.
  - destruct (destruct_poly f). reflexivity. contradiction.
Qed.  

Lemma ith_shift : forall f n i,
  ith (shift f n) i = ith f (i - Z.of_nat n).
Proof.
  intros. unfold ith. unfold shift. destruct (destruct_poly f).
  - simpl. subst; simpl. rewrite P.ith_zero. rewrite P.ith_zero. reflexivity.
  - simpl. destruct f; simpl. apply P.ith_shift.
Qed.

Lemma shift_deg: forall f n,
  f <> zero ->
  deg (shift f n) = deg f + Z.of_nat n.
Proof.
  intros. unfold shift; unfold deg. destruct (destruct_poly f).
  - contradiction.
  - simpl. destruct f; simpl. apply P.deg_shift.
Qed.

(** Summations describing coefficients of f(x)g(x) *)

Definition summation i (f g: poly) : bit := P.summation i (proj1_sig f) (proj1_sig g).

Lemma summation_comm: forall f g i,
  summation i f g = summation i g f.
Proof.
  intros. unfold summation; destruct f; destruct g; simpl; apply P.summation_comm.
Qed.

Lemma summation_distr: forall f g h i,
  summation i (f +~ g) h = bit_add (summation i f h) (summation i g h).
Proof.
  intros. unfold summation; unfold poly_add; destruct f; destruct g; destruct h; simpl; apply P.summation_distr.
Qed. 

(** Multiplication *)

Definition poly_mult (f g: poly) := exist _ (P.poly_mult (proj1_sig f) (proj1_sig g)) (P.wf_poly_mult _ _ (proj2_sig f)
  (proj2_sig g)).

Infix "*~" := poly_mult (at level 40).

Lemma poly_mult_comm: forall f g,
  f *~ g = g *~ f.
Proof.
  intros. unfold poly_mult; destruct f; destruct g; simpl; exist_eq; apply P.poly_mult_comm; try assumption.
Qed.

Lemma poly_mult_assoc: forall f g h,
  (f *~ g) *~ h = f *~ (g *~ h).
Proof.
  intros. unfold poly_mult; destruct f; destruct g; destruct h; simpl; exist_eq; apply P.poly_mult_assoc;
  assumption.
Qed.

Lemma poly_mult_distr_r: forall f g h,
  (f +~ g) *~ h = (f *~ h) +~ (g *~ h).
Proof.
  intros. unfold poly_mult; unfold poly_add; destruct f; destruct g; destruct h; simpl in *; exist_eq;
  apply P.poly_mult_distr_r; assumption.
Qed.

Lemma poly_mult_distr_l: forall f g h,
  f *~ (g +~ h) = (f *~ g) +~ (f *~ h).
Proof.
  intros. unfold poly_mult; unfold poly_add; destruct f; destruct g; destruct h; simpl in *; exist_eq;
  apply P.poly_mult_distr_l; assumption.
Qed.


Lemma poly_mult_0_l: forall f,
  zero *~ f = zero.
Proof.
  intros. unfold zero; unfold poly_mult; destruct f; exist_eq; apply P.poly_mult_0_l.
Qed.

Lemma poly_mult_0_r: forall f,
  f *~ zero = zero.
Proof.
  intros. rewrite poly_mult_comm. apply poly_mult_0_l. 
Qed.

Lemma poly_mult_1_l: forall f,
  one *~ f = f.
Proof.
  intros; unfold poly_mult; unfold one; destruct f; exist_eq; simpl.
  unfold P.poly_mult. destruct x. reflexivity. simpl. reflexivity.
Qed.

Lemma poly_mult_1_r: forall f,
  f *~ one = f.
Proof.
  intros. rewrite poly_mult_comm. apply poly_mult_1_l.
Qed.

Lemma poly_mult_zero_iff: forall f g,
  f *~ g = zero <-> f = zero \/ g = zero.
Proof.
  intros; unfold poly_mult; unfold zero; destruct f; destruct g; simpl. split; intros.
  inversion H. apply P.poly_mult_zero_iff in H1; try assumption.
  destruct H1. left. exist_eq. assumption. right. exist_eq. assumption.
  exist_eq. destruct H; inversion H; apply P.poly_mult_zero_iff; try assumption; auto.
  all: apply wf_zero.
Qed.

Lemma poly_mult_cancel: forall f g h,
  f <> zero ->
  f *~ g = f *~ h -> g = h.
Proof.
  intros. rewrite <- poly_add_0_r in H0. rewrite <- poly_add_cancel_1 in H0.
  rewrite <- poly_mult_distr_l in H0. rewrite poly_mult_zero_iff in H0. destruct H0.
  contradiction. rewrite poly_add_inv_iff in H0. assumption.
Qed.

Lemma poly_mult_deg: forall f g,
  f <> zero ->
  g <> zero ->
  deg (f *~ g) = deg f + deg g.
Proof.
  intros. unfold deg in *; unfold poly_mult; unfold zero in *; destruct f; destruct g; simpl in *.
  apply P.poly_mult_deg; try assumption. intro; subst. apply H. exist_eq. reflexivity.
  intro; subst. apply H0. exist_eq; reflexivity.
Qed.

Lemma ith_poly_mult: forall f g i,
  ith (f *~ g) i = summation i f g.
Proof.
  intros. unfold ith; unfold summation; unfold poly_mult; destruct f; destruct g; simpl; apply P.ith_poly_mult; assumption.
Qed.

Lemma poly_mult_id: forall f g, f *~ g = f -> f = zero \/ g = one.
Proof.
  intros. destruct (destruct_poly f). subst. left. reflexivity.
  destruct (destruct_poly g). subst. rewrite poly_mult_0_r in H. subst. contradiction.
  assert (deg (f *~ g) = deg f) by (rewrite H; reflexivity). rewrite poly_mult_deg in H0; try assumption.
  assert (deg g = 0%Z) by lia. symmetry in H1. rewrite deg_one in H1. right. assumption.
Qed. 

Lemma poly_mult_eq_one: forall f g, f *~ g = one -> f = one /\ g = one.
Proof.
  intros. destruct (destruct_poly f). subst. rewrite poly_mult_0_l in H. inversion H.
  destruct (destruct_poly g). subst. rewrite poly_mult_0_r in H. inversion H. 
  assert (deg (f *~ g) = deg one) by (rewrite H; reflexivity). rewrite poly_mult_deg in H0;
  try assumption. assert (deg one = 0%Z) by (symmetry; rewrite deg_one; reflexivity).
  rewrite H1 in H0. rewrite <- deg_nonzero in n. rewrite <- deg_nonzero in n0. 
  assert (0%Z = deg g) by lia. assert (0%Z = deg f) by lia. rewrite deg_one in H2.
  rewrite deg_one in H3. subst. split; reflexivity.
Qed.

Lemma shift_monomial: forall f n,
  shift f n = (monomial n) *~ f.
Proof.
  intros. unfold shift. destruct (destruct_poly f).
  - subst.  rewrite poly_mult_0_r. reflexivity.
  - destruct f; simpl. unfold poly_mult; unfold monomial; simpl. exist_eq.
    apply P.shift_monomial. intro. subst. apply nonzero_not_nil' in n0. simpl in n0. contradiction.
Qed.

(** Ring structure of GF2(x) *)
Definition poly_ring: ring_theory zero one poly_add poly_mult poly_add id eq.
Proof.
  apply mk_rt.
  - apply poly_add_0_l.
  - apply poly_add_comm.
  - intros. symmetry. apply poly_add_assoc.
  - apply poly_mult_1_l.
  - apply poly_mult_comm.
  - intros. symmetry. apply poly_mult_assoc.
  - apply poly_mult_distr_r.
  - reflexivity.
  - apply poly_add_inv.
Qed.

(** Euclidean division *)

Definition poly_div (a b: poly) : poly * poly :=
  proj1_sig (poly_div_aux (proj1_sig a) (proj1_sig b) nil (proj1_sig a)
  (proj2_sig b) (proj2_sig a) wf_zero). 

Lemma remainder_unique: forall (a b q1 r1 q2 r2: poly),
  b <> zero ->
  deg r1 < deg b ->
  deg r2 < deg b ->
  a = (q1 *~ b) +~ r1 ->
  a = (q2 *~ b) +~ r2 ->
  q1 = q2 /\ r1 = r2.
Proof.
  intros. subst. rewrite poly_add_comm in H3. rewrite poly_add_cancel_1 in H3. symmetry in H3.
  rewrite <- poly_add_assoc in H3.
  rewrite poly_add_cancel_1 in H3.
  rewrite <- poly_mult_distr_r in H3.
  assert (deg (r2 +~ r1) = deg ((q1 +~ q2) *~ b)). rewrite H3. reflexivity.
  destruct (destruct_poly (q1 +~ q2)). rewrite e in H2. rewrite poly_mult_0_l in H2.
  pose proof (deg_zero zero). destruct H4. clear H4. assert (deg (r2 +~ r1) < 0).
  rewrite H2. apply H5. reflexivity. clear H5. rewrite deg_zero in H4.
  rewrite poly_add_inv_iff in e. rewrite poly_add_inv_iff in H4. subst. auto.
  rewrite poly_mult_deg in H2. pose proof (poly_add_deg_max r2 r1).
  rewrite <- deg_nonzero in n. lia. assumption. assumption.
Qed.

Lemma poly_div_correct: forall (a b q r: poly),
  b <> zero ->
  poly_div a b = (q,r) <-> (a = (q *~ b) +~ r /\ deg r < deg b).
Proof.
  intros. split; intros.
  - unfold poly_div in H0.
    destruct (poly_div_aux (proj1_sig a) (proj1_sig b) nil (proj1_sig a) (proj2_sig b) (proj2_sig a) wf_zero).
    simpl in H0. destruct x; inversion H0; simpl in *; subst.
    rewrite poly_mult_comm. assert (A:= H). rewrite nonzero_not_nil in H.
    specialize (a0 H). destruct a0. split. unfold poly_mult. unfold poly_add.
    destruct a; destruct b; destruct q; destruct r; simpl in *.
    exist_eq. apply H2. rewrite P.poly_add_id. reflexivity. assumption. unfold deg. assumption.
  - destruct H0. unfold poly_div. destruct 
    (poly_div_aux (proj1_sig a) (proj1_sig b) nil (proj1_sig a) (proj2_sig b) (proj2_sig a) wf_zero).
    simpl. assert (A:= H). rewrite nonzero_not_nil in H. specialize (a0 H). destruct a0.
    destruct x as [q' r']. simpl in H3.
    assert (q' = q /\ r' = r). eapply remainder_unique with(a:=a). apply A. unfold deg; assumption. assumption.
    rewrite poly_mult_comm. unfold poly_mult; unfold poly_add; simpl. destruct a; simpl in *; exist_eq.
    apply H3. rewrite P.poly_add_id. reflexivity. assumption. assumption. destruct H4. auto.
Qed.
(*
(*begin hide*)
Definition testa := from_list (0 :: 1 :: 0 :: 0 :: 1 :: nil).
Definition testb := from_list (1 :: 0 :: 1 :: nil).

Definition test (x : poly * poly) : list bit * list bit :=
  match x with
  | (a, b) => (proj1_sig a, proj1_sig b)
  end.

Eval compute in (test (poly_div testa testb)).
(*end hide*)
*)

(** Enumerating Polynomials over GF(2) *)

(*get all polynomials of degree at most n - exponential complexity obviously*)
Definition polys_leq_degree (n: nat) : list poly := zero :: (P.list_of_polys_fst n).

Lemma polys_leq_degree_spec: forall n p,
  (deg p <= Z.of_nat n) <-> In p (polys_leq_degree n).
Proof.
  intros. 
  unfold polys_leq_degree. destruct (destruct_poly p).
  - subst. simpl. split; intros. left. reflexivity.
    assert (deg zero < 0) by (rewrite deg_zero; reflexivity). lia.
  - split; intros. right.  rewrite P.in_list_of_polys_fst. rewrite P.list_of_polys_fst_spec.
    split. apply nonzero_not_nil'. assumption. split. destruct p. simpl. assumption.
    unfold deg in H. assumption.
    simpl in H. destruct H. subst. contradiction. rewrite P.in_list_of_polys_fst in H.
    rewrite P.list_of_polys_fst_spec in H. destruct H. destruct H0. unfold deg; assumption.
Qed.

Lemma polys_leq_degree_length: forall n,
  length (polys_leq_degree n) = (2^(n+1))%nat.
Proof.
  intros. unfold polys_leq_degree. simpl.
  rewrite P.list_of_polys_fst_length.
  assert ((2^(n+1) > 0)%nat). remember (2^(n+1))%nat as m.
  assert (m = 0%nat \/ (m > 0)%nat) by lia. destruct H.
  subst. rewrite Nat.pow_eq_0_iff in H. destruct H. inversion H0. assumption.
  lia.
Qed.

(*we need this list for the map from powers of primitive element -> polynomials*)
Definition polys_leq_degree_nonzero (n: nat) : list poly := (P.list_of_polys_fst n).

Lemma polys_leq_degree_nonzero_spec: forall n p,
  (p <> zero /\ deg p <= Z.of_nat n) <-> In p (polys_leq_degree_nonzero n).
Proof.
  intros. unfold polys_leq_degree_nonzero. rewrite P.in_list_of_polys_fst.
  rewrite P.list_of_polys_fst_spec. split; intros.
  - destruct H. split. apply nonzero_not_nil. assumption. split. destruct p; simpl. assumption.
    unfold deg; assumption.
  - destruct H. destruct H0. split. apply nonzero_not_nil. assumption. unfold deg; assumption.
Qed.

Lemma polys_leq_degree_nonzero_length: forall n,
  length (polys_leq_degree_nonzero n) = (2^(n+1) - 1)%nat.
Proof.
  unfold polys_leq_degree_nonzero. apply P.list_of_polys_fst_length.
Qed.

(*True for the others too but we dont need it for now*)
Lemma polys_leq_degree_nonzero_NoDup: forall n,
  NoDup (polys_leq_degree_nonzero n).
Proof.
  intros. unfold polys_leq_degree_nonzero. apply P.list_of_polys_fst_NoDup.
Qed.

(*It computes!
Require Import Helper.
Eval compute in (dep_list_to_list _ (polys_leq_degree 4)).
*)
 
(*A version without zero and one is helpful for computing irreducibility*)
Definition polys_leq_degree_nontrivial (n: nat) : list poly := (P.list_of_nontrivial_polys n).

Lemma polys_leq_degree_nontrivial_spec: forall n p,
  (p <> zero /\ p <> one /\ deg p <= Z.of_nat n) <-> In p (polys_leq_degree_nontrivial n).
Proof.
  intros. unfold polys_leq_degree_nontrivial. rewrite P.list_of_nontrivial_polys_in.
  rewrite P.list_of_nontrivial_polys_spec. split; intros.
  - destruct H. destruct H0. split. apply nonzero_not_nil. assumption. split.
    intro. apply H0. unfold one. destruct p. simpl in H2. subst. exist_eq. reflexivity.
    split. destruct p; simpl; assumption. unfold deg in H1; assumption.
  - destruct H. destruct H0. destruct H1. split. apply nonzero_not_nil. assumption.
    split. intro. apply H0. destruct p. unfold one in H3. inversion H3.
    subst. simpl. reflexivity. unfold deg; assumption.
Qed.

(*get all polynomials of degree exactly n*)
Definition polys_of_degree (n: nat) : list poly :=(P.list_of_polys_snd n).

Lemma polys_of_degree_spec: forall n p,
  (deg p = Z.of_nat n) <-> In p (polys_of_degree n).
Proof.
  intros. unfold polys_of_degree. rewrite P.in_list_of_polys_snd.
  rewrite P.list_of_polys_snd_spec. split; intros.
  - split. rewrite <- nonzero_not_nil. intro. subst.
    assert (deg zero  < 0) by (rewrite deg_zero; reflexivity). lia. split. destruct p; simpl; assumption.
    unfold deg in H. assumption.
  - destruct H. destruct H0. unfold deg. assumption.
Qed.

Lemma polys_of_degree_length: forall n,
  length (polys_of_degree n) = (2^n)%nat.
Proof.
  intros. unfold polys_of_degree. apply P.list_of_polys_snd_length. 
Qed.


End WPoly.