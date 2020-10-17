(** * Polynomial operations modulo a nonzero polynomial **)
Require Import VST.floyd.functional_base.
Require Import Poly.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Import WPoly.

Definition pmod g f : poly := snd (poly_div g f). 

Notation "a %~ b" := (pmod a b) (at level 40).

Section Mod.

Variable f : poly.
(*Quotienting by 1 gives a trivial ring*)
Variable Hnontrivial: deg f > 0.

Lemma f_nonzero: f <> zero.
Proof.
  intro. rewrite <- deg_zero in H. lia.
Qed.

Definition eq_pmod f g h : Prop :=
  pmod g f = pmod h f.

Instance eq_pmod_equiv : Equivalence (eq_pmod f).
Proof.
  apply Build_Equivalence.
  - unfold Reflexive. intros. unfold eq_pmod. reflexivity.
  - unfold Symmetric. intros. unfold eq_pmod in *. unfold pmod in *.
    destruct (poly_div x f) as [q1 r1] eqn : P1.
    destruct (poly_div y f) as [q2 r2] eqn : P2.
    simpl in *. subst. reflexivity.
  - unfold Transitive. intros. unfold eq_pmod in *. unfold pmod in *.
    destruct (poly_div x f). destruct (poly_div y f). destruct (poly_div z f).
    simpl in *. subst. reflexivity.
Defined.

(*begin hide*)
(*
Require Import Ring.
Add Ring poly_ring_inst : poly_ring.
*)
(*end hide*)
Instance eq_pmod_proper_poly_add: forall g, Proper (eq_pmod f ==> eq_pmod f) (poly_add g).
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold eq_pmod in *. unfold pmod in *.
  destruct (poly_div x f) as [q1 r1] eqn : P1.
  destruct (poly_div y f) as [q2 r2] eqn : P2.
  simpl in H. subst. rewrite poly_div_correct in P1. rewrite poly_div_correct in P2.
  destruct P1. destruct P2.
  destruct (poly_div (g +~ x) f) as [q3 r3] eqn : P3.
  simpl. rewrite poly_div_correct in P3. destruct P3.
  rewrite H in H3.
  assert (g +~ y = g +~ y) by reflexivity. rewrite H1 in H5 at 2.
  rewrite poly_add_cancel_1 in H3. rewrite H3 in H5 at 2.
  assert (g +~ y = ((q1 +~ q3 +~ q2) *~ f) +~ (r2 +~ r2 +~ r3)). rewrite H5. 
  (* ring doesn't work for some reason - says it can't find a ring structure even though one is declared*)
  rewrite poly_add_assoc. rewrite poly_add_assoc. 
  assert (r2 +~ (((q3 *~ f) +~ r3)) = (r2 +~ (q3 *~ f)) +~ r3). rewrite poly_add_assoc. reflexivity.
  rewrite <- (poly_add_assoc r2).
  rewrite (poly_add_comm r2). rewrite (poly_add_assoc (q3 *~ f)).
  rewrite (poly_add_assoc _ _ ((q2 *~ f) +~ r2)). rewrite <- poly_add_assoc.
  rewrite <- (poly_add_assoc (r3 +~ r2)).
  rewrite (poly_add_comm (r3 +~ r2)). rewrite <- poly_mult_distr_r.
  rewrite <- (poly_add_assoc (q2 *~ f)). 
  rewrite (poly_add_assoc _ r2).
  rewrite poly_add_inv. rewrite poly_add_0_l.
  rewrite poly_add_0_r. rewrite <- poly_add_assoc.
  rewrite <- poly_mult_distr_r. reflexivity. 
  rewrite poly_add_inv in H6. rewrite poly_add_0_l in H6.
  assert (poly_div (g +~ y) f = ((q1 +~ q3) +~ q2, r3)). apply poly_div_correct.
  all: try (apply f_nonzero).
  split; assumption. rewrite H7. reflexivity. 
Qed.

Instance eq_pmod_proper_poly_mult: forall g, Proper (eq_pmod f ==> eq_pmod f) (poly_mult g).
Proof.
  intros. unfold respectful. unfold Proper. intros.
  unfold eq_pmod in *; unfold pmod in *.
  destruct (poly_div x f) as [q1 r1] eqn : P1.
  destruct (poly_div y f) as [q2 r2] eqn : P2.
  simpl in H. subst. rewrite poly_div_correct in P1; try assumption.
  rewrite poly_div_correct in P2; try assumption. destruct P1. destruct P2.
  destruct (poly_div (g *~ x) f) as [q3 r3] eqn : P3.
  destruct (poly_div (g *~ y) f) as [q4 r4] eqn : P4.
  rewrite poly_div_correct in P3; try (apply f_nonzero).
  rewrite poly_div_correct in P4; try (apply f_nonzero).
  destruct P3. destruct P4. 
  (*proof idea: (g r2 mod f = r3, and g mod r2 = r4, so equal *)
  assert (poly_div (g *~ r2) f = ((q3 +~ (g *~ q1)), r3)). { rewrite H in H3.
  rewrite poly_mult_distr_l in H3. rewrite <- poly_add_cancel_1 in H3.
  rewrite poly_add_assoc  in H3. rewrite poly_add_comm in H3.
  rewrite poly_add_assoc in H3. rewrite <- poly_mult_assoc in H3.
  rewrite <- poly_mult_distr_r in H3. rewrite poly_add_cancel_1 in H3.
  rewrite poly_div_correct; try (apply f_nonzero). split; assumption. }
  assert (poly_div (g *~ r2) f = ((g *~ q2) +~ q4, r4)). {
  rewrite H1 in H5. rewrite poly_mult_distr_l in H5.
  rewrite <- poly_add_cancel_1 in H5. rewrite poly_add_assoc in H5.
  rewrite (poly_add_comm (g *~ r2)) in H5. rewrite <- poly_add_assoc in H5.
  rewrite <- poly_mult_assoc in H5. rewrite <- poly_mult_distr_r in H5.
  rewrite poly_add_comm in H5.
  rewrite poly_add_cancel_1 in H5.
  rewrite poly_div_correct; try (apply f_nonzero). split; assumption. }
  rewrite H8 in H7. inversion H7; subst. simpl. reflexivity.
  all: apply f_nonzero.
Qed.

(** Useful Results about [pmod] *)

Lemma pmod_refl: forall g,
  deg g < deg f ->
  g %~ f = g.
Proof.
  intros. unfold pmod.
  assert (poly_div g f = (zero, g)). rewrite poly_div_correct.
  split. rewrite poly_mult_0_l. rewrite poly_add_0_l. reflexivity.
  assumption. apply f_nonzero. rewrite H0. reflexivity.
Qed.

(*key property (or definition) of mod*)
Lemma pmod_multiple_of_f: forall (g h: poly),
  (exists (q: poly), g = (q *~ f) +~ h) <->
  g %~ f = h %~ f.
Proof.
  intros. split; intros.
  - destruct H as [q]. unfold pmod.
    destruct (poly_div g f) as [q1 r1] eqn : P1.
    rewrite poly_div_correct in P1. destruct P1. simpl.
    rewrite <- poly_add_cancel_1 in H.
    rewrite H0 in H. rewrite poly_add_assoc in H. rewrite (poly_add_comm r1) in H.
    rewrite <- poly_add_assoc in H. rewrite <- poly_mult_distr_r in H.
    assert ((poly_div h f) = (q1 +~ q, r1)). apply poly_div_correct.
    all: try (apply f_nonzero).  symmetry in H. split; assumption.
    rewrite H2. reflexivity.
  - unfold pmod in H. destruct (poly_div g f) as [q1 r1] eqn : P1.
    destruct (poly_div h f) as [q2 r2] eqn : P2.
    simpl in H. subst. rewrite poly_div_correct in P1; try (apply f_nonzero).
    rewrite poly_div_correct in P2; try (apply f_nonzero). destruct P1. destruct P2.
    rewrite <- poly_add_cancel_1 in H1. rewrite <- H1 in H.
    rewrite (poly_add_comm h) in H.
    rewrite <- poly_add_assoc in H. rewrite <- poly_mult_distr_r in H.
    exists (q1 +~ q2). apply H.
Qed.

(*we can bring mod outside a sum *)
Lemma pmod_add_reduce: forall g h,
  (g +~ (h %~ f)) %~ f = (g +~ h) %~ f.
Proof.
  intros. unfold pmod. 
  destruct (poly_div h f) as [q1 r1] eqn : P1. 
  rewrite poly_div_correct in P1. destruct P1.
  simpl. assert (g +~ h = g +~ (q1 *~ f +~ r1)). rewrite H. reflexivity.
  rewrite (poly_add_comm _ (q1 *~ f +~ r1)) in H1.
  rewrite poly_add_assoc in H1. rewrite (poly_add_comm r1) in H1.
  assert ((g +~ h) %~ f = (g +~ r1) %~ f). apply pmod_multiple_of_f. exists q1. assumption.
  unfold pmod in H2. symmetry. assumption. apply f_nonzero.
Qed. 

Lemma pmod_add_distr: forall g h,
  (g +~ h) %~ f = ((g %~ f) +~ (h %~ f)) %~ f.
Proof.
  intros. rewrite <- pmod_add_reduce. rewrite poly_add_comm. rewrite <- pmod_add_reduce. rewrite poly_add_comm.
  reflexivity.
Qed. 

Lemma pmod_mult_reduce: forall g h,
  ( g *~ (h %~ f)) %~ f = (g *~ h) %~ f.
Proof.
  intros. unfold pmod. destruct (poly_div h f) as [q1 r1] eqn : P1.
  rewrite poly_div_correct in P1. destruct P1.
  simpl. rewrite <- poly_add_cancel_1 in H. symmetry in H.
  assert (g *~ r1 = g*~ (h +~ (q1 *~ f))). rewrite H. reflexivity.
  rewrite poly_mult_distr_l in H1. rewrite poly_add_comm in H1. rewrite <- poly_mult_assoc in H1.
  assert ((g *~ r1) %~ f = (g *~ h) %~ f). apply pmod_multiple_of_f. exists (g *~ q1). apply H1.
  unfold pmod in H2. apply H2. apply f_nonzero.
Qed.

Lemma pmod_mult_distr: forall g h,
  (g *~ h) %~ f = ((g %~ f) *~ (h %~ f)) %~ f.
Proof.
  intros. rewrite <- pmod_mult_reduce. rewrite poly_mult_comm.
  rewrite <- pmod_mult_reduce. rewrite poly_mult_comm. reflexivity.
Qed. 

Lemma pmod_lt_deg: forall g, deg (g %~ f) < deg f.
Proof.
  intros. unfold pmod. destruct (poly_div g f) as [r q] eqn : P.
  rewrite poly_div_correct in P; try (apply f_nonzero). simpl. apply P.
Qed.

Lemma pmod_twice: forall g,
  (g %~ f) %~ f = g %~ f.
Proof.
  intros. apply pmod_refl. apply pmod_lt_deg.
Qed. 

Lemma pmod_zero: zero %~ f = zero.
Proof.
  apply pmod_refl. assert (deg zero < 0). apply deg_zero. reflexivity.
  lia.
Qed.

(** Ring instances for GF2(x)/(f), where f is a nonzero polynomial *)

(* First, We restrict the size of polynomials and prove that under addition and multiplication modulo f,
  this is a ring. We will need this to define finite fields.*)
Definition qpoly : Type := { p: poly | deg p < deg f}.

Definition poly_mult_mod g h : poly :=
  (g *~ h) %~ f.

Lemma poly_mult_mod_lt_deg: forall g h,
  deg (poly_mult_mod g h) < deg f.
Proof.
  intros. unfold poly_mult_mod. apply pmod_lt_deg.
Qed.

Definition poly_add_mod g h : poly :=
  (g +~ h) %~ f.

Lemma poly_add_mod_lt_deg: forall g h,
  deg (poly_add_mod g h) < deg f.
Proof.
  unfold poly_add_mod. intros. apply pmod_lt_deg.
Qed.

Lemma zero_lt_deg: deg zero < deg f.
Proof.
pose proof (deg_zero zero). assert (deg zero < 0) by (apply H; reflexivity). lia.
Qed.

Lemma one_lt_deg: deg one < deg f.
Proof.
assert (deg one = 0%Z). symmetry. rewrite deg_one. reflexivity. lia.
Qed.

Definition r0 : qpoly := exist _ zero zero_lt_deg.
Definition r1 : qpoly := exist _ one one_lt_deg.
Definition r_add (g h : qpoly) : qpoly := exist _ (poly_add_mod (proj1_sig g) (proj1_sig h)) 
  (poly_add_mod_lt_deg (proj1_sig g) (proj1_sig h)).
Definition r_mul (g h : qpoly) : qpoly := exist _ (poly_mult_mod (proj1_sig g) (proj1_sig h)) 
  (poly_mult_mod_lt_deg _ _).

(** For polynomial f of degree n > 0, the set of polynomials with degree < n forms a ring under
  addition and multiplications modulo f *)
Definition qpoly_quotient_ring : @ring_theory qpoly r0 r1 r_add r_mul r_add id eq.
Proof.
  apply mk_rt.
  - intros. unfold r_add. destruct x. simpl. exist_eq.
    unfold poly_add_mod. rewrite poly_add_0_l. apply pmod_refl. assumption.
  - intros. unfold r_add. destruct x; destruct y; simpl. exist_eq.
    unfold poly_add_mod. rewrite poly_add_comm. reflexivity.
  - intros. unfold r_add; destruct x; destruct y; destruct z; simpl.
    exist_eq. unfold poly_add_mod.
    rewrite pmod_add_reduce. rewrite (poly_add_comm ((x +~ x0) %~ f)).
    rewrite pmod_add_reduce. rewrite <- poly_add_assoc. rewrite (poly_add_comm x1). reflexivity.
  - intros. unfold r_mul. destruct x; simpl. exist_eq. unfold poly_mult_mod.
    rewrite poly_mult_1_l. apply pmod_refl. assumption.
  - intros. unfold r_mul. exist_eq. destruct x; destruct y; simpl. 
    unfold poly_mult_mod. rewrite poly_mult_comm. reflexivity.
  - intros. unfold r_mul; destruct x; destruct y; destruct z; simpl. exist_eq. unfold poly_mult_mod.
    rewrite pmod_mult_reduce. rewrite (poly_mult_comm ((x *~ x0) %~ f)). rewrite pmod_mult_reduce.
    rewrite <- poly_mult_assoc. rewrite (poly_mult_comm _ x1). reflexivity.
  - intros. unfold r_mul; unfold r_add; destruct x; destruct y; exist_eq; simpl.
    unfold poly_mult_mod; unfold poly_add_mod. destruct z; simpl.
    rewrite? pmod_add_reduce. rewrite <- (poly_add_comm (x0 *~ x1)). 
    rewrite pmod_add_reduce. 
    rewrite poly_mult_comm. rewrite pmod_mult_reduce. rewrite poly_mult_comm.
    rewrite poly_add_comm.
    rewrite poly_mult_distr_r. reflexivity.
  - reflexivity.
  - intros. unfold r_add; destruct x; unfold r0; simpl; exist_eq. unfold poly_add_mod.
    rewrite poly_add_inv. apply pmod_zero. 
Defined.

(** Alternately, the polynomials form a ring under addition and multiplication modulo f, where equivalence
  is taken modulo f *)
Definition poly_quotient_ring: @ring_theory poly zero one poly_add_mod poly_mult_mod poly_add_mod id (eq_pmod f).
Proof.
  apply mk_rt; try unfold eq_pmod; intros; unfold poly_add_mod; unfold poly_mult_mod.
  - rewrite poly_add_0_l. apply pmod_twice. 
  - rewrite poly_add_comm. reflexivity.
  - rewrite? pmod_add_reduce. rewrite pmod_twice.
    rewrite pmod_twice. rewrite (poly_add_comm ((x +~ y) %~ f)). 
    rewrite pmod_add_reduce. rewrite <- poly_add_assoc. rewrite (poly_add_comm z). reflexivity.
  - rewrite poly_mult_1_l. apply pmod_twice.
  - rewrite poly_mult_comm. reflexivity.
  - rewrite? pmod_twice. rewrite pmod_mult_reduce. rewrite (poly_mult_comm ((x *~ y) %~ f)).
    rewrite pmod_mult_reduce. rewrite <- poly_mult_assoc. rewrite poly_mult_comm. reflexivity.
  - rewrite? pmod_twice. rewrite (poly_mult_comm _ z). rewrite pmod_mult_reduce.
    rewrite <- (pmod_add_distr (x *~ z) (y *~ z)). rewrite (poly_mult_comm z). rewrite poly_mult_distr_r.
    reflexivity.
  - reflexivity.
  - unfold id. rewrite pmod_twice. rewrite poly_add_inv. reflexivity.
Defined.
End Mod.

(*begin hide*)
(* test *)
(*
Definition testf := from_list (1 :: 0 :: 0 :: 1 :: nil).

Lemma testf_deg: deg testf > 0.
Proof.
  (*dont think there is way to do this except with just calcuating or breaking abstraction*)
  assert (deg testf = 3). reflexivity.
  lia.
Qed.

Definition testg := from_list (1 :: 0 :: 0 :: 1 :: 1 :: 1 :: nil).

Eval compute in (proj1_sig (testg %~ testf)).
*)
(*end hide*)
