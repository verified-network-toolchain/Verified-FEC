(** * Polynomial operations modulo a nonzero polynomial **)
Require Import VST.floyd.functional_base.
Require Import Poly.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.FinFun.
Require Import Helper.
Require Import Coq.setoid_ring.Field_theory.

(*So we don't have to use inversion, which takes a long time*)
Ltac exist_inv H := apply EqdepFacts.eq_sig_fst in H; simpl in H.

Definition pmod g f : poly := snd (poly_div g f). 

Notation "a %~ b" := (pmod a b) (at level 40).

(*Typeclass for a non-constant - so that we don't need to give the proof each time*)
Class PosPoly (f: poly) := {
  Hpos : deg f > 0;}.

Lemma f_nonzero: forall f `{PosPoly f}, f <> zero.
Proof.
  intros. destruct H. intro. rewrite <- deg_zero in H. lia.
Qed.

Section Mod.

(*Quotienting by 1 gives trivial ring*)
Context (f: poly) `{Hpos: PosPoly f}.

Definition eq_pmod f g h : Prop :=
  g %~ f = h %~ f.

(** Useful Results about [pmod] *)

Lemma pmod_refl: forall g,
  deg g < deg f ->
  g %~ f = g.
Proof.
  intros. unfold pmod.
  assert (poly_div g f = (zero, g)). rewrite poly_div_correct.
  split. rewrite poly_mult_0_l. rewrite poly_add_0_l. reflexivity.
  assumption. apply f_nonzero. apply Hpos. rewrite H0. reflexivity.
Qed.

Lemma pmod_same: 
  f %~ f = zero.
Proof.
  unfold pmod. destruct (poly_div f f) as [q r] eqn : P.
  rewrite poly_div_correct in P.
  - destruct P. rewrite <- poly_add_cancel_1 in H.
    rewrite <- (poly_mult_1_l f) in H at 1. rewrite <- poly_mult_distr_r in H.
    simpl. assert (deg r = deg r) by reflexivity. rewrite <- H in H1 at 1.
    destruct (destruct_poly (one +~ q)). rewrite e in H.
    rewrite poly_mult_0_l in H. subst. reflexivity.
    rewrite poly_mult_deg in H1. rewrite <- deg_nonzero in n. lia.
    assumption. apply f_nonzero; assumption.
  - apply f_nonzero; assumption.
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
    all: try (apply f_nonzero).  symmetry in H. apply Hpos. split.
    rewrite H. reflexivity. assumption.
    rewrite H2. reflexivity. apply Hpos.
  - unfold pmod in H. destruct (poly_div g f) as [q1 r1] eqn : P1.
    destruct (poly_div h f) as [q2 r2] eqn : P2.
    simpl in H. subst. rewrite poly_div_correct in P1; try (apply f_nonzero).
    rewrite poly_div_correct in P2; try (apply f_nonzero). destruct P1. destruct P2.
    rewrite <- poly_add_cancel_1 in H1. rewrite <- H1 in H.
    rewrite (poly_add_comm h) in H.
    rewrite <- poly_add_assoc in H. rewrite <- poly_mult_distr_r in H.
    exists (q1 +~ q2). apply H. all: auto.
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
  unfold pmod in H2. symmetry. assumption. apply f_nonzero. auto.
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
  unfold pmod in H2. apply H2. apply f_nonzero. auto.
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
  rewrite poly_div_correct in P; try (apply f_nonzero). simpl. apply P. auto.
Qed.

Lemma pmod_twice: forall g,
  (g %~ f) %~ f = g %~ f.
Proof.
  intros. apply pmod_refl. apply pmod_lt_deg.
Qed. 

Lemma pmod_zero: zero %~ f = zero.
Proof.
  apply pmod_refl. assert (deg zero < 0). apply deg_zero. reflexivity. destruct Hpos. lia. 
Qed.

Lemma pmod_cancel: forall g h,
  g %~ f = h %~ f <-> (g +~ h) %~ f = zero.
Proof.
  intros. split; intros. 
  - rewrite <- pmod_multiple_of_f in H. destruct H. rewrite poly_add_comm in H.
    rewrite <- poly_add_cancel_1 in H. 
    rewrite <- pmod_zero. apply pmod_multiple_of_f. exists x. rewrite H. rewrite poly_add_0_r.
    reflexivity.
  - rewrite <- pmod_zero in H. rewrite <- pmod_multiple_of_f in H. destruct H.
    rewrite poly_add_0_r in H. apply pmod_multiple_of_f. exists x. rewrite poly_add_comm.
    rewrite <- poly_add_cancel_1. apply H.
Qed. 

End Mod.
    

(** Polynomial GCD *)

(*p divides q if p is a factor of q, ie, q % p = 0 *)
(*we use a definition in terms of existence (rather than just pmod) to handle to zero cases, since 0 | 0 is true
but 0 | p is false for any p <> zero*)
Definition divides p q := exists m, p *~ m = q.

Definition divides_pmod p q := q %~ p = zero.

Lemma divides_pmod_iff: forall p q, (p <> zero \/ q = zero) -> divides p q <-> divides_pmod p q.
Proof.
  intros. unfold divides; unfold divides_pmod; split; intros.
  - destruct H.
    + unfold pmod. destruct (poly_div q p) as [a b] eqn : P. rewrite poly_div_correct in P; try assumption.
      simpl. destruct P. destruct H0. rewrite <- H0 in H1.
      rewrite <- poly_add_cancel_1 in H1. rewrite poly_mult_comm in H1.
      rewrite <- poly_mult_distr_r in H1.
      destruct (destruct_poly (x +~ a)).
      rewrite e in H1. rewrite poly_mult_0_l in H1. subst. reflexivity.
      assert (deg b = deg ((x +~ a) *~ p)) by (rewrite H1; reflexivity).
      rewrite poly_mult_deg in H3; try assumption. 
      rewrite <- deg_nonzero in n. lia.
    + subst. destruct (destruct_poly p).
      * subst. unfold pmod. simpl. unfold zero. exist_eq. reflexivity.
      * assert (0 <= deg p) by (rewrite deg_nonzero; apply n). assert (0%Z = deg p \/ 0 < deg p) by lia.
        destruct H1. rewrite deg_one in H1. subst. unfold pmod; simpl. unfold zero. exist_eq. reflexivity.
        apply pmod_zero. apply Build_PosPoly. lia.
  - destruct H.
    + unfold pmod in H0. destruct (poly_div q p) as [a b] eqn : P. rewrite poly_div_correct in P; try assumption.
      destruct P. simpl in H0. subst. rewrite poly_add_0_r. exists a. apply poly_mult_comm.
    + subst. exists zero. apply poly_mult_0_r.
Qed.

Notation "a |~ b" := (divides a b) (at level 40). 

Lemma divides_refl: forall p, p |~ p.
Proof.
  intros. unfold divides. exists one. rewrite poly_mult_1_r. reflexivity.
Qed.

Lemma divides_zero: forall p, p |~ zero.
Proof.
  intros. unfold divides. exists zero. apply poly_mult_0_r.
Qed.

Lemma zero_does_not_divide: forall (p: poly), zero |~ p <-> p = zero.
Proof.
  intros. split; intros.
  - unfold divides in H. destruct H. rewrite poly_mult_0_l in H. subst. reflexivity.
  - subst. apply divides_refl.
Qed. 

Lemma divides_sum: forall a b c, a |~ b -> a |~ c -> a |~ (b +~ c).
Proof.
  intros. unfold divides in *. destruct H as [x1]. destruct H0 as [x2].
  subst. rewrite <- poly_mult_distr_l. exists (x1 +~ x2). reflexivity.
Qed. 

Lemma divides_factor_r: forall a b c, a |~ b -> a |~ (b *~ c).
Proof.
  intros. unfold divides in *. destruct H. subst. exists (x *~ c). rewrite poly_mult_assoc. reflexivity.
Qed.

Lemma divides_factor_l: forall a b c, a |~ c -> a |~ (b *~ c).
Proof.
  intros. rewrite poly_mult_comm. apply divides_factor_r; assumption.
Qed.

(*f = g iff f divides g and g divides f*)
Lemma divides_eq_iff: forall (f g: poly), (f |~ g /\ g |~ f) <-> f = g.
Proof.
  intros. split; intros.
  - unfold divides in H. destruct H. destruct H. destruct H0.
    rewrite <- H0 in H. rewrite poly_mult_assoc in H.
    apply poly_mult_id in H. destruct H. subst. apply poly_mult_0_l. 
    apply poly_mult_eq_one in H. destruct H. subst. apply poly_mult_1_r.
  - subst. split; apply divides_refl.
Qed.

Lemma divides_smaller_zero: forall (f g: poly), deg g < deg f -> f |~ g -> g = zero.
Proof.
  intros. unfold divides in H0. destruct H0. 
  destruct (destruct_poly x). subst. apply poly_mult_0_r.
  destruct (destruct_poly f). subst. rewrite poly_mult_0_l in H. lia.
  rewrite <- H0 in H. rewrite poly_mult_deg in H; try assumption.
  rewrite <- deg_nonzero in n. lia.
Qed.

Lemma divides_x: forall (g: poly),
  deg g > 0 ->
  g |~ x <-> g = x.
Proof.
  intros.
  - unfold divides. split; intros.
    + destruct H0 as [x0 Hx0]. assert (deg (g *~ x0) = deg x) by (rewrite Hx0; reflexivity).
      destruct (destruct_poly x0). subst.
      rewrite poly_mult_0_r in Hx0. inversion Hx0.
      rewrite poly_mult_deg in H0. rewrite deg_x in H0.
      rewrite <- deg_nonzero in n.
      assert (deg g = 1%Z /\ deg x0 = 0%Z) by lia. destruct H1.
      symmetry in H2. rewrite deg_one in H2. subst. rewrite poly_mult_1_r in Hx0.
      assumption. apply f_nonzero. apply Build_PosPoly. assumption. assumption.
    + subst. exists one. apply poly_mult_1_r.
Qed.

(*expresses "g is the gcd of a and b"*)
Definition gcd_def g a b :=
  g |~ a /\ g |~ b /\ forall c, c |~ a /\ c |~ b -> c |~ g.

(*Have to break the abstraction to define GCD - need to destruct on list, not use [destruct_poly]
  May be able to fix by making everything Defined*)
Program Fixpoint gcd_aux (a b : poly) {measure (Z.to_nat (deg b + 1))} : {g: poly | deg b <= deg a ->
  gcd_def g a b /\ exists x' y', (a *~ x') +~ (b *~ y') = g} :=
  match (proj1_sig b) with
  | nil => exist _ a _
  | _ :: _ => match (poly_div a b) with
              | (_, r) => exist _ (gcd_aux b r) _
              end
  end.
Next Obligation.
assert (b = zero). { destruct b.
unfold zero. exist_eq. simpl in Heq_anonymous. subst. reflexivity. } subst.
split.
- unfold gcd_def. split. apply divides_refl. split. apply  divides_zero. intros.
  destruct H0. assumption.
- exists one. exists zero. rewrite poly_mult_1_r. rewrite poly_mult_0_r. rewrite poly_add_0_r. reflexivity.
Defined.
Next Obligation.
assert (b <> zero). { intro. subst. unfold zero in Heq_anonymous0. simpl in Heq_anonymous0.
inversion Heq_anonymous0. } clear Heq_anonymous0. symmetry in Heq_anonymous.
rewrite poly_div_correct in Heq_anonymous; try assumption.
destruct Heq_anonymous. pose proof ( deg_lower_bound r). lia.
Defined.
Next Obligation.
destruct ((gcd_aux b r
           (gcd_aux_func_obligation_2 a b gcd_aux wildcard'1 wildcard'0 Heq_anonymous0 wildcard' r
              Heq_anonymous))). simpl.
assert (b <> zero). { intro. subst. unfold zero in Heq_anonymous0. simpl in Heq_anonymous0.
inversion Heq_anonymous0. } clear Heq_anonymous0. symmetry in Heq_anonymous.
rewrite poly_div_correct in Heq_anonymous; try assumption.
destruct Heq_anonymous. assert (deg r <= deg b) by lia. apply a0 in H3; clear a0.
destruct H3. split.
- unfold gcd_def; unfold gcd_def in H3. destruct H3. destruct H5. split.
  rewrite H1. apply divides_sum. apply divides_factor_l. assumption. assumption.
  split. assumption. intros. apply H6. split. apply H7. rewrite <- poly_add_cancel_1 in H1.
  rewrite <- H1. apply divides_sum. apply H7. apply divides_factor_l. apply H7.
- destruct H4 as [a']. destruct H4 as [b']. rewrite <- poly_add_cancel_1 in H1.
  rewrite <- H1 in H4.
  rewrite poly_mult_distr_r in H4. rewrite poly_add_comm in H4. rewrite poly_add_assoc in H4.
  rewrite (poly_mult_comm _ b) in H4. rewrite poly_mult_assoc in H4.
  rewrite <- poly_mult_distr_l in H4. 
  exists b'. exists (wildcard' *~ b' +~ a'). subst. reflexivity.
Defined.

(*the definition just puts the arguments in the right order and removes the dependent type*)
Definition gcd (a b : poly) : poly :=
   match (Z_le_lt_dec (deg b) (deg a)) with
              | left H => proj1_sig (gcd_aux a b)
              | right H => proj1_sig (gcd_aux b a)
              end.

Lemma gcd_unique: forall (g1 g2 a b : poly),
  gcd_def g1 a b ->
  gcd_def g2 a b ->
  g1 = g2.
Proof.
  intros.
  - unfold gcd_def in H. unfold gcd_def in H0.
    destruct H. destruct H1. destruct H0. destruct H3.
    assert (g2 |~ g1). apply H2. split; assumption.
    assert (g1 |~ g2). apply H4. split; assumption.
    apply divides_eq_iff. split; assumption.
Qed. 

Lemma gcd_sym: forall (g a b: poly),
  gcd_def g a b <-> gcd_def g b a.
Proof.
  intros.
  unfold gcd_def; split; intros; intuition.
Qed.

Lemma gcd_correct': forall a b,
  gcd_def (gcd a b) a b.
Proof.
  intros. unfold gcd. if_tac.
  - destruct (gcd_aux a b). simpl. apply a0. assumption.
  - rewrite gcd_sym. destruct (gcd_aux b a). simpl. apply a0. lia.
Qed.

(*follows from [gcd_correct'] and uniqueness*)
Lemma gcd_correct: forall a b g,
  g = gcd a b <-> gcd_def g a b.
Proof.
  intros. split; intros.
  - subst. apply gcd_correct'.
  - eapply gcd_unique. apply H. apply gcd_correct'.
Qed.

(* Bezout's identity for polynomials*)
Lemma bezout: forall a b,
  exists x y, a *~ x +~ b *~ y = gcd a b.
Proof.
  intros. unfold gcd. if_tac.
  - destruct (gcd_aux a b). simpl.
    apply a0. assumption.
  - destruct (gcd_aux b a). simpl.
    assert (deg a <= deg b) by lia. apply a0 in H0; clear a0. destruct H0.
    destruct H1. destruct H1. exists x1. exists x0. rewrite <- H1. rewrite poly_add_comm. reflexivity.
Qed.

(** Irreducible Polynomials *)

Definition reducible p := exists q, deg q > 0 /\ q <> p /\ q |~ p.

Definition irreducible p := ~ (reducible p).

(*a bit nicer formulation, although the same idea*)
Lemma reducible_alt: forall p,
  p <> zero ->
  reducible p <-> exists a b, deg a > 0 /\ deg b > 0 /\ p = a *~ b.
Proof.
  intros. unfold reducible. unfold divides. split; intros.
  - destruct H0 as [q]. destruct H0. destruct H1. destruct H2 as [x]. exists q. exists x.
    split. assumption. split.
    assert (deg x < 0 \/ 0%Z = deg x \/ deg x > 0) by lia. destruct H3.
    rewrite deg_zero in H3. subst. rewrite poly_mult_0_r in H. contradiction.
    destruct H3. rewrite deg_one in H3. subst. rewrite poly_mult_1_r in H1. contradiction.
    assumption. subst. reflexivity.
  - destruct H0 as [a]. destruct H0 as [b]. destruct H0. destruct H1.
    exists a. split. assumption. split. intro. subst.
    symmetry in H3. apply poly_mult_id in H3. destruct H3. subst.
    assert (deg zero < 0) by (apply deg_zero, reflexivity). lia.
    subst. assert (0%Z = deg one) by (apply deg_one; reflexivity). lia.
    exists b. subst. reflexivity.
Qed.

Lemma irreducible_alt: forall p,
  irreducible p <-> forall (a: poly), a |~ p -> a = one \/ a = p.
Proof.
  intros. unfold irreducible. unfold reducible. split; intros.
  - destruct (destruct_poly a).
    + subst. apply zero_does_not_divide in H0. right. subst. reflexivity.
    + rewrite <- deg_nonzero in n. assert (0%Z = deg a \/ deg a > 0) by lia.
      destruct H1. rewrite deg_one in H1. left. assumption.
      destruct (poly_eq_dec a p).
      * right. assumption.
      * exfalso. apply H. exists a. split. assumption. split; assumption.
  - intro. destruct H0. destruct H0. destruct H1. apply H in H2.
    destruct H2. subst. assert (0%Z = deg one) by (apply deg_one; reflexivity). lia.
    contradiction.
Qed.

(*Definition of a prime element in a ring, specific to polynomials*)
Definition prime f := forall a b, f |~ (a *~ b) -> f |~ a \/ f |~ b.

(*Why we need GCDs - we need to show that all irreducible elements are prime without using ideals and quotients.
  We instead follow the proof of Euclid's Lemma*)
Lemma irreducible_is_prime: forall f,
  irreducible f -> prime f.
Proof.
  intros. rewrite irreducible_alt in H. unfold prime. intros.
  remember (gcd a f) as g. assert (A:= Heqg).
  (*we don't even need to know that (gcd a f) is a gcd, we just need to know that it is a divisor and that
    bezout's identity holds*)
  rewrite gcd_correct in Heqg. unfold gcd_def in Heqg. destruct Heqg. destruct H2.
  apply H in H2. destruct H2. subst.
  pose proof (bezout a f). destruct H2 as [x]. destruct H2 as [y].
  rewrite <- A in H2. 
  assert (b *~ (a *~ x +~ f *~ y) = b). rewrite H2. apply poly_mult_1_r.
  rewrite poly_mult_distr_l in H4.
  right. rewrite <- H4. apply divides_sum. rewrite <- poly_mult_assoc.
  rewrite (poly_mult_comm b). apply divides_factor_r. apply H0. 
  rewrite (poly_mult_comm f). rewrite <- poly_mult_assoc. apply divides_factor_l. apply divides_refl.
  subst. left. assumption.
Qed.

(*don't strictly need this, but it is true in any integral domain. We exclude the special case of 0*)
Lemma prime_is_irreducible: forall f,
  f <> zero ->
  prime f -> irreducible f.
Proof.
  intros. unfold prime in H0. unfold irreducible. intro.
  rewrite reducible_alt in H1; try assumption. destruct H1 as [a].
  destruct H1 as [b]. destruct H1. destruct H2.
  assert (f |~ (a *~ b)). rewrite H3. apply divides_refl.
  apply H0 in H4. destruct H4.
  - subst. unfold divides in H4. destruct H4. rewrite poly_mult_assoc in H3.
    apply poly_mult_id in H3. destruct H3. subst.
    assert (deg zero < 0) by (apply deg_zero; reflexivity). lia.
    apply poly_mult_eq_one in H3. destruct H3. subst.
    assert (0%Z = deg one) by (apply deg_one; reflexivity). lia.
  - subst. unfold divides in H4. destruct H4. rewrite (poly_mult_comm a) in H3.
    rewrite poly_mult_assoc in H3. apply poly_mult_id in H3.
    destruct H3. subst. assert (deg zero <0) by (apply deg_zero; reflexivity). lia.
    apply poly_mult_eq_one in H3. destruct H3. subst. 
    assert (0%Z = deg one) by (apply deg_one; reflexivity). lia.
Qed.

Lemma prime_irreducible_iff: forall f,
  f <> zero ->
  irreducible f <-> prime f.
Proof.
  intros. split; intros. apply irreducible_is_prime; assumption.
  apply prime_is_irreducible; assumption.
Qed.

(** qpolys - polys quotiented by a nonzero polynomial. We define the (ssreflect) field structure in [PolyField.v]*)

Section Qpoly.

Context (f: poly) `{Hpos: PosPoly f}.

(*In our finite fields (and rings), the elements are polynomials of degree smaller than f*)
Definition qpoly : Type := { p: poly | deg p < deg f}.

Lemma zero_lt_deg: deg zero < deg f.
Proof.
pose proof (deg_zero zero). assert (deg zero < 0) by (apply H; reflexivity). destruct Hpos. lia.
Qed.

Lemma one_lt_deg: deg one < deg f.
Proof.
assert (deg one = 0%Z). symmetry. rewrite deg_one. reflexivity. destruct Hpos. lia.
Qed.

Definition poly_mult_mod g h : poly :=
  (g *~ h) %~ f.

Definition poly_add_mod g h : poly :=
  (g +~ h) %~ f.

Definition r0 : qpoly := exist _ zero zero_lt_deg.
Definition r1 : qpoly := exist _ one one_lt_deg.
Definition r_add (g h : qpoly) : qpoly := exist _ (poly_add_mod (proj1_sig g) (proj1_sig h)) 
  (pmod_lt_deg f _).
Definition r_mul (g h : qpoly) : qpoly := exist _ (poly_mult_mod (proj1_sig g) (proj1_sig h)) (pmod_lt_deg f _).

(*From here, we could define a ring of qpolys, but that is not needed in our case. We only care about when f is
  irreducible, and thus we will get a field of qpolys (in [PolyField.v]*)

Variable Hirred : irreducible f.

(*First, we prove that GF(2)/(f) is an integral domain when f is irreducible. This will prove that it is
  a field, since any finite integral domain is a field. There is a bit more work to do in Coq, though*)
Lemma irreducible_integral_domain: forall (a b: poly),
  (a *~ b) %~ f = zero -> a %~ f = zero \/ b %~ f = zero.
Proof.
  intros.
  assert (f |~ (a *~ b)). apply divides_pmod_iff. left. apply f_nonzero; assumption. 
  unfold divides_pmod. apply H. 
  apply irreducible_is_prime in Hirred. unfold prime in Hirred.
  apply Hirred in H0. destruct H0.
  - left. apply divides_pmod_iff in H0. apply H0.
    left. apply f_nonzero; assumption.
  - right. apply divides_pmod_iff in H0. apply H0. left. apply f_nonzero; assumption. 
Qed.

(* Now, we show that the type qpoly f is finite*)

(*have to wrap list polys_leq_degree in a dependent type to make it a list of qpolys (so that we can show
  that the set of qpolys is finite*)
Lemma in_leq_degree: forall x,
  In x(polys_leq_degree (Z.to_nat (deg f) - 1)) -> deg x < deg f.
Proof.
  intros. apply polys_leq_degree_spec in H. destruct Hpos. lia.
Qed.

Definition list_of_qpoly : list qpoly := exist_list (fun x => deg x < deg f) 
  (polys_leq_degree (Z.to_nat (deg f) - 1)) in_leq_degree.

Lemma list_of_qpoly_in: forall (x: qpoly), In x list_of_qpoly.
Proof.
  intros. unfold list_of_qpoly. apply exist_list_in.
  apply polys_leq_degree_spec. destruct x. simpl. lia.
Qed. 

Lemma qpoly_finite: Finite qpoly.
Proof.
  unfold Finite. exists (list_of_qpoly). unfold Full. apply list_of_qpoly_in. 
Qed.

Lemma mult_map_injective: forall (a: qpoly),
  a <> r0 ->
  Injective (r_mul a).
Proof.
  intros. unfold Injective. intros.  destruct x; destruct y; destruct a; simpl in *. exist_inv H0. 
  exist_eq. unfold poly_mult_mod in H0. apply pmod_cancel in H0; try assumption.
  rewrite <- poly_mult_distr_l in H0. apply irreducible_integral_domain in H0.
  destruct H0.
  - rewrite pmod_refl in H0; try lia. subst. exfalso. apply H. exist_eq. reflexivity. auto.
  - rewrite pmod_refl in H0. rewrite poly_add_inv_iff in H0. assumption. auto.
     pose proof (poly_add_deg_max x x0). lia.
Qed.

Lemma mult_map_surjective: forall (a: qpoly),
  a <> r0 ->
  Surjective (r_mul a).
Proof.
  intros. apply Endo_Injective_Surjective. apply qpoly_finite.
  unfold ListDec.decidable_eq. intros. unfold Decidable.decidable. 
  destruct x; destruct y. destruct (poly_eq_dec x x0).
  - left. subst. exist_eq. reflexivity.
  - right. intro. inversion H0. contradiction.
  - apply mult_map_injective. assumption.
Qed.

Lemma inverses_exist: forall (a: qpoly),
  a <> r0 ->
  exists b, r_mul a b = r1.
Proof.
  intros. pose proof (mult_map_surjective a H). unfold Surjective in H0.
  specialize (H0 r1). apply H0.
Qed.

(*coq's fields require a computable inverse function, so we have to iterate through the whole list to find
  the appropriate element. This is not too hard*)

Lemma qpoly_eq_dec: forall (a b: qpoly) ,
  {a = b} + { a <> b}.
Proof.
  intros. destruct a. destruct b.
  destruct (poly_eq_dec x x0).
  - left. subst. exist_eq. reflexivity.
  - right. intro. inversion H. contradiction.
Qed.

(*inv_bool a b = true iff a and b are inverses*)
Definition inv_bool (a b : qpoly) : bool :=
  if (qpoly_eq_dec (r_mul a b) r1) then true else false.

Definition find_inv (a: qpoly) : qpoly :=
  find_default list_of_qpoly a inv_bool r0.

Lemma find_inv_correct: forall a,
  a <> r0 ->
  r_mul a (find_inv a) = r1.
Proof.
  intros. unfold find_inv. pose proof (find_default_in list_of_qpoly a inv_bool r0).
  assert (forall a b : qpoly, inv_bool a b = true -> b <> r0). intros. unfold inv_bool in H1.
  destruct (qpoly_eq_dec (r_mul a0 b) r1). intro. subst. 
  unfold r_mul in e. unfold r1 in e. unfold r0 in e. simpl in e. exist_inv e.
  unfold poly_mult_mod in e. rewrite poly_mult_0_r in e. rewrite pmod_zero in e; try assumption.
  inversion e. inversion H1. apply H0 in H1; clear H0.
  destruct H1. clear H1.
  assert (exists y : qpoly, In y list_of_qpoly /\ inv_bool a y = true).
  pose proof (inverses_exist a H). destruct H1 as [b]. exists b. split.
  apply list_of_qpoly_in. unfold inv_bool.
  if_tac. reflexivity. contradiction. apply H0 in H1; clear H0.
  unfold inv_bool at 1 in H1. 
  destruct (qpoly_eq_dec (r_mul a (find_default list_of_qpoly a inv_bool r0)) r1).
  assumption. inversion H1.
Qed.

Lemma negate_iff: forall P Q,
  (P <-> Q) <-> (~P <-> ~ Q).
Proof.
intros. tauto.
Qed.


Lemma find_inv_zero: forall a,
  a = r0 <-> find_inv a = r0.
Proof.
  intros. unfold find_inv.
  pose proof (find_default_notin list_of_qpoly a inv_bool r0).
   assert (forall a b : qpoly, inv_bool a b = true -> b <> r0). intros. unfold inv_bool in H0.
  destruct (qpoly_eq_dec (r_mul a0 b) r1). intro. subst. 
  unfold r_mul in e. unfold r1 in e. unfold r0 in e. simpl in e. exist_inv e. 
  unfold poly_mult_mod in e. rewrite poly_mult_0_r in e. rewrite pmod_zero in e; try assumption.
  inversion e. inversion H0. apply H in H0; clear H.
  destruct H0. split; intros.
  - subst. rewrite H. reflexivity. intros. unfold inv_bool. destruct (qpoly_eq_dec (r_mul r0 y) r1).
    + unfold r_mul in e. unfold r1 in e. exist_inv e. unfold poly_mult_mod in e.
      rewrite poly_mult_0_l in e. rewrite pmod_zero in e. inversion e. assumption.
    + reflexivity.
  - destruct (qpoly_eq_dec a r0).
    + assumption.
    + apply inverses_exist in n. destruct n as [i].
      apply H0 with(y:=i) in H1. unfold inv_bool in H1.
      destruct (qpoly_eq_dec (r_mul a i) r1). inversion H1. contradiction.
      apply list_of_qpoly_in.
Qed.

Definition r_div (a: qpoly) (b: qpoly) := r_mul a (find_inv b).

Definition poly_to_qpoly (p: poly) : qpoly :=exist (fun x => deg x < deg f)  (p %~ f) (pmod_lt_deg f p).

Definition poly_inv (a: poly) := proj1_sig (find_inv (poly_to_qpoly a)). 

(*Proving that inverses are unique *)
Lemma poly_inv_unique: forall p q1 q2,
  p %~ f <> zero ->
  (p *~ q1) %~ f = one ->
  (p *~ q2) %~ f = one ->
  deg q1 < deg f ->
  deg q2 < deg f ->
  q1 %~ f = q2 %~ f.
Proof.
  intros. assert ((p *~ q1) %~ f = (p *~ q2) %~ f). rewrite H0. rewrite H1. reflexivity.
  rewrite pmod_cancel in H4; try assumption. 
  rewrite <- poly_mult_distr_l in H4.
  apply irreducible_integral_domain in H4.
  destruct H4.
  - contradiction.
  - rewrite pmod_refl in H4. rewrite poly_add_inv_iff in H4. subst. reflexivity. assumption.
    pose proof (poly_add_deg_max q1 q2). lia.
Qed.

Lemma poly_inv_spec: forall p,
  p %~ f <> zero ->
  (p *~ (poly_inv p)) %~ f = one /\ deg (poly_inv p) < deg f.
Proof.
  intros. unfold poly_inv. destruct (find_inv (poly_to_qpoly p)) eqn : F. simpl.
  pose proof (find_inv_correct (poly_to_qpoly p)).
  assert (poly_to_qpoly p <> r0). intro. unfold poly_to_qpoly in H1.
  unfold r0 in H1. exist_inv H1. contradiction. apply H0 in H1; clear H0.
  unfold r_mul in H1. unfold r1 in H1. exist_inv H1.
  rewrite F in H1; simpl in H1. rewrite <- H1.
  unfold poly_mult_mod. split.
  - symmetry. rewrite poly_mult_comm. rewrite pmod_mult_reduce. rewrite poly_mult_comm. reflexivity. assumption.
  - assumption.
Qed.

Lemma poly_inv_iff: forall p q,
  p %~ f <> zero ->
  (p *~ q) %~ f = one /\ deg q < deg f <-> q = poly_inv p.
Proof.
  intros. split; intros.
  - pose proof (poly_inv_spec p H).
    destruct H0. destruct H1. rewrite <- (pmod_refl f); try assumption.
    symmetry. rewrite <- (pmod_refl f); try assumption.
    apply (poly_inv_unique p); assumption.
  - subst. apply poly_inv_spec. assumption.
Qed.

(*we define 0's inverse to be 0 to make things simpler*)
Lemma poly_inv_zero: forall p,
  p %~ f = zero <-> 
  poly_inv p = zero.
Proof.
  intros. pose proof (find_inv_zero (poly_to_qpoly p)). destruct H. unfold poly_inv.
  destruct (poly_to_qpoly p) eqn : Q.
  split; intros.
  - rewrite H. reflexivity. unfold r0. exist_eq. unfold poly_to_qpoly in Q. exist_inv Q. 
    rewrite <- H1; rewrite <- Q; reflexivity.
  - assert (exist (fun p : poly => deg p < deg f) x l = r0). apply H0. 
    unfold r0. apply exist_ext'. simpl. assumption.
    unfold r0 in H2. exist_inv H2.
    unfold poly_to_qpoly in Q. exist_inv Q. subst. assumption.
Qed.

Lemma poly_inv_of_zero: poly_inv zero = zero.
Proof.
  apply poly_inv_zero. apply pmod_zero. assumption.
Qed.

Lemma poly_inv_sym: forall p q,
  deg p < deg f ->
  deg q < deg f ->
  (q = poly_inv p) <-> (p = poly_inv q).
Proof.
  intros. destruct (destruct_poly p).
  - subst. split; intros. symmetry. apply poly_inv_zero. rewrite poly_inv_of_zero in H1.
    subst. rewrite pmod_zero. reflexivity. assumption.
    symmetry in H1. apply poly_inv_zero in H1. rewrite pmod_refl in H1. subst.
     rewrite poly_inv_of_zero. reflexivity. all: assumption.
  - destruct (destruct_poly q).
    + subst. split; intros. symmetry in H1. apply poly_inv_zero in H1. rewrite pmod_refl in H1.
      subst. rewrite poly_inv_of_zero. reflexivity. all: try assumption.
      rewrite poly_inv_of_zero in H1. subst. rewrite poly_inv_of_zero. reflexivity.
    + assert (p %~ f <> zero). intro. rewrite pmod_refl in H1. contradiction. assumption.
      assumption. assert (q %~ f <> zero). intro. rewrite pmod_refl in H2. contradiction. assumption.
      assumption.
      split; intros.
      * rewrite <- poly_inv_iff. rewrite <- poly_inv_iff in H3. destruct H3.
        split. rewrite poly_mult_comm. all: assumption.
      * rewrite <- poly_inv_iff. rewrite <- poly_inv_iff in H3. destruct H3.
        split. rewrite poly_mult_comm. all: assumption.
Qed.

End Qpoly.

(** Constructing Finite Fields *)

(* To construct an actual finite field, we just need an irreducible polynomial. We provide a function to determine
  if a given polynomial is irreducible*)

(*Yet another characterization of reducibility that makes things easier for us. In particular, we only need
  to check polynomials up to (deg f)/2*)

(*If we are given a nonzero and a bound n such that deg p <= 2 *n, it suffices to check all polynomials up 
  to degree n for reducibility*)
Lemma reducible_check: forall p n,
  p <> zero ->
  n < deg p <= 2 * n ->
  reducible p <-> exists g, deg g > 0 /\ deg g <= n /\ p %~ g = zero.
Proof.
  intros. split; intros.
  - rewrite reducible_alt in H1; try assumption. destruct H1 as [a]. destruct H1 as [b].
    destruct H1. destruct H2. 
    (*since deg a + deg b = deg p, both cannot be greater than n*)
    assert (deg p = deg a + deg b). rewrite H3. rewrite poly_mult_deg. reflexivity.
    all: try(intro; subst; assert (deg zero < 0) by (rewrite deg_zero; reflexivity); lia).
    assert (deg a <= n \/ deg b <= n) by lia.
    destruct H5.
    + exists a. split3; try assumption. rewrite H3.
      assert (Ha: PosPoly a). apply Build_PosPoly. assumption.
      rewrite <- (pmod_zero a); try assumption.
      rewrite <- pmod_multiple_of_f. exists b. rewrite poly_add_0_r. apply poly_mult_comm. assumption.
    + exists b. split3; try assumption. rewrite H3.
      assert (Hb: PosPoly b) by (apply Build_PosPoly; assumption). 
      rewrite <- (pmod_zero b); try assumption.
      rewrite <- pmod_multiple_of_f. exists a. symmetry. apply poly_add_0_r. assumption.
  - unfold reducible. destruct H1 as [g]. exists g. destruct H1. destruct H2. split3; try assumption.
    intro. subst. lia. rewrite divides_pmod_iff. unfold divides_pmod. assumption. left. intro.
    subst. assert (deg zero < 0) by (rewrite deg_zero; reflexivity); lia.
Qed.

(*This gives us a natural algorithm: check all polynomials up to degree n*)
(*we make a generic version with an arbitrary list for induction purposes*)
Definition find_factor_aux (p: poly) (l: list poly) : option poly :=
  fold_right (fun q acc => 
    match (poly_div p q) with
    | (_, r) =>
      match (proj1_sig r) with
      | nil => Some q
      | _ :: _ => acc
      end
     end) None l.

Lemma find_factor_aux_finds_factor: forall p l y,
  ~ In zero l ->
  find_factor_aux p l = Some y -> y |~ p.
Proof.
  intros. induction l.
  - simpl in H0. inversion H0.
  - simpl in H0. destruct (poly_div p a) as [q r] eqn : P.
    destruct (destruct_poly r).
    + subst. simpl in H0. inversion H0; subst.
      unfold divides. rewrite poly_div_correct in P.
      destruct P. exists q. rewrite H1. rewrite poly_add_0_r. apply poly_mult_comm.
      intro. subst. apply H. left. reflexivity.
    + rewrite nonzero_not_nil in n. destruct (proj1_sig r) eqn : M. contradiction.
      apply IHl. intuition. apply H0.
Qed.

Lemma find_factor_aux_some_iff: forall p l,
  ~In zero l ->
  (exists y, find_factor_aux p l = Some y) <-> (exists y, In y l /\ y |~ p).
Proof.
  intros. induction l; split; intros.
  - simpl in H0. destruct H0. inversion H0.
  - destruct H0. destruct H0. inversion H0.
  - destruct H0 as [y]. assert (A:= H0).
    simpl in H0.
    destruct (poly_div p a) as [q r] eqn : P.
    destruct (proj1_sig r) eqn : E.
    + inversion H0; subst. exists y. intuition. eapply find_factor_aux_finds_factor. 2 : apply A.
      intro. apply H; assumption.
    + assert (~ In zero l ) by intuition. apply IHl in H1; clear IHl. destruct H1. clear H2.
      assert (exists y : poly, In y l /\ y |~ p). apply H1. exists y. assumption.
      destruct H2. exists x. intuition.
  - simpl. destruct (poly_div p a) as [ q r] eqn : P. simpl in H0. destruct H0.
    destruct H0. destruct H0.
    + subst. destruct (proj1_sig r) eqn : E. exists x. reflexivity.
      rewrite poly_div_correct in P. destruct P. 
      unfold divides in H1. destruct H1 as [a]. rewrite <- H1 in H0.
      rewrite poly_mult_comm in H0. 
      rewrite <- poly_add_cancel_1 in H0. rewrite <- poly_mult_distr_r in H0.
      destruct (destruct_poly (a +~ q)).
      * rewrite e in H0. rewrite poly_mult_0_l in H0. subst.
        inversion E.
      * destruct(destruct_poly x). 
        -- rewrite e in H2. assert (deg zero < 0) by (subst; rewrite deg_zero; reflexivity).
           assert (deg zero >= -1) by (apply deg_lower_bound). 
           assert (deg r >= -1) by (apply deg_lower_bound). lia.
        -- assert (deg r = deg (a +~ q) + deg x). rewrite <- H0.
           rewrite poly_mult_deg. reflexivity. all: try assumption.
           assert (0 <= deg (a +~ q)). apply deg_nonzero. assumption. lia.
      * intro. subst. intuition.
    + destruct (proj1_sig r) eqn : E. exists a. reflexivity.
      apply IHl. intuition. exists x. split; assumption.
Qed. 


(*find a factor of degree at most n if one exists*)
Definition find_factor p n :=
  find_factor_aux p (polys_leq_degree_nontrivial n).

Lemma find_factor_some_iff: forall p n,
  p <> zero ->
  n < deg p <= 2 * n ->
  (exists y, find_factor p (Z.to_nat n) = Some y) <-> (reducible p).
Proof.
  intros. split; intros.
  -  apply find_factor_aux_some_iff in H1.
    + unfold reducible. destruct H1 as [q]. exists q. 
      destruct H1. rewrite <- polys_leq_degree_nontrivial_spec in H1.
      destruct H1. destruct H3. split. assert (0 <= deg q) by (apply deg_nonzero; assumption).
      assert (0%Z = deg q \/ 0 < deg q) by lia. destruct H6.
      rewrite deg_one in H6. contradiction. lia. split. intro. subst.
      lia. assumption.
    + intro. rewrite <- polys_leq_degree_nontrivial_spec in H3.
      destruct H3. contradiction.
  - rewrite reducible_check in H1. 3 : { apply H0. } 2 : assumption. unfold find_factor.
    rewrite find_factor_aux_some_iff.
    + destruct H1 as [g]. exists g. assert (g <> zero). intro; subst.
      assert (deg zero < 0) by (apply deg_zero; reflexivity); lia.
      destruct H1. destruct H3.
      split. rewrite <- polys_leq_degree_nontrivial_spec. split. assumption.
      split. intro; subst. assert (0%Z = deg one) by (apply deg_one; reflexivity). lia.
      lia. rewrite divides_pmod_iff. unfold divides_pmod. assumption. left. assumption.
    + intro. rewrite <- polys_leq_degree_nontrivial_spec in H2. destruct H2. contradiction.
Qed.

(*An easy corollary - gives us a necessary and sufficient test for irreducibility*)
Lemma irreducible_test: forall p n,
  n < deg p <= 2 * n ->
  find_factor p (Z.to_nat n) = None <-> irreducible p.
Proof.
  intros. assert (p <> zero). intro. subst.
  assert ( deg zero < 0) by (apply deg_zero; reflexivity). lia.
  pose proof (find_factor_some_iff _ _ H0 H). apply negate_iff in H1.
  unfold irreducible. rewrite <- H1. split; intros.
  - rewrite H2. intro. destruct H3. inversion H3.
  - destruct (find_factor p (Z.to_nat n)). exfalso. apply H2. exists p0. reflexivity. reflexivity.
Qed.

(*x is an annoying special case - x is irreducible but no other powers of x are *)
Lemma irred_doesnt_divide_monomial: forall (g: poly) (n: nat),
  deg g > 0 ->
  irreducible g ->
  g <> x ->
  ~ (g |~ (monomial n)).
Proof.
  intros. induction n.
  - rewrite monomial_0. intro. unfold divides in H2. destruct H2.
    apply poly_mult_eq_one in H2. destruct H2. subst.
    assert (0%Z = deg one) by (rewrite deg_one; reflexivity). lia.
  - rewrite monomial_expand. intro. 
    apply irreducible_is_prime in H0. unfold prime in H0. apply H0 in H2.
    destruct H2. 
    + apply divides_x in H2. subst. contradiction. assumption.
    + contradiction.
Qed.

(** Primitive Polynomials *)
Section Primitive.

(*The polynomial x^n - 1 (=x^n + 1 over GF(2)*)
Definition nth_minus_one (n: nat) := (monomial n) +~ one.

(*A primitive polynomial is an irreducible polynomial and the first n such that p divides x^n-1 is 2^(deg p)*)
Definition primitive (p: poly) :=
  0 < deg p /\ irreducible p /\ p |~ (nth_minus_one (Nat.pow 2 (Z.to_nat (deg p)) - 1))
  /\ forall n, p |~ (nth_minus_one n) -> (n = 0%nat \/ n >= Nat.pow 2 (Z.to_nat (deg p)) - 1)%nat.

(*check if p divides any polynomial in the list - reverse of find_factor_aux*)
Definition find_nth_aux (p: poly) l :=
  fold_right (fun f acc =>
    match (poly_div f p) with
    | (_, r) => match (proj1_sig r) with
                | nil => Some f
                | _ :: _ => acc
                end
    end) None l.

Lemma find_nth_aux_some_iff: forall p l,
  p <> zero ->
  (exists f, find_nth_aux p l = Some f) <-> (exists f, In f l /\ p |~ f).
Proof.
  intros. induction l; intros.
  - simpl. split; intros H0; destruct H0; try inversion H0. destruct H1.
  - simpl. split; intros.
    + destruct H0 as [f]. destruct (poly_div a p) as [q r] eqn : P.
      destruct (proj1_sig r) eqn : R.
      * inversion H0; subst. exists f. split. left. reflexivity.
        rewrite poly_div_correct in P; try assumption. destruct P.
        assert (r = zero). destruct (destruct_poly r). assumption. apply nonzero_not_nil in n.
        contradiction. subst. clear R. rewrite poly_add_0_r. apply divides_factor_l. apply divides_refl.
      * destruct IHl. clear H2. assert (exists f, find_nth_aux p l = Some f). exists f. assumption.
        apply H1 in H2; clear H1. destruct H2 as [f']. exists f'. intuition.
    + destruct H0 as [f]. destruct H0. destruct (poly_div a p) as [q r] eqn : P.
      rewrite poly_div_correct in P; try assumption. destruct P. destruct H0.
      * subst. destruct (proj1_sig r) eqn : R.
        -- exists (q *~ p +~ r). reflexivity.
        -- unfold divides in H1. destruct H1 as [x].
           rewrite <- poly_add_cancel_1 in H0. rewrite poly_mult_comm in H0.
           rewrite <- poly_mult_distr_r in H0. 
           assert (r <> zero). destruct (destruct_poly r). rewrite e in R. simpl in R. inversion R.
           assumption. assert (deg r = deg ((x+~ q) *~ p)). rewrite H0. reflexivity.
           destruct (destruct_poly (x +~ q)). rewrite e in H0. rewrite poly_mult_0_l in H0.
           subst. contradiction. rewrite poly_mult_deg in H2; try assumption. 
           rewrite <- deg_nonzero in n. lia.
      * assert (exists f, In f l /\ p |~ f). exists f. auto. apply IHl in H4; clear IHl. destruct H4 as [f'].
        destruct (proj1_sig r). exists a. reflexivity. exists f'. assumption.
Qed.

Lemma find_nth_aux_none_iff: forall p l,
  p <> zero ->
  (find_nth_aux p l = None) <-> (forall f, In f l -> ~(p |~ f)).
Proof.
  intros. apply (find_nth_aux_some_iff p l) in H. apply negate_iff in H.
  split; intros. intro. destruct H. apply H. intro. destruct H4. rewrite H4 in H0. inversion H0.
  exists f. auto.
  destruct H. destruct (find_nth_aux p l) eqn : P. 
  exfalso. apply H1. intro. destruct H2. destruct H2. apply H0 in H2. contradiction.
  exists p0. reflexivity. reflexivity.
Qed. 

(*all x^n + 1 from x + 1 to x^(bound - 1) + 1*)
Fixpoint all_nth_polys (bound: nat) :=
  match bound with
  | O => nil
  | S O => nil
  | S(n') => nth_minus_one (n') :: all_nth_polys n'
  end.

Lemma all_nth_polys_spec: forall bound (p: poly),
  In p (all_nth_polys bound) <-> exists n, (0 < n < bound)%nat /\ p = nth_minus_one n.
Proof.
  intros. induction bound.
  - simpl. split; intros.
    + destruct H.
    + destruct H as [n]. lia.
  - simpl. destruct bound.
    + simpl. split; intros. destruct H. destruct H. lia.
    + split; intros. destruct H.
      * exists (S bound). split. lia. rewrite H. reflexivity.
      * apply IHbound in H. destruct H as [n]. exists n. split. lia. apply H.
      * destruct H as [n]. destruct H. assert ((0 < n < S bound)%nat \/ (n = S bound)%nat) by lia.
        destruct H1. right. apply IHbound. exists n. split. lia. assumption. left. subst. reflexivity.
Qed.

Lemma nat_mul_1_iff: forall (m n : nat),
  (m * n = 1)%nat <-> n = 1%nat /\ m = 1%nat.
Proof.
  intros. split; intros. induction m.
  - simpl in H. inversion H.
  - simpl in H. assert (n = 0%nat \/ n = 1%nat) by lia. destruct H0.
    + subst. lia.
    + split. assumption. subst. lia.
  - destruct H; subst. reflexivity.
Qed. 

Lemma pow_1_iff: forall (m n: nat),
  (m ^ n)%nat = 1%nat <-> m = 1%nat \/ (n = 0%nat).
Proof.
  intros. split; intros.
  - induction n.
    + right. reflexivity.
    + simpl in H. apply nat_mul_1_iff in H. destruct H.
      subst. left. reflexivity.
  - destruct H. subst. induction n. reflexivity.
    simpl. lia. subst. reflexivity.
Qed.
 

(*The 4 (computable) things we have to check to prove a polynomial is primitive*)
Lemma test_primitive (p: poly) :
  (0 < deg p /\
  irreducible p /\
  divides_pmod p (nth_minus_one (Nat.pow 2 (Z.to_nat (deg p)) - 1))  /\
  (find_nth_aux p (all_nth_polys (Nat.pow 2 (Z.to_nat (deg p))- 1)) = None)) <-> primitive p.
Proof.
  unfold primitive; split; intros.
  - destruct H. destruct H0. destruct H1.
    assert (p <> zero). 
    rewrite <- deg_nonzero. lia. split. assumption. split. assumption. split.
    rewrite divides_pmod_iff. assumption. left. assumption. intros.
    assert (Z: n = 0%nat \/ (n > 0)%nat) by lia. destruct Z. left. assumption. rename H5 into Z.
    assert (((0 <= n < 2 ^ Z.to_nat (deg p) - 1)%nat) \/ (n >= 2 ^ Z.to_nat (deg p) - 1)%nat) by lia.
    destruct H5.
    + assert ((2 ^ Z.to_nat (deg p) - 1) > 0)%nat. lia.
      pose proof  (all_nth_polys_spec (2 ^ Z.to_nat (deg p) - 1)%nat (nth_minus_one n)). 
      rewrite find_nth_aux_none_iff in H2; try assumption.
      destruct H7. clear H7. 
      assert (In (nth_minus_one n) (all_nth_polys (2 ^ Z.to_nat (deg p) - 1))). apply H8.
      exists n. split. lia. reflexivity. clear H8.
      apply H2 in H7. contradiction.
    + right. assumption.
  - destruct H. destruct H0. destruct H1.
    split. assumption. split. assumption. split.
    rewrite <- divides_pmod_iff. assumption. left. rewrite <- deg_nonzero. lia.
    rewrite find_nth_aux_none_iff; try assumption. intros.
    intro.
    apply all_nth_polys_spec in H3. 
    destruct H3 as [n]. destruct H3. rewrite H5 in H4. apply H2 in H4. lia. rewrite <- deg_nonzero. lia.
Qed.

End Primitive.