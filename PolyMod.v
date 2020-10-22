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
  g %~ f = h %~ f.

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

(** Polynomial GCD *)

(*p divides q if p is a factor of q, ie, q % p = 0 *)
(*we use a definition in terms of existence (rather than just pmod) to handle to zero cases, since 0 | 0 is true
but 0 | p is false for any p <> zero*)
Definition divides p q := exists x, p *~ x = q.

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
      assert (deg b = deg ((x+~ a) *~ p)) by (rewrite H1; reflexivity).
      rewrite poly_mult_deg in H3; try assumption. 
      rewrite <- deg_nonzero in n. lia.
    + subst. destruct (destruct_poly p).
      * subst. unfold pmod. simpl. unfold zero. exist_eq. reflexivity.
      * assert (0 <= deg p) by (rewrite deg_nonzero; apply n). assert (0%Z = deg p \/ 0 < deg p) by lia.
        destruct H1. rewrite deg_one in H1. subst. unfold pmod; simpl. unfold zero. exist_eq. reflexivity.
        apply pmod_zero. lia.
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

(*expresses "g is the gcd of a and b"*)
Definition gcd_def g a b :=
  g |~ a /\ g |~ b /\ forall c, c |~ a /\ c |~ b -> c |~ g.

(*test*)
(*unfortunately, have to break the abstraction to define GCD - need to destruct on list, not use [destruct_poly]*)
Program Fixpoint gcd_aux (a b : poly) {measure (Z.to_nat (deg b + 1))} : {g: poly | deg b <= deg a ->
  gcd_def g a b /\ exists x y, (a *~ x) +~ (b *~ y) = g} :=
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
(*[gcd] does not compute bc we match on <=, but [gcd_aux] does. This is OK for our purposes, maybe try to fix *)
(*
Eval compute in (to_list (gcd (from_list (0 :: 1 :: 1 :: nil)) (from_list (0 :: 0 :: 1 :: nil)))).
Eval compute in (to_list (proj1_sig (gcd_aux (from_list (0 :: 1 :: 1 :: nil)) (from_list (0 :: 0 :: 1 :: nil))))).
*)


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

(* Now, we can prove the existence of inverses for the ring Z2[x]/(f), where f is irreducible*)
    
Require Import Coq.Logic.FinFun.
Require Import Helper.

Section FiniteField.

Variable f : poly.
Variable Hnontrivial: deg f > 0.
Variable Hirred : irreducible f.

Definition z := (r0 f Hnontrivial).

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
Definition list_of_qpoly : {l: list (qpoly f)| forall x, In x l}.
Proof.
remember (exist_list_strong (fun x => deg x < deg f) (polys_leq_degree (Z.to_nat (deg f) - 1))) as l.
assert (forall x : poly,
     In x (polys_leq_degree (Z.to_nat (deg f) - 1)) -> (fun x0 : poly => deg x0 < deg f) x).
intros. rewrite <- (polys_leq_degree_spec (Z.to_nat (deg f) - 1)) in H. lia.
apply l in H. destruct H. eapply exist. intros. rewrite i. 
apply polys_leq_degree_spec. unfold qpoly in x0. destruct x0. simpl. lia.
Defined. 

Lemma qpoly_finite: Finite (qpoly f).
Proof.
  unfold Finite. exists (proj1_sig list_of_qpoly). destruct list_of_qpoly. simpl.
  unfold Full. apply i.
Qed.

Definition mult_map (a b : qpoly f) := (r_mul f Hnontrivial) a b.
Print Injective.
Lemma mult_map_injective: forall (a: qpoly f),
  a <> z ->
  Injective (mult_map a).
Proof.
  intros. unfold Injective. intros. unfold mult_map in H0.
  unfold r_mul in H0. destruct x; destruct y; destruct a; simpl in *. inversion H0.
  exist_eq. unfold poly_mult_mod in H2. apply pmod_cancel in H2; try assumption.
  rewrite <- poly_mult_distr_l in H2. apply  irreducible_integral_domain in H2.
  destruct H2.
  - rewrite pmod_refl in H1; try lia. subst. exfalso. apply H. exist_eq. reflexivity.
  - rewrite pmod_refl in H1. rewrite poly_add_inv_iff in H1. assumption.
    lia. pose proof (poly_add_deg_max x x0). lia.
Qed.

Lemma mult_map_surjective: forall (a: qpoly f),
  a <> z ->
  Surjective (mult_map a).
Proof.
  intros. apply Endo_Injective_Surjective. apply qpoly_finite.
  unfold ListDec.decidable_eq. intros. unfold Decidable.decidable. 
  destruct x; destruct y. destruct (poly_eq_dec x x0).
  - left. subst. exist_eq. reflexivity.
  - right. intro. inversion H0. contradiction.
  - apply mult_map_injective. assumption.
Qed.

Lemma inverses_exist: forall (a: qpoly f),
  a <> z ->
  exists b, r_mul f Hnontrivial a b = (r1 f Hnontrivial).
Proof.
  intros. pose proof (mult_map_surjective a H). unfold Surjective in H0.
  specialize (H0 (r1 f Hnontrivial)). unfold mult_map in H0. apply H0.
Qed.

(*coq's fields require a computable inverse function, so we have to iterate through the whole list to find
  the appropriate element. This is not hard. Will do next (+ prove specific polys irred*)
End FiniteField.
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
