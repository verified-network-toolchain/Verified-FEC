Require Import VST.floyd.functional_base.
Require Import Poly.
Require Import PolyMod.
Require Import Coq.Logic.FinFun.
Require Import Helper.
Require Import InjectiveSurjective.
Import WPoly.

(** * Working with Primitive Polynomials and Primitive Elements*)

Section Primitive.

Variable f : poly.
Variable Hnontrivial: deg f > 0.
Variable Hprim: primitive f.

(*we want to prove that x is a primitive element of GF(2)/(f) - ie, for any nonzero
  poly p with degree smaller than deg f,
  there is some 0 <= i < 2^(deg f) - 1 such that (x^i = p) mod f*)

Definition bounded_int (u: nat) : Type := {z : Z | (0 <= z < Z.of_nat u) }.

(*Prove that bounded ints are finite*)
Definition all_bounded_ints_non_dep u : list Z :=
  map (fun x => Z.of_nat x) (seq 0 u).

Lemma all_bounded_ints_non_dep_spec: forall u z,
  In z (all_bounded_ints_non_dep u) <-> (0 <= z < Z.of_nat u).
Proof.
  intros. unfold all_bounded_ints_non_dep. rewrite in_map_iff.  split; intros.
  - destruct H. destruct H. rewrite in_seq in H0. lia.
  - exists (Z.to_nat z). split. lia. rewrite in_seq. lia.
Qed. 

Lemma all_bounded_ints_non_dep_spec': forall u z,
  In z (all_bounded_ints_non_dep u) -> (0 <= z < Z.of_nat u).
Proof.
  apply all_bounded_ints_non_dep_spec.
Qed.

Lemma all_bounded_ints_nodup: forall u, NoDup (all_bounded_ints_non_dep u).
Proof.
  intros. unfold all_bounded_ints_non_dep. apply Injective_map_NoDup.
  unfold Injective. intros. lia. apply seq_NoDup.
Qed.

Definition all_bounded_ints u : list (bounded_int u) :=
  exist_list _ (all_bounded_ints_non_dep u) (all_bounded_ints_non_dep_spec' u).

Lemma all_bounded_ints_spec: forall u (b: bounded_int u),
  In b (all_bounded_ints u).
Proof.
  intros. destruct b. unfold all_bounded_ints. apply exist_list_in.
  simpl. apply all_bounded_ints_non_dep_spec. assumption.
Qed.

Lemma all_bounded_ints_length: forall u, length (all_bounded_ints u) = u.
Proof.
  intros. unfold all_bounded_ints. epose proof exist_list_length ((fun z : Z => 0 <= z < Z.of_nat u)).
  rewrite H. unfold all_bounded_ints_non_dep. rewrite map_length. apply seq_length.
Qed.

(*The range of our function: nonzero qpolys*)
(*ugh the nested dependent type is not very nice, maybe there is a better way*)
Definition nonzero_qpoly := {q: qpoly f | proj1_sig q <> zero}.

Lemma in_leq_degree_nonzero: forall x,
  In x (polys_leq_degree_nonzero (Z.to_nat (deg f) - 1)) -> deg x < deg f.
Proof.
  intros. apply polys_leq_degree_nonzero_spec in H. lia.
Qed.

Definition list_of_qpoly_nonzero' : list (qpoly f) := exist_list (fun x => deg x < deg f) 
  (polys_leq_degree_nonzero (Z.to_nat (deg f) - 1)) in_leq_degree_nonzero.

Lemma in_leq_degree_nonzero_nonzero: forall x, In x (list_of_qpoly_nonzero') ->
  proj1_sig x <> zero.
Proof.
  intros. unfold list_of_qpoly_nonzero' in H. rewrite (exist_list_in (fun x : poly => deg x < deg f))  in H.
  apply polys_leq_degree_nonzero_spec in H. destruct H. assumption.
Qed.

Definition all_nonzero_qpolys: list (nonzero_qpoly) :=
  exist_list _ list_of_qpoly_nonzero' (in_leq_degree_nonzero_nonzero).

Lemma all_nonzero_qpolys_in: forall (q: nonzero_qpoly),
  In q all_nonzero_qpolys.
Proof.
  intros. unfold all_nonzero_qpolys. rewrite (exist_list_in (fun x : qpoly f => proj1_sig x <> zero) ).
  unfold list_of_qpoly_nonzero'. rewrite (exist_list_in  (fun x : poly => deg x < deg f)).
  apply polys_leq_degree_nonzero_spec. destruct q. simpl. split. assumption.
  destruct x. simpl. lia.
Qed.

Definition field_size := (2 ^ (Z.to_nat (deg f)) - 1)%nat.

Lemma all_nonzero_qpolys_length: length (all_nonzero_qpolys) = field_size.
Proof.
  unfold field_size. unfold all_nonzero_qpolys. rewrite (exist_list_length (fun x : qpoly f => proj1_sig x <> zero)).
  unfold list_of_qpoly_nonzero'. rewrite (exist_list_length (fun x : poly => deg x < deg f)).
  rewrite polys_leq_degree_nonzero_length.
  assert ((Z.to_nat (deg f) - 1 + 1)%nat = Z.to_nat (deg f)) by lia. rewrite H. reflexivity.
Qed.

Lemma all_nonzero_qpolys_NoDups: NoDup (all_nonzero_qpolys).
Proof.
  unfold all_nonzero_qpolys. rewrite (exist_list_NoDup (fun x : qpoly f => proj1_sig x <> zero)).
  unfold list_of_qpoly_nonzero'. rewrite (exist_list_NoDup (fun x : poly => deg x < deg f)).
  apply polys_leq_degree_nonzero_NoDup.
Qed.

Lemma bounded_int_listing: forall u, Listing (all_bounded_ints u).
Proof.
  intros. unfold Listing. split. unfold all_bounded_ints.
  rewrite (exist_list_NoDup  (fun z : Z => 0 <= z < Z.of_nat u)). apply all_bounded_ints_nodup.
  unfold Full. apply all_bounded_ints_spec.
Qed.

Lemma nonzero_qpoly_listing: Listing (all_nonzero_qpolys).
Proof.
  unfold Listing. split. apply all_nonzero_qpolys_NoDups. unfold Full. apply all_nonzero_qpolys_in.
Qed.

(*We now define the map i -> (x^i %f) for 0 <= i < 2^(deg f) - 1 and show that it is injective. Since boundedInts
  are finite, it is surjective as well*)



Definition primitive_map' (b: bounded_int field_size) : qpoly f :=
  exist _ (monomial (Z.to_nat (proj1_sig b)) %~ f) (pmod_lt_deg f Hnontrivial _).

(*TODO move*)
Lemma monomial_exp_law: forall a b,
  monomial a *~ monomial b = monomial (a + b).
Proof.
  intros. rewrite <- shift_monomial. unfold monomial. unfold shift. 
  destruct (destruct_poly (exist PolyDefs.P.wf_poly (PolyDefs.P.monomial b) (PolyDefs.P.wf_monomial b))).
  - unfold zero in e. inversion e. exfalso. eapply PolyDefs.P.monomial_not_0. apply H0.
  - exist_eq. simpl. unfold PolyDefs.P.shift.
    unfold PolyDefs.P.monomial. if_tac.
    + subst. if_tac. assert (a = 0%nat) by lia. subst. simpl. reflexivity. unfold PolyDefs.P.shift.
      replace (a + 0)%nat with (a) by lia. reflexivity.
    + if_tac. lia. unfold PolyDefs.P.shift.
      rewrite <- list_repeat_app. rewrite app_assoc. reflexivity.
Qed.

(*move this too*)
Definition x : poly := monomial 1.

Lemma deg_x: deg x = 1%Z.
Proof.
  intros. unfold x. unfold monomial. unfold deg. simpl. reflexivity.
Qed.

Lemma monomial_expand: forall n,
  monomial (S(n)) = x *~ monomial n.
Proof.
  intros. replace (S(n)) with (n+1)%nat by lia. rewrite <- monomial_exp_law.
  unfold x. apply poly_mult_comm.
Qed.

Lemma divides_x: forall (g: poly),
  deg g > 0 ->
  g |~ x <-> g = x.
Proof.
  intros.
  - unfold divides. split; intros.
    + destruct H0. assert (deg (g *~ x0) = deg x) by (rewrite H0; reflexivity).
      destruct (destruct_poly x0). subst.
      rewrite poly_mult_0_r in H0. inversion H0.
      rewrite poly_mult_deg in H1. rewrite deg_x in H1.
      rewrite <- deg_nonzero in n.
      assert (deg g = 1%Z /\ deg x0 = 0%Z) by lia. destruct H2.
      symmetry in H3. rewrite deg_one in H3. subst. rewrite poly_mult_1_r in H0.
      assumption. apply f_nonzero. assumption. assumption.
    + subst. exists one. apply poly_mult_1_r.
Qed.

(*maybe move also*)
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


Lemma primitive_map'_nonzero: forall b,
  proj1_sig (primitive_map' b) <> zero.
Proof.
  intros. unfold primitive_map'. simpl. intro.
  destruct b; simpl in H.
  assert (f |~ (monomial (Z.to_nat x0))). rewrite divides_pmod_iff.
  unfold divides_pmod. apply H. left. apply f_nonzero. assumption. 
  destruct (poly_eq_dec f x).
  - unfold field_size in a. rewrite e in a. rewrite deg_x in a. simpl in a.
    assert (x0 = 0%Z) by lia. rewrite H1 in H0. simpl in H0. 
    rewrite monomial_0 in H0. unfold divides in H0.
    subst. destruct H0. apply poly_mult_eq_one in H0.
    destruct H0. subst. rewrite H0 in Hnontrivial.
    assert (0%Z = deg one) by (apply deg_one; reflexivity). lia.
  - apply (irred_doesnt_divide_monomial f (Z.to_nat x0)); try assumption.
    unfold primitive in Hprim. apply Hprim.
Qed.

Definition primitive_map (b: bounded_int field_size) : nonzero_qpoly :=
  exist _ (primitive_map' b) (primitive_map'_nonzero b). 

Lemma primitive_map_injective: Injective primitive_map.
Proof.
  unfold Injective. intros. unfold primitive_map in H. inversion H. clear H.
  destruct x0; destruct y; simpl in H1. exist_eq.
  rewrite pmod_cancel in H1; try assumption.
  (*special case - if f is x - then GF(2)/(x) = GF(2) - only 2 elements to deal with - only nontrivial elt is 1*)
  destruct (poly_eq_dec f x).
  - rewrite e in H1. assert (field_size = 1%nat). unfold field_size.
    rewrite e. rewrite deg_x. simpl. reflexivity. rewrite H in a. simpl in a. rewrite H in a0.
    simpl in a0. lia. 
  -
  (*2 cases are the same, so we abstract in an assertion*)
  (*Proof idea: if x^i = x^j mod f, wlog assume i <= j. Then x^ix^(j-i) - x^i = 0 %f, so
    x^i(x^(j-i) - 1) = 0% f. Since f is irreducible, x^i = 0 % f or x^(j-i) -1 = 0 % f.
    In the first case, x^i = q * f, so f has the factor x (x itself is a special case),
    in the second case, this contradicts the definition of a primitive poly, since j - i < 2 ^ deg f - 1*)
  assert (forall y y', (0 <= y < Z.of_nat field_size) -> (0 <= y' < Z.of_nat field_size) ->
  (monomial (Z.to_nat y) +~ monomial (Z.to_nat y')) %~ f = zero -> y <= y' -> y = y'). {
  intros. assert ((Z.to_nat y') = (Z.to_nat y +  Z.to_nat (y' - y))%nat) by lia.
  rewrite H4 in H2. rewrite <- monomial_exp_law in H2.
  rewrite <- (poly_mult_1_r (monomial (Z.to_nat y))) in H2 at 1.
  rewrite <- poly_mult_distr_l in H2.
  apply irreducible_integral_domain in H2; try assumption.
  destruct H2.
  - unfold pmod in H2. destruct (poly_div (monomial (Z.to_nat y)) f ) as [q r] eqn : P.
    simpl in H2. subst. rewrite poly_div_correct in P; try assumption.
    destruct P. rewrite poly_add_0_r in H2.
    assert (f |~ monomial (Z.to_nat y)). unfold divides. exists q. rewrite H2. apply poly_mult_comm.
    exfalso. apply (irred_doesnt_divide_monomial f (Z.to_nat y)); try assumption. unfold primitive in Hprim.
    apply Hprim. apply f_nonzero. assumption.
  - unfold primitive in Hprim. 
    assert (f |~ nth_minus_one (Z.to_nat (y' - y))). unfold nth_minus_one.
    rewrite poly_add_comm. rewrite divides_pmod_iff. unfold divides_pmod. apply H2. left.
    apply f_nonzero; assumption. destruct Hprim. destruct H7. destruct H8.
    apply H9 in H5. 
    destruct H5. lia. unfold field_size in H. unfold field_size in H0. lia.
  - unfold primitive in Hprim. apply Hprim. }
  assert (x0 <= x1 \/ x0 > x1) by lia.
  destruct H0. apply H; try assumption. 
  symmetry. apply H; try assumption; try lia. rewrite poly_add_comm. apply H1.
Qed.

Lemma primitive_map_surjective: Surjective primitive_map.
Proof.
  eapply injective_surjective.
  apply (bounded_int_listing field_size). 
  apply nonzero_qpoly_listing.
  rewrite all_nonzero_qpolys_length.
  rewrite all_bounded_ints_length. lia. 
  apply primitive_map_injective.
Qed.

Lemma primitive_power_exists: forall (q: qpoly f),
  (proj1_sig q <> zero) ->
  exists (n: Z), (0 <= n < Z.of_nat field_size)%Z /\ monomial (Z.to_nat n) %~ f = (proj1_sig q).
Proof.
  intros. pose proof (primitive_map_surjective). unfold Surjective in H0.
  remember (exist (fun x => proj1_sig x <> zero) q H) as q'.
  specialize (H0 q'). destruct H0. destruct x0. exists x0. split. assumption.
  rewrite Heqq' in H0. unfold primitive_map in H0. inversion H0.
  destruct q. unfold primitive_map' in H2. inversion H2.
  simpl. reflexivity.
Qed.

Definition find_power_aux (l: list Z) (p: poly) : Z :=
  fold_right (fun z acc => if (poly_eq_dec p ((monomial (Z.to_nat z)) %~ f)) then z else acc) (-1) l.

Lemma find_power_aux_spec: forall l p,
  (forall z, In z l -> 0 <= z < Z.of_nat field_size)%Z ->
   (exists z, In z l /\ monomial (Z.to_nat z) %~ f = p) ->
  p = monomial (Z.to_nat (find_power_aux l p)) %~ f /\ In (find_power_aux l p) l.
Proof.
  intros. induction l.
  - simpl. simpl in H0. destruct H0. destruct H0. destruct H0.
  - simpl. split. destruct H0. destruct H0. destruct H0. subst. if_tac. reflexivity. contradiction.
    if_tac. assumption. apply IHl. intros. apply H. right. assumption.
    exists x0. split; assumption. if_tac. left. reflexivity.
    destruct H0. destruct H0. destruct H0. subst. contradiction. 
    right. apply IHl. intros. apply H. right. assumption. exists x0. split; assumption.
Qed.


Definition find_power (p: poly) : Z :=
  find_power_aux (all_bounded_ints_non_dep field_size) p.

Lemma find_power_spec: forall p,
  p <> zero ->
  deg p < deg f ->
  p = monomial (Z.to_nat (find_power p)) %~ f /\ 0 <= (find_power p) < Z.of_nat field_size.
Proof.
  intros. pose proof (find_power_aux_spec (all_bounded_ints_non_dep field_size) p).
  unfold find_power.
  assert (forall z : Z, In z (all_bounded_ints_non_dep field_size) -> 0 <= z < Z.of_nat field_size). {
  apply all_bounded_ints_non_dep_spec. }
  specialize (H1 H2); clear H2.
  assert (exists z : Z, In z (all_bounded_ints_non_dep field_size) /\ monomial (Z.to_nat z) %~ f = p). {
  pose proof primitive_power_exists.
  remember  ((exist (fun x => deg x < deg f) p H0)) as q. specialize (H2 q).
  assert (proj1_sig q <> zero). intro. rewrite Heqq in H3. simpl in H3. contradiction.
  apply H2 in H3. destruct H3. exists x0. destruct H3. split. 
  apply all_bounded_ints_non_dep_spec. apply H3. rewrite Heqq in H4. simpl in H4.
  apply H4. }
  specialize (H1 H2); clear H2.
  destruct H1. split. assumption. 
  apply all_bounded_ints_non_dep_spec in H2. apply H2.
Qed.


End Primitive.
