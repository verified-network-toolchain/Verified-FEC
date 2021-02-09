Require Import VST.floyd.functional_base.
Require Import Poly.
Require Import PolyMod.
Require Import Coq.Logic.FinFun.
Require Import Helper.
Require Import InjectiveSurjective.

(** * Working with Primitive Polynomials and Primitive Elements*)

(*If f = x, GF(2)/(f) = gf(2). This is a trivial case that is annoying and we don't need, since none of our
  finite fields are GF(2)*)
Class PrimPoly (f: poly) `{Hpos: PosPoly f} := {
  Hprim : primitive f;
  Hnotx: f <> x}.

Lemma f_irred: forall f `{PrimPoly f}, irreducible f.
Proof.
  intros f Hpos Hprim. destruct Hprim. unfold primitive in Hprim0.
  apply Hprim0.
Qed.

Lemma deg_gt_one: forall f `{PrimPoly f}, deg one < deg f.
Proof.
  intros f Hpos Hprim. replace (deg one) with (0%Z) by (rewrite deg_one; reflexivity).
  destruct Hpos; lia.
Qed.

Section Primitive.

Context (f: poly) `{Hprim: PrimPoly f}.

Definition field_size := (2 ^ (Z.to_nat (deg f)) - 1)%nat.

(*we want to prove that x is a primitive element of GF(2)/(f) - ie, for any nonzero
  poly p with degree smaller than deg f,
  there is some 0 <= i < 2^(deg f) - 1 such that (x^i = p) mod f*)

Definition bounded_int (u: nat) : Type := {z : Z | (0 < z <= Z.of_nat u) }.

(*Prove that bounded ints are finite*)
Definition all_bounded_ints_non_dep u : list Z :=
  map (fun x => Z.of_nat x) (seq 1 u).

Lemma all_bounded_ints_non_dep_spec: forall u z,
  In z (all_bounded_ints_non_dep u) <-> (0 < z <= Z.of_nat u).
Proof.
  intros. unfold all_bounded_ints_non_dep. rewrite in_map_iff.  split; intros.
  - destruct H. destruct H. rewrite in_seq in H0. lia.
  - exists (Z.to_nat z). split. lia. rewrite in_seq. lia.
Qed. 

Lemma all_bounded_ints_non_dep_spec': forall u z,
  In z (all_bounded_ints_non_dep u) -> (0 < z <= Z.of_nat u).
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
  intros. unfold all_bounded_ints. epose proof exist_list_length ((fun z : Z => 0 < z <= Z.of_nat u)).
  rewrite H. unfold all_bounded_ints_non_dep. rewrite map_length. apply seq_length.
Qed.

(*The range of our function: nonzero qpolys*)
(*ugh the nested dependent type is not very nice, maybe there is a better way*)
Definition nonzero_qpoly := {q: qpoly f | proj1_sig q <> zero}.

Lemma in_leq_degree_nonzero: forall x,
  In x (polys_leq_degree_nonzero (Z.to_nat (deg f) - 1)) -> deg x < deg f.
Proof.
  intros. apply polys_leq_degree_nonzero_spec in H. destruct Hpos0. lia.
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

Lemma all_nonzero_qpolys_length: length (all_nonzero_qpolys) = field_size.
Proof.
  unfold field_size. unfold all_nonzero_qpolys. rewrite (exist_list_length (fun x : qpoly f => proj1_sig x <> zero)).
  unfold list_of_qpoly_nonzero'. rewrite (exist_list_length (fun x : poly => deg x < deg f)).
  rewrite polys_leq_degree_nonzero_length. destruct Hpos0.
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
  rewrite (exist_list_NoDup  (fun z : Z => 0 < z <= Z.of_nat u)). apply all_bounded_ints_nodup.
  unfold Full. apply all_bounded_ints_spec.
Qed.

Lemma nonzero_qpoly_listing: Listing (all_nonzero_qpolys).
Proof.
  unfold Listing. split. apply all_nonzero_qpolys_NoDups. unfold Full. apply all_nonzero_qpolys_in.
Qed.

(*We now define the map i -> (x^i %f) for 0 <= i < 2^(deg f) - 1 and show that it is injective. Since boundedInts
  are finite, it is surjective as well*)

Definition primitive_map' (b: bounded_int field_size) : qpoly f :=
  exist _ (monomial (Z.to_nat (proj1_sig b)) %~ f) (pmod_lt_deg f _).

Lemma primitive_map'_nonzero: forall b,
  proj1_sig (primitive_map' b) <> zero.
Proof.
  intros. unfold primitive_map'. simpl. intro.
  destruct b; simpl in H.
  assert (f |~ (monomial (Z.to_nat x))). rewrite divides_pmod_iff.
  unfold divides_pmod. apply H. left. apply f_nonzero. assumption. 
  apply (irred_doesnt_divide_monomial f (Z.to_nat x)); try assumption. apply Hpos.
  apply (@f_irred f Hpos0). apply Hprim. apply Hnotx.
Qed.

Definition primitive_map (b: bounded_int field_size) : nonzero_qpoly :=
  exist _ (primitive_map' b) (primitive_map'_nonzero b). 

Lemma primitive_map_injective: Injective primitive_map.
Proof.
  unfold Injective. intros. unfold primitive_map in H. unfold primitive_map' in H. repeat(exist_inv H).
  destruct x; destruct y; simpl in H. exist_eq.
  rewrite pmod_cancel in H; try assumption.
  (*2 cases are the same, so we abstract in an assertion*)
  (*Proof idea: if x^i = x^j mod f, wlog assume i <= j. Then x^ix^(j-i) - x^i = 0 %f, so
    x^i(x^(j-i) - 1) = 0% f. Since f is irreducible, x^i = 0 % f or x^(j-i) -1 = 0 % f.
    In the first case, x^i = q * f, so f has the factor x (x itself is a special case),
    in the second case, this contradicts the definition of a primitive poly, since j - i < 2 ^ deg f - 1*)
  assert (forall y y', (0 < y <= Z.of_nat field_size) -> (0 < y' <= Z.of_nat field_size) ->
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
    exfalso. apply (irred_doesnt_divide_monomial f (Z.to_nat y)); try assumption. apply Hpos. 
    eapply f_irred. apply Hprim. apply Hnotx. apply f_nonzero. apply Hpos0. 
  - unfold primitive in Hprim. 
    assert (f |~ nth_minus_one (Z.to_nat (y' - y))). unfold nth_minus_one.
    rewrite poly_add_comm. rewrite divides_pmod_iff. unfold divides_pmod. apply H2. left.
    apply f_nonzero; assumption. destruct Hprim. destruct Hprim0. destruct H7. destruct H8.
    apply H9 in H5. 
    destruct H5. lia. unfold field_size in H0. unfold field_size in H1. lia.
  - eapply f_irred. assumption.  }
  assert (x <= x0 \/ x > x0) by lia.
  destruct H1. apply H0; try assumption. 
  symmetry. apply H0; try assumption; try lia. rewrite poly_add_comm. apply H.
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
  exists (n: Z), (0 < n <= Z.of_nat field_size)%Z /\ monomial (Z.to_nat n) %~ f = (proj1_sig q).
Proof.
  intros. pose proof (primitive_map_surjective). unfold Surjective in H0.
  remember (exist (fun x => proj1_sig x <> zero) q H) as q'.
  specialize (H0 q'). destruct H0. destruct x. exists x. split. assumption.
  rewrite Heqq' in H0. unfold primitive_map in H0. inversion H0.
  destruct q. unfold primitive_map' in H2. exist_inv H2. reflexivity. 
Qed.

Definition find_power_aux (l: list Z) (p: poly) : Z :=
  fold_right (fun z acc => if (poly_eq_dec p ((monomial (Z.to_nat z)) %~ f)) then z else acc) 0%Z l.

Lemma find_power_aux_spec: forall l p,
   (exists z, In z l /\ monomial (Z.to_nat z) %~ f = p) ->
  p = monomial (Z.to_nat (find_power_aux l p)) %~ f /\ In (find_power_aux l p) l.
Proof.
  intros. induction l.
  - simpl. simpl in H. destruct H. destruct H. destruct H.
  - simpl. split. destruct H. destruct H. destruct H. subst. if_tac. reflexivity. contradiction.
    if_tac. assumption. apply IHl. 
    exists x. split; assumption. if_tac. left. reflexivity.
    destruct H. destruct H. destruct H. subst. contradiction. 
    right. apply IHl. exists x. split; assumption.
Qed.

Lemma find_power_aux_notin_spec: forall l p,
  (forall z, In z l -> monomial (Z.to_nat z) %~ f <> p) ->
  find_power_aux l p = 0%Z.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. if_tac. exfalso. apply (H a). left. reflexivity. subst. reflexivity.
    apply IHl. intros. apply H. right. assumption.
Qed.

(* we cannot go from 0 -> field_size - 2, instead we go from 1 -> field_size - 1 because of the way the
  array is populated (0 is filled twice)*)
Definition find_power (p: poly) : Z :=
  find_power_aux (all_bounded_ints_non_dep field_size) p.

Lemma find_power_spec: forall p,
  p <> zero ->
  deg p < deg f ->
  p = monomial (Z.to_nat (find_power p)) %~ f /\ 0 < (find_power p) <= Z.of_nat field_size.
Proof.
  intros. pose proof (find_power_aux_spec (all_bounded_ints_non_dep field_size) p).
  unfold find_power.
  assert (exists z : Z, In z (all_bounded_ints_non_dep field_size) /\ monomial (Z.to_nat z) %~ f = p). {
  pose proof primitive_power_exists.
  remember  ((exist (fun x => deg x < deg f) p H0)) as q. specialize (H2 q).
  assert (proj1_sig q <> zero). intro. rewrite Heqq in H3. simpl in H3. contradiction.
  apply H2 in H3. destruct H3. exists x. destruct H3. split. 
  apply all_bounded_ints_non_dep_spec. apply H3. rewrite Heqq in H4. simpl in H4.
  apply H4. }
  specialize (H1 H2); clear H2.
  destruct H1. split. assumption. 
  apply all_bounded_ints_non_dep_spec in H2. apply H2.
Qed.

(*The stronger and needed condition: find_power gives the unqiue int i between 0 and Z.of_nat field_size such that
  x^i % f = p. This follows the injectivity of [primitive_map]*)
Lemma find_power_iff: forall p z,
  p <> zero ->
  deg p < deg f ->
  (p = monomial (Z.to_nat z) %~ f /\ 0 < z <= Z.of_nat field_size) <-> z = find_power p.
Proof.
  intros. split; intros.
  - pose proof primitive_map_injective. unfold Injective in H2.
    remember (find_power p) as z'.
    pose proof (find_power_spec p H H0). rewrite <- Heqz' in H3. destruct H3.
    remember (exist (fun x => 0 < x <= Z.of_nat field_size) z' H4) as bz'. destruct H1.
    remember (exist (fun x => 0 < x <= Z.of_nat field_size) z H5) as bz.
    specialize (H2 bz bz'). unfold primitive_map in H2.
    assert (bz = bz'). apply H2. exist_eq. unfold primitive_map'.
    exist_eq. rewrite Heqbz. rewrite Heqbz'. simpl. rewrite <- H3. rewrite <- H1. reflexivity.
    rewrite Heqbz in H6. rewrite Heqbz' in H6. inversion H6. reflexivity.
  - subst. apply find_power_spec; assumption.
Qed.

Lemma find_power_zero: find_power zero = 0%Z.
Proof.
  unfold find_power. apply find_power_aux_notin_spec. intros.
  intro. apply (irred_doesnt_divide_monomial f (Z.to_nat z)); try assumption. apply Hpos.
  eapply f_irred. assumption. apply Hnotx. 
  rewrite divides_pmod_iff. unfold divides_pmod. assumption. left. apply f_nonzero. assumption.
Qed. 

Lemma field_size_pos: (0 < field_size)%nat.
Proof.
  unfold field_size. destruct Hpos0. assert (1 < 2 ^ (Z.to_nat (deg f)))%nat; try lia.
  replace 1%nat with (2 ^ 0)%nat at 1 by reflexivity.
  apply Nat.pow_lt_mono_r; lia.
Qed.

(*Something that will be helpful in multiple VST proofs: if i = j (mod (field_size f)), then x^i %f = x^j %f*)
Lemma monomial_powers_eq_mod: forall i j,
  Nat.modulo i field_size = Nat.modulo j field_size ->
 (monomial i) %~ f = (monomial j) %~ f.
Proof.
  intros i j Hmod. pose proof field_size_pos as Hsize.
  rewrite (Nat.div_mod i field_size) by lia.
  rewrite (Nat.div_mod j field_size) by lia.
  destruct Hprim. destruct Hprim0 as [Hdeg [Hirred [Hnth Hnodiv]]].
  rewrite <- !monomial_exp_law.
  assert(forall (n: nat), monomial (field_size * n) %~ f = one). {
    intros n. induction n.
    - rewrite Nat.mul_0_r. rewrite monomial_0. rewrite pmod_refl; auto.
    - replace (field_size * S n)%nat with (field_size + field_size * n)%nat by lia. rewrite <- monomial_exp_law.
      rewrite pmod_mult_distr by auto.
      rewrite IHn. rewrite poly_mult_1_r. rewrite pmod_twice by auto. unfold field_size.
      unfold nth_minus_one in Hnth. rewrite divides_pmod_iff in Hnth. unfold divides_pmod in Hnth.
      rewrite <- pmod_cancel in Hnth by auto. rewrite Hnth. rewrite pmod_refl; auto. left.
      apply f_nonzero. auto. }
  rewrite pmod_mult_distr by auto.
  rewrite (pmod_mult_distr f (monomial (field_size * (j / field_size)))) by auto. rewrite !H.
  rewrite !poly_mult_1_l. rewrite !pmod_twice by auto. rewrite Hmod. reflexivity.
Qed.

(*In particular, we can add the field size*)

Lemma monomial_add_field_size: forall n,
  (monomial n) %~ f = monomial (n + field_size) %~ f.
Proof.
  intros. apply monomial_powers_eq_mod. pose proof field_size_pos.
  rewrite <- Nat.add_mod_idemp_r by lia. rewrite Nat.mod_same by lia. f_equal. lia.
Qed.

(*One other useful lemma*)
Lemma poly_to_qpoly_unfold: forall (f: poly) (Hpos: PosPoly f) (a: qpoly f),
  poly_to_qpoly f (proj1_sig a) = a.
Proof.
  intros. unfold poly_to_qpoly.
  destruct a. simpl. exist_eq. apply pmod_refl; auto.
Qed.

End Primitive.
