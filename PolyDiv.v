Require Import VST.floyd.functional_base.
Require Import GF2.
Require Import Poly.
(** * A verified, executable version of Euclidean division on polynomials over GF2 *)

(** Monomials *)

(*We provide a special shorthand for the monomial x^n, which will be useful in division*)

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

(** Euclidean Division **)

(*note: may want to make more efficient by shifting instead of add a monomial*)
Program Fixpoint poly_div_aux (a b q r : poly) (Hb: wf_poly b) (Hr: wf_poly r) {measure (Z.to_nat (deg r + 1))} : 
  {x: poly * poly | (0<= deg b) ->  wf_poly q ->
   (deg (snd x) < deg b /\ wf_poly (fst x) /\ wf_poly (snd x) /\
   (a = poly_add (poly_mult b q) r -> a = poly_add (poly_mult b (fst x)) (snd x)))}
  :=
  match b with
  | nil => (nil, nil) (*cannot divide by zero *)
  | (x :: t) =>
  match (zlt (deg r) (deg b)) with
  | left H => (q,r)
  | right H' => let pow := monomial (Z.to_nat (deg r - deg b)) in
                let q' := poly_add q pow in
                let r' := poly_add r (poly_mult b pow) in
                poly_div_aux a b q' r' Hb (wf_poly_add _ _)
  end
end.
(*begin hide*)
Next Obligation.
lia.
Defined.
Next Obligation.
destruct r.
(*if r = 0 - contradiction*)
simpl in H'. assert (Zlength (x :: t) > 0) by list_solve. lia.
(*now handle case when r' = 0*)
assert (forall l, deg l = -1 \/ 0 <= deg l). { intros. unfold deg; destruct l. left. reflexivity.
right. list_solve. }
remember (poly_add (b :: r) (poly_mult (x :: t) (monomial (Z.to_nat (deg (b :: r) - deg (x :: t)))))) as r'.
specialize (H r'). destruct H.
- destruct r'. simpl. list_solve. unfold deg in H. list_solve. 
- (*now we can handle the usual case, and use the fact that polys of same degree result in a smaller poly when
    multiplied together *)
assert (deg (b :: r) = deg  (poly_mult (x :: t) (monomial (Z.to_nat (deg (b :: r) - deg (x :: t)))))). {
rewrite poly_mult_deg. rewrite monomial_deg. lia. assumption. apply wf_monomial. simpl. 
solve_neq. apply monomial_not_0. }
assert ((deg (poly_add (b :: r) (poly_mult (x :: t) (monomial (Z.to_nat (deg (b :: r) - deg (x :: t)))))))
  < (deg (b :: r))). {
apply (poly_add_degree_same (b :: r) (poly_mult (x :: t) (monomial (Z.to_nat (deg (b :: r) - deg (x :: t)))))).
- assumption.
- apply wf_poly_mult. assumption. apply wf_monomial.
- assumption.
- simpl. list_solve. } 
subst. list_solve.
Defined.
Next Obligation.
destruct ((poly_div_aux a (x :: t) (poly_add q (monomial (Z.to_nat (deg r - deg (x :: t)))))
           (poly_add r (poly_mult (x :: t) (monomial (Z.to_nat (deg r - deg (x :: t)))))) Hb
           (wf_poly_add r (poly_mult (x :: t) (monomial (Z.to_nat (deg r - deg (x :: t))))))
           (poly_div_aux_func_obligation_3 (x :: t) r Hb Hr poly_div_aux x t eq_refl H' Heq_anonymous))). simpl.
(*in a more workable form - now to prove correctness - ie, that invariant is preserved*)
destruct x0; simpl in *. 
assert (wf_poly (poly_add q (monomial (Z.to_nat (deg r - (Zlength (x :: t) - 1)))))).
apply wf_poly_add. specialize (a0 H H1). destruct a0. destruct H3. destruct H4. split.
assumption. split. assumption. split. assumption. intros. apply H5. rewrite H6.
remember (x :: t) as b.
remember  (monomial (Z.to_nat (deg r - (Zlength b - 1)))) as pow.
rewrite poly_mult_distr_l.
symmetry. rewrite poly_add_assoc. f_equal. rewrite poly_add_comm.
rewrite poly_add_assoc. rewrite poly_add_inv. rewrite poly_add_comm. apply poly_add_id. apply Hr.
assumption. assumption. subst. apply wf_monomial.
Defined.
(*end hide*)

Definition poly_div a b (Ha: wf_poly a) (Hb : wf_poly b) : poly * poly :=
  proj1_sig (poly_div_aux a b nil a Hb Ha).

(*begin hide*)

Definition testa := (1 :: 1 :: 0 :: 1 :: nil).
Lemma wf_a : wf_poly testa.
Proof.
unfold wf_poly. unfold testa. simpl. intros. reflexivity.
Qed.

Definition testb := (1 :: 1 :: nil).
Lemma wf_b : wf_poly testb.
Proof.
  unfold wf_poly. unfold testb. simpl. reflexivity.
Qed.

Eval compute in (poly_add(poly_mult (0 :: 1 :: 1 :: nil) (1 :: 1 :: nil)) (1 :: nil)).
Eval compute in ( poly_div testa testb wf_a wf_b  ).
(*it works!*)
(*end hide*)
Section DivFacts.

Lemma remainder_unique: forall a b q1 r1 q2 r2,
  wf_poly a ->
  wf_poly b ->
  wf_poly q1 ->
  wf_poly r1 ->
  wf_poly q2 ->
  wf_poly r2 ->
  b <> nil ->
  deg r1 < deg b ->
  deg r2 < deg b ->
  a = poly_add (poly_mult q1 b) r1 ->
  a = poly_add (poly_mult q2 b) r2 ->
  q1 = q2 /\ r1 = r2.
Proof.
  intros. subst. rewrite poly_add_comm in H9. rewrite poly_add_cancel_1 in H9. symmetry in H9.
  rewrite <- poly_add_assoc in H9.
  rewrite poly_add_cancel_1 in H9.
  assert (deg (poly_add r2 r1) = deg (poly_add (poly_mult q1 b) (poly_mult q2 b))). rewrite H9; reflexivity.
  pose proof (poly_add_degree_max r2 r1).
  rewrite <- poly_mult_distr_r in H8.
  destruct (poly_add q1 q2) eqn : P. all: try assumption. all: try (apply wf_poly_add).
  - rewrite poly_add_inv_iff in P; try assumption. subst. 
    rewrite poly_mult_0_l in H8. simpl in H8.
    destruct (poly_add r2 r1) eqn : R. rewrite poly_add_inv_iff in R; try assumption. auto.
    simpl in H8. list_solve.
  - rewrite <- P in H8. rewrite poly_mult_deg in H8.
    assert (deg (poly_add q1 q2) < 0) by lia.
    assert (poly_add q1 q2 = nil). destruct (poly_add q1 q2). reflexivity. simpl in H11.
    list_solve. rewrite poly_add_inv_iff in H12. subst.
    rewrite poly_add_inv in H9. symmetry in H9. rewrite poly_add_inv_iff in H9. subst. auto.
    all: try assumption. all: try(apply wf_poly_add). intro. rewrite P in H11. inversion H11.
Qed.

Lemma poly_div_wf: forall a b q r (Ha: wf_poly a) (Hb: wf_poly b),
  b <> nil ->
  poly_div a b Ha Hb = (q,r) ->
  wf_poly q /\ wf_poly r.
Proof.
  intros. unfold poly_div in H0. destruct  (poly_div_aux a b nil a Hb Ha).
  simpl in H0. destruct x; subst. simpl in a0. inversion H0; subst. split. apply a0.
  unfold deg. destruct b. contradiction. list_solve. apply wf_poly_nil.
  apply a0. destruct b; simpl. contradiction. list_solve. apply wf_poly_nil.
Qed. 
  
 
Lemma poly_div_correct: forall a b q r (Ha: wf_poly a) (Hb : wf_poly b),
  wf_poly q ->
  wf_poly r ->
  b <> nil ->
  deg r < deg b ->
  poly_div a b Ha Hb = (q,r) <-> a = poly_add (poly_mult q b) r.
Proof.
  intros. split; intros.
  - unfold poly_div in H3. destruct (poly_div_aux a b nil a Hb Ha). simpl in H3.
    destruct x; inversion H3; subst; simpl in *. clear H3.
    assert (deg r < deg b /\ wf_poly q /\ wf_poly r /\ (a = poly_add nil a -> a = poly_add (poly_mult b q) r)).
    apply a0. destruct b; simpl. contradiction. list_solve. apply wf_poly_nil. clear a0.
    rewrite poly_mult_comm;try apply H3. symmetry. apply poly_add_id. all: assumption.
  - unfold poly_div. destruct (poly_div_aux a b nil a Hb Ha). simpl. destruct x; simpl in *.
    assert (deg p0 < deg b /\
     wf_poly p /\ wf_poly p0 /\ (a = poly_add nil a -> a = poly_add (poly_mult b p) p0)).
    apply a0. destruct b; simpl. contradiction. list_solve. apply wf_poly_nil. clear a0.
    destruct H4. destruct H5. destruct H6.
    assert (p = q /\ p0 = r). eapply remainder_unique. apply Ha. apply Hb. 
    all: try assumption. rewrite poly_mult_comm; try assumption. apply H7.
    symmetry. apply poly_add_id. assumption. destruct H8; subst. reflexivity.
Qed.  
    
End DivFacts.