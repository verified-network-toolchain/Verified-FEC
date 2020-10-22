Require Import VST.floyd.functional_base.
Require Import GF2.
Require Import PolyDefs.
(** * A verified, executable version of Euclidean division on polynomials over GF2 *)

(** Note: we define the function in this file as operating on pure lists, then in Poly.v, lift this
  to polynomials. We do it this way because [poly_div_aux] did not compute when given dependent types as inputs.
  We have to do the computations on lists, then wrap the outputs in the poly type *)
Import P.

(** Euclidean Division **)

Program Fixpoint poly_div_aux (a b q r : poly) (Hb: wf_poly b) (Hr: wf_poly r) (Hq: wf_poly q) {measure (Z.to_nat (deg r + 1))} : 
  {x: { l: poly | wf_poly l} * {l: poly | wf_poly l} |  (b <> nil ->
   (deg (snd x) < deg b /\ 
   (a = poly_add (poly_mult b q) r -> a = poly_add (poly_mult b (fst x)) (snd x))))}
  :=
  match b with
  | nil => (nil, nil) (*cannot divide by zero *)
  | (x :: t) =>
  match (zlt (deg r) (deg b)) with
  | left H => (q,r)
  | right H' => let pow := monomial (Z.to_nat (deg r - deg b)) in
                let q' := poly_add q pow in
                let r' := poly_add r (poly_mult b pow) in
                poly_div_aux a b q' r' Hb (wf_poly_add _ _) _
  end
end.
Next Obligation.
apply wf_poly_add.
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
destruct  (poly_div_aux a (x :: t) (poly_add q (monomial (Z.to_nat (deg r - deg (x :: t)))))
                  (poly_add r (poly_mult (x :: t) (monomial (Z.to_nat (deg r - deg (x :: t)))))) Hb
                  (wf_poly_add r (poly_mult (x :: t) (monomial (Z.to_nat (deg r - deg (x :: t))))))
                  (poly_div_aux_func_obligation_7 (x :: t) q r Hb x t eq_refl H' Heq_anonymous)
                  (poly_div_aux_func_obligation_8 (x :: t) r Hb Hr poly_div_aux x t eq_refl H'
                     Heq_anonymous)). simpl.
(*in a more workable form - now to prove correctness - ie, that invariant is preserved*)
destruct x0; simpl in *. 
assert (wf_poly (poly_add q (monomial (Z.to_nat (deg r - (Zlength (x :: t) - 1)))))).
apply wf_poly_add. specialize (a0 H). destruct a0.
split.
assumption. intros. apply H2. rewrite H3.
remember (x :: t) as b.
remember  (monomial (Z.to_nat (deg r - (Zlength b - 1)))) as pow.
rewrite poly_mult_distr_l.
symmetry. rewrite poly_add_assoc. f_equal. rewrite poly_add_comm.
rewrite poly_add_assoc. rewrite poly_add_inv. rewrite poly_add_comm. apply poly_add_id. apply Hr.
assumption. assumption. subst. apply wf_monomial.
Defined.

