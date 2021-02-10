Require Import VST.floyd.proofauto.

Require Import Common.
Require Import CommonVST.
Require Import Poly.

(*Solves goals of form ?p <> zero*)
Ltac solve_poly_zero :=
  let N := fresh in intro N;
  repeat match goal with
  | [ H: x = zero |- _ ] => inversion H
  | [ H: poly_of_int ?x = zero |- _ ] => rewrite poly_of_int_zero in H; rep_lia
  | [ H: mod_poly = zero |- _ ] => pose proof (@f_nonzero _ mod_poly_PosPoly); contradiction
  | [ H: monomial ?n = zero |- _ ] => pose proof (monomial_nonzero n); contradiction
  | [ H: monomial ?n %~ mod_poly = zero |- _ ] => pose proof (monomial_mod_nonzero n); contradiction
  | [ H: ?p *~ ?q = zero |- _ ] => rewrite poly_mult_zero_iff in H; destruct H
  end.

(*put information into the context about poly bounds from the goal (of the form 0 <= poly_to_int ?p < fec_n),
  or degree info for [poly_to_int[*)
Ltac pose_poly_bounds :=
  (*inner/more general bounds*)
  try (lazymatch goal with
   | [ |- context [ poly_to_int (proj1_sig ?p) ]] => 
      pose proof (modulus_poly_bound (proj1_sig p) (@ssrfun.svalP _ (fun y => deg y < deg mod_poly) p))
  | [ |- context [ poly_to_int (?p %~ mod_poly) ]] => 
      pose proof (modulus_poly_bound (p %~ mod_poly) (pmod_lt_deg mod_poly p))
  | [ |- context [ poly_of_int ?n ]] => 
      let N := fresh in
      assert (N: 0 <= n < fec_n) by rep_lia;
      pose proof (polys_deg_bounded n N);
      try(assert (poly_of_int n <> zero) by solve_poly_zero)
  end);
  (*more specific functions built from the smaller pieces*)
  repeat(lazymatch goal with 
  | [Hnz: ?p <> zero, Hdeg: deg ?p < deg mod_poly |- context [find_power mod_poly ?p]] =>
      tryif (assert (0 < find_power mod_poly p <= fec_n - 1 ) by assumption) then fail else
      let Hfp := fresh in
      let Hfpbound := fresh in
      pose proof (@find_power_spec mod_poly _ mod_poly_PrimPoly p Hnz Hdeg) as N;
      destruct N as [Hfp Hfpbound]; rewrite field_size_fec_n in Hfpbound 
  end).

(*Solves goals with Int.unsigned (Int.repr _) and Zbits.Zzero_ext when the value is an integer, not a qpoly (ie,
  rep_lia can prove that z is small enough)*)
Ltac solve_repr_int :=
  repeat match goal with
  |  [ |- context [ Int.zero_ext 8 ?x ]] => unfold Int.zero_ext
  |  [ |- context [ Int.unsigned (Int.repr ?x)]] => rewrite unsigned_repr by rep_lia
  |  [ |- context [ Zbits.Zzero_ext 8 ?x]] => rewrite zbits_small by rep_lia
  end; try rep_lia; auto.

(*Solve goals that deal with poly bounds*)
Ltac solve_poly_bounds :=
  match goal with
  | [ |- deg (poly_of_int ?n) < deg mod_poly] => apply polys_deg_bounded; rep_lia
  | [ H: deg ?p < deg mod_poly |- 0 <= poly_to_int ?p < ?n] => pose proof (modulus_poly_bound p H); rep_lia
  | [ |- _ ] => simpl; try rep_lia; pose_poly_bounds; solve_repr_int; rep_lia
  end.

(*Simplify expressions with [Int.unsigned (Int.repr (poly_to_int ?p))] and [Int.zero_ext 8 (poly_to_int ?p)],
  where p is a poly that is smaller than mod_poly*)
Ltac simpl_repr :=
  repeat match goal with
  | [ |- context [ Zbits.Zzero_ext 8 ?x]] =>
       let N := fresh in
      assert (N: Zbits.Zzero_ext 8 x = x) by (subst; rewrite zbits_small; [reflexivity | solve_poly_bounds]);
      rewrite -> N; clear N
  |  [ |- context [ Int.zero_ext 8 ?x ]] => unfold Int.zero_ext
  |  [ |-  context [ Int.unsigned (Int.repr ?x)]] =>
        let N := fresh in
        assert (N: Int.unsigned (Int.repr x) = x) by (subst;
        rewrite unsigned_repr; [ reflexivity | solve_poly_bounds]); rewrite -> N; clear N
  end; auto; try rep_lia; try solve_poly_bounds.

(*Simplify an integer expression with zeroes*)
Ltac simplify_zeroes  :=
  repeat lazymatch goal with
    | [ |- context [ 0%Z + ?z ] ] => rewrite Z.add_0_l
    | [ |- context [ ?z + 0%Z ] ] => rewrite Z.add_0_r
    | [ |- context [ 0%Z * ?z ] ] => rewrite Z.mul_0_l
    | [ |- context [ ?z * 0%Z ] ] => rewrite Z.mul_0_r
  end.

(*Put info about [find_power mod_poly p] in the context, solves obligations automatically. H1 and H2 are the
  names for the new info (find_power def and bounds)*)
Ltac pose_power p H1 H2 :=
  let H := fresh in
  assert (H: p = monomial (Z.to_nat (find_power mod_poly p)) %~ mod_poly /\ 0 < find_power mod_poly p <= fec_n - 1) by
  (rewrite <- field_size_fec_n; pose_poly_bounds; apply (@find_power_spec mod_poly _ mod_poly_PrimPoly p); auto);
  destruct H as [H1 H2].

(*Similar, but for [poly_inv mod_poly p/*)
Ltac pose_inv p H1 H2 :=
  let P := fresh in
  assert (P : p %~ mod_poly <> zero) by (rewrite (@pmod_refl _ mod_poly_PosPoly); [ solve_poly_zero | solve_poly_bounds ]);
  let H := fresh in
  assert (H: ((p *~ poly_inv mod_poly p) %~ mod_poly = one) /\ deg (poly_inv mod_poly p) < deg mod_poly) by
    (pose_poly_bounds; apply (poly_inv_spec _ (@f_irred _ _ mod_poly_PrimPoly) _ P));
  destruct H as [H1 H2].

(*replace [poly_of_int 0%Z] with [zero] everywhere*)
Ltac rewrite_zero:=
  let N := fresh in
  assert (N: poly_of_int 0%Z = zero) by (rewrite poly_of_int_zero; lia); rewrite N in *; clear N.

(*Solve goals of the form [wf_matrix mx m n]*)
Ltac solve_wf :=
  repeat(match goal with
  | [H: _ |- wf_matrix (F:=F) (scalar_mul_row_partial (F:=F) _ _ _ _) _ _] => apply scalar_mul_row_partial_wf
  | [H: _ |- wf_matrix (F:=F) (scalar_mul_row (F:=F) _ _ _) _ _ ] => apply scalar_mul_row_partial_wf
  | [H: _ |- wf_matrix (F:=F) (all_cols_one_partial (F:=F) _ _ _) _ _ ] => apply all_cols_one_partial_wf
  | [H: _ |- wf_matrix (F:=F) (add_multiple_partial (F:=F) _ _ _ _ _) _ _] => apply add_multiple_partial_wf
  | [H: _ |- wf_matrix (F:=F) (add_multiple (F:=F) _ _ _ _ ) _ _] => apply add_multiple_partial_wf
  | [H: _ |- wf_matrix (F:=F) (sub_all_rows_partial (F:=F) _ _ _ ) _ _] => apply sub_all_rows_partial_wf
  | [H: _ |- wf_matrix (F:=F) (gauss_all_steps_rows_partial (F:=F) _ _ _ ) _ _] => apply gauss_all_steps_rows_partial_wf
  | [H: _ |- wf_matrix (F:=F) (all_lc_one_rows_partial (F:=F) _ _ ) _ _] => apply all_lc_one_rows_partial_wf
  | [H: _ |- wf_matrix (F:=F) (all_lc_one_rows_partial (F:=F) _ _ ) _ _] => apply all_lc_one_rows_partial_wf
  end; try lia); assumption.


(*Solve goals relating to [offset_val], adding/subtracting pointers, showing offsets are equal, and
  relating offsets to array fields*)
Ltac solve_offset :=
  repeat (simpl; lazymatch goal with
  | [ |- context [ sem_sub_pi ?a ?b ?c ?d ]] => rewrite sem_sub_pi_offset; auto; try rep_lia
  | [ |- context [ sem_add_ptr_int ?a ?b ?c ?d ]] => rewrite sem_add_pi_ptr_special; auto; try rep_lia
  | [ |- context [ offset_val ?n (offset_val ?m ?p) ]] => rewrite offset_offset_val
  | [ |- offset_val ?n ?p = offset_val ?m ?p] => f_equal; rep_lia
  | [ |- context [ field_address (tarray ?t ?sz) [ArraySubsc ?n] ?p ]] => rewrite arr_field_address; 
        auto; try rep_lia; try nia
  | [ |- context [ field_address0 (tarray ?t ?sz) [ArraySubsc ?n] ?p ]] => rewrite arr_field_address0; 
        auto; try rep_lia; try nia
  | [ H : ?n <= Byte.max_unsigned |- Int.min_signed <= ?k * ?n <= Int.max_signed ] => 
      assert (0 <= k * n <= Byte.max_unsigned * Byte.max_unsigned) by nia; rep_lia
  end).

(*Determines the integer corresponding to a nested series of pointer arithmetic operations, used in [pointer_to_offset]*)
Ltac build_offset op v1 v2 := 

  let rec build_offset' op' v1' v2' :=
    let one_side va :=
      lazymatch va with
      | Vint (Int.repr ?n) => constr:(n)
      | offset_val ?n ?p => constr:(n)
      | eval_binop ?op1 ?t1 ?t2 ?v3 ?v4 => build_offset' op1 v3 v4
      | ?s => constr:(0%Z)
      end
    in 
    let l := one_side v1' in
    let r := one_side v2' in
       lazymatch op' with
        | Oadd => constr:((l + r)%Z)
        | Osub => constr:((l - r)%Z)
        | Omul => constr:((l * r)%Z)
        | _ => idtac "ERROR: UNKNOWN OPERATION" op 
       end
    in

  build_offset' op v1 v2.

(*replace a big expression with (force_val (sem_binary_operation' ...)) with the corresponding
  offset val expression (only allows addition, multiplication, and subtraction)*)
Ltac pointer_to_offset p :=
  match goal with
  | [ |- context [ force_val (sem_binary_operation' ?opp ?t1 ?t2 ?a1 ?a2)]] =>
      let n := build_offset opp a1 a2 in
      let N := fresh in
      assert_PROP (force_val (sem_binary_operation' opp t1 t2 a1 a2) = offset_val n p) as N
      by (entailer!; solve_offset); rewrite N; clear N; simplify_zeroes
  | [ |- context [ force_val (sem_add_ptr_int ?t ?s ?a1 ?a2)]] =>
      let n := build_offset Oadd a1 a2 in
      let N := fresh in
      assert_PROP (force_val (sem_add_ptr_int t s a1 a2) = offset_val n p) as N
      by (entailer!; solve_offset); rewrite N; clear N; simplify_zeroes
  end.

(*Does the same, but replaces the offset with the given expression e, as long as [rep_lia] can prove
  they are equal*)
Ltac pointer_to_offset_with p e :=
    match goal with
  | [ |- context [ force_val (sem_binary_operation' ?opp ?t1 ?t2 ?a1 ?a2)]] =>
      let n := build_offset opp a1 a2 in
      let Eq := fresh in
      let N := fresh in
      assert (Eq: n = e) by rep_lia;
      assert_PROP (force_val (sem_binary_operation' opp t1 t2 a1 a2) = offset_val n p) as N
      by (entailer!; solve_offset); rewrite N; clear N; rewrite Eq; clear Eq
  | [ |- context [ force_val (sem_add_ptr_int ?t ?s ?a1 ?a2)]] =>
    let n := build_offset Oadd a1 a2 in
    let Eq := fresh in
    let N := fresh in
    assert (Eq: n = e) by rep_lia;
    assert_PROP (force_val (sem_add_ptr_int t s a1 a2) = offset_val n p) as N
    by (entailer!; solve_offset); rewrite N; clear N; rewrite Eq; clear Eq
  end.
