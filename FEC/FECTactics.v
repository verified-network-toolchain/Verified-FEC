Require Import VST.floyd.proofauto.

Require Import Common.
Require Import CommonVST.
(*Require Import Poly.
Require Import VandermondeList.*)
Require Import List2D.
Require Import ByteFacts.
(*
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

(*get fact that deg t < deg mod_poly in the context*)
Ltac pose_poly_deg t H :=
  lazymatch t with
    | f_to_poly ?p => unfold f_to_poly in *; pose proof (@proj2_sig _ (fun y => deg y < deg mod_poly) p) as H; simpl in H
    | proj1_sig ?p => pose proof (@proj2_sig _ (fun y => deg y < deg mod_poly) p) as H; simpl in H
    | ?p %~ mod_poly => pose proof (pmod_lt_deg mod_poly p) as H
    | poly_of_int ?n => let N := fresh in assert (N: 0 <= n < fec_n) by rep_lia;
        pose proof (polys_deg_bounded _ N) as H; clear N  
  end.

(*Put info about [find_power mod_poly p] in the context, solves obligations automatically. H1 and H2 are the
  names for the new info (find_power def and bounds)*)
Ltac pose_power p H1 H2 :=
  let H := fresh in 
  let N1 := fresh in 
  let N2 := fresh in
  assert (N1 : p <> zero) by (try assumption; solve_poly_zero);
  pose_poly_deg p N2;
  let N := fresh in
  pose proof (@find_power_spec mod_poly _ mod_poly_PrimPoly p N1 N2) as N;
  destruct N as [H1  H2]; rewrite field_size_fec_n in H2.

(*get fact that 0 <= t < fec_n*)
Ltac pose_poly_bounds t :=
  lazymatch t with
    | poly_to_int ?p => let N := fresh in pose_poly_deg p N; let N1 := fresh in
        pose proof (modulus_poly_bound p N) as N1; simpl in N1; unfold f_to_poly in *
    | find_power mod_poly ?p => let N1 := fresh in let N2 := fresh in
       pose_power p N1 N2
  end.
*)
(*Solves goals with Int.unsigned (Int.repr _) and Zbits.Zzero_ext when the value is an integer, not a qpoly (ie,
  rep_lia can prove that z is small enough)*)
Ltac simpl_repr_byte :=
  repeat match goal with
  |  [ |- context [ Byte.unsigned (Byte.repr ?b) ]] => rewrite Byte.unsigned_repr by rep_lia
  |  [ |- context [ Int.unsigned (Int.repr ?x)]] => rewrite Int.unsigned_repr by rep_lia
  |  [ |- context [ Zbits.Zzero_ext 8 ?x]] => rewrite zbits_small by rep_lia
  |  [ |- context [ Int.zero_ext 8 ?x ]] => unfold Int.zero_ext
  end; try rep_lia; auto.

(*


Ltac solve_poly_bounds :=
  lazymatch goal with
  | [ |- deg ?p < deg mod_poly ] => let N := fresh in pose_poly_deg p N; apply N
  | [ H: deg ?p < deg mod_poly |- 0 <= poly_to_int ?p < ?n] => pose proof (modulus_poly_bound p H); rep_lia
  | [ |- ?a <= ?t <= ?b ] => simpl; try rep_lia; pose_poly_bounds t; simpl; solve_repr_int; rep_lia
  | [ |- ?a <= ?t < ?b ] => simpl; try rep_lia; pose_poly_bounds t; simpl; solve_repr_int; rep_lia
  | [ |- ?t < ?b ] => simpl; try rep_lia; pose_poly_bounds t; simpl; solve_repr_int; rep_lia
  | [ |- ?t <= ?b ] => simpl; try rep_lia; pose_poly_bounds t; simpl; solve_repr_int; rep_lia
  end.

(*Simplify expressions with [Int.unsigned (Int.repr (poly_to_int ?p))] and [Int.zero_ext 8 (poly_to_int ?p)],
  where p is a poly that is smaller than mod_poly*)
Ltac simpl_repr :=
  repeat lazymatch goal with
   |  [ |- is_int ?i ?u ?x] => progress simpl
   |  [ |- context [ Int.unsigned (Int.repr (poly_to_int ?x))]] =>
        let N := fresh in
        assert (N: Int.unsigned (Int.repr (poly_to_int x)) = poly_to_int x) by (subst;
        rewrite unsigned_repr; [ reflexivity | solve_poly_bounds]); rewrite -> N; clear N
   |  [ |- context [ Int.unsigned (Int.repr ?x)]] => (*want to handle [poly_to_int] first*)
        let N := fresh in
        assert (N: Int.unsigned (Int.repr x) = x) by (subst;
        rewrite unsigned_repr; [ reflexivity | solve_poly_bounds]); rewrite -> N; clear N
  | [ |- context [ Zbits.Zzero_ext 8 ?x]] =>
       let N := fresh in
      assert (N: Zbits.Zzero_ext 8 x = x) by (subst; rewrite zbits_small; [reflexivity | solve_poly_bounds]);
      rewrite -> N; clear N
  |  [ |- context [ Int.zero_ext 8 ?x ]] => unfold Int.zero_ext
  end; auto; try rep_lia; try solve_poly_bounds.

*)
(*Simplify an integer expression with zeroes*)
Ltac simplify_zeroes  :=
  repeat lazymatch goal with
    | [ |- context [ 0%Z + ?z ] ] => rewrite Z.add_0_l
    | [ |- context [ ?z + 0%Z ] ] => rewrite Z.add_0_r
    | [ |- context [ 0%Z * ?z ] ] => rewrite Z.mul_0_l
    | [ |- context [ ?z * 0%Z ] ] => rewrite Z.mul_0_r
  end.
(*
(*Similar to [pose_power], but for [poly_inv mod_poly p/*)
Ltac pose_inv p H1 H2 :=
  let P := fresh in
  assert (P : p %~ mod_poly <> zero) by (rewrite (@pmod_refl _ mod_poly_PosPoly); [ solve_poly_zero | solve_poly_bounds ]);
  let H := fresh in
  assert (H: ((p *~ poly_inv mod_poly p) %~ mod_poly = one) /\ deg (poly_inv mod_poly p) < deg mod_poly) by
    (apply (poly_inv_spec _ (@f_irred _ _ mod_poly_PrimPoly) _ P));
  destruct H as [H1 H2].

(*replace [poly_of_int 0%Z] with [zero] everywhere*)
Ltac rewrite_zero:=
  let N := fresh in
  assert (N: poly_of_int 0%Z = zero) by (rewrite poly_of_int_zero; lia); rewrite N in *; clear N.

*)
(*To make things nicer*)
Definition B := ByteField.byte_fieldType.

(*Solve goals of the form [wf_matrix mx m n]*)
Ltac solve_wf :=
  repeat(match goal with
  | [H: _ |- wf_lmatrix (F:=B) (scalar_mul_row_partial (F:=B)  _ _ _ _ _ _) _ _] => apply scalar_mul_row_partial_wf
  | [H: _ |- wf_lmatrix (F:=B) (scalar_mul_row (F:=B) _ _ _ _ _) _ _ ] => apply scalar_mul_row_partial_wf
  | [H: _ |- wf_lmatrix (F:=B) (all_cols_one_partial (F:=B) _ _ _ _ _) _ _ ] => apply all_cols_one_partial_wf
  | [H: _ |- wf_lmatrix (F:=B) (add_multiple_partial (F:=B) _ _ _ _ _ _ _) _ _] => apply add_multiple_partial_wf
  | [H: _ |- wf_lmatrix (F:=B) (add_multiple (F:=B) _ _ _ _ _ _) _ _] => apply add_multiple_partial_wf
  | [H: _ |- wf_lmatrix (F:=B) (sub_all_rows_partial (F:=B) _ _ _ _ _) _ _] => apply sub_all_rows_partial_wf
  | [H: _ |- wf_lmatrix (F:=B) (gauss_all_steps_rows_partial (F:=B) _ _ _ _) _ _] => apply gauss_all_steps_rows_partial_wf
  | [H: _ |- wf_lmatrix (F:=B) (all_lc_one_rows_partial (F:=B) _ _ _ _) _ _] => apply all_lc_one_rows_partial_wf
  (*| [H: _ |- wf_lmatrix (F:=B) (weight_mx_list _ _ ) _ _] => apply weight_matrix_wf*)
  end; try lia); assumption.

(*Maybe move elsewhere*)
Lemma byte_int_repr: forall z: Z,
  0 <= z <= Byte.max_unsigned ->
  Vubyte (Byte.repr z) = Vint (Int.repr z).
Proof.
  intros z Hz. unfold Vubyte. simpl_repr_byte.
Qed.

(*Solve goals relating to [offset_val], adding/subtracting pointers, showing offsets are equal, and
  relating offsets to array fields*)
Ltac solve_offset :=
  repeat (simpl; simpl_repr_byte; match goal with
  | [ |- context [ Vubyte (Byte.repr ?z) ]] => rewrite byte_int_repr by rep_lia
  | [ |- context [ sem_sub_pi ?a ?b ?c ?d ]] => rewrite sem_sub_pi_offset; auto; try rep_lia
  | [ |- context [ sem_add_ptr_int ?a ?b ?c ?d ]] => rewrite sem_add_pi_ptr_special; auto; try rep_lia
  | [ |- context [ offset_val ?n (offset_val ?m ?p) ]] => rewrite offset_offset_val
  | [ |- offset_val ?n ?p = offset_val ?m ?p] => f_equal; rep_lia
  (*deal with 1D array subscripts*)
  | [ |- context [ field_address (tarray ?t ?sz) [ArraySubsc ?n] ?p ]] => rewrite arr_field_address; 
        auto; try rep_lia; try nia
  | [ |- context [ field_address0 (tarray ?t ?sz) [ArraySubsc ?n] ?p ]] => rewrite arr_field_address0; 
        auto; try rep_lia; try nia 
  (*deal with 2D array subscripts*)
  | [ H: field_compatible (Tarray (tarray ?t ?n1) ?m1 noattr) [] ?p |- context [
          field_address (tarray (tarray ?t ?n2) ?m2) [ArraySubsc ?a; ArraySubsc ?b] ?p ]] =>
     replace n1 with n2 in H by rep_lia;
     replace m1 with m2 in H by rep_lia;
     let N := fresh in
     assert (N : field_compatible (tarray (tarray t n2) m2) [ArraySubsc a; ArraySubsc b] p) by 
      (unfold field_compatible; simpl;
       repeat split; try apply H; auto; rep_lia);
     rewrite (field_compatible_field_address _ _ _ N)
  | [ H: field_compatible (Tarray (tarray ?t ?n1) ?m1 noattr) [] ?p |- context [
          field_address0 (tarray (tarray ?t ?n2) ?m2) [ArraySubsc ?a; ArraySubsc ?b] ?p ]] =>
     replace n1 with n2 in H by rep_lia;
     replace m1 with m2 in H by rep_lia;
     let N := fresh in
     assert (N : field_compatible (tarray (tarray t n2) m2) [ArraySubsc a; ArraySubsc b] p) by 
      (unfold field_compatible; simpl;
       repeat split; try apply H; auto; rep_lia);
     rewrite (field_compatible0_field_address0 _ _ _ (field_compatible_field_compatible0 _ _ _ N))
  | [ |- Int.min_signed <= ?k * ?n <= Int.max_signed ] => 
      assert (0 <= k * n <= Byte.max_unsigned * Byte.max_unsigned) by nia; rep_lia
  end).

(*Determines the integer corresponding to a nested series of pointer arithmetic operations, used in [pointer_to_offset]*)
Ltac build_offset op v1 v2 := 

  let rec build_offset' op' v1' v2' :=
    let one_side va :=
      lazymatch va with
      | Vint (Int.repr ?n) => constr:(n)
      | Vubyte (Byte.repr ?b) => constr:(b)
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

(*To fold and unfold abbreviations for LOCALx and SEPx*)
Ltac rewrite_eqs :=
  repeat match goal with
    | [H : ?x = ?y |- context [ ?x ]] => rewrite H
    end.


(*We have lots of hypothesis of the form: Forall (fun x => Zlength x = c) l and want to prove something
  about Zlength (Znth i l) where i is in bounds. This tactic does this.*)
Ltac inner_length :=
  lazymatch goal with
    | [ H: Forall (fun x => Zlength x = ?c) ?l |- context [ Zlength (Znth ?i ?l)]] =>
      rewrite Forall_Znth in H; rewrite H by rep_lia; try rep_lia
    | [ H: Forall (fun x => Zlength x <= ?c) ?l |- context [ Zlength (Znth ?i ?l)]] =>
      let N := fresh in
      assert (N: 0 <= i < Zlength l) by lia;
      rewrite Forall_Znth in H; specialize (H _ N); rep_lia
    | [ H: Forall2D (fun x => ?a <= x <= ?c) ?l |- context [ (Znth ?j (Znth ?i ?l))]] =>
      let N := fresh in
      let N' := fresh in
      assert (N: 0 <= i < Zlength l) by lia;
      assert (N': 0 <= j < Zlength (Znth i l)) by lia;
      rewrite Forall2D_Znth in H; specialize (H _ _ N N'); simpl_repr_byte; clear N; clear N'
   end.
