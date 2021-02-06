Require Import VST.floyd.proofauto.

Require Import Common.
Require Import CommonVST.
Require Import Poly.

(*For any polynomial of degree < deg (mod_poly), poly_of_int p is within the bounds needed for all the VST goals.
  This tactic solves many of these goals for qpolys and polys taken modulo mod_poly*)
Ltac solve_qpoly_bounds :=
  let pose_bounds p :=
    pose proof (modulus_poly_bound (proj1_sig p) (@ssrfun.svalP _ (fun y => deg y < deg mod_poly) p));
    pose proof fec_n_eq; rep_lia in
  let pose_mod_bounds p :=
    pose proof (modulus_poly_bound (p %~ mod_poly) (pmod_lt_deg mod_poly p));
    pose proof fec_n_eq; rep_lia in
  match goal with
  | [H: _ |- poly_to_int (proj1_sig ?p) <= ?x] => pose_bounds p
  | [H: _ |- ?y <= poly_to_int (proj1_sig ?p) <= ?x] => pose_bounds p
  | [H: _ |- ?y <= poly_to_int (proj1_sig ?p) < ?x] => pose_bounds p
  | [H: _ |- poly_to_int (?p %~ mod_poly) <= ?x] => pose_mod_bounds p
  | [H: _ |- ?y <= poly_to_int (?p %~ mod_poly) <= ?x] => pose_mod_bounds p
  | [H: _ |- ?y <= poly_to_int (?p %~ mod_poly) < ?x] => pose_mod_bounds p
  end.

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

(* Remove Int.unsigned (Int.repr ?z) and Zbits.Zzero_ext 8 x for qpolys*)
Ltac simpl_repr :=
  repeat match goal with
  | [ |- context [ Zbits.Zzero_ext 8 ?x]] =>
       let N := fresh in
    assert (N: Zbits.Zzero_ext 8 x = x) by (
      rewrite Zbits.Zzero_ext_mod; [|rep_lia]; replace (two_p 8) with (256) by reflexivity;
      rewrite Zmod_small; [reflexivity | solve_qpoly_bounds]); rewrite -> N; clear N
  |  [ |- context [ Int.zero_ext 8 ?x ]] => unfold Int.zero_ext
  |  [ |-  context [ Int.unsigned (Int.repr ?x)]] =>
        let N := fresh in
        assert (N: Int.unsigned (Int.repr x) = x) by (subst;
        rewrite unsigned_repr; [ reflexivity | solve_qpoly_bounds]); rewrite -> N; clear N
  end.

(*Solves goals with Int.unsigned (Int.repr _) and Zbits.Zzero_ext when the value is an integer, not a qpoly (ie,
  rep_lia can prove that z is small enough)*)
Ltac solve_repr_int :=
  repeat lazymatch goal with
  |  [ |- context [ Int.zero_ext 8 ?x ]] => unfold Int.zero_ext
  |  [ |-  context [ Int.unsigned (Int.repr ?x)]] => rewrite unsigned_repr by rep_lia
  |  [ |- context [ Zbits.Zzero_ext 8 ?x]] => rewrite zbits_small; try rep_lia
  end.

(*Simplify an integer expression with zeroes*)
Ltac simplify_zeroes  :=
  repeat lazymatch goal with
    | [ |- context [ 0%Z + ?z ] ] => rewrite Z.add_0_l
    | [ |- context [ ?z + 0%Z ] ] => rewrite Z.add_0_r
    | [ |- context [ 0%Z * ?z ] ] => rewrite Z.mul_0_l
    | [ |- context [ ?z * 0%Z ] ] => rewrite Z.mul_0_r
  end.

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
  end).

(*Determines the integer corresponding to a nested series of pointer arithmetic operations, used in [pointer_to_offset]*)
Ltac build_offset op v1 v2 := 

  let rec build_offset' op' v1' v2' :=
    let one_side va :=
      lazymatch va with
      | Vint (Int.repr ?n) => constr:(n)
      | offset_val ?n ?p => n
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




