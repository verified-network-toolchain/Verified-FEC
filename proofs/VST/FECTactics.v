(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

Require Import VST.floyd.proofauto.
Require Import MatrixTransform.
Require Import CommonVST.
Require Import ByteFacts.

Lemma is_int_Vubyte: forall b: byte, is_int I8 Unsigned (Vubyte b).
Proof.
  intros b. simpl. pose proof (Byte.unsigned_range_2 b) as Hrange.
  rewrite Int.unsigned_repr; rep_lia.
Qed. 

(*Simplifies expressions given that the underlying data is a byte*)
Ltac simpl_repr_byte :=
  repeat match goal with
  |  [ |- is_int I8 Unsigned (Vubyte ?b)] => apply is_int_Vubyte
  |  [ |- context [ Byte.unsigned (Byte.repr ?b) ]] => rewrite Byte.unsigned_repr by rep_lia
  |  [ |- context [ Int.unsigned (Int.repr ?x)]] => rewrite Int.unsigned_repr by rep_lia
  |  [ |- context [ Zbits.Zzero_ext 8 ?x]] => rewrite zbits_small by rep_lia
  |  [ |- context [ Int.zero_ext 8 ?x ]] => unfold Int.zero_ext
  |  [ |- context [ is_int ?x ?y ?y ]] => simpl 
  end; try rep_lia; auto.

(*Simplify an integer expression with zeroes*)
Ltac simplify_zeroes  :=
  repeat lazymatch goal with
    | [ |- context [ 0%Z + ?z ] ] => rewrite Z.add_0_l
    | [ |- context [ ?z + 0%Z ] ] => rewrite Z.add_0_r
    | [ |- context [ 0%Z * ?z ] ] => rewrite Z.mul_0_l
    | [ |- context [ ?z * 0%Z ] ] => rewrite Z.mul_0_r
  end.

(*To make things nicer*)
Notation B := byte.

(*maybe expand this with needed definitions for decoder (only 2-3 places it would be needed)*)
(*Solve goals of the form [wf_matrix mx m n]*)
Ltac solve_wf :=
  repeat(lazymatch goal with
  | [H: _ |- wf_lmatrix (scalar_mul_list_partial  _ _ _ _ _ _) _ _] => apply scalar_mul_list_partial_wf
  | [H: _ |- wf_lmatrix (scalar_mul_list _ _ _ _ _) _ _ ] => apply scalar_mul_list_partial_wf
  | [H: _ |- wf_lmatrix (all_cols_one_partial _ _ _ _ _) _ _ ] => apply all_cols_one_partial_wf
  | [H: _ |- wf_lmatrix (add_multiple_partial _ _ _ _ _ _ _) _ _] => apply add_multiple_partial_wf
  | [H: _ |- wf_lmatrix (add_multiple _ _ _ _ _ _) _ _] => apply add_multiple_partial_wf
  | [H: _ |- wf_lmatrix (sub_all_rows_partial _ _ _ _ _) _ _] => apply sub_all_rows_partial_wf
  | [H: _ |- wf_lmatrix (gauss_all_steps_list_partial _ _ _ _) _ _] => apply gauss_all_steps_list_partial_wf
  | [H: _ |- wf_lmatrix (all_lc_one_partial _ _ _ _) _ _] => apply all_lc_one_partial_wf
  end); try lia; try assumption.

(*These lemmas are easy to prove with [simpl_repr_byte], which is why they are here*)

(*Maybe move elsewhere*)
Lemma byte_int_repr: forall z: Z,
  0 <= z <= Byte.max_unsigned ->
  Vubyte (Byte.repr z) = Vint (Int.repr z).
Proof.
  intros z Hz. unfold Vubyte. simpl_repr_byte.
Qed.

(*For some reason it unfold [byte_inv] even though it shouldn't so we need separate lemma*)
Lemma force_val_byte: forall (b: byte),
  force_val (sem_cast tuchar tuchar (Vubyte b)) = Vubyte b.
Proof.
  intros b. simpl. simpl_repr_byte.
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

(*To fold and unfold abbreviations for LOCALx and SEPx. This is super hacky*)
Ltac rewrite_eqs :=
  repeat match goal with
    | [H : ?x = cons ?y ?z |- context [ ?x ]] => rewrite H 
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
   end.
