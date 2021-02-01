Require Import VST.floyd.proofauto.

Require Import fec.
Require Import Common.
Require Import CommonVST.
Require Import Specs.

Import WPoly.

Set Bullet Behavior "Strict Subproofs".

Ltac solve_qpoly_bounds :=
  let pose_bounds p :=
    pose proof (modulus_poly_bound (proj1_sig p) (@ssrfun.svalP _ (fun y => deg y < deg mod_poly) p));
    pose proof fec_n_eq; rep_lia in
  match goal with
  | [H: _ |- poly_to_int (proj1_sig ?p) <= ?x] => pose_bounds p
  | [H: _ |- 0 <= poly_to_int (proj1_sig ?p) <= ?x] => pose_bounds p
  | [H: _ |- 0 <= poly_to_int (proj1_sig ?p) < ?x] => pose_bounds p
  end.

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

(*Remove (Int.repr (Int.unsigned _)) and (Int.zero_ext) from qpolys*)
Ltac rewrite_repr x :=
    let N := fresh in
      assert (N: Int.unsigned (Int.repr (poly_to_int (proj1_sig x))) = poly_to_int (proj1_sig x)) by (subst;
        rewrite unsigned_repr; [ reflexivity | solve_qpoly_bounds]); rewrite -> N; clear N.
Ltac rewrite_zbits x :=
  let N := fresh in
    assert (N: Zbits.Zzero_ext 8 (poly_to_int (proj1_sig x)) = poly_to_int (proj1_sig x)) by (
      rewrite Zbits.Zzero_ext_mod; [|rep_lia]; replace (two_p 8) with (256) by reflexivity;
      rewrite Zmod_small; [reflexivity | solve_qpoly_bounds]); rewrite -> N; clear N.

(*TODO: move*)
Lemma zbits_small: forall i,
  0 <= i < 256 ->
  Zbits.Zzero_ext 8 i = i.
Proof.
  intros i Hi. rewrite Zbits.Zzero_ext_mod; [|rep_lia]. replace (two_p 8) with (256) by reflexivity.
  rewrite Zmod_small; lia.
Qed.
      
(** Verification of [fec_matrix_transform]*)

Lemma body_fec_matrix_transform : semax_body Vprog Gprog f_fec_matrix_transform fec_matrix_transform_spec.
Proof.
  start_function. destruct H as [Hm0 [Hmnpos [Hmn [Hnbound [Hwf Hstr]]]]].
  forward_loop (EX (k : Z),
    PROP (0 <= k <= m)
    LOCAL (temp _k (Vint (Int.repr (k))); temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n));
      gvars gv)
    SEP(data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
   data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
   data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
   data_at Ews (tarray tuchar (m * n))
     (map Vint (map Int.repr (flatten_mx 
        (gauss_all_steps_rows_partial mx m k )))) s))
    break: (PROP ()
           LOCAL (temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n));
      gvars gv)
            SEP(data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
   data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
   data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
   data_at Ews (tarray tuchar (m * n))
     (map Vint (map Int.repr (flatten_mx 
        (gauss_all_steps_rows_partial mx m m )))) s)). 
{ forward. Exists 0%Z. entailer!. }
{ Intros k. forward_if.
  { (*body of outer loop *) 
    (*now there are 2 inner loops; the first is [all_cols_one_partial]*)
    forward_loop 
    (EX (i : Z),
      PROP (0 <= i <= m)
      LOCAL (temp _i (Vint (Int.repr i)); temp _k (Vint (Int.repr k)); temp _p s; 
      temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); gvars gv)
      SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
        data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
        data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr 
          (flatten_mx (all_cols_one_partial 
            (gauss_all_steps_rows_partial (F:=F) mx m k) k i )))) s))
      break: (PROP ()
        LOCAL (temp _k (Vint (Int.repr k)); temp _p s; 
      temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); gvars gv)
      SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
        data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
        data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr 
          (flatten_mx (all_cols_one_partial 
            (gauss_all_steps_rows_partial (F:=F) mx m k) k m )))) s)).
    { forward. Exists 0%Z. entailer!. }
    { Intros i. forward_if.
      { forward. (*Want to simplify pointer in q*)
        assert_PROP ((force_val (sem_binary_operation' Osub (tptr tuchar) tint
          (eval_binop Oadd (tptr tuchar) tuchar (eval_binop Oadd (tptr tuchar) tint s
           (eval_binop Omul tuchar tuchar (Vint (Int.repr i))
           (Vint (Int.repr n)))) (Vint (Int.repr n))) (Vint (Int.repr 1)))) =
           (offset_val (((i * n) + n) - 1) s)). { entailer!.
        rewrite sem_sub_pi_offset; auto. rep_lia. }
        rewrite H3. clear H3.
        forward.
        { entailer!. rewrite sem_sub_pi_offset; auto; try rep_lia. }
        { (*Now, we will simplify pointer in m*)
          assert_PROP ((force_val
               (sem_binary_operation' Oadd (tptr tuchar) tint
                  (eval_binop Osub (tptr tuchar) tuchar (offset_val (i * n + n - 1) s)
                     (Vint (Int.repr n))) (Vint (Int.repr 1)))) =
            offset_val (i * n) s). { entailer!.
          rewrite sem_sub_pi_offset; auto; try rep_lia. f_equal. simpl. rewrite sem_add_pi_ptr_special; auto;
          try rep_lia. simpl. rewrite offset_offset_val. f_equal. lia. }
          rewrite H3; clear H3.
          assert_PROP ((offset_val (i * n) s) = field_address (tarray tuchar (m * n)) 
            (SUB ((i * n) + n - 1 - (n-1))) s). { entailer!. rewrite arr_field_address; auto.
            simpl. f_equal. lia. apply (matrix_bounds_within); lia. } rewrite H3; rename H3 into Hm_offset. 
          forward.
          assert (Hwf' : wf_matrix (F:=F) (all_cols_one_partial (F:=F) 
            (gauss_all_steps_rows_partial (F:=F) mx m k) k i) m n) by solve_wf.
        (*Now we are at the while loop - because of the [strong_inv] condition of the matrix,
          the loop guard is false (the loop finds the element to swap if one exists, but returns
          with an error whether or not one exists*)
        (*Because of this, we give a trivial loop invariant*)
        remember ((PROP ( )
           LOCAL (temp _w (Vint (Int.zero_ext 8 (Int.repr i)));
           temp _m (field_address (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s);
           temp _q (offset_val (i * n + n - 1) s);
           temp _i (Vint (Int.repr i)); temp _k (Vint (Int.repr k)); 
           temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); 
           gvars gv)
           SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
           data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
           data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
           data_at Ews (tarray tuchar (m * n))
             (map Vint
                (map Int.repr
                   (flatten_mx
                      (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k)
                         k i)))) s))) as x.
         forward_loop x break: x; subst. (*so I don't have to write it twice*)
        { entailer!. }
        { assert_PROP (force_val (sem_sub_pi tuchar Signed 
            (offset_val (i * n + n - 1) s) (Vint (Int.repr k))) =
            offset_val (i * n + n - 1 - k) s). { entailer!.
           rewrite sem_sub_pi_offset;auto. simpl. f_equal. lia. rep_lia. }
           (*TODO: will need more general stuff probably*)
           assert (0 <= i * n + n - 1 - k < m * n). {
            apply matrix_bounds_within; lia. }
           assert_PROP (force_val (sem_sub_pi tuchar Signed 
            (offset_val (i * n + n - 1) s) (Vint (Int.repr k))) =
            field_address (tarray tuchar (m * n)) (SUB  (i * n + n - 1 - k)) s). {
            entailer!. rewrite H3. rewrite arr_field_address; auto. simpl. f_equal. lia. }
            clear H3. 
           assert_PROP ((0 <= i * n + n - 1 - k <
              Zlength (map Int.repr (flatten_mx
              (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k)
              k i))))). {
           entailer!. list_solve. } simpl_reptype. rewrite Zlength_map in H3.
           forward.
          { entailer!. rewrite (@flatten_mx_Znth m n); try lia. 
            pose proof (qpoly_int_bound (get (F:=F) (all_cols_one_partial (F:=F) 
                (gauss_all_steps_rows_partial (F:=F) mx m k) k i) 
                i k)).  rewrite Int.unsigned_repr; rep_lia. assumption. }
          { entailer!. rewrite sem_sub_pi_offset; auto. rep_lia. }
          { forward_if.
            { (*contradiction due to [strong_inv]*)
              assert (Znth (i * n + n - 1 - k)
                (flatten_mx (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k)
                k i)) <> 0%Z). {
              rewrite (@flatten_mx_Znth m n); try lia. 2: assumption. intro Hzero.
              rewrite poly_to_int_zero_iff in Hzero. 
              assert (Hrm : 0 <= k < m) by lia.
              assert (Hcm : 0 <= i < m) by lia.
              apply (gauss_all_steps_columns_partial_zeroes_list Hrm H1 (proj2 Hmn) Hwf Hstr Hcm). 
              replace (ssralg.GRing.zero (ssralg.GRing.Field.zmodType F)) with (q0 modulus_poly_deg_pos) by reflexivity.
              destruct ((get (F:=F)
              (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k)  k i) i k)) eqn : G.
              unfold q0. unfold r0. exist_eq.
              simpl in Hzero. assumption. } 
              apply mapsto_memory_block.repr_inj_unsigned in H6. contradiction. 2: rep_lia.
              rewrite (@flatten_mx_Znth m n); try lia. eapply Z_expand_bounds.
              3 : { apply qpoly_int_bound. } lia. rep_lia. assumption. }
            { forward. entailer!. }
          }
        }
      { (*after the while loop*)
         assert_PROP (force_val (sem_sub_pi tuchar Signed 
            (offset_val (i * n + n - 1) s) (Vint (Int.repr k))) =
            field_address (tarray tuchar (m * n)) (SUB  (i * n + n - 1 - k)) s). {
            entailer!. rewrite sem_sub_pi_offset;auto. simpl. rewrite arr_field_address; auto. simpl. f_equal. lia.
            apply matrix_bounds_within; lia. rep_lia. } 
         assert (0 <= i * n + n - 1 - k < m * n). {
            apply matrix_bounds_within; lia. }
         assert_PROP ((0 <= i * n + n - 1 - k <
          Zlength (map Int.repr (flatten_mx
         (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k) k i))))). 
         entailer!. list_solve. rewrite Zlength_map in H5.
         (*Doing some stuff to simplify here so we don't need to repeat this in each branch*)
         pose proof (Hpolybound:= (qpoly_int_bound (get (F:=F) (all_cols_one_partial (F:=F) 
                (gauss_all_steps_rows_partial (F:=F) mx m k) k i) i k))).
          forward; try rewrite (@flatten_mx_Znth m n); try lia; try assumption.
        { entailer!. lia. }
        { entailer!. rewrite sem_sub_pi_offset; auto. rep_lia. }
        { forward.
          { entailer!. solve_qpoly_bounds. }
          { entailer!. rewrite inverse_contents_Znth. rewrite poly_of_int_inv.
            simpl. unfold poly_inv. rewrite unsigned_repr. all: solve_qpoly_bounds. } 
          { forward. forward. (*simplify before for loop*)
            rewrite inverse_contents_Znth. 2: solve_qpoly_bounds. rewrite poly_of_int_inv. simpl.
            remember (get (F:=F) (all_cols_one_partial (F:=F)
                      (gauss_all_steps_rows_partial (F:=F) mx m k) k i) i k) as qij eqn : Hqij. 
            (*remember (proj1_sig qij) as pij eqn : Hpij.*)
            remember (find_inv mod_poly modulus_poly_deg_pos qij) as qij_inv eqn : Hqinv.
            replace (poly_inv mod_poly modulus_poly_deg_pos (proj1_sig qij)) with (proj1_sig qij_inv). 2 : {
            unfold poly_inv. rewrite poly_to_qpoly_unfold. rewrite Hqinv. reflexivity. }
            unfold Int.zero_ext.
            rewrite_repr qij_inv. rewrite_zbits qij_inv.
            rewrite unsigned_repr; [| rep_lia]. rewrite zbits_small; [| rep_lia].
            assert_PROP ((force_val
               (sem_add_ptr_int tuchar Signed (offset_val (i * n + n - 1) s)
                  (Vint (Int.repr 1)))) = offset_val (i * n + n) s). { entailer!.
            f_equal. lia. } rewrite H6; clear H6.
            assert (Hmn_leq: 0 <= i * n + n <= m * n). { split; try lia. 
              replace n with (1 * n) at 2 by lia. rewrite <- Z.mul_add_distr_r.
              apply Z.mul_le_mono_nonneg_r; lia. } 
            (*Scalar multiplication loop*)
            (*Unfortunately, lots of duplication here: can we save locals in a variable?*)
            forward_loop (EX (j : Z),
            PROP (0 <= j <= n)
            LOCAL (temp _inv (Vint (Int.repr (poly_to_int (proj1_sig qij_inv))));
              temp _t'11 (Vint (Int.repr (poly_to_int (proj1_sig qij_inv))));
              temp _t'10 (Vint (Int.repr (poly_to_int (proj1_sig qij))));
              temp _w (Vint (Int.repr i));
              temp _m (field_address (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s);
              (*temp _q (field_address (tarray tuchar (m * n)) [ArraySubsc (cols_one_row * n + n - 1)] s);*)
              temp _q (offset_val (i * n + n - 1) s);
              temp _i (Vint (Int.repr i)); temp _k (Vint (Int.repr k)); 
              temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); 
              gvars gv;
              temp _n (field_address0 (tarray tuchar (m * n)) (SUB (i * n + n - j)) s))
              (*temp _n (offset_val (cols_one_row * n + n - 1 - j) s))*)
            SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
                 data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
                 data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
                 data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr
                  (flatten_mx (scalar_mul_row_partial (all_cols_one_partial (F:=F) 
                    (gauss_all_steps_rows_partial (F:=F) mx m k) k i) 
                    i qij_inv j)))) s))
            break: (PROP ()
              LOCAL (temp _inv (Vint (Int.repr (poly_to_int (proj1_sig qij_inv))));
              temp _t'11 (Vint (Int.repr (poly_to_int (proj1_sig qij_inv))));
              temp _t'10 (Vint (Int.repr (poly_to_int (proj1_sig qij))));
              temp _w (Vint (Int.repr i));
              temp _m (field_address (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s); 
              temp _q (field_address (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1)] s);
              temp _i (Vint (Int.repr i)); temp _k (Vint (Int.repr k)); 
              temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); 
              gvars gv)
              SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
                 data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
                 data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
                 data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr
                  (flatten_mx (scalar_mul_row (all_cols_one_partial (F:=F) 
                    (gauss_all_steps_rows_partial (F:=F) mx m k) k i) 
                    i qij_inv)))) s)).
            { Exists 0%Z. entailer!. rewrite arr_field_address0; auto. simpl. f_equal; lia.
              rewrite scalar_mul_row_partial_0. cancel. }
            { Intros j. assert (Hcn : 0 <= i * n). { apply Z.mul_nonneg_nonneg; lia. } 
              forward_if.
              { rewrite !arr_field_address0; auto. rewrite arr_field_address; auto.
                rewrite isptr_denote_tc_test_order; auto. unfold test_order_ptrs.
                assert (Hsame: sameblock (offset_val (sizeof tuchar * (i * n + n - j)) s)
                (offset_val (sizeof tuchar * (i * n + n - 1 - (n - 1))) s) = true). {
                eapply sameblock_trans. apply sameblock_symm. all: apply isptr_offset_val_sameblock; auto. }
                rewrite Hsame; clear Hsame. repeat(sep_apply data_at_memory_block).
                apply andp_right.
                - sep_eapply memory_block_weak_valid_pointer; auto; try(simpl; lia).
                  instantiate (1 := sizeof tuchar * (i * n + n - j)). simpl. lia. entailer!.
                - sep_eapply memory_block_weak_valid_pointer; auto; try(simpl; lia).
                  instantiate (1 := sizeof tuchar * (i * n + n - 1 - (n - 1))). simpl. lia. 
                  entailer!.
                - apply matrix_bounds_within; lia.
                - lia. }
              { forward. entailer!. apply field_address0_isptr. apply arr_field_compatible0; auto; try lia.
                assert_PROP ((field_address (tarray tuchar (m * n)) 
                    [ArraySubsc (i * n + n - 1 - (n - 1))] s) =
                    (field_address0 (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s)). {
                entailer!. rewrite <- Hm_offset. rewrite arr_field_address0; auto. f_equal; simpl; lia. lia. }
                rewrite H8 in H7; clear H8.
                assert_PROP (j < n). { entailer!. apply ptr_comparison_gt_iff in H7; auto. all: simpl; lia. }
                clear H7.
                assert_PROP ((force_val
                (sem_binary_operation' Osub (tptr tuchar) tint
                  (field_address0 (tarray tuchar (m * n)) [ArraySubsc (i * n + n - j)] s)
                  (Vint (Int.repr 1)))) = 
                (field_address (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - j)] s)). {
                entailer!. rewrite !arr_field_address0; auto; try lia.
                rewrite !arr_field_address; auto; try lia. rewrite sem_sub_pi_offset; auto; try rep_lia.
                f_equal; simpl; lia. } rewrite H7; clear H7. 
                (*Need length bound also*)
                assert_PROP (0 <= i * n + n - 1 - j < Zlength (map Int.repr
                (flatten_mx (scalar_mul_row_partial (F:=F)
                (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k) k i) i qij_inv j)))).
                 { entailer!. list_solve. }
                rewrite Zlength_map in H7.
                assert (Hwf'' : wf_matrix (F:=F) (scalar_mul_row_partial (F:=F)
                  (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k) k i) i qij_inv j) m n)
                by solve_wf.
                forward.
                - entailer!. rewrite (@flatten_mx_Znth m n); try lia.
                  rewrite unsigned_repr; solve_qpoly_bounds. auto. 
                - rewrite (@flatten_mx_Znth m n); try lia; auto.
                  remember ((get (F:=F)
                           (scalar_mul_row_partial (F:=F)
                              (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k)
                                 k i) i qij_inv j) i j)) as aij.
                  forward_call.
                  + rewrite_repr aij. rewrite_repr qij_inv. rewrite_zbits aij. rewrite_zbits qij_inv. split; solve_qpoly_bounds.
                  + (*simplify result of function call*)
                    rewrite_repr aij. rewrite_repr qij_inv. rewrite_zbits aij. rewrite_zbits qij_inv.
                    rewrite !poly_of_int_inv. forward. Exists (j+1). entailer!.
                    rewrite arr_field_address; auto; try lia.
                    rewrite arr_field_address0; auto; try lia. f_equal; lia.
                    rewrite !upd_Znth_map. (*need to simplify the scalar_mult*)
                    rewrite (@scalar_mul_row_plus_1 F _ m n). simpl_reptype.
                    remember ((scalar_mul_row_partial (F:=F) (all_cols_one_partial (F:=F)
                      (gauss_all_steps_rows_partial (F:=F) mx m k) k i) i
                      (find_inv mod_poly modulus_poly_deg_pos (get (F:=F) (all_cols_one_partial (F:=F)
                      (gauss_all_steps_rows_partial (F:=F) mx m k) k i) i k)) j)) as mx'.
                    replace (ssralg.GRing.mul (R:=ssralg.GRing.Field.ringType F)) with
                     (r_mul _ modulus_poly_deg_pos) by reflexivity. unfold r_mul. 
                    unfold poly_mult_mod. 
                    remember ((get (F:=F)(all_cols_one_partial (F:=F) 
                      (gauss_all_steps_rows_partial (F:=F) mx m k) k i) i k)) as elt.
                    assert (Hget: (get (F:=F) mx' i j) = (get (F:=F) (all_cols_one_partial (F:=F)
                            (gauss_all_steps_rows_partial (F:=F) mx m k) k i) i j)). {
                     rewrite Heqmx'. rewrite (@scalar_mul_row_outside _ m n); try lia. reflexivity.
                     auto. } rewrite Hget. clear Hget. rewrite poly_mult_comm.
                      rewrite <- (@flatten_mx_set m n). simpl. cancel. all: try lia; auto. } 
              { (*scalar mul loop return*) forward. entailer!.
                - rewrite arr_field_address; auto; try lia. f_equal; simpl; lia. 
                - assert_PROP ((field_address (tarray tuchar (m * n)) 
                    [ArraySubsc (i * n + n - 1 - (n - 1))] s) =
                    (field_address0 (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s)). {
                  entailer!. rewrite <- Hm_offset. rewrite arr_field_address0; auto. f_equal; simpl; lia. lia. }
                  rewrite H29 in H7; clear H29.
                  (*need to know that j = n at end of loop*)
                  assert (Hjn: j >= n). { 
                    assert (Hft: forall a b, typed_false a b -> ~(typed_true a b)). { intros a b F T.
                    unfold typed_true in T; unfold typed_false in F; rewrite T in F; inversion F. }
                    apply Hft in H7; clear Hft. rewrite (not_iff_compat) in H7. 2: {
                    rewrite ptr_comparison_gt_iff. reflexivity. all: auto. all: simpl; lia. }
                    lia. } 
                  assert (j = n) by lia. subst; clear Hjn H7. unfold scalar_mul_row. 
                  assert (Hlenn: (Zlength (Znth i (all_cols_one_partial (F:=F)
                          (gauss_all_steps_rows_partial (F:=F) mx m k) k i))) = n).
                  { destruct Hwf' as [Hlen [Hn' Hin]]. apply Hin.
                    apply Znth_In; lia. } rewrite Hlenn; cancel. } }
            (*no idea what level I'm on - coqide has stopped highlighting brackets, but at end of col loop*)
            forward. Exists (i + 1). entailer!.
            { f_equal. unfold Int.zero_ext. f_equal. rewrite unsigned_repr; 
             [ rewrite zbits_small; [reflexivity | rep_lia] | rep_lia]. }
            { rewrite all_cols_one_plus_1; try lia. 
              replace (ssralg.GRing.inv (R:=ssralg.GRing.Field.unitRingType F)) with (find_inv _ modulus_poly_deg_pos) by reflexivity.
              rewrite (@all_cols_one_outside F m n); try lia. cancel. solve_wf. } } } } } }
      (*now we are completely finishing the col loop*)
    { forward. entailer!. replace (i) with m by lia. cancel. } }
  { (*start of second part: add kth row to all other rows*)
    forward. (*simplify r*)
    assert_PROP ((force_val (sem_binary_operation' Osub (tptr tuchar) tint
                  (eval_binop Oadd (tptr tuchar) tuchar (eval_binop Oadd (tptr tuchar) tint s
                  (eval_binop Omul tuchar tuchar (Vint (Int.repr k))
                  (Vint (Int.repr n)))) (Vint (Int.repr n))) (Vint (Int.repr 1)))) = 
                 offset_val (k * n + n - 1) s). { entailer!.
    rewrite sem_sub_pi_offset; auto. rep_lia. } rewrite H1; clear H1.
    (*can't use [forward_for_simple_bound] because it cases i to a tuchar*)
    (*TODO: again, lots of duplication*)
    forward_loop (EX (i : Z),
      PROP (0 <= i <= m)
      LOCAL  (temp _r (offset_val (k * n + n - 1) s); temp _k (Vint (Int.repr k));
              temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); temp _i (Vint (Int.repr i));
              gvars gv)
      SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
            data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
            data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
            data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr (flatten_mx
          (sub_all_rows_partial (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k) k m) k i)))) s))
      break: 
      (PROP ()
      LOCAL  (temp _r (offset_val (k * n + n - 1) s); temp _k (Vint (Int.repr k));
              temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n));
              gvars gv)
      SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
            data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
            data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
            data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr (flatten_mx
          (sub_all_rows_partial (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k) k m) k m)))) s)).
    { (*initialization of subtract all rows loop*) 
      forward. Exists 0%Z. entailer!. }
    { (*Body of subtract all rows loop *) 
      Intros i. forward_if.
      { (*i < m (loop body)*) 
        forward_if (PROP ()
            LOCAL ( temp _r (offset_val (k * n + n - 1) s);
              temp _k (Vint (Int.repr k)); temp _p s; temp _i_max (Vint (Int.repr m));
              temp _j_max (Vint (Int.repr n)); temp _i (Vint (Int.repr i)); gvars gv)
            SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
             data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
             data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
             data_at Ews (tarray tuchar (m * n))
               (map Vint (map Int.repr (flatten_mx (if Z.eq_dec i k then
                (sub_all_rows_partial (F:=F)(all_cols_one_partial (F:=F) 
                  (gauss_all_steps_rows_partial (F:=F) mx m k) k m) k i) else
               (add_multiple_partial (sub_all_rows_partial (F:=F)(all_cols_one_partial (F:=F) 
                  (gauss_all_steps_rows_partial (F:=F) mx m k) k m) k i) k i (q1 modulus_poly_deg_pos) n)
                )))) s)). 
        { (*when i != k*)
          forward. (*simplify q*)
          assert_PROP ((force_val (sem_binary_operation' Osub (tptr tuchar) tint
            (eval_binop Oadd (tptr tuchar) tuchar (eval_binop Oadd (tptr tuchar) tint s
            (eval_binop Omul tuchar tuchar (Vint (Int.repr i)) (Vint (Int.repr n))))
            (Vint (Int.repr n))) (Vint (Int.repr 1)))) =
            offset_val (i * n + n - 1) s). { entailer!. rewrite sem_sub_pi_offset; auto. rep_lia. }
          rewrite H4; clear H4.
          forward_for (fun (j : Z) => PROP (0 <= j <= n)
            LOCAL (temp _q (offset_val (i * n + n - 1) s); temp _r (offset_val (k * n + n - 1) s);
              temp _k (Vint (Int.repr k)); temp _p s; temp _i_max (Vint (Int.repr m));
              temp _j_max (Vint (Int.repr n)); temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)); gvars gv)
            SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
             data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
             data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
             data_at Ews (tarray tuchar (m * n))
               (map Vint (map Int.repr (flatten_mx
               (add_multiple_partial (sub_all_rows_partial (F:=F)(all_cols_one_partial (F:=F) 
                  (gauss_all_steps_rows_partial (F:=F) mx m k) k m) k i) k i (q1 modulus_poly_deg_pos) j)))) s)).
           { (*beginning of subtraction loop*) forward. Exists 0%Z. entailer!. rewrite add_multiple_partial_0.
             cancel. }
           { entailer!. }
           { rename x0 into j. (*simplify *(q-j)*)
             assert_PROP (force_val (sem_sub_pi tuchar Signed (offset_val (i * n + n - 1) s) (Vint (Int.repr j))) =
                offset_val (i * n + n - 1 - j) s). { entailer!.  rewrite sem_sub_pi_offset; auto. simpl.
                f_equal; rep_lia. rep_lia. }
             assert_PROP (offset_val (i * n + n - 1 - j) s = 
              field_address (tarray tuchar (m * n)) (SUB (i * n + n - 1 - j)) s). { entailer!.
                rewrite arr_field_address; auto; try lia. simpl. f_equal; lia. apply matrix_bounds_within; lia. }
             rewrite H6 in H5. (*TODO: can we automate this? *)
             assert (Hij: 0 <= i * n + n - 1 - j < m * n) by (apply matrix_bounds_within; lia).
             assert_PROP ((0 <= i * n + n - 1 - j < Zlength (map Int.repr (flatten_mx (add_multiple_partial (F:=F)
              (sub_all_rows_partial (F:=F) (all_cols_one_partial (F:=F) 
              (gauss_all_steps_rows_partial (F:=F) mx m k) k m) k i) k i
              (q1 (f:=mod_poly) modulus_poly_deg_pos) j))))). { entailer!. list_solve. }
            rewrite Zlength_map in H7. forward.
            { entailer!. rewrite (@flatten_mx_Znth m n); try lia. rewrite unsigned_repr; solve_qpoly_bounds.
              solve_wf. }
            { entailer!. rewrite H5. rewrite <- H6. auto. }
            { (*Simplify *(r-j) *)
              rewrite (@flatten_mx_Znth m n); try lia. 2: solve_wf.
              assert_PROP (force_val (sem_sub_pi tuchar Signed (offset_val (k * n + n - 1) s) (Vint (Int.repr j))) =
                 offset_val (k * n + n - 1 - j) s). { entailer!. rewrite sem_sub_pi_offset; auto. simpl.
               f_equal; rep_lia. rep_lia. }
              assert_PROP (offset_val (k * n + n - 1 - j) s = field_address (tarray tuchar (m * n))
                (SUB (k * n + n - 1 - j)) s). { entailer!. rewrite arr_field_address; auto; try lia.
              simpl; f_equal; lia. apply matrix_bounds_within; lia. } rewrite H9 in H8. 
              assert (Hkj : 0 <= k * n + n - 1 - j < m * n) by (apply matrix_bounds_within; lia).
              assert_PROP ((0 <= k * n + n - 1 - j < Zlength (map Int.repr (flatten_mx
              (add_multiple_partial (F:=F)  (sub_all_rows_partial (F:=F)(all_cols_one_partial (F:=F) 
              (gauss_all_steps_rows_partial (F:=F) mx m k) k m) k i) k i 
              (q1 (f:=mod_poly) modulus_poly_deg_pos) j))))). { entailer!. list_solve. } rewrite Zlength_map in H10.
              forward.
              { entailer!. rewrite (@flatten_mx_Znth m n); try lia. rewrite unsigned_repr; solve_qpoly_bounds.
              solve_wf. }
              { entailer!. rewrite H8. rewrite <- H9. auto. }
              { (*actual subtraction*) 
                rewrite (@flatten_mx_Znth m n); try lia. 2: solve_wf. forward.
                { entailer!. rewrite H5; rewrite <- H6; auto. }
                { (*need lots of simplification*)
                  unfold Int.xor. rewrite !unsigned_repr; try solve_qpoly_bounds.
                  rewrite xor_poly_to_int.
                  remember (add_multiple_partial (F:=F) (sub_all_rows_partial (F:=F)
                           (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k) k m) k i) k i
                           (q1 (f:=mod_poly) modulus_poly_deg_pos) j) as mx'.
                  forward. 
                  (*end of subtraction loop*)
                  Exists (j+1). entailer!.
                  { f_equal. unfold Int.zero_ext. f_equal. 
                    rewrite unsigned_repr; [ rewrite zbits_small; rep_lia | rep_lia]. } 
                  { rewrite (@add_multiple_partial_plus_1 _ m n); try lia. 2: solve_wf.
                    rewrite <- (@flatten_mx_set m n); try lia. 2: solve_wf.
                    rewrite ssralg.GRing.mul1r. 
                    replace (ssralg.GRing.add (V:=ssralg.GRing.Field.zmodType F)) with (qadd modulus_poly_deg_pos) by reflexivity.
                    unfold qadd. unfold r_add. simpl. unfold poly_add_mod. simpl_reptype.
                    (*TODO: fix spelling*)
                    rewrite (@add_multiple_partial_outside _ m n); try lia. 2: solve_wf.
                    rewrite (@add_multiple_partial_other_row _ m n); try lia. 2: solve_wf.
                    (*We can get rid of the other [add_multiple_add_partial] since i <> k*)
                    remember ((proj1_sig  (get (F:=F)
                      (sub_all_rows_partial (F:=F) 
                        (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k) k m) k i) i j) +~
                      proj1_sig  (get (F:=F) (sub_all_rows_partial (F:=F)
                        (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k) k m)  k i) k j)))
                    as sum. 
                    (*now we just need to show the two pieces are equal*)
                     rewrite <- !upd_Znth_map. 
                    assert (Hsum: Int.zero_ext 8 (Int.repr (poly_to_int sum)) = 
                        (Int.repr (poly_to_int (sum %~ mod_poly)))). {
                     unfold Int.zero_ext. f_equal.
                     assert (Hdeg: deg sum < deg mod_poly). { rewrite Heqsum.
                     eapply Z.le_lt_trans. apply poly_add_deg_max. apply Z.max_lub_lt;
                     apply (@ssrfun.svalP _ (fun y => deg y < deg mod_poly)). }
                     rewrite pmod_refl; auto.
                     apply modulus_poly_bound in Hdeg. 
                     rewrite Zbits.Zzero_ext_mod; [|lia]. replace (two_p 8) with (256) by reflexivity.
                     pose proof fec_n_bound; rewrite Zmod_small; rewrite unsigned_repr; rep_lia.
                     apply modulus_poly_deg_pos. } rewrite Hsum. cancel. }
                }
              }
            }
          }
          { (*end of subtraction loop*) entailer!. destruct (Z.eq_dec i k); try lia. rename x0 into j. replace j with n by lia. cancel. }
        }
        { (*i = k case (easier)*)
           forward. entailer!. destruct (Z.eq_dec k k); try lia. cancel. }
        { (*postcondition of sub_all_rows loop*) forward. Exists (i+1). entailer!.
          { f_equal. unfold Int.zero_ext. f_equal. rewrite unsigned_repr; [rewrite zbits_small ; rep_lia | rep_lia]. } 
          { rewrite sub_all_rows_plus_1; try lia. 
            replace (ssralg.GRing.opp (V:=ssralg.GRing.Ring.zmodType (ssralg.GRing.Field.ringType F))
                      (ssralg.GRing.one (ssralg.GRing.Field.ringType F))) with
              (q1 (f:=mod_poly) modulus_poly_deg_pos) by reflexivity. 
            destruct (Z.eq_dec i k); simpl; cancel. unfold add_multiple.
            assert (Hwf' : wf_matrix (sub_all_rows_partial (F:=F)
                           (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k) k m)
                           k i) m n) by solve_wf.
            destruct Hwf' as [Hlen [Hn Hin]]. rewrite Hin. cancel. apply Znth_In. lia. }
            }
          }
          { (*end of sub all rows loop*) forward. entailer!. replace i with m by lia. cancel. }
        }
        { (*postcondition of gauss_one_step loop*)
          forward. Exists (k+1). entailer!.
          { f_equal. unfold Int.zero_ext. f_equal.
            rewrite unsigned_repr; [rewrite zbits_small ; rep_lia | rep_lia]. }
          { rewrite gauss_all_steps_rows_partial_plus_1. cancel. lia. }
        }
      }
    }
    { (*indentation is messed up again*) (*end of gauss_one_step] loop*)
      forward. entailer!. replace k with m by lia. cancel.
    }
  }
  { (*Start of third part: make all leading coefficients one*)
    (*Note that the loop goes from 0 to m - 1 so we need 0 < m here*)
    forward_loop (EX (i : Z),
      PROP (0 <= i <= m - 1)
      LOCAL (temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); temp _i (Vint (Int.repr i));
            gvars gv)
      SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
           data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
           data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
           data_at Ews (tarray tuchar (m * n))
            (map Vint (map Int.repr (flatten_mx (all_lc_one_rows_partial 
              (gauss_all_steps_rows_partial (F:=F) mx m m) i)))) s))
      break:
       (PROP ()
        LOCAL (temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); gvars gv) 
        SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
           data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
           data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
           data_at Ews (tarray tuchar (m * n))
            (map Vint (map Int.repr (flatten_mx (all_lc_one_rows_partial 
              (gauss_all_steps_rows_partial (F:=F) mx m m) (m-1))))) s)).
    { (*initialization*) forward. Exists 0%Z. entailer!. }
    { (*outer loop for lc's 1*) Intros i. forward_if.
      { (*loop body*) forward.
        (*simplify q*) assert_PROP ((force_val (sem_binary_operation' Osub (tptr tuchar) tint
        (eval_binop Oadd (tptr tuchar) tuchar (eval_binop Oadd (tptr tuchar) tint s
        (eval_binop Omul tuchar tuchar (Vint (Int.repr i)) (Vint (Int.repr n))))
        (Vint (Int.repr n))) (Vint (Int.repr 1)))) = offset_val (i * n + n - 1) s). {
        entailer!. rewrite sem_sub_pi_offset; auto. rep_lia. } rewrite H1; clear H1.
        assert_PROP (offset_val (i * n + n - 1) s = field_address (tarray tuchar (m * n)) (SUB (i * n + n - 1)) s). {
        entailer!. rewrite arr_field_address; auto. simpl. f_equal; lia.
        replace (i * n + n - 1) with (i * n + n - 1 - 0) by lia. apply matrix_bounds_within; lia. }
        forward.
        { entailer!. rewrite sem_sub_pi_offset; auto. rep_lia. }
        { (*simplify m*) assert_PROP (force_val
               (sem_binary_operation' Oadd (tptr tuchar) tint
                  (eval_binop Osub (tptr tuchar) tuchar (offset_val (i * n + n - 1) s)
                     (Vint (Int.repr n))) (Vint (Int.repr 1))) = offset_val (i * n + n - 1 - (n - 1)) s). {
          entailer!. rewrite sem_sub_pi_offset; auto. simpl. rewrite sem_add_pi'; auto.
          rewrite offset_offset_val. simpl; f_equal; lia. rep_lia. rep_lia. } rewrite H2; clear H2. 
          assert_PROP (offset_val (i * n + n - 1 - (n - 1)) s = field_address (tarray tuchar (m * n))
            (SUB ( i * n + n - 1 - ( n - 1))) s). { entailer!. rewrite arr_field_address; auto.
          f_equal. simpl. lia. apply matrix_bounds_within; lia. } rewrite H2. 
          (*simplify (q-i)*) 
          assert_PROP (force_val (sem_sub_pi tuchar Signed (offset_val (i * n + n - 1) s) (Vint (Int.repr i))) =
            field_address (tarray tuchar (m * n)) (SUB (i * n + n - 1 - i)) s). { entailer!.
          rewrite sem_sub_pi_offset; auto. rewrite arr_field_address; auto. simpl. f_equal; lia.
          apply matrix_bounds_within; lia. rep_lia. }
          (*Also need length info in context*)
          assert_PROP ((0 <= i * n + n - 1 - i < Zlength (map Int.repr
            (flatten_mx (all_lc_one_rows_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m m) i))))). {
          entailer!. assert (0 <= i * n + n - 1 - i < m * n). apply matrix_bounds_within; lia. list_solve. }
          rewrite Zlength_map in H4. forward.
          { (*pointer access is valid*) entailer!. rewrite (@flatten_mx_Znth m n); try lia. 2: solve_wf.
            rewrite unsigned_repr; solve_qpoly_bounds. }
          { entailer!. rewrite sem_sub_pi_offset; auto. rep_lia. }
          { rewrite (@flatten_mx_Znth m n); [| solve_wf | lia |lia ].
            pose proof (Hpolybound:= (qpoly_int_bound (get (F:=F) (all_lc_one_rows_partial (F:=F) 
                  (gauss_all_steps_rows_partial (F:=F) mx m m) i) i i))).
            forward.
            { entailer!. solve_qpoly_bounds. }
            { entailer!. rewrite inverse_contents_Znth; [| solve_qpoly_bounds]. simpl.
              rewrite poly_of_int_inv. unfold poly_inv.
              rewrite unsigned_repr; solve_qpoly_bounds. }
            { rewrite inverse_contents_Znth; [| solve_qpoly_bounds]. rewrite poly_of_int_inv.
              remember ((get (F:=F)(all_lc_one_rows_partial (F:=F) 
                (gauss_all_steps_rows_partial (F:=F) mx m m) i) i i)) as aii.
              forward. (*simplify inv*)
              remember (find_inv mod_poly modulus_poly_deg_pos aii) as aii_inv eqn : Haiiinv.
              replace (poly_inv mod_poly modulus_poly_deg_pos (proj1_sig aii)) with (proj1_sig aii_inv). 2 : {
              unfold poly_inv. rewrite poly_to_qpoly_unfold. rewrite Haiiinv. reflexivity. }
              unfold Int.zero_ext. rewrite_repr aii_inv. rewrite_zbits aii_inv.
              forward.
              (*simplify n*)
              assert_PROP (force_val (sem_binary_operation' Oadd (tptr tuchar) tint (offset_val (i * n + n - 1) s)
                  (Vint (Int.repr 1))) = offset_val (i * n + n) s). { entailer!. f_equal; lia. }
              rewrite H5; clear H5.
              assert (Himn: 0 <= i * n + n <= m * n). { split; try lia. replace (i * n + n) with ((i+1) * n) by lia.
              apply Z.mul_le_mono_nonneg_r; lia. }
              assert (Hin0: 0 <= i * n). { apply Z.mul_nonneg_nonneg; lia. }
              (*inner loop (scalar multiply)*)
              forward_loop (EX (j: Z),
                PROP (0 <= j <= n)
                LOCAL (temp _n (field_address0 (tarray tuchar (m * n)) (SUB ( i * n + n - j)) s);
                  temp _inv (Vint (Int.repr (poly_to_int (proj1_sig aii_inv))));
                  temp _t'6 (Vint (Int.repr (poly_to_int (proj1_sig aii_inv))));
                  temp _t'5 (Vint (Int.repr (poly_to_int (proj1_sig aii))));
                  temp _m (field_address (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s);
                  temp _q (offset_val (i * n + n - 1) s); temp _p s; temp _i_max (Vint (Int.repr m));
                  temp _j_max (Vint (Int.repr n)); temp _i (Vint (Int.repr i)); gvars gv)
                SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
                  data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
                  data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
                  data_at Ews (tarray tuchar (m * n))(map Vint (map Int.repr
                    (flatten_mx (scalar_mul_row_partial 
                      (all_lc_one_rows_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m m) i) i aii_inv j)))) s)).
              { Exists 0%Z. entailer!. rewrite arr_field_address0; auto. simpl. f_equal; lia.
                rewrite scalar_mul_row_partial_0. cancel.  }
              { entailer!. assert (Hbound: 0 <= (i * n + n - j) <= m * n) by lia. 
                rewrite !arr_field_address0; auto. rewrite arr_field_address; auto.
                rewrite isptr_denote_tc_test_order; auto. unfold test_order_ptrs.
                assert (Hsame: sameblock (offset_val (sizeof tuchar * (i * n + n - j)) s)
                (offset_val (sizeof tuchar * (i * n + n - 1 - (n - 1))) s) = true). {
                eapply sameblock_trans. apply sameblock_symm. all: apply isptr_offset_val_sameblock; auto. }
                rewrite Hsame; clear Hsame. repeat(sep_apply data_at_memory_block).
                apply andp_right.
                - sep_eapply memory_block_weak_valid_pointer; auto; try(simpl; lia).
                  instantiate (1 := sizeof tuchar * (i * n + n - j)). simpl. lia. entailer!.
                - sep_eapply memory_block_weak_valid_pointer; auto; try(simpl; lia).
                  instantiate (1 := sizeof tuchar * (i * n + n - 1 - (n - 1))). simpl. lia. entailer!.
                - apply matrix_bounds_within; lia. } 
              { forward.
                { entailer!. rewrite arr_field_address0; auto. lia. }
                { (*simplify if condition*)
                  assert_PROP (field_address (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s = 
                    (field_address0 (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s)). { entailer!.
                  rewrite arr_field_address; auto; try lia. rewrite arr_field_address0; auto; try lia. }
                  rewrite H6 in HRE; clear H6.
                  assert_PROP (j < n). { entailer!. 
                   rewrite ptr_comparison_gt_iff in HRE; auto; simpl; lia. } rename H6 into Hjn; clear HRE.
                  (*simplify n so we can dereference*)
                   assert_PROP ((force_val (sem_binary_operation' Osub (tptr tuchar) tint
                  (field_address0 (tarray tuchar (m * n)) [ArraySubsc (i * n + n - j)] s)
                  (Vint (Int.repr 1)))) = field_address (tarray tuchar (m * n)) (SUB (i * n + n - 1 - j)) s). {
                  entailer!. rewrite arr_field_address0; auto; try lia. rewrite sem_sub_pi_offset; auto; try rep_lia.
                  rewrite arr_field_address; auto; try lia. f_equal; simpl; lia. } rewrite H6; clear H6.
                  (*length goal*)
                  assert_PROP (0 <= i * n + n - 1 - j < Zlength (map Int.repr
                    (flatten_mx (scalar_mul_row_partial (F:=F)  (all_lc_one_rows_partial (F:=F) 
                    (gauss_all_steps_rows_partial (F:=F) mx m m) i) i aii_inv j)))). {
                   entailer!. assert (0 <= i * n + n - 1 - j < m * n) by (apply matrix_bounds_within; lia).
                   list_solve. }
                  rewrite Zlength_map in H6. 
                  forward.
                  { entailer!. rewrite (@flatten_mx_Znth m n); try lia. 2: solve_wf.
                    rewrite unsigned_repr; solve_qpoly_bounds. }
                  { rewrite (@flatten_mx_Znth m n); [ | solve_wf | lia | lia].
                    remember ((get (F:=F)(scalar_mul_row_partial (F:=F)  (all_lc_one_rows_partial (F:=F)
                              (gauss_all_steps_rows_partial (F:=F) mx m m) i) i aii_inv j) i j)) as aij.
                    forward_call.
                    { rewrite_repr aij. rewrite_repr aii_inv. rewrite_zbits aij. rewrite_zbits aii_inv. 
                      split; solve_qpoly_bounds. }
                    { rewrite_repr aij. rewrite_repr aii_inv. rewrite_zbits aij. rewrite_zbits aii_inv.
                      forward. (*loop invariant preservation*)
                      Exists (j+1). entailer!.
                      { rewrite arr_field_address0; auto; try lia. rewrite arr_field_address; auto; try lia. f_equal; lia. }
                      { rewrite !poly_of_int_inv. 
                        remember ((get (F:=F) (scalar_mul_row_partial (F:=F)
                        (all_lc_one_rows_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m m) i)i
                        (find_inv mod_poly modulus_poly_deg_pos(get (F:=F)
                        (all_lc_one_rows_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m m) i) i i)) j) i j)) as aij.
                         remember ((find_inv mod_poly modulus_poly_deg_pos (get (F:=F)
                         (all_lc_one_rows_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m m) i)
                         i i))) as aii_inv.
                        rewrite (@scalar_mul_row_plus_1 F _ m n); try lia. 2: solve_wf.
                        replace (ssralg.GRing.mul (R:=ssralg.GRing.Field.ringType F)) with  
                          (r_mul _ modulus_poly_deg_pos) by reflexivity. unfold r_mul. unfold poly_mult_mod.
                        rewrite !upd_Znth_map.
                        rewrite <- (@flatten_mx_set m n); try lia. 2: solve_wf. simpl.
                        rewrite Heqaij. rewrite poly_mult_comm.
                        rewrite (@scalar_mul_row_outside _ m n); try lia. cancel. solve_wf. }
                    }
                  }
                }
              }
              { (*end of outer loop*) forward. Exists (i+1). entailer!.
                f_equal; unfold Int.zero_ext; f_equal.
                rewrite unsigned_repr; [rewrite zbits_small; rep_lia | rep_lia].
                rewrite all_lc_one_plus_one; [| lia]. unfold scalar_mul_row.
                (*need to know that j = n*)
                assert (Haddr: (field_address (tarray tuchar (m * n)) 
                    [ArraySubsc (i * n + n - 1 - (n - 1))] s) =
                    (field_address0 (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s)). {
                 rewrite arr_field_address; auto; try lia. rewrite arr_field_address0; auto; try lia. }
                rewrite Haddr in HRE; clear Haddr.
                assert (Hjn: j >= n). {
                  (*TODO: make separate lemma and replace both*)
                  assert (Hft: forall a b, typed_false a b -> ~(typed_true a b)). { intros a b F T.
                  unfold typed_true in T; unfold typed_false in F; rewrite T in F; inversion F. }
                  apply Hft in HRE; clear Hft. rewrite (not_iff_compat) in HRE. 2: {
                  rewrite ptr_comparison_gt_iff. reflexivity. all: auto. all: simpl; lia. }
                  lia. } 
                  assert (j = n) by lia. subst; clear Hjn HRE. 
                  assert (Hlenn: (Zlength (Znth i (all_lc_one_rows_partial (F:=F)
                          (gauss_all_steps_rows_partial (F:=F) mx m m) i))) = n).
                  { assert (Hwf' : wf_matrix (all_lc_one_rows_partial (F:=F)
                          (gauss_all_steps_rows_partial (F:=F) mx m m) i) m n) by solve_wf.
                    destruct Hwf' as [Hlen [Hn0 Hin]].
                    apply Hin. apply Znth_In; lia. }
                   rewrite Hlenn.
                   replace (ssralg.GRing.inv (R:=ssralg.GRing.Field.unitRingType F)) with 
                  (find_inv _ modulus_poly_deg_pos) by reflexivity.
                   rewrite (@all_lc_one_outside _ m n); try lia. cancel. solve_wf.
              }
            }
          }
        }
      }
      { forward. entailer!. replace i with (m-1) by lia. cancel. }
    }
    { forward. }
  }
Qed.

