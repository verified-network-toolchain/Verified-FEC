Require Import VST.floyd.proofauto.

Require Import fec.
Require Import Common.
Require Import Specs.

Import WPoly.

Set Bullet Behavior "Strict Subproofs".

(** Verification of [fec_matrix_transform]*)

Lemma body_fec_matrix_transform : semax_body Vprog Gprog f_fec_matrix_transform fec_matrix_transform_spec.
Proof.
  start_function. destruct H as [Hmn [Hnbound [Hwf Hstr]]].
  forward_loop (EX (row : Z),
    PROP (0 <= row <= m)
    LOCAL (temp _k (Vint (Int.repr (row))); temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n));
      gvars gv)
    SEP(data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
   data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
   data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
   data_at Ews (tarray tuchar (m * n))
     (map Vint (map Int.repr (flatten_mx 
        (gauss_all_steps_rows_partial mx m row )))) s))
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
{ Intros gauss_step_row. forward_if.
  { (*body of outer loop *) 
    (*now there are 2 inner loops; the first is [all_cols_one_partial]*)
    forward_loop 
    (EX (row : Z),
      PROP (0 <= row <= m)
      LOCAL (temp _i (Vint (Int.repr (row))); temp _k (Vint (Int.repr gauss_step_row)); temp _p s; 
      temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); gvars gv)
      SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
        data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
        data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr 
          (flatten_mx (all_cols_one_partial 
            (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row row )))) s))
      break: (PROP ()
        LOCAL (temp _k (Vint (Int.repr gauss_step_row)); temp _p s; 
      temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); gvars gv)
      SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
        data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
        data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr 
          (flatten_mx (all_cols_one_partial 
            (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row m )))) s)).
    { forward. Exists 0%Z. entailer!. }
    { Intros cols_one_row. forward_if.
      { forward. (*Want to simplify pointer in q*)
        assert_PROP ((force_val (sem_binary_operation' Osub (tptr tuchar) tint
          (eval_binop Oadd (tptr tuchar) tuchar (eval_binop Oadd (tptr tuchar) tint s
           (eval_binop Omul tuchar tuchar (Vint (Int.repr cols_one_row))
           (Vint (Int.repr n)))) (Vint (Int.repr n))) (Vint (Int.repr 1)))) =
           (offset_val (((cols_one_row * n) + n) - 1) s)). { entailer!.
        rewrite sem_sub_pi_offset; auto. rep_lia. }
        rewrite H3. clear H3.
        forward.
        { entailer!. rewrite sem_sub_pi_offset; auto; try rep_lia. }
        { (*Now, we will simplify pointer in m*)
          assert_PROP ((force_val
               (sem_binary_operation' Oadd (tptr tuchar) tint
                  (eval_binop Osub (tptr tuchar) tuchar (offset_val (cols_one_row * n + n - 1) s)
                     (Vint (Int.repr n))) (Vint (Int.repr 1)))) =
            offset_val (cols_one_row * n) s). { entailer!.
          rewrite sem_sub_pi_offset; auto; try rep_lia. f_equal. simpl. rewrite sem_add_pi_ptr_special; auto;
          try rep_lia. simpl. rewrite offset_offset_val. f_equal. lia. }
          rewrite H3; clear H3.
          assert_PROP ((offset_val (cols_one_row * n) s) = field_address (tarray tuchar (m * n)) 
            (SUB ((cols_one_row * n) + n - 1 - (n-1))) s). { entailer!. rewrite arr_field_address; auto.
            simpl. f_equal. lia. apply (matrix_bounds_within); lia. } rewrite H3; rename H3 into Hm_offset. 
          forward.
          assert (Hwf' : wf_matrix (F:=F) (all_cols_one_partial (F:=F) 
            (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row cols_one_row) m n). {
          apply all_cols_one_partial_wf. lia. apply gauss_all_steps_rows_partial_wf. lia. assumption. }
        (*Now we are at the while loop - because of the [strong_inv] condition of the matrix,
          the loop guard is false (the loop finds the element to swap if one exists, but returns
          with an error whether or not one exists*)
        (*Because of this, we give a trivial loop invariant*)
        remember ((PROP ( )
           LOCAL (temp _w (Vint (Int.zero_ext 8 (Int.repr cols_one_row)));
           temp _m (field_address (tarray tuchar (m * n)) [ArraySubsc (cols_one_row * n + n - 1 - (n - 1))] s);
           temp _q (offset_val (cols_one_row * n + n - 1) s);
           temp _i (Vint (Int.repr cols_one_row)); temp _k (Vint (Int.repr gauss_step_row)); 
           temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); 
           gvars gv)
           SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
           data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
           data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
           data_at Ews (tarray tuchar (m * n))
             (map Vint
                (map Int.repr
                   (flatten_mx
                      (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row)
                         gauss_step_row cols_one_row)))) s))) as x.
         forward_loop x break: x; subst. (*so I don't have to write it twice*)
        { entailer!. }
        { assert_PROP (force_val (sem_sub_pi tuchar Signed 
            (offset_val (cols_one_row * n + n - 1) s) (Vint (Int.repr gauss_step_row))) =
            offset_val (cols_one_row * n + n - 1 - gauss_step_row) s). { entailer!.
           rewrite sem_sub_pi_offset;auto. simpl. f_equal. lia. rep_lia. }
           (*TODO: will need more general stuff probably*)
           assert (0 <= cols_one_row * n + n - 1 - gauss_step_row < m * n). {
            apply matrix_bounds_within; lia. }
           assert_PROP (force_val (sem_sub_pi tuchar Signed 
            (offset_val (cols_one_row * n + n - 1) s) (Vint (Int.repr gauss_step_row))) =
            field_address (tarray tuchar (m * n)) (SUB  (cols_one_row * n + n - 1 - gauss_step_row)) s). {
            entailer!. rewrite H3. rewrite arr_field_address; auto. simpl. f_equal. lia. }
            clear H3.
           assert_PROP ((0 <= cols_one_row * n + n - 1 - gauss_step_row <
              Zlength (map Int.repr (flatten_mx
              (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row)
              gauss_step_row cols_one_row))))). {
           entailer!. list_solve. } simpl_reptype. rewrite Zlength_map in H3.
           forward.
          { entailer!. rewrite (@flatten_mx_Znth m n); try lia. 
            pose proof (qpoly_int_bound (get (F:=F) (all_cols_one_partial (F:=F) 
                (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row cols_one_row) 
                cols_one_row gauss_step_row)). rewrite Int.unsigned_repr; rep_lia. assumption. }
          { entailer!. rewrite sem_sub_pi_offset; auto. rep_lia. }
          { forward_if.
            { (*contradiction due to [strong_inv]*)
              assert (Znth (cols_one_row * n + n - 1 - gauss_step_row)
                (flatten_mx (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row)
                gauss_step_row cols_one_row)) <> 0%Z). {
              rewrite (@flatten_mx_Znth m n); try lia. 2: assumption. intro Hzero.
              rewrite poly_to_int_zero_iff in Hzero. 
              assert (Hrm : 0 <= gauss_step_row < m) by lia.
              assert (Hcm : 0 <= cols_one_row < m) by lia.
              apply (gauss_all_steps_columns_partial_zeroes_list Hrm H1 (proj2 Hmn) Hwf Hstr Hcm). 
              replace (ssralg.GRing.zero (ssralg.GRing.Field.zmodType F)) with (q0 modulus_poly_deg_pos) by reflexivity.
              destruct ((get (F:=F)
              (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row)
                gauss_step_row cols_one_row) cols_one_row gauss_step_row)) eqn : G. unfold q0. unfold r0. exist_eq.
              simpl in Hzero. assumption. } 
              apply mapsto_memory_block.repr_inj_unsigned in H6. contradiction. 2: rep_lia.
              rewrite (@flatten_mx_Znth m n); try lia. eapply Z_expand_bounds.
              3 : { apply qpoly_int_bound. } lia. rep_lia. assumption. }
            { forward. entailer!. }
          }
        }
      { (*after the while loop*)
         assert_PROP (force_val (sem_sub_pi tuchar Signed 
            (offset_val (cols_one_row * n + n - 1) s) (Vint (Int.repr gauss_step_row))) =
            field_address (tarray tuchar (m * n)) (SUB  (cols_one_row * n + n - 1 - gauss_step_row)) s). {
            entailer!. rewrite sem_sub_pi_offset;auto. simpl. rewrite arr_field_address; auto. simpl. f_equal. lia.
            apply matrix_bounds_within; lia. rep_lia. } 
         assert (0 <= cols_one_row * n + n - 1 - gauss_step_row < m * n). {
            apply matrix_bounds_within; lia. }
         assert_PROP ((0 <= cols_one_row * n + n - 1 - gauss_step_row <
          Zlength (map Int.repr (flatten_mx
         (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row)
            gauss_step_row cols_one_row))))). entailer!. list_solve. rewrite Zlength_map in H5.
         (*Doing some stuff to simplify here so we don't need to repeat this in each branch*)
         pose proof (Hpolybound:= (qpoly_int_bound (get (F:=F) (all_cols_one_partial (F:=F) 
                (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row cols_one_row) 
                cols_one_row gauss_step_row))).
          forward; try rewrite (@flatten_mx_Znth m n); try lia; try assumption.
        { entailer!. lia. }
        { entailer!. rewrite sem_sub_pi_offset; auto. rep_lia. }
        { forward.
          { entailer!. apply modulus_poly_bound. apply (@ssrfun.svalP _ (fun x => deg x < deg mod_poly)). }
          { entailer!. rewrite inverse_contents_Znth. rewrite poly_of_int_inv.
            simpl. rewrite unsigned_repr. unfold poly_inv. apply (proj2 (qpoly_int_bound _)).
            unfold poly_inv. split. apply (proj1 (qpoly_int_bound _)). eapply Z.le_lt_trans.
            apply (proj2 (qpoly_int_bound _)). rep_lia. apply modulus_poly_bound.
            apply (@ssrfun.svalP _ (fun x => deg x < deg mod_poly)). }
          { forward. (*simplify before for loop*)
            rewrite inverse_contents_Znth. 2 : { apply modulus_poly_bound.
            apply (@ssrfun.svalP _ (fun x => deg x < deg mod_poly)). } rewrite poly_of_int_inv. simpl.
            remember (get (F:=F) (all_cols_one_partial (F:=F)
                      (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row
                       cols_one_row) cols_one_row gauss_step_row) as qij eqn : Hqij. 
            remember (proj1_sig qij) as pij eqn : Hpij.
            (*assert_PROP ((offset_val (cols_one_row * n + n - 1) s) = 
              field_address (tarray tuchar (m * n)) (SUB (cols_one_row * n + n - 1)) s). {
            entailer!. rewrite arr_field_address. simpl. f_equal. lia. auto. 
            pose proof (matrix_bounds_within m n cols_one_row 0). lia. } rewrite H6. clear H6.*)
            remember (find_inv mod_poly modulus_poly_deg_pos qij) as qij_inv eqn : Hqinv.
            replace (poly_inv mod_poly modulus_poly_deg_pos pij) with (proj1_sig qij_inv). 2 : {
            unfold poly_inv. rewrite Hpij. rewrite poly_to_qpoly_unfold. rewrite Hqinv. reflexivity. }
            (*Scalar multiplication loop*)
            (*Unfortunately, lots of duplication here: can we save locals in a variable?*)
            forward_loop (EX (j : Z),
            PROP (0 <= j <= n)
            LOCAL (temp _inv (Vint (Int.zero_ext 8 (Int.repr (poly_to_int (proj1_sig qij_inv)))));
              temp _t'11 (Vint (Int.repr (poly_to_int (proj1_sig qij_inv))));
              temp _t'10 (Vint (Int.repr (poly_to_int pij)));
              temp _w (Vint (Int.zero_ext 8 (Int.repr cols_one_row)));
              temp _m (field_address (tarray tuchar (m * n)) [ArraySubsc (cols_one_row * n + n - 1 - (n - 1))] s);
              (*temp _q (field_address (tarray tuchar (m * n)) [ArraySubsc (cols_one_row * n + n - 1)] s);*)
              temp _q (offset_val (cols_one_row * n + n - 1) s);
              temp _i (Vint (Int.repr cols_one_row)); temp _k (Vint (Int.repr gauss_step_row)); 
              temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); 
              gvars gv;
              (*temp _n (field_address0 (tarray tuchar (m * n)) (SUB (cols_one_row * n + n - 1 - j)) s))*)
              temp _n (offset_val (cols_one_row * n + n - 1 - j) s))
            SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
                 data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
                 data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
                 data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr
                  (flatten_mx (scalar_mul_row_partial (all_cols_one_partial (F:=F) 
                    (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row cols_one_row) 
                    cols_one_row qij_inv j)))) s))
            break: (PROP ()
              LOCAL (temp _inv (Vint (Int.zero_ext 8 (Int.repr (poly_to_int (proj1_sig qij_inv)))));
              temp _t'11 (Vint (Int.repr (poly_to_int (proj1_sig qij_inv))));
              temp _t'10 (Vint (Int.repr (poly_to_int pij)));
              temp _w (Vint (Int.zero_ext 8 (Int.repr cols_one_row)));
              temp _m (field_address (tarray tuchar (m * n)) [ArraySubsc (cols_one_row * n + n - 1 - (n - 1))] s); 
              temp _q (field_address (tarray tuchar (m * n)) [ArraySubsc (cols_one_row * n + n - 1)] s);
              temp _i (Vint (Int.repr cols_one_row)); temp _k (Vint (Int.repr gauss_step_row)); 
              temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); 
              gvars gv)
              SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
                 data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
                 data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
                 data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr
                  (flatten_mx (scalar_mul_row (all_cols_one_partial (F:=F) 
                    (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row cols_one_row) 
                    cols_one_row qij_inv)))) s)).
            { forward. Exists 0%Z. entailer!. rewrite scalar_mul_row_partial_0. cancel. }
            { Intros j. (*TODO: this still doesn't quite work because when the loop exits, n is too small and so the
                          if conditions doesn't typecheck*)


