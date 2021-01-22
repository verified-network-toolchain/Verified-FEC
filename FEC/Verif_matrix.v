Require Import VST.floyd.proofauto.

Require Import fec.
Require Import Common.
Require Import Specs.

Import WPoly.

Set Bullet Behavior "Strict Subproofs".

(*TODO: move probably*)

Lemma lt_plus_lt: forall z1 z2 z3, 
  0 <= z1 -> 
  z1 + z2 < z3 -> 
  z2 < z3.
Proof.
  intros z1 z2 z3 Hz1 Hz12. rewrite Z.lt_add_lt_sub_r in Hz12. lia.
Qed.

(*Transform the "if" condition in a pointer comparison into something usable (for the gt case)*)
Lemma ptr_comparison_gt_iff: forall t size p i j,
  field_compatible (tarray t size) [] p ->
  0 <= i <= size ->
  0 <= j <= size ->
  0 < sizeof t ->
  isptr p ->
  typed_true tint (force_val (sem_cmp_pp Cgt (field_address0 (tarray t size) (SUB i) p)
    (field_address0 (tarray t size) (SUB j) p))) <-> i > j.
Proof.
  intros t size p i j Hcomp Hi Hj Hszof Hptr.
  assert (Hptri : isptr (field_address0 (tarray t size) [ArraySubsc i] p)).
  apply field_address0_isptr. apply arr_field_compatible0; auto.
  assert (Hptrj: isptr (field_address0 (tarray t size) [ArraySubsc j] p)).
  apply field_address0_isptr. apply arr_field_compatible0; auto.
  rewrite force_sem_cmp_pp; auto. unfold compare_pp.
  destruct (field_address0 (tarray t size) [ArraySubsc i] p) eqn : Fi; inversion Hptri.
  destruct (field_address0 (tarray t size) [ArraySubsc j] p) eqn : Fj; inversion Hptrj.
  clear Hptri Hptrj.
  assert (Hsame: sameblock (Vptr b i0) (Vptr b0 i1) = true). { rewrite <- Fi. rewrite <- Fj.
  rewrite !arr_field_address0; auto. eapply sameblock_trans. apply sameblock_symm.
  all: apply  isptr_offset_val_sameblock; auto. } 
  simpl in Hsame. unfold eq_block. destruct (peq b b0); try inversion Hsame. subst. clear Hsame.
  simpl. rewrite arr_field_address0 in Fi; auto. rewrite arr_field_address0 in Fj; auto.
  destruct p; inversion Hptr. simpl in *. inversion Fi; subst. inversion Fj; subst.
  clear Fi Fj Hptr. unfold Ptrofs.ltu.
  assert (Hi2 : 0 <= Ptrofs.unsigned i2) by rep_lia. unfold field_compatible in Hcomp. 
  destruct Hcomp as [Ht [Hcomp [HHsz Hrest]]]. simpl in HHsz.
  replace (Z.max 0 size) with size in HHsz by lia.
  (*We will use these a bunch of times*)
  assert (Hij: forall k, 0 <= k <= size -> 0 <= sizeof t * k < Ptrofs.modulus). {
    intros k Hk. unfold sizeof in *. split. lia.
    assert (Ctypes.sizeof t * k <= Ctypes.sizeof t * size).  apply Z.mul_le_mono_pos_l; lia.
    assert (Ctypes.sizeof t * size < Ptrofs.modulus). apply (lt_plus_lt (Ptrofs.unsigned i2)). lia. assumption.
    lia. } 
  assert (Hij' : forall k, 0 <= k <= size ->
      0 <= Ptrofs.unsigned i2 + Ptrofs.unsigned (Ptrofs.repr (sizeof t * k)) < Ptrofs.modulus). {
    intros k Hk. unfold sizeof in *. rewrite Ptrofs.unsigned_repr_eq. rewrite Zmod_small.
    2: apply Hij; lia. split. lia. 
    assert (Ptrofs.unsigned i2 + Ctypes.sizeof t * k <= Ptrofs.unsigned i2 + Ctypes.sizeof t * size).
    apply Zplus_le_compat_l. apply Z.mul_le_mono_nonneg_l; lia. eapply Z.le_lt_trans. apply H. assumption. }
  unfold Ptrofs.unsigned. simpl. rewrite !Ptrofs.Z_mod_modulus_eq. rewrite !Zmod_small.
  all: try apply Hij'; auto.
  destruct (zlt (Ptrofs.unsigned i2 + Ptrofs.unsigned (Ptrofs.repr (sizeof t * j)))
          (Ptrofs.unsigned i2 + Ptrofs.unsigned (Ptrofs.repr (sizeof t * i)))).
    - assert (Hptrlt: Ptrofs.unsigned (Ptrofs.repr (sizeof t * j)) < Ptrofs.unsigned (Ptrofs.repr (sizeof t * i))) by lia.
      clear l. unfold Ptrofs.unsigned in Hptrlt. simpl in Hptrlt. rewrite !Ptrofs.Z_mod_modulus_eq in Hptrlt.
      rewrite !Zmod_small in Hptrlt. rewrite <- Z.mul_lt_mono_pos_l in Hptrlt; auto. all: try apply Hij; auto.
      split; intros; auto. lia. reflexivity.
    - assert (Hptrlt: Ptrofs.unsigned (Ptrofs.repr (sizeof t * i)) <= Ptrofs.unsigned (Ptrofs.repr (sizeof t * j))) by lia.
      clear g. unfold Ptrofs.unsigned in Hptrlt. simpl in Hptrlt. rewrite !Ptrofs.Z_mod_modulus_eq in Hptrlt.
      rewrite !Zmod_small in Hptrlt. rewrite <- Z.mul_le_mono_pos_l in Hptrlt; auto. all: try apply Hij; auto.
      split; intros; try lia. inversion H.
Qed.

Ltac solve_qpoly_bounds :=
  let pose_bounds p :=
    pose proof (modulus_poly_bound (proj1_sig p) (@ssrfun.svalP _ (fun y => deg y < deg mod_poly) p));
    pose proof fec_n_eq; rep_lia in
  match goal with
  | [H: _ |- poly_to_int (proj1_sig ?p) <= ?x] => pose_bounds p
  | [H: _ |- 0 <= poly_to_int (proj1_sig ?p) <= ?x] => pose_bounds p
  | [H: _ |- 0 <= poly_to_int (proj1_sig ?p) < ?x] => pose_bounds p
  end.

(** Verification of [fec_matrix_transform]*)

Lemma body_fec_matrix_transform : semax_body Vprog Gprog f_fec_matrix_transform fec_matrix_transform_spec.
Proof.
  start_function. destruct H as [Hmnpos [Hmn [Hnbound [Hwf Hstr]]]].
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
            (gauss_all_steps_rows_partial (F:=F) mx m k) k i) m n). {
          apply all_cols_one_partial_wf. lia. apply gauss_all_steps_rows_partial_wf. lia. assumption. }
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
                i k)). rewrite Int.unsigned_repr; rep_lia. assumption. }
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
            rewrite inverse_contents_Znth. 2: solve_qpoly_bounds.  rewrite poly_of_int_inv. simpl.
            remember (get (F:=F) (all_cols_one_partial (F:=F)
                      (gauss_all_steps_rows_partial (F:=F) mx m k) k i) i k) as qij eqn : Hqij. 
            remember (proj1_sig qij) as pij eqn : Hpij.
            remember (find_inv mod_poly modulus_poly_deg_pos qij) as qij_inv eqn : Hqinv.
            replace (poly_inv mod_poly modulus_poly_deg_pos pij) with (proj1_sig qij_inv). 2 : {
            unfold poly_inv. rewrite Hpij. rewrite poly_to_qpoly_unfold. rewrite Hqinv. reflexivity. }
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
            LOCAL (temp _inv (Vint (Int.zero_ext 8 (Int.repr (poly_to_int (proj1_sig qij_inv)))));
              temp _t'11 (Vint (Int.repr (poly_to_int (proj1_sig qij_inv))));
              temp _t'10 (Vint (Int.repr (poly_to_int pij)));
              temp _w (Vint (Int.zero_ext 8 (Int.repr i)));
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
              LOCAL (temp _inv (Vint (Int.zero_ext 8 (Int.repr (poly_to_int (proj1_sig qij_inv)))));
              temp _t'11 (Vint (Int.repr (poly_to_int (proj1_sig qij_inv))));
              temp _t'10 (Vint (Int.repr (poly_to_int pij)));
              temp _w (Vint (Int.zero_ext 8 (Int.repr i)));
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
                  (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m k) k i) i qij_inv j) m n). 
                { apply scalar_mul_row_partial_wf; try lia. auto. }
                forward.
                - entailer!. rewrite (@flatten_mx_Znth m n); try lia.
                  rewrite unsigned_repr; solve_qpoly_bounds. auto. 
                - rewrite (@flatten_mx_Znth m n); try lia; auto.
                  forward_call.
                  + rewrite !Zbits.Zzero_ext_mod; [| lia| lia]. 
                    rewrite Int.zero_ext_mod; [| rep_lia].
                    split; rewrite unsigned_repr; replace (two_p 8) with (256) by reflexivity; 
                    try rewrite Zmod_small; try rewrite Zmod_small;  simpl; solve_qpoly_bounds.
                  + (*simplify result of function call*)
                    rewrite !Zbits.Zzero_ext_mod; [| lia | lia].
                    rewrite Int.zero_ext_mod; [| rep_lia]. replace (two_p 8) with (256) by reflexivity.
                    rewrite !unsigned_repr; [| solve_qpoly_bounds| solve_qpoly_bounds]. 
                    rewrite Zmod_small; [| solve_qpoly_bounds].
                    replace (poly_to_int (proj1_sig qij_inv) mod 256) with (poly_to_int (proj1_sig qij_inv))
                    by (rewrite Zmod_small; [reflexivity | solve_qpoly_bounds]).
                    rewrite Zmod_small; [| solve_qpoly_bounds]. rewrite !poly_of_int_inv.
                    forward. Exists (j+1). entailer!.
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
                  rewrite H31 in H7; clear H31.
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
            { f_equal. unfold Int.zero_ext. f_equal. rewrite Zbits.Zzero_ext_mod; try lia.
              replace (two_p 8) with (256) by reflexivity. rewrite Z.mod_small; rewrite unsigned_repr; rep_lia. }
            { rewrite all_cols_one_plus_1; try lia. 
              replace (ssralg.GRing.inv (R:=ssralg.GRing.Field.unitRingType F)) with (find_inv _ modulus_poly_deg_pos) by reflexivity.
              rewrite (@all_cols_one_outside F m n); try lia. cancel.
              apply gauss_all_steps_rows_partial_wf; try lia; assumption. } } } } } }
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
        forward_if True. (*TODO: see*)
        { (*when i != k*)
          forward. (*simplify q*)
          assert_PROP ((force_val (sem_binary_operation' Osub (tptr tuchar) tint
            (eval_binop Oadd (tptr tuchar) tuchar (eval_binop Oadd (tptr tuchar) tint s
            (eval_binop Omul tuchar tuchar (Vint (Int.repr i)) (Vint (Int.repr n))))
            (Vint (Int.repr n))) (Vint (Int.repr 1)))) =
            offset_val (i * n + n - 1) s). { entailer!. rewrite sem_sub_pi_offset; auto. rep_lia. }
          rewrite H4; clear H4.
          forward_for (fun (j : Z) => PROP (0 <= j <= m)
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
           { (*beginning of subtraction loop*) forward. Exists 0%Z. entailer!.
             
    


)))
     s))
          



        }
      }
      { (*i >= m (end of loop)*) }


    }
    { (*postcondition of subtract all rows loop*) admit. } 


    forward_for_simple_bound n 
    


























  