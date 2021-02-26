Require Import VST.floyd.proofauto.

Require Import fec.
Require Import Common.
Require Import CommonVST.
Require Import VandermondeList.
Require Import Specs.
Require Import Poly.
Require Import FECTactics.

Set Bullet Behavior "Strict Subproofs".

(** Verification of [rse_init]*)
(*This is an extremely simple function that just calls fec_generate_math_tables and fec_generate_weights*)
Lemma body_rse_init : semax_body Vprog Gprog f_rse_init rse_init_spec.
Proof.
  start_function. forward_call. forward_call. entailer!.
Qed.

(** Verification of [fec_generate_weights]*)
Lemma body_fec_generate_weights : semax_body Vprog Gprog f_fec_generate_weights fec_generate_weights_spec.
Proof.
  pose proof (mod_poly_PosPoly) as Hpospoly.
  pose proof (mod_poly_PrimPoly) as Hprimpoly.
  start_function. freeze Ftrace := (data_at _ _ _ (gv _trace)).
    forward_loop (EX (i : Z) (l: list (list Z)),
    PROP (0 <= i <= fec_max_h /\ Zlength l = fec_max_h /\ Forall (fun x => Zlength x = fec_n - 1) l /\
        forall (x: Z), 0 <= x < i -> (forall (y: Z), 0 <= y < fec_n - 1 -> Znth y (Znth x l) = 
        poly_to_int ((monomial (Z.to_nat (x * y)) %~ mod_poly ))))
    LOCAL (gvars gv; temp _i (Vint (Int.repr i)))
    SEP (FRZL Ftrace; FIELD_TABLES gv;
        data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (map_int_val_2d l) (gv _fec_weights)))
    break:
      (PROP ()
      LOCAL (gvars gv)
      SEP (data_at Ews tint (Vint (Int.zero)) (gv _trace); FIELD_TABLES gv;
          data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) 
          (rev_mx_val (weight_mx_list fec_max_h (fec_n - 1)))  (gv _fec_weights))). 
  - forward. Exists 0%Z. Exists (list_repeat (Z.to_nat fec_max_h) (list_repeat (Z.to_nat (fec_n - 1)) 0%Z)).
    entailer!. split. rewrite Zlength_list_repeat'. rep_lia. rewrite Forall_forall. intros x Hin.
    apply in_list_repeat in Hin. subst. rewrite Zlength_list_repeat'. rep_lia. unfold map_int_val_2d. unfold map_2d.
    rewrite !map_list_repeat. cancel. 
  - Intros i. Intros l. forward_if.
    + forward_loop (EX (j : Z) (l: list (list Z)),
         PROP (0 <= j <= fec_n - 1 /\ Zlength l = fec_max_h /\ Forall (fun x => Zlength x = fec_n - 1) l  /\
      (forall (x y: Z), (0 <= x < i /\ 0 <= y < fec_n - 1) \/ (x = i /\ 0 <= y < j) -> Znth y (Znth x l) = 
        poly_to_int ((monomial (Z.to_nat (x * y)) %~ mod_poly ))))
      LOCAL (gvars gv; temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)))
      SEP (FRZL Ftrace; FIELD_TABLES gv;
           data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (map_int_val_2d l) (gv _fec_weights)))
      break: (EX (l: list (list Z)),
        (PROP (Zlength l = fec_max_h /\ Forall (fun x => Zlength x = fec_n - 1) l /\
          forall (x: Z), 0 <= x <= i -> (forall (y: Z), 0 <= y < fec_n - 1 -> Znth y (Znth x l) = 
          poly_to_int ((monomial (Z.to_nat (x * y)) %~ mod_poly ))))
        LOCAL (gvars gv; temp _i (Vint (Int.repr i)))
        SEP (FRZL Ftrace; FIELD_TABLES gv;
             data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (map_int_val_2d l) (gv _fec_weights)))).
      * forward. Exists 0%Z. Exists l. entailer!. intros x y [Hbefore | Hcont]. apply H2; lia. lia.
      * Intros j. Intros lj. forward_if.
        -- (*Want to simplify the index*)
            assert (Hprod: 0 <= (i * j) mod 255 < fec_n). {  pose proof (Z.mod_pos_bound (i * j) 255). rep_lia. }
            assert (Hidx : Int.signed (Int.mods (Int.repr (i * j)) (Int.repr 255)) = (i * j) mod 255). {
              assert (Int.min_signed <= i * j <= Int.max_signed). {
              split. rep_lia. assert (i * j <= fec_max_h * (fec_n - 1)).
              apply Z.mul_le_mono_nonneg; lia. assert (fec_max_h * (fec_n - 1) = 32640). rewrite fec_max_h_eq.
              rewrite fec_n_eq. reflexivity. rep_lia. }
              unfold Int.mods. rewrite !Int.signed_repr; try rep_lia. rewrite Z.rem_mod_nonneg by rep_lia.
              reflexivity. rewrite !Int.signed_repr by rep_lia. pose proof (Z.rem_bound_pos_pos (i * j) 255). rep_lia. }
            unfold FIELD_TABLES. unfold INDEX_TABLES. Intros.
            forward.
          ++ entailer!. simpl. rewrite Hidx. assumption. 
          ++ entailer!. rewrite Hidx. rewrite power_to_index_contents_Znth. simpl. simpl_repr. rep_lia.         
          ++ entailer!. (*Why do I get this goal?*)
             destruct H23. apply repr_inj_signed in H24;  rep_lia.
          ++ simpl. rewrite Hidx. rewrite power_to_index_contents_Znth; [| assumption]. 
             assert_PROP (force_val  (sem_add_ptr_int tuchar Signed
              (force_val (sem_add_ptr_int (tarray tuchar 255) Signed (gv _fec_weights) (Vint (Int.repr i))))
              (Vint (Int.repr j))) = field_address (tarray (tarray tuchar (fec_n - 1)) fec_max_h)  
                [ArraySubsc j; ArraySubsc i] (gv _fec_weights)).
              { entailer!. solve_offset. }
             forward. simpl_repr. forward.
             Exists (j+1). Exists (upd_Znth i lj  (upd_Znth j (Znth i lj)
              (poly_to_int (monomial (Z.to_nat ((i * j) mod 255)) %~ mod_poly)))). entailer!. (*inner loop re establish invariant*)
            ** repeat split.
              --- rewrite upd_Znth_Zlength. auto. rep_lia.
              --- rewrite Forall_Znth. intros i' Hi'. rewrite Zlength_upd_Znth in Hi'.
                  assert (Hii': i = i' \/ i <> i') by lia.
                  destruct Hii' as [Hii' | Hneq]. subst. rewrite upd_Znth_same. 2: rep_lia.
                  rewrite Zlength_upd_Znth. inner_length. rewrite upd_Znth_diff; try lia. inner_length. rep_lia.
              --- intros x y [Hbef | Hcurr]. rewrite upd_Znth_diff by rep_lia. apply H7; lia.
                  destruct Hcurr as [H' Hy]. subst. rewrite upd_Znth_same by rep_lia.
                  assert (Hycase: 0 <= y < j \/ y = j) by lia.
                  assert (Hlen: Zlength (Znth i lj) = fec_n - 1) by inner_length. 
                  destruct Hycase as [Hbefore | Hcurr].
                  rewrite upd_Znth_diff by rep_lia. apply H7; lia. 
                  subst. rewrite upd_Znth_same by rep_lia. f_equal. apply (@monomial_powers_eq_mod _ _ Hprimpoly).
                  rewrite Zmod_mod by lia. assert (Hfsz: Z.to_nat 255 = field_size mod_poly). {
                  apply Nat2Z.inj. rewrite field_size_fec_n. rep_lia. } rewrite Hfsz. apply Nat.mod_mod; lia.
              --- solve_repr_int. 
            ** unfold map_int_val_2d. unfold map_2d. rewrite <- !upd_Znth_map. rewrite !Znth_map. entailer!.
               rep_lia.
        -- (*end of inner loop*) forward. Exists lj. entailer!. intros x Hx y Hy.
           apply H7. rep_lia.
      * Intros lj. forward. Exists (i+1)%Z. Exists lj. entailer!. split.
        -- intros x Hx y Hy. apply H6; lia.
        -- solve_repr_int. 
    + (*end of outer loop*) forward. entailer!.
      assert (Hweight: (map_int_val_2d l) = (rev_mx_val (weight_mx_list fec_max_h (fec_n - 1)))). {
      unfold rev_mx_val. unfold map_int_val_2d. unfold rev_mx. unfold map_2d. unfold map_2d_rev. rewrite !map_map.
      apply Znth_eq_ext.
        - rewrite !Zlength_map. unfold weight_mx_list. unfold mk_matrix; rewrite prop_list_length. lia. rep_lia.
        - intros i' Hi'. rewrite Zlength_map in Hi'. rewrite H0 in Hi'.
          assert (Hfn: 0 <= fec_n - 1) by rep_lia. assert (Hfh: 0 <= fec_max_h) by rep_lia. 
          pose proof (weight_matrix_wf Hfn Hfh) as Hwf.
          destruct Hwf as [Hlen [Hn Hinlen]]. 
          rewrite !Znth_map;[ | | list_solve]. f_equal. f_equal.
          unfold weight_mx_list. unfold mk_matrix; rewrite prop_list_Znth by rep_lia.
          apply Znth_eq_ext.
          + rewrite Zlength_rev. rewrite Zlength_map. rewrite prop_list_length. inner_length. rep_lia. 
          + intros j' Hj'. assert (0 <= j' < fec_n - 1) by (revert Hj'; inner_length).
            rewrite Znth_rev; rewrite !Zlength_map; rewrite !prop_list_length; try rep_lia.
            rewrite !Znth_map; [ | rewrite prop_list_length; rep_lia].
            rewrite prop_list_Znth by rep_lia. rewrite H2 by rep_lia. simpl. repeat f_equal. lia.
          + simpl in *. rep_lia. }
      rewrite Hweight. cancel. thaw Ftrace. cancel. 
  - forward. forward_if True. contradiction. forward. entailer!.
    assert (Hfn: 0 <= fec_n - 1) by rep_lia. assert (Hfh: 0 <= fec_max_h) by rep_lia. 
    pose proof (weight_matrix_wf Hfn Hfh) as Hwf. assert (Hwf' := Hwf).
    destruct Hwf' as [Hlen [Hn Hinlen]].
    forward_call(gv, fec_max_h, fec_n - 1,  (weight_mx_list fec_max_h (fec_n - 1)),
      (gv _fec_weights)).
    + entailer!. simpl. f_equal. solve_repr_int. repeat(f_equal); rep_lia. 
    +  (*need the result about 2d and 1d arrays*) unfold FIELD_TABLES.
      rewrite data_at_2darray_concat. unfold rev_mx_val. unfold map_int_val_2d. rewrite <- map_map.
      unfold map_2d. rewrite <- !concat_map. unfold flatten_mx. rewrite !map_map. cancel.
      simpl_map2d. auto. rewrite Forall_Znth; simpl_map2d. rewrite Hlen. intros i Hi.
      simpl_map2d. rewrite Forall_Znth in Hinlen. apply Hinlen. lia. auto. 
    + repeat(split; try rep_lia; auto).
      unfold strong_inv_list. destruct (range_le_lt_dec 0 0 fec_max_h ); try rep_lia.
      destruct (Z_le_lt_dec fec_max_h (fec_n - 1)); try rep_lia. rewrite weight_mx_list_spec by rep_lia.
      apply Vandermonde.vandermonde_strong_inv.
      apply (ssrbool.introT (ssrnat.leP)). rewrite <- field_size_fec_n. unfold field_size. lia.
    + Intros vret. forward. forward_if. contradiction. forward. 
      assert (Hwf': (wf_matrix (gauss_restrict_rows (F:=F) fec_max_h (fec_n - 1) 
          (weight_mx_list fec_max_h (fec_n - 1))) fec_max_h (fec_n - 1))).
      apply gauss_restrict_rows_wf; solve_wf. assert (Hwf'' := Hwf'). destruct Hwf'' as [Hlen' [Hn' Hinlen']].
      entailer!.
      (*need to go back 1D-> 2D array*)
      rewrite data_at_2darray_concat.
      * apply derives_refl'. f_equal. unfold flatten_mx. unfold rev_mx_val. unfold map_int_val_2d. unfold map_2d.
        unfold rev_mx. unfold map_2d_rev. rewrite !concat_map. rewrite !map_map. f_equal. unfold weight_mx.
        simpl. apply map_ext. intros. rewrite !map_map. reflexivity.
      * simpl_map2d. apply weight_mx_wf.
      * rewrite Forall_Znth. simpl_map2d. intros i Hi. simpl_map2d. pose proof weight_mx_wf as [Hwlen [? Hwinlen]]. 
        inner_length.
      * auto.
Qed.
      
(** Verification of [fec_matrix_transform]*)

Lemma body_fec_matrix_transform : semax_body Vprog Gprog f_fec_matrix_transform fec_matrix_transform_spec.
Proof.
  start_function. destruct H as [Hm0 [Hmnpos [Hmn [Hnbound [Hwf Hstr]]]]].
  forward_loop (EX (k : Z),
    PROP (0 <= k <= m)
    LOCAL (temp _k (Vint (Int.repr (k))); temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n));
      gvars gv)
    SEP(FIELD_TABLES gv;
        data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr (flatten_mx 
          (gauss_all_steps_rows_partial m n mx k )))) s))
    break: (
      PROP ()
      LOCAL (temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); gvars gv)
      SEP(FIELD_TABLES gv;
          data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr (flatten_mx   
            (gauss_all_steps_rows_partial m n mx m )))) s)). 
{ forward. Exists 0%Z. entailer!. }
{ Intros k. forward_if.
  { (*body of outer loop *) 
    (*now there are 2 inner loops; the first is [all_cols_one_partial]*)
    forward_loop 
    (EX (i : Z),
      PROP (0 <= i <= m)
      LOCAL (temp _i (Vint (Int.repr i)); temp _k (Vint (Int.repr k)); temp _p s; 
             temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); gvars gv)
      SEP (FIELD_TABLES gv;
        data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr (flatten_mx (all_cols_one_partial m n
            (gauss_all_steps_rows_partial (F:=F) m n mx k) k i )))) s))
      break: (
        PROP ()
        LOCAL (temp _k (Vint (Int.repr k)); temp _p s; 
               temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); gvars gv)
        SEP (FIELD_TABLES gv;
             data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr (flatten_mx (all_cols_one_partial m n
                (gauss_all_steps_rows_partial (F:=F) m n mx k) k m )))) s)).
    { forward. Exists 0%Z. entailer!. }
    { Intros i. forward_if.
      { forward. pointer_to_offset s.  (*simplify q*)
        forward.
        { entailer!. solve_offset. }
        { pointer_to_offset_with s (i * n).  (*Now, we will simplify pointer in m*)
          forward.
          assert (Hwf' : wf_matrix (F:=F) (all_cols_one_partial (F:=F) m n
            (gauss_all_steps_rows_partial (F:=F) m n mx k) k i) m n) by solve_wf.
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
           SEP (FIELD_TABLES gv;
           data_at Ews (tarray tuchar (m * n))
             (map Vint
                (map Int.repr
                   (flatten_mx
                      (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx k)
                         k i)))) s))) as x.
         forward_loop x break: x; subst. (*so I don't have to write it twice*)
        { entailer!. solve_offset. } 
        {  assert (0 <= i * n + n - 1 - k < m * n). {
            apply matrix_bounds_within; lia. } 
           assert_PROP (force_val (sem_sub_pi tuchar Signed 
            (offset_val (i * n + n - 1) s) (Vint (Int.repr k))) =
            field_address (tarray tuchar (m * n)) (SUB  (i * n + n - 1 - k)) s). { entailer!. solve_offset. }  
           assert_PROP ((0 <= i * n + n - 1 - k <
              Zlength (map Int.repr (flatten_mx
              (all_cols_one_partial m n (F:=F) (gauss_all_steps_rows_partial (F:=F) m n mx k)
              k i))))). {
           entailer!. list_solve. } simpl_reptype. rewrite Zlength_map in H5.
           forward.
          { entailer!. rewrite (@flatten_mx_Znth m n); try lia. simpl_repr. solve_wf. } 
          { entailer!. solve_offset. }
          { forward_if.
            { (*contradiction due to [strong_inv]*)
              assert (Znth (i * n + n - 1 - k)
                (flatten_mx (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx  k)
                k i)) <> 0%Z). {
              rewrite (@flatten_mx_Znth m n); [ |assumption | lia | lia]. intro Hzero.
              rewrite poly_to_int_zero_iff in Hzero. 
              assert (Hrm : 0 <= k < m) by lia.
              assert (Hcm : 0 <= i < m) by lia.
              apply (gauss_all_steps_columns_partial_zeroes_list Hrm H1 (proj2 Hmn) Hwf Hstr Hcm). 
              replace (ssralg.GRing.zero (ssralg.GRing.Field.zmodType F)) with (q0 (f:=mod_poly)) by reflexivity.
              destruct ((get (F:=F)
              (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx k)  k i) i k)) eqn : G.
              unfold q0. unfold r0. exist_eq.
              simpl in Hzero. assumption. } 
              apply mapsto_memory_block.repr_inj_unsigned in H6. contradiction. 2: rep_lia.
              rewrite (@flatten_mx_Znth m n); try lia. solve_poly_bounds. assumption.  }
            { forward. entailer!. }
          }
        }
      { (*after the while loop*)
         assert_PROP (force_val (sem_sub_pi tuchar Signed 
            (offset_val (i * n + n - 1) s) (Vint (Int.repr k))) =
            field_address (tarray tuchar (m * n)) (SUB  (i * n + n - 1 - k)) s). {
            entailer!. solve_offset. }
         assert (0 <= i * n + n - 1 - k < m * n) by nia. 
         assert_PROP ((0 <= i * n + n - 1 - k <
          Zlength (map Int.repr (flatten_mx
         (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx k) k i))))). 
         entailer!. list_solve. rewrite Zlength_map in H5.
         (*Doing some stuff to simplify here so we don't need to repeat this in each branch*)
          forward; try (rewrite (@flatten_mx_Znth m n); try lia; try assumption).
        { entailer!. simpl_repr.  }
        { entailer!. solve_offset.  }
        { unfold FIELD_TABLES. unfold INDEX_TABLES. Intros. (*need for "forward"*)
          assert ((Int.min_signed <= poly_to_int (proj1_sig (get (F:=F) 
            (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx k) k i) i k)) <=
            Int.max_signed)) by solve_poly_bounds. forward.
          { entailer!. solve_poly_bounds. }
          { entailer!. rewrite inverse_contents_Znth. rewrite poly_of_int_inv. simpl. 
            unfold poly_inv. rewrite unsigned_repr. all: solve_poly_bounds. } 
          { forward. forward. (*simplify before for loop*)
            rewrite inverse_contents_Znth by solve_poly_bounds. rewrite poly_of_int_inv. simpl. 
            remember (get (F:=F) (all_cols_one_partial (F:=F) m n
                      (gauss_all_steps_rows_partial (F:=F) m n mx k) k i) i k) as qij eqn : Hqij. 
            remember (find_inv mod_poly qij) as qij_inv eqn : Hqinv.
            replace (poly_inv mod_poly (proj1_sig qij)) with (proj1_sig qij_inv). 2 : {
            unfold poly_inv. rewrite poly_to_qpoly_unfold. rewrite Hqinv. reflexivity. } simpl_repr.
            solve_repr_int. pointer_to_offset_with s (i * n + n). (*simplify pointer in n*)
            assert (Hmn_leq: 0 <= i * n + n <= m * n) by nia. 
            (*Scalar multiplication loop*)
            (*Lots of duplication here, so we save the locals in a variable*)
            remember [temp _inv (Vint (Int.repr (poly_to_int (proj1_sig qij_inv))));
              temp _t'11 (Vint (Int.repr (poly_to_int (proj1_sig qij_inv))));
              temp _t'10 (Vint (Int.repr (poly_to_int (proj1_sig qij))));
              temp _w (Vint (Int.repr i));
              temp _m (field_address (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s);
              temp _i (Vint (Int.repr i)); temp _k (Vint (Int.repr k)); 
              temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); 
              gvars gv ] as LOCALS.
            forward_loop (EX (j : Z),
            PROP (0 <= j <= n)
            (LOCALx (
              temp _n (field_address0 (tarray tuchar (m * n)) (SUB (i * n + n - j)) s) ::
              temp _q (offset_val (i * n + n - 1) s) :: LOCALS)
            (SEP (FIELD_TABLES gv;
                 data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr
                    (flatten_mx (scalar_mul_row_partial m n (all_cols_one_partial (F:=F) m n
                    (gauss_all_steps_rows_partial (F:=F) m n mx k) k i)  i qij_inv j)))) s))%assert5))
            break: (PROP ()
              (LOCALx (temp _q (field_address (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1)] s) :: LOCALS)
              (SEP (FIELD_TABLES gv;
                    data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr
                    (flatten_mx (scalar_mul_row m n (all_cols_one_partial (F:=F) m n 
                    (gauss_all_steps_rows_partial (F:=F) m n mx k) k i) i qij_inv)))) s)))%assert5).
            { Exists 0%Z. rewrite HeqLOCALS. entailer!. solve_offset. 
              rewrite scalar_mul_row_partial_0. unfold FIELD_TABLES. unfold INDEX_TABLES. cancel. solve_wf.  }
            { Intros j. assert (Hcn : 0 <= i * n). { apply Z.mul_nonneg_nonneg; lia. } rewrite HeqLOCALS.
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
              { forward. entailer!. solve_offset.
                assert_PROP ((field_address (tarray tuchar (m * n)) 
                    [ArraySubsc (i * n + n - 1 - (n - 1))] s) =
                    (field_address0 (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s)). {
                entailer!. solve_offset. } 
                rewrite H9 in H8; clear H9.
                assert_PROP (j < n). { entailer!. apply ptr_comparison_gt_iff in H8; auto. all: simpl; lia. }
                clear H8.
                assert_PROP ((force_val
                (sem_binary_operation' Osub (tptr tuchar) tint
                  (field_address0 (tarray tuchar (m * n)) [ArraySubsc (i * n + n - j)] s)
                  (Vint (Int.repr 1)))) = 
                (field_address (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - j)] s)). {
                entailer!. rewrite !arr_field_address0; auto; try lia.
                rewrite !arr_field_address; auto; try lia. solve_offset. } rewrite H8; clear H8. 
                (*Need length bound also*)
                assert_PROP (0 <= i * n + n - 1 - j < Zlength (map Int.repr
                (flatten_mx (scalar_mul_row_partial (F:=F) m n
                (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx k) k i) i qij_inv j)))).
                 { entailer!. list_solve. }
                rewrite Zlength_map in H8.
                assert (Hwf'' : wf_matrix (F:=F) (scalar_mul_row_partial (F:=F) m n
                  (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx k) k i) i qij_inv j) m n)
                by solve_wf.
                forward.
                - entailer!. rewrite (@flatten_mx_Znth m n); try lia. simpl_repr. solve_wf.
                - rewrite (@flatten_mx_Znth m n); try lia; auto.
                  remember ((get (F:=F)
                           (scalar_mul_row_partial (F:=F) m n
                              (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx k)
                                 k i) i qij_inv j) i j)) as aij.
                  forward_call.
                  + unfold FIELD_TABLES. unfold INDEX_TABLES. entailer!.
                  + simpl_repr. subst. split; solve_poly_bounds.
                  + (*simplify result of function call*) simpl_repr.
                    rewrite !poly_of_int_inv. forward. Exists (j+1). rewrite HeqLOCALS. entailer!. solve_offset.
                    unfold FIELD_TABLES. unfold INDEX_TABLES. cancel. 
                    rewrite !upd_Znth_map. (*need to simplify the scalar_mult*)
                    rewrite (@scalar_mul_row_plus_1 F _ m n). simpl_reptype.
                    remember ((scalar_mul_row_partial (F:=F) m n (all_cols_one_partial (F:=F) m n
                      (gauss_all_steps_rows_partial (F:=F) m n mx k) k i) i
                      (find_inv mod_poly (get (F:=F) (all_cols_one_partial (F:=F) m n
                      (gauss_all_steps_rows_partial (F:=F) m n mx k) k i) i k)) j)) as mx'.
                    replace (ssralg.GRing.mul (R:=ssralg.GRing.Field.ringType F)) with
                     (r_mul mod_poly) by reflexivity. unfold r_mul. 
                    unfold poly_mult_mod. 
                    remember ((get (F:=F)(all_cols_one_partial (F:=F) m n
                      (gauss_all_steps_rows_partial (F:=F) m n mx k) k i) i k)) as elt.
                    assert (Hget: (get (F:=F) mx' i j) = (get (F:=F) (all_cols_one_partial (F:=F) m n
                            (gauss_all_steps_rows_partial (F:=F) m n mx k) k i) i j)). {
                     rewrite Heqmx'. rewrite scalar_mul_row_outside; try lia. reflexivity.
                     auto. } rewrite Hget. clear Hget. rewrite poly_mult_comm.
                      rewrite <- (@flatten_mx_set m n). simpl. cancel. all: try lia; auto. } 
              { (*scalar mul loop return*) forward. rewrite HeqLOCALS; entailer!.
                - solve_offset.
                - assert_PROP ((field_address (tarray tuchar (m * n)) 
                    [ArraySubsc (i * n + n - 1 - (n - 1))] s) =
                    (field_address0 (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s)). {
                  entailer!. solve_offset. }
                  rewrite H21 in H8; clear H21.
                  (*need to know that j = n at end of loop*)
                  assert (Hjn: j >= n). { apply typed_false_not_true in H8. rewrite (not_iff_compat) in H8.
                  2: { rewrite ptr_comparison_gt_iff. reflexivity. all: auto. all: simpl; lia. }
                  lia. } 
                  assert (j = n) by lia. subst; clear Hjn H8. unfold scalar_mul_row. cancel.  } }
            (*no idea what level I'm on - coqide has stopped highlighting brackets, but at end of col loop*)
            rewrite HeqLOCALS; forward. Exists (i + 1). entailer!.
            { solve_repr_int. }
            { rewrite all_cols_one_plus_1 by lia. 
              replace (ssralg.GRing.inv (R:=ssralg.GRing.Field.unitRingType F)) with (find_inv mod_poly) by reflexivity.
              rewrite (@all_cols_one_outside F m n); try lia. cancel. solve_wf. } } } } } }
      (*now we are completely finishing the col loop*)
    { forward. entailer!. replace (i) with m by lia. cancel. } }
  { (*start of second part: add kth row to all other rows*)
    forward.
    (*simplify r*) pointer_to_offset s.
    (*can't use [forward_for_simple_bound] because it casts i to a tuchar*)
    remember [temp _r (offset_val (k * n + n - 1) s); temp _k (Vint (Int.repr k)); 
              temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); 
              gvars gv] as LOCALS.
    forward_loop (EX (i : Z),
      PROP (0 <= i <= m)
      (LOCALx  (temp _i (Vint (Int.repr i)) :: LOCALS)
      (SEP (FIELD_TABLES gv;
            data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr (flatten_mx (sub_all_rows_partial m n
           (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx k) k m) k i)))) s))%assert5))
      break: 
      (PROP ()
      (LOCALx  (LOCALS)
      (SEP (FIELD_TABLES gv;
            data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr (flatten_mx (sub_all_rows_partial m n
            (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx k) k m) k m)))) s))%assert5)).
    { (*initialization of subtract all rows loop*) 
      rewrite HeqLOCALS; forward. Exists 0%Z. rewrite HeqLOCALS; entailer!. }
    { (*Body of subtract all rows loop *) 
      Intros i. rewrite HeqLOCALS; forward_if.
      { (*i < m (loop body)*) 
        forward_if (PROP ()
            (LOCALx (temp _i (Vint (Int.repr i)) :: LOCALS)
            (SEP (FIELD_TABLES gv;
             data_at Ews (tarray tuchar (m * n))
               (map Vint (map Int.repr (flatten_mx (if Z.eq_dec i k then
                (sub_all_rows_partial (F:=F) m n(all_cols_one_partial (F:=F) m n
                  (gauss_all_steps_rows_partial (F:=F) m n mx k) k m) k i) else
               (add_multiple_partial m n (sub_all_rows_partial (F:=F) m n (all_cols_one_partial (F:=F) m n
                  (gauss_all_steps_rows_partial (F:=F) m n mx k) k m) k i) k i (q1 (f:=mod_poly)) n)
                )))) s))%assert5)). 
        { (*when i != k*)
          forward.  (*simplify q*) pointer_to_offset s.
          forward_for (fun (j : Z) => PROP (0 <= j <= n)
            LOCAL (temp _q (offset_val (i * n + n - 1) s); temp _r (offset_val (k * n + n - 1) s);
              temp _k (Vint (Int.repr k)); temp _p s; temp _i_max (Vint (Int.repr m));
              temp _j_max (Vint (Int.repr n)); temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)); gvars gv)
            SEP (FIELD_TABLES gv;
             data_at Ews (tarray tuchar (m * n))
               (map Vint (map Int.repr (flatten_mx
               (add_multiple_partial m n (sub_all_rows_partial (F:=F) m n (all_cols_one_partial (F:=F) m n
                  (gauss_all_steps_rows_partial (F:=F) m n mx k) k m) k i) k i (q1 (f:=mod_poly)) j)))) s)).
           { (*beginning of subtraction loop*) forward. Exists 0%Z. entailer!. rewrite add_multiple_partial_0.
             cancel. solve_wf. }
           { entailer!. }
           { rename x into j. (*simplify *(q-j)*)
             assert_PROP (force_val (sem_sub_pi tuchar Signed (offset_val (i * n + n - 1) s) (Vint (Int.repr j))) =
                offset_val (i * n + n - 1 - j) s). { entailer!. solve_offset.  }
             assert_PROP (offset_val (i * n + n - 1 - j) s = 
              field_address (tarray tuchar (m * n)) (SUB (i * n + n - 1 - j)) s). { entailer!. solve_offset. }
             rewrite H6 in H5.
             assert (Hij: 0 <= i * n + n - 1 - j < m * n) by (apply matrix_bounds_within; lia).
             assert_PROP ((0 <= i * n + n - 1 - j < Zlength (map Int.repr (flatten_mx (add_multiple_partial (F:=F) m n
              (sub_all_rows_partial (F:=F) m n (all_cols_one_partial (F:=F) m n 
              (gauss_all_steps_rows_partial (F:=F) m n mx k) k m) k i) k i
              (q1 (f:=mod_poly)) j))))). { entailer!. list_solve. }
            rewrite Zlength_map in H7. forward.
            { entailer!. rewrite (@flatten_mx_Znth m n); try lia. simpl_repr. solve_wf. }
            { entailer!. solve_offset. }
            { (*Simplify *(r-j) *)
              rewrite (@flatten_mx_Znth m n); [ | solve_wf | lia | lia].
              assert_PROP (force_val (sem_sub_pi tuchar Signed (offset_val (k * n + n - 1) s) (Vint (Int.repr j))) =
                 offset_val (k * n + n - 1 - j) s). { entailer!. solve_offset. }
              assert_PROP (offset_val (k * n + n - 1 - j) s = field_address (tarray tuchar (m * n))
                (SUB (k * n + n - 1 - j)) s). { entailer!. solve_offset. }  rewrite H9 in H8. 
              assert (Hkj : 0 <= k * n + n - 1 - j < m * n) by (apply matrix_bounds_within; lia).
              assert_PROP ((0 <= k * n + n - 1 - j < Zlength (map Int.repr (flatten_mx
              (add_multiple_partial (F:=F) m n (sub_all_rows_partial (F:=F) m n (all_cols_one_partial (F:=F) m n
              (gauss_all_steps_rows_partial (F:=F) m n mx k) k m) k i) k i 
              (q1 (f:=mod_poly)) j))))). { entailer!. list_solve. } rewrite Zlength_map in H10.
              forward.
              { entailer!. rewrite (@flatten_mx_Znth m n); try lia. simpl_repr. solve_wf.  }
              { entailer!. solve_offset. }
              { (*actual subtraction*) 
                rewrite (@flatten_mx_Znth m n); [ | solve_wf | lia | lia]. forward.
                { entailer!. solve_offset. }
                { (*need lots of simplification*)
                  unfold Int.xor. simpl_repr. solve_repr_int.
                  rewrite xor_poly_to_int.
                  remember (add_multiple_partial (F:=F) m n (sub_all_rows_partial (F:=F) m n
                           (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx k) k m) k i) k i
                           (q1 (f:=mod_poly)) j) as mx'.
                  forward. 
                  (*end of subtraction loop*)
                  Exists (j+1). entailer!.
                  { solve_repr_int. } 
                  { rewrite add_multiple_partial_plus_1; [| solve_wf | lia |lia]. 
                    rewrite <- (@flatten_mx_set m n); [| solve_wf | lia | lia].
                    rewrite ssralg.GRing.mul1r. 
                    replace (ssralg.GRing.add (V:=ssralg.GRing.Field.zmodType F)) with (qadd (f:=mod_poly)) by reflexivity.
                    unfold qadd. unfold r_add. unfold poly_add_mod. simpl_reptype.
                    rewrite (@add_multiple_partial_outside _ m n); try lia; [| solve_wf].
                    rewrite (@add_multiple_partial_other_row _ m n); try lia; [ | solve_wf].
                    (*We can get rid of the other [add_multiple_add_partial] since i <> k*)
                    remember ((proj1_sig  (get (F:=F)
                      (sub_all_rows_partial (F:=F) m n
                        (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx k) k m) k i) i j) +~
                      proj1_sig  (get (F:=F) (sub_all_rows_partial (F:=F) m n
                        (all_cols_one_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx k) k m)  k i) k j)))
                    as sum. 
                    (*now we just need to show the two pieces are equal*)
                     rewrite <- !upd_Znth_map. 
                    assert (Hdeg: deg sum < deg mod_poly). { rewrite Heqsum.
                    eapply Z.le_lt_trans. apply poly_add_deg_max. apply Z.max_lub_lt;
                     apply (@ssrfun.svalP _ (fun y => deg y < deg mod_poly)). }
                    assert (Hsum_bound: 0 <= (poly_to_int sum) < fec_n). {
                     apply modulus_poly_bound in Hdeg. assumption. } solve_repr_int. simpl.
                     rewrite (pmod_refl mod_poly sum); auto. cancel. }
                }
              }
            }
          }
          { (*end of subtraction loop*) rewrite HeqLOCALS; entailer!. destruct (Z.eq_dec i k); try lia.
            rename x into j. replace j with n by lia. cancel. }
        }
        { (*i = k case (easier)*)
           forward. rewrite HeqLOCALS; entailer!. destruct (Z.eq_dec k k); try lia. cancel. }
        { (*postcondition of sub_all_rows loop*) rewrite HeqLOCALS; forward. Exists (i+1). rewrite HeqLOCALS; entailer!.
          { solve_repr_int. }
          { rewrite sub_all_rows_plus_1 by lia.
            replace (ssralg.GRing.opp (V:=ssralg.GRing.Ring.zmodType (ssralg.GRing.Field.ringType F))
                      (ssralg.GRing.one (ssralg.GRing.Field.ringType F))) with
              (q1 (f:=mod_poly)) by reflexivity. 
            destruct (Z.eq_dec i k); simpl; cancel. }
            }
          }
          { (*end of sub all rows loop*) forward. rewrite HeqLOCALS; entailer!. replace i with m by lia. cancel. }
        }
        { (*postcondition of gauss_one_step loop*)
          rewrite HeqLOCALS; forward. Exists (k+1). entailer!.
          { solve_repr_int.  }
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
      SEP (FIELD_TABLES gv;
           data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr (flatten_mx (all_lc_one_rows_partial m n
            (gauss_all_steps_rows_partial (F:=F) m n mx m) i)))) s))
      break:
       (PROP ()
        LOCAL (temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); gvars gv) 
        SEP (FIELD_TABLES gv;
           data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr (flatten_mx (all_lc_one_rows_partial m n
            (gauss_all_steps_rows_partial (F:=F) m n mx m) (m-1))))) s)).
    { (*initialization*) forward. Exists 0%Z. entailer!. }
    { (*outer loop for lc's 1*) Intros i. forward_if.
      { (*loop body*) forward.
        (*simplify q*) pointer_to_offset s. 
        assert_PROP (offset_val (i * n + n - 1) s = field_address (tarray tuchar (m * n)) (SUB (i * n + n - 1)) s). {
        entailer!. solve_offset. }
        forward.
        { entailer!. solve_offset.  }
        { (*simplify m*) pointer_to_offset_with s (i * n + n - 1 - (n - 1)).  
          assert_PROP (offset_val (i * n + n - 1 - (n - 1)) s = field_address (tarray tuchar (m * n))
            (SUB ( i * n + n - 1 - ( n - 1))) s). { entailer!. solve_offset. } rewrite H2. 
          (*simplify (q-i)*) 
          assert_PROP (force_val (sem_sub_pi tuchar Signed (offset_val (i * n + n - 1) s) (Vint (Int.repr i))) =
            field_address (tarray tuchar (m * n)) (SUB (i * n + n - 1 - i)) s). { entailer!. solve_offset. }
          (*Also need length info in context*)
          assert_PROP ((0 <= i * n + n - 1 - i < Zlength (map Int.repr
            (flatten_mx (all_lc_one_rows_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx m) i))))). {
          entailer!. assert (0 <= i * n + n - 1 - i < m * n). apply matrix_bounds_within; lia. list_solve. }
          rewrite Zlength_map in H4. forward.
          { (*pointer access is valid*) entailer!. rewrite (@flatten_mx_Znth m n); [ | solve_wf | lia | lia].
            simpl_repr. }
          { entailer!. solve_offset. }
          { rewrite (@flatten_mx_Znth m n); [| solve_wf | lia |lia ]. (*need for "forward"*)
            assert (Hpolybound: 0 <= poly_to_int (proj1_sig (get (F:=F) (all_lc_one_rows_partial (F:=F) m n
              (gauss_all_steps_rows_partial (F:=F) m n mx m) i) i i)) <= Byte.max_unsigned) by solve_poly_bounds.
            unfold FIELD_TABLES. Intros.
            forward.
            { entailer!. }
            { entailer!. rewrite inverse_contents_Znth; [| solve_poly_bounds]. simpl. 
              rewrite poly_of_int_inv. unfold poly_inv. simpl_repr. }
            { rewrite inverse_contents_Znth; [| solve_poly_bounds]. rewrite poly_of_int_inv.
              remember ((get (F:=F)(all_lc_one_rows_partial (F:=F) m n
                (gauss_all_steps_rows_partial (F:=F) m n mx m) i) i i)) as aii.
              forward. (*simplify inv*)
              remember (find_inv mod_poly aii) as aii_inv eqn : Haiiinv.
              replace (poly_inv mod_poly (proj1_sig aii)) with (proj1_sig aii_inv). 2 : {
              unfold poly_inv. rewrite poly_to_qpoly_unfold. rewrite Haiiinv. reflexivity. }
              simpl_repr. forward. pointer_to_offset_with s (i * n + n).
              assert (Himn: 0 <= i * n + n <= m * n) by nia. 
              assert (Hin0: 0 <= i * n) by nia.
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
                SEP (FIELD_TABLES gv;
                  data_at Ews (tarray tuchar (m * n))(map Vint (map Int.repr
                    (flatten_mx (scalar_mul_row_partial m n
                      (all_lc_one_rows_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx m) i) i aii_inv j)))) s)).
              { Exists 0%Z. entailer!. solve_offset. unfold FIELD_TABLES. 
                rewrite scalar_mul_row_partial_0. cancel. solve_wf.  }
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
                { entailer!. solve_offset. }
                { (*simplify if condition*)
                  assert_PROP (field_address (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s = 
                    (field_address0 (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s)). { entailer!.
                  solve_offset. } rewrite H6 in HRE; clear H6.
                  assert_PROP (j < n). { entailer!. 
                   rewrite ptr_comparison_gt_iff in HRE; auto; simpl; lia. } rename H6 into Hjn; clear HRE.
                  (*simplify n so we can dereference*)
                   assert_PROP ((force_val (sem_binary_operation' Osub (tptr tuchar) tint
                  (field_address0 (tarray tuchar (m * n)) [ArraySubsc (i * n + n - j)] s)
                  (Vint (Int.repr 1)))) = field_address (tarray tuchar (m * n)) (SUB (i * n + n - 1 - j)) s). {
                  entailer!. rewrite arr_field_address0; auto; try lia. solve_offset. }  rewrite H6; clear H6.
                  (*length goal*)
                  assert_PROP (0 <= i * n + n - 1 - j < Zlength (map Int.repr
                    (flatten_mx (scalar_mul_row_partial (F:=F) m n (all_lc_one_rows_partial (F:=F) m n
                    (gauss_all_steps_rows_partial (F:=F) m n mx m) i) i aii_inv j)))). {
                   entailer!. assert (0 <= i * n + n - 1 - j < m * n) by (apply matrix_bounds_within; lia).
                   list_solve. }
                  rewrite Zlength_map in H6. 
                  forward.
                  { entailer!. rewrite (@flatten_mx_Znth m n); [| solve_wf | lia | lia]. simpl_repr. }
                  { rewrite (@flatten_mx_Znth m n); [ | solve_wf | lia | lia].
                    remember ((get (F:=F)(scalar_mul_row_partial (F:=F) m n (all_lc_one_rows_partial (F:=F) m n
                              (gauss_all_steps_rows_partial (F:=F) m n mx m) i) i aii_inv j) i j)) as aij.
                    forward_call.
                    { unfold FIELD_TABLES. entailer!. }
                    { simpl_repr. split; solve_poly_bounds. } 
                    { simpl_repr.
                      forward. (*loop invariant preservation*)
                      Exists (j+1). entailer!.
                      { solve_offset. }
                      { rewrite !poly_of_int_inv. 
                        remember ((get (F:=F) (scalar_mul_row_partial (F:=F) m n
                        (all_lc_one_rows_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx m) i)i
                        (find_inv mod_poly(get (F:=F)
                        (all_lc_one_rows_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx m) i) i i)) j) i j)) as aij.
                         remember ((find_inv mod_poly (get (F:=F)
                         (all_lc_one_rows_partial (F:=F) m n (gauss_all_steps_rows_partial (F:=F) m n mx m) i)
                         i i))) as aii_inv.
                        rewrite (@scalar_mul_row_plus_1 F _ m n); [| solve_wf | lia | lia].
                        replace (ssralg.GRing.mul (R:=ssralg.GRing.Field.ringType F)) with  
                          (r_mul mod_poly) by reflexivity. unfold r_mul. unfold poly_mult_mod.
                        rewrite !upd_Znth_map.
                        rewrite <- (@flatten_mx_set m n); [|solve_wf | lia | lia]. simpl.
                        rewrite Heqaij. rewrite poly_mult_comm.
                        rewrite (@scalar_mul_row_outside _ m n); try lia; [ unfold FIELD_TABLES; cancel | solve_wf]. }
                    }
                  }
                }
              }
              { (*end of outer loop*) forward. Exists (i+1). entailer!. solve_repr_int.
                rewrite all_lc_one_plus_one; [| lia]. unfold scalar_mul_row.
                (*need to know that j = n*)
                assert (Haddr: (field_address (tarray tuchar (m * n)) 
                    [ArraySubsc (i * n + n - 1 - (n - 1))] s) =
                    (field_address0 (tarray tuchar (m * n)) [ArraySubsc (i * n + n - 1 - (n - 1))] s)) by solve_offset.
                rewrite Haddr in HRE; clear Haddr.
                assert (Hjn: j >= n). {
                  apply typed_false_not_true in HRE. rewrite (not_iff_compat) in HRE. 2: {
                  rewrite ptr_comparison_gt_iff. reflexivity. all: auto. all: simpl; lia. }
                  lia. } 
                assert (j = n) by lia. subst; clear Hjn HRE. 
                replace (ssralg.GRing.inv (R:=ssralg.GRing.Field.unitRingType F)) with 
                (find_inv mod_poly) by reflexivity.
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

