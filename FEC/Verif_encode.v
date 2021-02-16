Require Import VST.floyd.proofauto.

Require Import fec.
Require Import Common.
Require Import CommonVST.
Require Import VandermondeList.
Require Import Specs.
Require Import Poly.
Require Import FECTactics.

Set Bullet Behavior "Strict Subproofs".

Ltac rewrite_eqs :=
  repeat match goal with
    | [H : ?x = ?y |- context [ ?x ]] => rewrite H
    end.

Ltac solve_in :=
  subst;
  match goal with
  | [ |- In ?x (?x :: ?z)] => left; reflexivity
  | [ |- In ?x (?y :: ?z)] => right; solve_in
  | [ H : _ |- In ?x (?l1 ++ ?l2)] => apply in_or_app; first [left; solve_in | right; solve_in] (*not sure if this works*)
  | [ H : _ |- In ?x ?l] => assumption; auto
  end.

Ltac solve_in_eq :=
  repeat match goal with
   | [ H : In ?x ?y |-In ?x ?y] => apply H 
   | [ H : In ?x (?y :: ?z) |- In ?k ?l] => destruct H
   | [ H : In ?x (?a ++ ?b) |- In ?k ?l] => apply list_in_insert in H; destruct H
   end; solve_in.

(*Due to bug in VST *)
Ltac no_loads_expr e as_lvalue ::=
 match e with
 | Econst_int _ _ => idtac
 | Econst_float _ _ => idtac
 | Econst_single _ _ => idtac
 | Econst_long _ _ => idtac
 | Evar _ ?t => lazymatch as_lvalue with true => idtac | false => is_array_type t end
 | Etempvar _ _ => idtac
 | Ederef ?e1 ?t => lazymatch as_lvalue with true => idtac | false => is_array_type t end;
                               no_loads_expr e1 true
 | Eaddrof ?e1 _ => no_loads_expr e1 true
 | Eunop _ ?e1 _ => no_loads_expr e1 as_lvalue
 | Ebinop _ ?e1 ?e2 _ => no_loads_expr e1 as_lvalue ; no_loads_expr e2 as_lvalue
 | Ecast ?e1 _ => no_loads_expr e1 as_lvalue
 | Efield ?e1 _ ?t => lazymatch as_lvalue with true => idtac | false => is_array_type t end;
                               no_loads_expr e1 true 
 | Esizeof _ _ => idtac
 | Ealignof _ _ => idtac
end.

(*TODO: see if this should be global or not*)
Section Encoder.
Hint Resolve iter_sepcon_arrays_local_facts : saturate_local.

Lemma body_fec_blk_encode : semax_body Vprog Gprog f_fec_blk_encode fec_blk_encode_spec.
Proof.
  start_function. forward. forward. (*TODO: make easier with tactic (need sizeof)*)
  assert_PROP (force_val (sem_binary_operation' Oadd (tptr (tptr tuchar)) tint pd (Vint (Int.repr k))) =
    field_address0 (tarray (tptr (tuchar)) (k + h)) [ArraySubsc k] pd) as Hpd. { entailer!. simpl. 
    rewrite arr_field_address0; auto. lia. } rewrite Hpd.
  (*we want to pull out z from the locals*)
  erewrite LOCALx_Permutation. 2 : { apply perm_swap. } 
  remember [ temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd); gvars gv;
      temp _k (Vint (Int.repr k));
      temp _h (Vint (Int.repr h)); temp _c (Vint (Int.repr c)); temp _pdata pd; 
      temp _plen pl; temp _pstat ps] as LOCALS.
  remember ( temp _z (Vint (Int.zero_ext 8 (Int.neg (Int.repr 1)))) :: LOCALS) as LOCALS1.
  remember [data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
       iter_sepcon_arrays packet_ptrs packets;
       data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl;
       data_at Ews (tarray tschar k) (list_repeat (Z.to_nat k) (Vint Int.zero)) ps; 
       INDEX_TABLES gv;
       data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx)
         (gv _fec_weights)] as SEPS.
  remember (iter_sepcon_arrays parity_ptrs parities :: SEPS) as SEPS1.
  (*remember the above because the loop invariant is basically trivial and we don't want to repeat twice*)
  forward_loop (EX (i: Z),
    PROP (0 <= i <= k)
    (LOCALx  ( temp _i (Vint (Int.repr i)) :: LOCALS1 )
    (SEPx SEPS1)))
   break: 
    (PROP ( )  (LOCALx LOCALS1 (SEPx SEPS1))).
  - rewrite_eqs. forward. Exists 0%Z. rewrite_eqs. entailer!.
  - Intros i. rewrite_eqs. forward_if.
    + forward. rewrite Znth_list_repeat_inrange by lia. entailer!.
      forward_if.
      * forward_if True.
        -- contradiction.
        -- forward. entailer!.
        -- rewrite Znth_list_repeat_inrange in H14 by lia. inversion H14.
      * forward. Exists (i+1)%Z. rewrite_eqs. entailer!. solve_repr_int.
    + forward. rewrite_eqs. entailer!.
  - (*another error check that isn't true*) rewrite_eqs. forward_if True. contradiction.
    forward. entailer!.
    (*The real function starts here*)
    (*outer loop - go through all rows selected by weight matrix*)
    rewrite <- HeqLOCALS. rewrite <- HeqSEPS. clear HeqLOCALS1 LOCALS1. clear HeqSEPS1 SEPS1.
   (*Loop invariant: each time, up to the ith row of the resulting matrix is correct (ie, each position
     is the dot product of the correct row from the weight mx and column from the packet matrix)*)
    (*z is super annoying bc its unsigned but starts at -1*)
    (*loop invariant will work with int matrices, in the postcondition we will convert this to the equivalent
      matrix in the field. This is because the initial parity matrix (which is overwritten) can be arbitrary*)
   forward_loop (EX (i:Z) (l: list (list Z)),
      PROP (0 <= i <= h; forall x y, 0 <= x < i -> 0 <= y < c -> Znth y (Znth x l) = 
        poly_to_int (proj1_sig (dot_prod (submatrix weight_mx h k) (extend_mx (int_to_poly_mx packets) c) x y k));
        Zlength l = h; Forall (fun l' => Zlength l' = c) l)
       (LOCALx (temp _i (Vint (Int.repr i)):: temp _z (Vint (Int.repr ((i - 1) mod 256))) :: LOCALS)
          (SEPx (iter_sepcon_arrays parity_ptrs l :: SEPS))))
    break: 
      (PROP ()
      (LOCALx (LOCALS)
        (SEPx ((iter_sepcon_arrays parity_ptrs (norev_mx (encode_list_mx h k c packets))) :: SEPS)))).
    + rewrite_eqs. forward. Exists (0%Z). Exists parities. rewrite_eqs. entailer!.
    + (*loop body*) Intros i. Intros mx. rewrite_eqs. forward_if.
      * (*loop for z*) rewrite <- HeqLOCALS. rewrite <- HeqSEPS.
        forward_loop (
          PROP () 
          (LOCALx (temp _i (Vint (Int.repr i)) :: temp _z (Vint (Int.repr ((i-1) mod 256))) :: LOCALS)
            (SEPx (iter_sepcon_arrays parity_ptrs mx :: SEPS))))
        break: 
          (PROP () 
          (LOCALx (temp _i (Vint (Int.repr i)) :: temp _z (Vint (Int.repr i)) :: LOCALS)
            (SEPx (iter_sepcon_arrays parity_ptrs mx :: SEPS)))). (*bc of simplifying assumption*)
        -- rewrite_eqs; entailer!.
        -- rewrite_eqs. forward. forward.
           assert (Hmod: (Int.zero_ext 8 (Int.add (Int.repr ((i - 1) mod 256)) (Int.repr 1))) = (Int.repr i)). {
            unfold Int.add. assert (0 <= (i-1) mod 256 < 256). apply Z.mod_pos_bound; lia.
            rewrite !unsigned_repr by rep_lia. solve_repr_int. f_equal. rewrite Zbits.Zzero_ext_mod by rep_lia.
            replace (two_p 8) with 256 by reflexivity. rewrite <- (Zmod_small 1 256) at 2 by rep_lia.
            rewrite <- Zplus_mod. rewrite Zmod_small; rep_lia. } rewrite Hmod. solve_repr_int. 
           assert_PROP (force_val (sem_add_ptr_int (tptr tuchar) Signed 
            (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd)
            (Vint (Int.repr i))) = field_address (tarray (tptr tuchar) (k + h)) (SUB (k + i)) pd). {
            entailer!. solve_offset. }
           (*We are accessing pparity[i] = pdata[k+i]. We want to know what is there - TODO: move earlier - dont think
             I will be able to bc we lose iter_sepcon info*) 
           assert (Hlens: Zlength parity_ptrs = Zlength mx) by lia.
           assert (Hith : 0 <= i < Zlength mx) by lia.
           assert (Hznth : (Znth (k + i) (packet_ptrs ++ parity_ptrs)) = Znth i parity_ptrs). {
            rewrite Znth_app2 by list_solve. f_equal. lia. }
           (*Would like to be able to get [data_at] info about [Znth i mx], but cannot bc we still need
             iter_sepcon for postcondition*)
           forward. 
          ++ entailer!. specialize (H20 Hlens _ Hith).
             replace (Znth (Zlength packets + i) (packet_ptrs ++ parity_ptrs)) with (Znth i parity_ptrs) by auto.
            (*TODO: Why doesn't rewriting work here? Why does this stupid trick work?*)
            apply isptr_is_pointer_or_null. apply H20.
          ++ entailer!. specialize (H20 Hlens _ Hith). rewrite !arr_field_address0 by (auto; list_solve). simpl. split.
             rewrite isptr_offset_val. auto. apply isptr_force_sem_add_ptr_int; auto.
          ++ replace ((Znth (k + i) (packet_ptrs ++ parity_ptrs))) with (Znth i parity_ptrs) by auto.
             (*TODO: again, why doesn't rewriting work?*)
             forward_if False. (*If condition is true due to assumption*)
            ** sep_apply (iter_sepcon_arrays_Znth _ _ _ Hlens Hith). Intros.
               apply (denote_tc_test_eq_split _ (Znth i parity_ptrs) (Vlong (Int64.zero))).
               sep_apply (data_at_memory_block). sep_apply (memory_block_valid_ptr). auto. simpl.
               replace (Zlength (Znth i mx)) with c. rep_lia. rewrite Forall_forall in H15. rewrite H15.
               reflexivity. apply Znth_In; lia. entailer!. apply valid_pointer_zero64; auto. (*relies on 64 bit*)
            ** forward. entailer!. specialize (H22 Hlens _ Hith). destruct H22 as [Hfc  ?]. rewrite H18 in Hfc.
               apply (field_compatible_nullval _ _ _ _ Hfc).
            ** forward. rewrite_eqs; entailer!.
            ** rewrite_eqs; entailer!.
        -- (*Now another trivial error check*)
           rewrite_eqs; forward_if True.
          ++ contradiction.
          ++ forward. entailer!.
          ++ (*now, at the (assert < FEC_MAX_H)*)
              forward_if True.
            ** forward. entailer!.
            ** rep_lia. (* the assertion holds*)
            ** (*finally, we are at the actual inner loop*)
               (*since i and w are not changing, we can add them to LOCALS (but we can't replace LOCALS bc
                 it is used in the POSTCONDITION*)
               rewrite <- HeqLOCALS. rewrite <- HeqSEPS.
               remember (temp _i (Vint (Int.repr i)) :: temp _z (Vint (Int.repr i)) :: LOCALS) as LOCALS1.
               forward_loop (EX (j : Z),
                PROP (0 <= j <= c; 
                  forall x y, (0 <= x < i /\ 0 <= y < c) \/ (x = i /\ 0 <= y < j) -> Znth y (Znth x mx) = 
                  poly_to_int (proj1_sig (dot_prod (submatrix weight_mx h k) 
                    (extend_mx (int_to_poly_mx packets) c) x y k)))
                 (LOCALx (temp _j (Vint (Int.repr j)) :: LOCALS1)
                   (SEPx (iter_sepcon_arrays parity_ptrs mx :: SEPS))))
                break: (PROP (forall x y, (0 <= x <= i /\ 0 <= y < c) -> Znth y (Znth x mx) = 
                  poly_to_int (proj1_sig (dot_prod (submatrix weight_mx h k) 
                    (extend_mx (int_to_poly_mx packets) c) x y k)))
                 (LOCALx LOCALS1
                   (SEPx (iter_sepcon_arrays parity_ptrs mx :: SEPS)))).
              --- rewrite_eqs. forward. Exists 0%Z. rewrite_eqs. entailer!. intros x y [[Hx Hy] | [Hx Hy]].
                  apply H13; auto. lia.
              --- Intros j. rewrite_eqs. forward_if.
                +++ (*body of j- loop*)
                    forward.
                    assert_PROP (force_val (sem_add_ptr_int (tarray tuchar 255) Signed (gv _fec_weights)
                        (Vint (Int.repr i))) =
                      field_address (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (SUB i) (gv _fec_weights)) as Hp. {
                    entailer!. solve_offset. }
                    forward. clear Hp.
                    (*Now we can express p as an actual address in the 2D array. TODO: maybe improve [solve_offset]
                      to handle 2D arrays (also appears in weight mx)*)
                    assert_PROP ((force_val (sem_binary_operation' Oadd (tarray (tarray tuchar 255) 128) tuchar 
                      (gv _fec_weights) (Vint (Int.repr i)))) = 
                      field_address0 (tarray (tarray tuchar 255) 128) [ArraySubsc 0; ArraySubsc i] 
                        (gv _fec_weights)) as Hp. {
                      entailer!. simpl. rewrite field_compatible0_field_address0.
                      simpl. f_equal. rep_lia. apply field_compatible_field_compatible0. 
                      unfold field_compatible; simpl.  replace (fec_n - 1) with 255 in H34 by rep_lia.
                      replace fec_max_h with 128 in H34 by rep_lia. 
                      destruct H34 as [Hptr [ Hleg [Hszcomp [Hal Hnest ]]]]. simpl in *.
                      repeat(split; auto); rep_lia. }
                    rewrite Hp. clear Hp. rewrite <- HeqLOCALS. rewrite <- HeqSEPS. solve_repr_int.
                    rewrite <- HeqLOCALS1.
                    (*to reduce repetition*)
                    remember (temp _j (Vint (Int.repr j)) :: LOCALS1) as LOCALS2.
                    (*Innermost loop (n loop) - our invariant is that y calculates the dot product up
                      to n*)
                    forward_loop (EX (n: Z),
                      PROP (0 <= n <= k)
                      (LOCALx (temp _n (Vint (Int.repr n)) :: 
                        temp _p (field_address0 (tarray (tarray tuchar 255) 128) 
                                [ArraySubsc n; ArraySubsc i] (gv _fec_weights)) ::
                        temp _y (Vint (Int.repr (poly_to_int (proj1_sig
                           (dot_prod (F:=F) (submatrix (F:=F) weight_mx h k)
                           (extend_mx (F:=F) (int_to_poly_mx packets) c) i j n))))) :: LOCALS2)
                      (SEPx (iter_sepcon_arrays parity_ptrs mx :: SEPS))))
                    break:
                     (PROP ()
                     (LOCALx (temp _p (field_address0 (tarray (tarray tuchar 255) 128) 
                                [ArraySubsc k; ArraySubsc i] (gv _fec_weights)) ::
                        temp _y (Vint (Int.repr (poly_to_int (proj1_sig
                           (dot_prod (F:=F) (submatrix (F:=F) weight_mx h k)
                           (extend_mx (F:=F) (int_to_poly_mx packets) c) i j k))))) :: LOCALS2)
                     (SEPx (iter_sepcon_arrays parity_ptrs mx :: SEPS)))).
                  *** rewrite_eqs; forward. Exists 0%Z. rewrite_eqs; entailer!.
                  *** Intros n. rewrite_eqs; forward_if.
                    { (*body of innermost loop*) forward. rewrite H11.
                      (*we have 2 cases: either we are in bounds, so we do usual multiplication, or
                        we are out of bounds, so we are implicitly extending the matrix with zeroes (which of course
                        does not affect the sum). We need to handle each case separately. The important thing
                        is that the dot product is still preserved*)
                      (*Unfortunately, folding the definitions makes "forward_if" take forever*)
                      forward_if ((PROP ( )
                        LOCAL (
                          temp _t'5 (Vint (Int.repr (Zlength (Znth n packets)))); temp _n (Vint (Int.repr n));
                          temp _p (field_address0 (tarray (tarray tuchar 255) 128) [ArraySubsc n; ArraySubsc i] 
                            (gv _fec_weights));
                          temp _y (Vint (Int.repr (poly_to_int (proj1_sig 
                            (dot_prod (F:=F) (submatrix (F:=F) weight_mx h k)
                            (extend_mx (F:=F) (int_to_poly_mx packets) c) i j (n + 1))))));
                          temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr i)); temp _z (Vint (Int.repr i));
                          temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd); 
                          gvars gv; temp _k (Vint (Int.repr k)); temp _h (Vint (Int.repr h)); 
                          temp _c (Vint (Int.repr c)); temp _pdata pd; temp _plen pl; temp _pstat ps)
                        SEP (iter_sepcon_arrays parity_ptrs mx;
                          data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
                          iter_sepcon_arrays packet_ptrs packets;
                          data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl;
                          data_at Ews (tarray tschar k) (list_repeat (Z.to_nat k) (Vint Int.zero)) ps; 
                          INDEX_TABLES gv;
                          data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) 
                            (gv _fec_weights)))).
                       { (*It will be useful to get the info about Znth n packet_ptrs from [iter_sepcon]*)
                         assert_PROP (field_compatible (tarray tuchar (Zlength (Znth n packets))) [] (Znth n packet_ptrs)) as Hfc. {
                           entailer!. apply H31. list_solve. lia. }
                         forward. rewrite Znth_app1 by list_solve. entailer!. 
                         assert (Hjlen: 0 <= j < Zlength (Znth n packets)). { rewrite Int.signed_repr in H22. lia.
                          rewrite Forall_forall in H8. specialize (H8 (Znth n packets)).
                          assert (Hin: In (Znth n packets) packets) by (apply Znth_In; lia). apply H8 in Hin. rep_lia. }
                         assert_PROP (force_val (sem_add_ptr_int tuchar Signed (Znth n (packet_ptrs ++ parity_ptrs)) 
                            (Vint (Int.repr j))) =
                            field_address (tarray tuchar (Zlength (Znth n packets))) (SUB j) (Znth n packet_ptrs)). {
                          entailer!. rewrite Znth_app1 by list_solve. solve_offset. }
                        (*We need to pull out the specific packet from [iter_sepcon] so we have a [data_at]*)
                         assert (Hlens: Zlength packet_ptrs = Zlength packets) by list_solve.
                         assert (Hjbound : 0 <= n < Zlength packets) by lia.
                         sep_apply (iter_sepcon_arrays_remove_one _ _ _ Hlens Hjbound). Intros. forward.
                         { entailer!. 
                        (*problem: we still need the iter_sepcon_arrays in the goal - TODO*) 
                           rewrite Forall_Znth in H31. specialize (H31 j). rewrite !Zlength_map in H31.
                           specialize (H31 Hjlen). unfold value_fits in H31. simpl in H31.
                           unfold tc_val' in H31. simpl in H31. rewrite !Znth_map in H31 by list_solve.
                           apply H31. intro C; inversion C.
                         }
                         { entailer!. rewrite !Znth_app1 by lia. auto. }
                         { forward.
                           (*TODO: start here*)
                          assert_PROP ( field_address0 (tarray (tarray tuchar 255) 128) 
                              [ArraySubsc n; ArraySubsc i] (gv _fec_weights) =
                            field_address (tarray (tarray tuchar (fec_n -1)) (fec_max_h)) 
                              [ArraySubsc n; ArraySubsc i] (gv _fec_weights)). {
                           replace (fec_n -1) with 255 by rep_lia. replace (fec_max_h) with 128 by rep_lia.
                           entailer!.
                            assert (field_compatible (tarray (tarray tuchar 255) 128) [ArraySubsc n; ArraySubsc i] 
                              (gv _fec_weights)). { unfold field_compatible; simpl. (*TODO: automate*)
                             unfold field_compatible in H44. simpl in H44.
                             replace (fec_n -1) with 255 in H44 by rep_lia.
                             replace (fec_max_h) with 128 in H44 by rep_lia.
                             repeat(split; try (apply H44); try rep_lia). }
                            rewrite field_compatible0_field_address0.
                            rewrite field_compatible_field_address. reflexivity. assumption.
                            apply field_compatible_field_compatible0. assumption. }
                          forward. (*TODO: start here, finish up tomorrow*)



     (*TODO: see what version of this we need, then make separate lemma*)
(*
     assert (forall l,
      Forall (fun l' : list Z => Forall (fun z : Z => 0 <= z <= Byte.max_unsigned) l') l ->
     (* Forall (fun x => Zlength x = c) l ->*)
      norev_mx (int_to_poly_mx l) = l). { intros l Hlens.
      unfold norev_mx. apply Znth_eq_ext. unfold int_to_poly_mx. list_solve. intros i Hilen.
      unfold int_to_poly_mx in Hilen; rewrite !Zlength_map in Hilen.
      rewrite Znth_map. 2: unfold int_to_poly_mx; list_solve. apply Znth_eq_ext.
      rewrite Zlength_map. apply int_to_poly_mx_length2. intros j HjLen.
      rewrite !Zlength_map in HjLen. rewrite Znth_map by auto.
      rewrite int_to_poly_mx_spec by auto. symmetry. rewrite <- poly_of_int_to_int. reflexivity.
      rewrite Forall_forall in Hlens. specialize (Hlens (Znth i l)). 
      assert (Hin: In (Znth i l) l). apply Znth_In; lia. 
      specialize (Hlens Hin). rewrite Forall_forall in Hlens. specialize (Hlens (Znth j (Znth i l))).
      assert (Hin' : In (Znth j (Znth i l)) (Znth i l)). rewrite int_to_poly_mx_length2 in HjLen.
      apply Znth_In; try lia. specialize (Hlens Hin'). lia. }*)


