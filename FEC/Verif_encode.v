Require Import VST.floyd.proofauto.

Require Import fec.
Require Import Common.
Require Import CommonVST.
Require Import VandermondeList.
Require Import Specs.
Require Import Poly.
Require Import FECTactics.
Require Import List2D.

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
        -- rewrite Znth_list_repeat_inrange in H15 by lia. inversion H15.
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
           assert (Hlens: Zlength parity_ptrs = Zlength mx) by lia.
           assert (Hith : 0 <= i < Zlength mx) by lia.
           assert (Hznth : (@Znth _ Vundef (k + i) (packet_ptrs ++ parity_ptrs)) = Znth i parity_ptrs). {
            rewrite Znth_app2 by list_solve. f_equal. lia. }
           (*Would like to be able to get [data_at] info about [Znth i mx], but cannot bc we still need
             iter_sepcon for postcondition*)
           rewrite (iter_sepcon_arrays_remove_one  _ _ _ Hlens Hith). Intros.
           forward. rewrite Hznth. 3: rewrite Hznth. 
          ++ entailer!.
          ++ entailer!. rewrite !arr_field_address0 by (auto; list_solve). simpl. split.
             rewrite isptr_offset_val. auto. apply isptr_force_sem_add_ptr_int; auto.
          ++ forward_if False. (*If condition is true due to assumption*)
            ** apply (denote_tc_test_eq_split _ (Znth i parity_ptrs) (Vlong (Int64.zero))).
               sep_apply (data_at_memory_block). sep_apply (memory_block_valid_ptr). auto. simpl.
               replace (Zlength (Znth i mx)) with c. rep_lia. rewrite Forall_Znth in H16. rewrite H16; lia.
               entailer!. apply valid_pointer_zero64; auto. (*relies on 64 bit*)
            ** forward. entailer!. rewrite H19 in H23.
               apply (field_compatible_nullval _ _ _ _ H23).
            ** forward. rewrite_eqs; entailer!. rewrite (iter_sepcon_arrays_remove_one _ _ _ Hlens Hith). entailer!.
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
               forward_loop (EX (j : Z)(l: list (list Z)),
                PROP (0 <= j <= c;  Zlength l = h; Forall (fun l' => Zlength l' = c) l;
                  forall x y, (0 <= x < i /\ 0 <= y < c) \/ (x = i /\ 0 <= y < j) -> Znth y (Znth x l) = 
                  poly_to_int (proj1_sig (dot_prod (submatrix weight_mx h k) 
                    (extend_mx (int_to_poly_mx packets) c) x y k)))
                 (LOCALx (temp _j (Vint (Int.repr j)) :: LOCALS1)
                   (SEPx (iter_sepcon_arrays parity_ptrs l :: SEPS))))
                break: ( EX (l: list (list Z)), 
                  PROP (Zlength l = h; Forall (fun l' => Zlength l' = c) l;
                        forall x y, (0 <= x <= i /\ 0 <= y < c) -> Znth y (Znth x l) = 
                  poly_to_int (proj1_sig (dot_prod (submatrix weight_mx h k) 
                    (extend_mx (int_to_poly_mx packets) c) x y k)))
                 (LOCALx LOCALS1
                   (SEPx (iter_sepcon_arrays parity_ptrs l :: SEPS)))).
              --- rewrite_eqs. forward. Exists 0%Z. Exists mx. rewrite_eqs. entailer!. intros x y [[Hx Hy] | [Hx Hy]].
                  apply H14; auto. lia.
              --- Intros j. Intros mx'. rewrite_eqs. forward_if.
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
                      unfold field_compatible; simpl.  replace (fec_n - 1) with 255 in H37 by rep_lia.
                      replace fec_max_h with 128 in H37 by rep_lia. repeat (split; try apply H37; try rep_lia). }
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
                      (SEPx (iter_sepcon_arrays parity_ptrs mx' :: SEPS))))
                    break:
                     (PROP ()
                     (LOCALx (temp _p (field_address0 (tarray (tarray tuchar 255) 128) 
                                [ArraySubsc k; ArraySubsc i] (gv _fec_weights)) ::
                        temp _y (Vint (Int.repr (poly_to_int (proj1_sig
                           (dot_prod (F:=F) (submatrix (F:=F) weight_mx h k)
                           (extend_mx (F:=F) (int_to_poly_mx packets) c) i j k))))) :: LOCALS2)
                     (SEPx (iter_sepcon_arrays parity_ptrs mx' :: SEPS)))).
                  *** rewrite_eqs; forward. Exists 0%Z. rewrite_eqs; entailer!.
                  *** Intros n. rewrite_eqs; forward_if.
                    { (*body of innermost loop*) forward. rewrite H12.
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
                        SEP (iter_sepcon_arrays parity_ptrs mx';
                          data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
                          iter_sepcon_arrays packet_ptrs packets;
                          data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl;
                          data_at Ews (tarray tschar k) (list_repeat (Z.to_nat k) (Vint Int.zero)) ps; 
                          INDEX_TABLES gv;
                          data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) 
                            (gv _fec_weights)))).
                       { (*It will be useful to get the info about Znth n packet_ptrs from [iter_sepcon]*)
                         (*assert_PROP (field_compatible (tarray tuchar (Zlength (Znth n packets))) [] (Znth n packet_ptrs)) as Hfc. {
                           entailer!. apply H31. list_solve. lia. }*)
                         (*We need to pull out the specific packet from [iter_sepcon] so we have a [data_at]*)
                         assert (Hlens: Zlength packet_ptrs = Zlength packets) by list_solve.
                         assert (Hjbound : 0 <= n < Zlength packets) by lia.
                         sep_apply (iter_sepcon_arrays_remove_one _ _ _ Hlens Hjbound). Intros. 
                         forward. rewrite Znth_app1 by list_solve. entailer!. 
                         assert (Hjlen: 0 <= j < Zlength (Znth n packets)). { rewrite Int.signed_repr in H25. lia.
                          rewrite Forall_Znth in H8. specialize (H8 _ Hjbound). rep_lia. }
                         assert_PROP (force_val (sem_add_ptr_int tuchar Signed (Znth n (packet_ptrs ++ parity_ptrs)) 
                            (Vint (Int.repr j))) =
                            field_address (tarray tuchar (Zlength (Znth n packets))) (SUB j) (Znth n packet_ptrs)). {
                          entailer!. rewrite Znth_app1 by list_solve. solve_offset. }
                        forward.
                         { entailer!. rewrite Forall2D_Znth in H11. specialize (H11 n j Hjbound Hjlen). solve_repr_int. 
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
                             unfold field_compatible in H47. simpl in H47.
                             replace (fec_n -1) with 255 in H47 by rep_lia.
                             replace (fec_max_h) with 128 in H47 by rep_lia.
                             repeat(split; try (apply H47); try rep_lia). }
                            rewrite field_compatible0_field_address0.
                            rewrite field_compatible_field_address. reflexivity. assumption.
                            apply field_compatible_field_compatible0. assumption. }
                          pose proof (weight_mx_wf) as [Hwlen [Hnotneed Hinwlen]].
                          forward.
                           { entailer!. simpl_map2d. simpl. solve_poly_bounds.
                             rewrite Hinwlen. rep_lia. apply Znth_In; rep_lia. 
                           }
                           { entailer!. apply field_address0_isptr.
                             (*TODO: again, automate this*)
                             unfold field_compatible0. unfold field_compatible in H48.
                             replace (fec_max_h) with 128 in H48 by rep_lia.
                             replace (fec_n - 1) with 255 in H48 by rep_lia.
                             simpl. repeat(split; try apply H48; try rep_lia).
                           }
                           { simpl_map2d.
                             (*For function, need data to b an Int.repr of something < 256*)
                             assert (Hdata: (Vint (Int.zero_ext 8 (Int.repr (Znth j (Znth n packets))))) = 
                               Vint (Int.repr ((Znth j (Znth n packets))))). {
                              rewrite Forall2D_Znth in H11. specialize (H11 n j Hjbound Hjlen). solve_repr_int. }
                             rewrite Hdata. 
                             (*See if this makes it faster*)
                              remember (poly_to_int
                     (f_to_poly (Znth (Zlength (Znth i weight_mx) - n - 1) (Znth i weight_mx)))) as f.
                              remember (Znth j (Znth n packets)) as g.
                              assert (Hf: 0 <= f < fec_n). { rewrite Heqf. solve_poly_bounds. }
                              assert (Hg: 0 <= g < fec_n). {  rewrite Forall2D_Znth in H11. 
                                specialize (H11 n j Hjbound Hjlen). rep_lia. }
                              assert (Hcond: 0 <= f < fec_n /\ 0 <= g < fec_n) by auto.
                              (*unfold MORE_COMMANDS. unfold abbreviate.*) (*no idea why it takes so long*)
                              forward_call (gv, f, g). 
                              (*TODO: figure out why it takes 2 mins to do that*)
                              forward.
                              (*finally, need to prove that the postcondition is satisfied*) entailer!.
                              { unfold Int.xor. rewrite !unsigned_repr. 2: { (*TODO: fix tactic, doesn't see outer, need more than context*)
                                match goal with
                                  | [ |- context [ poly_to_int (?p %~ mod_poly) ]] => 
                                        pose proof (modulus_poly_bound (p %~ mod_poly) (pmod_lt_deg mod_poly p))
                               end; rep_lia. }
                               2 : { solve_poly_bounds. }
                               rewrite xor_poly_to_int.
                               rewrite dot_prod_plus_1 by lia. simpl. 
                               rewrite (@submatrix_spec _ (fec_max_h) (fec_n - 1)); try rep_lia.
                               rewrite extend_mx_spec.
                               destruct (Z_lt_le_dec j (Zlength (Znth n (int_to_poly_mx packets)))); simpl. 
                               2 : { rewrite int_to_poly_mx_length2 in l; lia. }
                               unfold get. unfold poly_mult_mod. (*unfold poly_add_mod.*)
                               (*TODO: make separate lemma*)
                               assert (poly_add_mod_bound: forall (p1 p2: poly),
                                  deg p1 < deg mod_poly ->
                                  deg p2 < deg mod_poly ->
                                  poly_add_mod mod_poly p1 p2 = p1 +~ p2). { intros.
                                unfold poly_add_mod. rewrite pmod_refl. reflexivity.
                                apply mod_poly_PosPoly. pose proof (poly_add_deg_max p1 p2). lia. }
                               rewrite <- poly_add_mod_bound. f_equal. (*bc I don't want to type out these terms*)
                               match goal with | [|- Int.repr ?p = Int.zero_ext 8 (Int.repr ?q) ] => 
                                 assert (Hinner: p = q) end. { 
                                f_equal. f_equal. rewrite int_to_poly_mx_spec. rewrite poly_of_int_inv. unfold f_to_poly.
                                repeat f_equal. rewrite Hinwlen. reflexivity. apply Znth_In; lia. assumption. } rewrite Hinner.
                               (*TODO: fix [simpl_repr] to deal w this*)
                               unfold Int.zero_ext. unfold poly_add_mod.
                               match goal with | [ |- context [poly_to_int (?p %~ mod_poly)]] =>
                                  pose proof (modulus_poly_bound (p %~ mod_poly) (pmod_lt_deg mod_poly p))
                                end. solve_repr_int.
                              (*This proof is quite ugly, need to organize*) 
                              apply proj2_sig. apply pmod_lt_deg. apply mod_poly_PosPoly. simpl.
                              rewrite Forall_Znth. simpl_map2d. intros x' Hx'. simpl_map2d.
                              rewrite Forall_Znth in H8. apply H8. lia.  simpl_map2d. lia. lia.
                              apply weight_mx_wf.
                              }
                              { rewrite <- iter_sepcon_arrays_remove_one. cancel. lia. lia. }
                              { rewrite Hinwlen. lia. apply Znth_In; lia. }
                            }
                          }
                        }
                        { (*other if condition (when we are past the end*)
                          forward. entailer!.
                          { (*this time, the proof of the invariant is much simpler*)
                            rewrite dot_prod_plus_1. rewrite extend_mx_spec.
                            destruct (Z_lt_le_dec j (Zlength (Znth n (int_to_poly_mx packets)))). simpl.
                            rewrite int_to_poly_mx_length2 in l.  rewrite Forall_Znth in H8. 
                            assert (Hn: 0 <= n < Zlength packets) by lia.
                            specialize (H8 n Hn). rewrite Int.signed_repr in H25. lia. rep_lia.
                            simpl. clear l. unfold poly_mult_mod. rewrite poly_mult_0_r.
                            rewrite pmod_refl. unfold poly_add_mod. rewrite poly_add_0_r.
                            rewrite pmod_refl. reflexivity.
                            all: try apply mod_poly_PosPoly. apply proj2_sig.
                            apply zero_lt_deg. apply mod_poly_PosPoly. simpl.
                            rewrite Forall_Znth. simpl_map2d. intros x' Hx'.
                            simpl_map2d. rewrite Forall_Znth in H8. apply H8; lia. simpl_map2d. lia.
                            lia. lia.
                          }
                        }
                        { (*increment ptr p*) forward.
                          { entailer!. apply field_address0_isptr. (*again, automate*)
                            unfold field_compatible0; simpl.
                            replace (fec_max_h) with (128)%Z in H39 by rep_lia.
                            replace (fec_n - 1) with 255%Z in H39 by rep_lia.
                            repeat(split; try apply H39; try rep_lia).
                          }
                          { (*innermost loop invariant preserved*) forward. Exists (n+1)%Z. rewrite_eqs; entailer!.
                            replace (fec_max_h) with (128)%Z in H39 by rep_lia.
                            replace (fec_n - 1) with 255%Z in H39 by rep_lia.
                            rewrite !field_compatible0_field_address0. simpl. solve_offset.
                            all: repeat(split; try apply H39; try rep_lia).
                          }
                        }
                        { lia. }
                      }
                      { (*end of inner loop*) forward. rewrite_eqs; entailer!. 
                        replace (Zlength packets) with n by lia. auto.
                      }
                   *** (*write data back to parity*) rewrite_eqs.
                      (*need to remove the ith element of parities from iter_sepcon so we can access it*)
                      assert (Hparlen: Zlength parity_ptrs = Zlength mx') by lia.
                      assert (Hpari : 0 <= i < Zlength mx') by lia.
                      rewrite (iter_sepcon_arrays_remove_one _ _ _ Hparlen Hpari). Intros.                      
                      assert_PROP (force_val (sem_add_ptr_int (tptr tuchar) Signed 
                        (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd) (Vint (Int.repr i))) = 
                        (field_address (tarray (tptr tuchar) (k + h)) (SUB (k + i)) pd)). { entailer!.
                        solve_offset. } forward.
                      { entailer!. rewrite Znth_app2; [ | lia]. 
                        replace (Zlength packets + i - Zlength packet_ptrs) with i by lia.
                        apply isptr_is_pointer_or_null. auto.
                      }
                      { entailer!. split. apply field_address0_isptr. (*auto again*)
                        unfold field_compatible0. simpl. repeat(split; try (apply H32); try lia).
                        apply isptr_force_sem_add_ptr_int; auto.
                        apply field_address0_isptr. (*auto again*)
                        unfold field_compatible0. simpl. repeat(split; try (apply H32); try lia).
                      }
                      { rewrite !Znth_app2 by lia. replace (k + i - Zlength packet_ptrs) with i by lia. 
                        forward.
                        { rewrite Forall_Znth in H20. rewrite H20; try lia. entailer!. }
                        { (*end of j loop*) forward. Exists (j+1)%Z. simpl_repr.
                          Exists (upd_Znth i mx' (upd_Znth j (Znth i mx') (poly_to_int (proj1_sig
                            (dot_prod (F:=F) (submatrix (F:=F) weight_mx h k)
                            (extend_mx (F:=F) (int_to_poly_mx packets) c) i j k))))). 
                          rewrite_eqs. entailer!.
                          { (*invariant preservation*) rewrite Zlength_upd_Znth. split. lia. split.
                            - rewrite Forall_Znth. rewrite Zlength_upd_Znth. intros i' Hi'. 
                              assert (Hii': i = i' \/ i <> i') by lia. destruct Hii' as [Heq | Hneq].
                              + subst. rewrite upd_Znth_same by auto. rewrite Zlength_upd_Znth.
                                rewrite Forall_Znth in H20. apply H20; lia.
                              + rewrite upd_Znth_diff by auto. rewrite Forall_Znth in H20. apply H20; lia.
                            - intros x y [[Hx Hy] | [Hx Hy]].
                              + rewrite upd_Znth_diff by lia. apply H21; lia.
                              + subst. rewrite upd_Znth_same by auto.
                                assert (Zlength (Znth i mx') = c). { rewrite Forall_Znth in H20. apply H20; lia. } 
                                assert (Hyj : 0 <= y < j \/ y = j) by lia. destruct Hyj as [Hbef | Hnow].
                                * rewrite upd_Znth_diff by lia. apply H21; lia.
                                * subst. rewrite upd_Znth_same by lia. reflexivity.
                          }
                          { (*need to get the iter_sepcon back together*)
                            remember (upd_Znth i mx' (upd_Znth j (Znth i mx') (poly_to_int
                              (proj1_sig (dot_prod (F:=F) (submatrix (F:=F) weight_mx (Zlength parity_ptrs) 
                              (Zlength packets))  (extend_mx (F:=F) (int_to_poly_mx packets) c) i j  
                              (Zlength packets)))))) as mx''.
                            assert (Hlens: Zlength parity_ptrs = Zlength mx''). subst. list_solve. 
                            assert (Hith: 0 <= i < Zlength mx'') by list_solve. 
                            rewrite (iter_sepcon_arrays_remove_one _ _ _ Hlens Hith).
                            entailer!.
                            (*TODO: make separate lemma*)
                            assert (remove_upd_Znth: forall {A: Type} (l: list A) (i : Z) (x: A),
                              0 <= i < Zlength l ->
                              remove_nth i (upd_Znth i l x) = remove_nth i l). { intros.
                              unfold remove_nth.
                              rewrite sublist_upd_Znth_l by lia. rewrite sublist_upd_Znth_r; [| lia | list_solve].
                              f_equal. f_equal. list_solve. }
                            rewrite remove_upd_Znth. rewrite upd_Znth_same by lia. rewrite Zlength_upd_Znth.
                              rewrite !upd_Znth_map by lia. cancel. lia.
                          }
                        }
                      }
                 +++ forward. (*end of j loop - postcondition*) Exists mx'.
                     replace j with c by lia. rewrite_eqs. entailer!. intros x Hx y Hy.
                     apply H21. lia.
               --- Intros mx'. rewrite_eqs. forward. Exists (i+1). Exists mx'. (*invariant for i loop*)
                   rewrite_eqs; entailer!. split. intros x y Hx Hy. apply H20; lia.
                   rewrite Z.mod_small by rep_lia. split; repeat f_equal; try rep_lia. solve_repr_int.
      * (*end of outer loop*) forward. rewrite_eqs. entailer!.
        assert (mx = (norev_mx (encode_list_mx (Zlength parity_ptrs) (Zlength packets) c packets))). {
          (*To prove that these are the same, we need to compare the elements pointwise*)
          (*TODO: do this in common*)
          assert (norev_mx_length1: forall l, Zlength (norev_mx l) = Zlength l). {
            unfold norev_mx. apply map_2d_Zlength1. }
          assert (norev_mx_length2: forall l i,
            Zlength (Znth i (norev_mx l)) = Zlength (Znth i l)). { 
            unfold norev_mx. apply map_2d_Zlength2. }
          assert (norev_mx_Znth: forall l i j,
            0 <= i < Zlength l ->
            0 <= j <  Zlength (Znth i l) ->
            Znth j (Znth i (norev_mx l)) = poly_to_int (f_to_poly (Znth j (Znth i l)))). {
            intros. unfold norev_mx. rewrite map_2d_Znth; auto. }
          pose proof (@list_matrix_multiply_wf _ (Zlength parity_ptrs) (Zlength packets) c (submatrix (F:=F) weight_mx (Zlength parity_ptrs) (Zlength packets))
            (extend_mx (F:=F) (int_to_poly_mx packets) c)). 
          assert (0 <= Zlength parity_ptrs) by lia. assert (0 <= c) by lia. specialize (H4 H34 H35). clear H34 H35.
          rename H4 into Hwf. assert (Hwf' := Hwf). destruct Hwf' as [Hmulen [Hredundant Hmulin]]. clear Hredundant.
          apply Znth_eq_ext. rewrite norev_mx_length1. unfold encode_list_mx. lia. 
          intros x Hx.
          apply Znth_eq_ext. rewrite Forall_Znth in H16. rewrite H16 by lia.
          rewrite norev_mx_length2. unfold encode_list_mx. rewrite Hmulin. reflexivity. apply Znth_In; lia.
          intros y Hy. assert (Zlength (Znth x mx) = c). rewrite Forall_Znth in H16. apply H16; lia.
          rewrite norev_mx_Znth; (unfold encode_list_mx ; try lia). 2: rewrite Hmulin; [ lia | apply Znth_In; lia].
          rewrite H14 by lia. unfold list_matrix_multiply. rewrite !prop_list_Znth by lia. reflexivity. }
        rewrite H4. cancel.
    + (*trivial error again*) rewrite_eqs. forward_if True.
      * contradiction.
      * forward. entailer!.
      * forward. entailer!. simpl. entailer!.
Qed.

(*Proof is done but super ugly - need to improve*)
  