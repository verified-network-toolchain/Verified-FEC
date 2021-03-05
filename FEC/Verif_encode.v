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

Lemma remove_upd_Znth: forall {A: Type} (l: list A) (i : Z) (x: A),
  0 <= i < Zlength l ->
  remove_nth i (upd_Znth i l x) = remove_nth i l.
Proof. 
  intros. unfold remove_nth. list_solve.
Qed. 


(*TODO: see if this should be global or not*)
Section Encoder.
(*Hint Resolve iter_sepcon_arrays_local_facts : saturate_local.*)

Lemma body_fec_blk_encode : semax_body Vprog Gprog f_fec_blk_encode fec_blk_encode_spec.
Proof.
  start_function. forward. forward. 
  assert_PROP (force_val (sem_binary_operation' Oadd (tptr (tptr tuchar)) tint pd (Vint (Int.repr k))) =
    field_address0 (tarray (tptr (tuchar)) (k + h)) [ArraySubsc k] pd) as Hpd. { entailer!. solve_offset. } 
  rewrite Hpd.
  (*we want to pull out z from the locals*)
  erewrite LOCALx_Permutation; [| apply perm_swap].
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
  (*first loop - check for FLAG_WANTED, trivial bc of precondition*)
  forward_loop (EX (i: Z),
    PROP (0 <= i <= k)
    (LOCALx  ( temp _i (Vint (Int.repr i)) :: LOCALS1 )
    (SEPx SEPS1)))
   break: 
    (PROP ( )  (LOCALx LOCALS1 (SEPx SEPS1))).
  { rewrite_eqs. forward. Exists 0%Z. rewrite_eqs. entailer!. }
  { Intros i. rewrite_eqs. forward_if.
    { forward. rewrite Znth_list_repeat_inrange by lia. entailer!.
      forward_if.
      { forward_if True.
        { contradiction. }
        { forward. entailer!. }
        { rewrite Znth_list_repeat_inrange in H13 by lia. inversion H13. }
      }
      { forward. Exists (i+1)%Z. rewrite_eqs. entailer!. solve_repr_int. }
    }
    { forward. rewrite_eqs. entailer!. }
  }
  { (*error check that is trivial*) rewrite_eqs. forward_if True. contradiction.
    forward. entailer!.
    (*outer loop - go through all rows selected by weight matrix*)
    rewrite <- HeqLOCALS. rewrite <- HeqSEPS. clear HeqLOCALS1 LOCALS1. clear HeqSEPS1 SEPS1.
    (*Loop invariant: each time, up to the ith row of the resulting matrix is correct (ie, each position
     is the dot product of the correct row from the weight mx and column from the packet matrix)*)
    (*z is super annoying bc its unsigned but starts at -1*)
    forward_loop (EX (i:Z) (l: list (list Z)),
      PROP (0 <= i <= h; forall x y, 0 <= x < i -> 0 <= y < c -> Znth y (Znth x l) = 
        poly_to_int (proj1_sig (dot_prod (submatrix (fec_n - 1) weight_mx h k)
         (extend_mx k c (int_to_poly_mx packets)) x y k));
        Zlength l = h; Forall (fun l' => Zlength l' = c) l)
       (LOCALx (temp _i (Vint (Int.repr i)):: temp _z (Vint (Int.repr ((i - 1) mod 256))) :: LOCALS)
          (SEPx (iter_sepcon_arrays parity_ptrs l :: SEPS))))
    break: 
      (PROP ()
      (LOCALx (LOCALS)
        (SEPx ((iter_sepcon_arrays parity_ptrs (norev_mx (encode_list_mx h k c packets))) :: SEPS)))).
    { rewrite_eqs. forward. Exists (0%Z). Exists parities. rewrite_eqs. entailer!. }
    { (*loop body*) Intros i. Intros mx. rewrite_eqs. forward_if.
      { (*loop for z - basically trivial for us bc of precondition*) 
        rewrite <- HeqLOCALS. rewrite <- HeqSEPS.
        forward_loop (
          PROP () 
          (LOCALx (temp _i (Vint (Int.repr i)) :: temp _z (Vint (Int.repr ((i-1) mod 256))) :: LOCALS)
            (SEPx (iter_sepcon_arrays parity_ptrs mx :: SEPS))))
        break: 
          (PROP () 
          (LOCALx (temp _i (Vint (Int.repr i)) :: temp _z (Vint (Int.repr i)) :: LOCALS)
            (SEPx (iter_sepcon_arrays parity_ptrs mx :: SEPS)))). (*bc of simplifying assumption*)
        { rewrite_eqs; entailer!. }
        { rewrite_eqs. forward. forward. (*needed the mod 256 part bc z starts as -1, but now it is i*)
          assert (Hmod: (Int.zero_ext 8 (Int.add (Int.repr ((i - 1) mod 256)) (Int.repr 1))) = (Int.repr i)). {
            unfold Int.add. assert (0 <= (i-1) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
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
           (*We need the split the ith parity packet from the rest in the [iter_sepcon]*)
           rewrite (iter_sepcon_arrays_remove_one  _ _ _ Hlens Hith). Intros.
           forward; try rewrite Hznth.
          { entailer!. }
          { entailer!. solve_offset. }
          { forward_if False. (*If condition is true due to assumption*)
            { apply (denote_tc_test_eq_split _ (Znth i parity_ptrs) (Vlong (Int64.zero))).
              { sep_apply data_at_memory_block. sep_apply memory_block_valid_ptr. auto. simpl.
                inner_length. entailer!. 
              }
              { apply valid_pointer_zero64; auto. (*relies on 64 bit*) }
            }
            { forward. entailer!. rewrite H17 in H21. apply (field_compatible_nullval _ _ _ _ H21). }
            { forward. rewrite_eqs; entailer!. rewrite (iter_sepcon_arrays_remove_one _ _ _ Hlens Hith). entailer!. }
            { rewrite_eqs; entailer!. }
          }
        }
        { (*Now another trivial error check*) rewrite_eqs; forward_if True.
          { contradiction. }
          { forward. entailer!. }
          { (*now, at the (assert < FEC_MAX_H), which, again, is always true*) forward_if True.
            { forward. entailer!. }
            { rep_lia. (* the assertion holds*) }
            { (*finally, we are at the actual inner loop*)
               (*since i and w are not changing, we can add them to LOCALS (but we can't replace LOCALS bc
                 it is used in the POSTCONDITION*)
               rewrite <- HeqLOCALS. rewrite <- HeqSEPS.
               remember (temp _i (Vint (Int.repr i)) :: temp _z (Vint (Int.repr i)) :: LOCALS) as LOCALS1.
               forward_loop (EX (j : Z)(l: list (list Z)),
                PROP (0 <= j <= c;  Zlength l = h; Forall (fun l' => Zlength l' = c) l;
                  forall x y, (0 <= x < i /\ 0 <= y < c) \/ (x = i /\ 0 <= y < j) -> Znth y (Znth x l) = 
                  poly_to_int (proj1_sig (dot_prod (submatrix (fec_n - 1) weight_mx h k) 
                    (extend_mx k c (int_to_poly_mx packets)) x y k)))
                 (LOCALx (temp _j (Vint (Int.repr j)) :: LOCALS1)
                  (SEPx (iter_sepcon_arrays parity_ptrs l :: SEPS))))
                break: ( EX (l: list (list Z)), 
                  PROP (Zlength l = h; Forall (fun l' => Zlength l' = c) l;
                        forall x y, (0 <= x <= i /\ 0 <= y < c) -> Znth y (Znth x l) = 
                  poly_to_int (proj1_sig (dot_prod (submatrix (fec_n - 1) weight_mx h k) 
                    (extend_mx k c (int_to_poly_mx packets)) x y k)))
                 (LOCALx LOCALS1
                   (SEPx (iter_sepcon_arrays parity_ptrs l :: SEPS)))).
              { rewrite_eqs. forward. Exists 0%Z. Exists mx. rewrite_eqs. entailer!. intros x y [[Hx Hy] | [Hx Hy]].
                 apply H12; auto. lia. }
              { Intros j. Intros mx'. rewrite_eqs. forward_if.
                { (*body of j- loop*) forward.
                  assert_PROP (force_val (sem_add_ptr_int (tarray tuchar 255) Signed (gv _fec_weights)
                    (Vint (Int.repr i))) =
                    field_address (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (SUB i) (gv _fec_weights)) as Hp. {
                  entailer!. solve_offset. } forward. clear Hp.
                    (*Now we can express p as an actual address in the 2D array.*)
                  assert_PROP ((force_val (sem_binary_operation' Oadd (tarray (tarray tuchar 255) 128) tuchar 
                     (gv _fec_weights) (Vint (Int.repr i)))) = 
                     field_address0 (tarray (tarray tuchar 255) 128) [ArraySubsc 0; ArraySubsc i] 
                       (gv _fec_weights)) as Hp. {
                  entailer!. solve_offset. }
                  rewrite Hp. clear Hp. rewrite <- HeqLOCALS. rewrite <- HeqSEPS. solve_repr_int.
                  rewrite <- HeqLOCALS1. (*to reduce repetition, add a new LOCALS*)
                  remember (temp _j (Vint (Int.repr j)) :: LOCALS1) as LOCALS2.
                  (*Innermost loop (n loop) - our invariant is that y calculates the dot product up to n*)
                  forward_loop (EX (n: Z),
                    PROP (0 <= n <= k)
                    (LOCALx (temp _n (Vint (Int.repr n)) :: 
                      temp _p (field_address0 (tarray (tarray tuchar 255) 128) 
                              [ArraySubsc n; ArraySubsc i] (gv _fec_weights)) ::
                      temp _y (Vint (Int.repr (poly_to_int (proj1_sig
                         (dot_prod (F:=F) (submatrix (F:=F) (fec_n - 1) weight_mx h k)
                         (extend_mx (F:=F) k c (int_to_poly_mx packets)) i j n))))) :: LOCALS2)
                    (SEPx (iter_sepcon_arrays parity_ptrs mx' :: SEPS))))
                  break:
                   (PROP ()
                   (LOCALx (temp _p (field_address0 (tarray (tarray tuchar 255) 128) 
                              [ArraySubsc k; ArraySubsc i] (gv _fec_weights)) ::
                      temp _y (Vint (Int.repr (poly_to_int (proj1_sig
                         (dot_prod (F:=F) (submatrix (F:=F) (fec_n - 1) weight_mx h k)
                         (extend_mx (F:=F) k c (int_to_poly_mx packets)) i j k))))) :: LOCALS2)
                   (SEPx (iter_sepcon_arrays parity_ptrs mx' :: SEPS)))).
                  { rewrite_eqs; forward. Exists 0%Z. rewrite_eqs; entailer!. }
                  { Intros n. rewrite_eqs; forward_if.
                    { assert_PROP (Zlength lengths = k) as Hlengths. { entailer!. list_solve. } 
                      (*body of innermost loop*) forward. rewrite H10.
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
                            (dot_prod (F:=F) (submatrix (F:=F) (fec_n - 1) weight_mx h k)
                            (extend_mx (F:=F) k c (int_to_poly_mx packets)) i j (n + 1))))));
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
                      { (*We need to pull out the specific packet from [iter_sepcon] so we have a [data_at]*)
                        assert (Hlens: Zlength packet_ptrs = Zlength packets) by list_solve.
                        assert (Hjbound : 0 <= n < Zlength packets) by lia.
                        sep_apply (iter_sepcon_arrays_remove_one _ _ _ Hlens Hjbound). Intros. 
                        forward.
                        { rewrite Znth_app1 by list_solve. entailer!. }
                        { assert (Hjlen: 0 <= j < Zlength (Znth n packets)). { rewrite Int.signed_repr in H23. lia.
                            inner_length. }
                          assert_PROP (force_val (sem_add_ptr_int tuchar Signed (Znth n (packet_ptrs ++ parity_ptrs)) 
                            (Vint (Int.repr j))) =
                            field_address (tarray tuchar (Zlength (Znth n packets))) (SUB j) (Znth n packet_ptrs)). {
                            entailer!. rewrite Znth_app1 by list_solve. solve_offset. }
                          forward.
                          { entailer!. inner_length. }
                          { entailer!. rewrite !Znth_app1 by lia. auto. }
                          { forward.
                            assert_PROP (field_address0 (tarray (tarray tuchar 255) 128) 
                                [ArraySubsc n; ArraySubsc i] (gv _fec_weights) =
                              field_address (tarray (tarray tuchar (fec_n -1)) (fec_max_h)) 
                                [ArraySubsc n; ArraySubsc i] (gv _fec_weights)). { entailer!. solve_offset. }
                            pose proof (weight_mx_wf) as [Hwlen [Hnotneed Hinwlen]].
                            forward.
                            { entailer!. simpl_map2d. simpl_repr. inner_length. } 
                            { entailer!.  solve_offset. auto. }
                            { simpl_map2d.
                             (*For function, need data to b an Int.repr of something < 256*)
                              assert (Hdata: (Vint (Int.zero_ext 8 (Int.repr (Znth j (Znth n packets))))) = 
                               Vint (Int.repr ((Znth j (Znth n packets))))). {
                              rewrite Forall2D_Znth in H9. specialize (H9 n j Hjbound Hjlen). solve_repr_int. }
                              rewrite Hdata.
                              remember (poly_to_int (f_to_poly (Znth (Zlength (Znth i weight_mx) - n - 1) 
                                (Znth i weight_mx)))) as f.
                              remember (Znth j (Znth n packets)) as g.
                              assert (Hf: 0 <= f < fec_n). { rewrite Heqf. solve_poly_bounds. }
                              assert (Hg: 0 <= g < fec_n). { subst. inner_length. }
                              (*TODO: why is this ridiculously slow?*)
                              forward_call (gv, f, g). 
                              { forward. entailer!.
                              (*finally, need to prove that the postcondition is satisfied*) 
                                { unfold Int.xor. rewrite !unsigned_repr by simpl_repr. rewrite xor_poly_to_int.
                                  rewrite dot_prod_plus_1 by lia. simpl. rewrite submatrix_spec by rep_lia.
                                  rewrite extend_mx_spec by rep_lia.
                                  destruct (Z_lt_le_dec j (Zlength (Znth n (int_to_poly_mx packets)))); simpl. 
                                  2 : { rewrite int_to_poly_mx_length2 in l; lia. }
                                  unfold get. unfold poly_mult_mod.
                                  rewrite <- poly_add_mod_bound; [| solve_poly_bounds | solve_poly_bounds]. 
                                  f_equal. (*so I don't have to write out big term*)
                                  match goal with | [|- Int.repr ?p = Int.zero_ext 8 (Int.repr ?q) ] => 
                                    assert (Hinner: p = q) end. { 
                                   f_equal. f_equal. rewrite int_to_poly_mx_spec; [ | assumption].
                                   rewrite poly_of_int_inv. unfold f_to_poly.
                                   repeat f_equal. inner_length. } 
                                  rewrite Hinner. unfold poly_add_mod. simpl_repr.
                                }
                                { rewrite <- iter_sepcon_arrays_remove_one. cancel. lia. lia. }
                              }
                              { inner_length. } 
                            }
                          }
                        }
                      }
                      { (*other if condition (when we are past the end*)
                        forward. entailer!.
                        (*this time, the proof of the invariant is much simpler*)
                        rewrite dot_prod_plus_1 by lia. 
                        rewrite extend_mx_spec by rep_lia.
                        destruct (Z_lt_le_dec j (Zlength (Znth n (int_to_poly_mx packets)))); simpl.
                        rewrite int_to_poly_mx_length2 in l. 
                        assert (Zlength (Znth n packets) <= c) by inner_length. 
                        rewrite Int.signed_repr in H23; rep_lia. clear l. 
                        unfold poly_mult_mod. rewrite poly_mult_0_r. 
                        pose proof mod_poly_PosPoly as M.
                        rewrite pmod_refl; [ | apply M | apply zero_lt_deg; apply M].
                        unfold poly_add_mod. rewrite poly_add_0_r.
                        rewrite pmod_refl; [ | apply M | solve_poly_bounds]. reflexivity.
                      }
                      { (*increment ptr p*) forward.
                        { entailer!. solve_offset. auto. } 
                        { (*innermost loop invariant preserved*) forward. Exists (n+1)%Z.
                          rewrite_eqs; entailer!. solve_offset. auto.
                        }
                      }
                      { lia. }
                    }
                    { (*end of inner loop*) forward. rewrite_eqs; entailer!. 
                      replace (Zlength packets) with n by lia. auto.
                    }
                  }
                  { (*write data back to parity*) rewrite_eqs.
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
                    { entailer!. solve_offset. } 
                    { rewrite !Znth_app2 by lia. replace (k + i - Zlength packet_ptrs) with i by lia. 
                      forward.
                      { inner_length. entailer!. }
                      { (*end of j loop*) forward. Exists (j+1)%Z. simpl_repr.
                        Exists (upd_Znth i mx' (upd_Znth j (Znth i mx') (poly_to_int (proj1_sig
                          (dot_prod (F:=F) (submatrix (F:=F) (fec_n - 1) weight_mx h k)
                          (extend_mx (F:=F) k c (int_to_poly_mx packets)) i j k))))). 
                        rewrite_eqs. entailer!.
                        { (*invariant preservation*) rewrite Zlength_upd_Znth. repeat split; [lia | |].
                          - rewrite Forall_Znth. rewrite Zlength_upd_Znth. intros i' Hi'. 
                            assert (Hii': i = i' \/ i <> i') by lia. destruct Hii' as [Heq | Hneq].
                            + subst. rewrite upd_Znth_same by auto. rewrite Zlength_upd_Znth. inner_length.
                            + rewrite upd_Znth_diff by auto. inner_length.
                          - intros x y [[Hx Hy] | [Hx Hy]].
                            + rewrite upd_Znth_diff by lia. apply H19; lia.
                            + subst. rewrite upd_Znth_same by auto.
                              assert (Zlength (Znth i mx') = c) by inner_length. 
                              assert (Hyj : 0 <= y < j \/ y = j) by lia. destruct Hyj as [Hbef | Hnow].
                              * rewrite upd_Znth_diff by lia. apply H19; lia.
                              * subst. rewrite upd_Znth_same by lia. reflexivity.
                        }
                        { (*need to get the iter_sepcon back together*)
                          remember (upd_Znth i mx' (upd_Znth j (Znth i mx') (poly_to_int
                            (proj1_sig (dot_prod (F:=F) (submatrix (F:=F) (fec_n - 1) weight_mx (Zlength parity_ptrs) 
                            (Zlength packets))  (extend_mx (F:=F) (Zlength packets) c (int_to_poly_mx packets)) i j  
                            (Zlength packets)))))) as mx''.
                          assert (Hlens: Zlength parity_ptrs = Zlength mx'') by (subst; list_solve). 
                          assert (Hith: 0 <= i < Zlength mx'') by list_solve. 
                          rewrite (iter_sepcon_arrays_remove_one _ _ _ Hlens Hith).
                          entailer!.
                          rewrite remove_upd_Znth. rewrite upd_Znth_same by lia. rewrite Zlength_upd_Znth.
                          rewrite !upd_Znth_map by lia. cancel. lia.
                        }
                      }
                    }
                  }
                }
                { forward. (*end of j loop - postcondition*) Exists mx'.
                  replace j with c by lia. rewrite_eqs. entailer!. intros x Hx y Hy.
                  apply H19; lia.
                }
              }
              { Intros mx'. rewrite_eqs. forward. Exists (i+1). Exists mx'. (*invariant for i loop*)
                rewrite_eqs; entailer!. split. intros x y Hx Hy. apply H18; lia.
                rewrite Z.mod_small by rep_lia. split; repeat f_equal; try rep_lia. solve_repr_int.
              }
            }
          }
        }
      }
      { (*end of outer loop*) forward. rewrite_eqs. entailer!.
        assert (Hmx: mx = (norev_mx (encode_list_mx (Zlength parity_ptrs) (Zlength packets) c packets))). {
          (*To prove that these are the same, we need to compare the elements pointwise*)
          pose proof (@list_matrix_multiply_wf _ (Zlength parity_ptrs) (Zlength packets) c (submatrix (F:=F)
            (fec_n - 1) weight_mx (Zlength parity_ptrs) (Zlength packets))
            (extend_mx (F:=F) (Zlength packets) c (int_to_poly_mx packets))) as Hwf. 
          assert (Hplen: 0 <= Zlength parity_ptrs) by lia. assert (Hc: 0 <= c) by lia. 
          specialize (Hwf Hplen Hc). clear Hplen Hc. assert (Hwf' := Hwf). 
          destruct Hwf' as [Hmulen [Hother Hmulin]]. clear Hother. 
          apply Znth_eq_ext. simpl_map2d. unfold encode_list_mx. lia. 
          intros x Hx. apply Znth_eq_ext. inner_length. simpl_map2d. unfold encode_list_mx. inner_length.
          intros y Hy.  assert (Zlength (Znth x mx) = c) by inner_length.
          rewrite norev_mx_Znth; (unfold encode_list_mx ; try lia); [| inner_length].
          rewrite H12 by lia. unfold list_matrix_multiply. unfold mk_matrix. rewrite !prop_list_Znth by lia. reflexivity. }
        rewrite Hmx. cancel.
      }
    }
    { (*trivial error again*) rewrite_eqs. forward_if True.
      { contradiction. }
      { forward. entailer!. }
      { forward. entailer!. simpl. entailer!. }
    }
  }
Qed.

End Encoder.
  