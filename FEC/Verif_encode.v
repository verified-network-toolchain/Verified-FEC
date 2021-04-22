Require Import VST.floyd.proofauto.

Require Import fec.
Require Import Common.
Require Import CommonVST.
Require Import VandermondeByte.
Require Import Specs.
Require Import ByteFacts.
Require Import ZSeq.
Require Import FECTactics.
Require Import ReedSolomonList.

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


Section Encoder.

Opaque ByteField.byte_mul. 

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
       data_at Ews (tarray tschar k) (zseq fec_n (Vint Int.zero)) ps; INDEX_TABLES gv;
       data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx)
         (gv _fec_weights)] as SEPS.
  remember (iter_sepcon_arrays parity_ptrs (zseq h (zseq c Byte.zero)) :: SEPS) as SEPS1.
  (*first loop - check for FLAG_WANTED, trivial bc of precondition*)
  forward_loop (EX (i: Z),
    PROP (0 <= i <= k)
    (LOCALx  ( temp _i (Vint (Int.repr i)) :: LOCALS1 )
    (SEPx SEPS1)))
   break: 
    (PROP ( )  (LOCALx LOCALS1 (SEPx SEPS1))).
  { rewrite_eqs. forward. Exists 0%Z. rewrite_eqs. entailer!. }
  { Intros i. rewrite_eqs. forward_if.
    { forward. rewrite zseq_Znth by lia. entailer!.
      forward_if.
      { forward_if True.
        { contradiction. }
        { forward. entailer!. }
        { rewrite zseq_Znth in H9 by lia. inversion H9. }
      }
      { forward. Exists (i+1)%Z. rewrite_eqs. entailer!. simpl_repr_byte. }
    }
    { forward. rewrite_eqs. entailer!. }
  }
  { (*error check that is trivial*) rewrite_eqs. forward_if True. contradiction.
    forward. entailer!.
    (*outer loop - go through all rows selected by weight matrix*)
    rewrite <- HeqLOCALS. rewrite <- HeqSEPS. clear HeqLOCALS1 LOCALS1. clear HeqSEPS1 SEPS1.
    forward_loop (EX (i: Z),
      PROP (0 <= i <= h)
       (LOCALx (temp _i (Vint (Int.repr i)):: temp _z (Vint (Int.repr ((i - 1) mod 256))) :: LOCALS)
       (SEPx (iter_sepcon_arrays parity_ptrs 
        (pop_mx_mult h c k (submatrix (fec_n - 1) weight_mx h k) (extend_mx (F:=B) k c packets) i 0)  
        :: SEPS))))
      break: 
      (PROP ()  (LOCALx LOCALS (SEPx ((iter_sepcon_arrays parity_ptrs (encode_list_mx h k c packets)) :: SEPS)))).
    { rewrite_eqs. forward. Exists (0%Z).  rewrite_eqs. entailer!. rewrite pop_mx_mult_zero by lia.
      apply derives_refl'. reflexivity. }
    { (*loop body*) Intros i. rewrite_eqs.
      remember (pop_mx_mult h c k (submatrix (F:=B) (fec_n - 1) weight_mx h k) (extend_mx (F:=B) k c packets)i 0)
            as mx.
      assert (Hwf: wf_lmatrix mx h c) by (subst; apply pop_mx_mult_wf; rep_lia). destruct Hwf as [Hmxlen [_ Hinmx]].
      forward_if.
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
            unfold Int.add. assert (0 <= (i-1) mod 256 < 256) by (apply Z.mod_pos_bound; lia). simpl_repr_byte.
            f_equal. rewrite Zbits.Zzero_ext_mod by rep_lia.
            replace (two_p 8) with 256 by reflexivity. rewrite <- (Zmod_small 1 256) at 2 by rep_lia.
            rewrite <- Zplus_mod. rewrite Zmod_small; rep_lia. } rewrite Hmod. simpl_repr_byte. 
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
            { forward. entailer!. rewrite H10 in H14. apply (field_compatible_nullval _ _ _ _ H14). }
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
               forward_loop (EX (j: Z),
                PROP (0 <= j <= c)
                (LOCALx (temp _j (Vint (Int.repr j)) :: LOCALS1)
                  (SEPx (iter_sepcon_arrays parity_ptrs (pop_mx_mult h c k (submatrix (fec_n - 1) weight_mx h k) 
                    (extend_mx (F:=B) k c packets) i j) :: SEPS))))
                break: (PROP () (LOCALx LOCALS1 (SEPx (iter_sepcon_arrays parity_ptrs (pop_mx_mult h c k (submatrix (fec_n - 1) weight_mx h k) 
                    (extend_mx (F:=B) k c packets) i c) :: SEPS)))).
              { rewrite_eqs. forward. Exists 0%Z. rewrite_eqs. entailer!. }
              { Intros j. remember (pop_mx_mult h c k (submatrix (F:=B) (fec_n - 1) weight_mx h k)
               (extend_mx (F:=B) k c packets) i j) as mx'. rewrite_eqs. forward_if.
                { (*body of j- loop*) forward. simpl_repr_byte.
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
                  rewrite Hp. clear Hp. rewrite <- HeqLOCALS. rewrite <- HeqSEPS.
                  rewrite <- HeqLOCALS1. (*to reduce repetition, add a new LOCALS*)
                  remember (temp _j (Vint (Int.repr j)) :: LOCALS1) as LOCALS2.
                  (*Innermost loop (n loop) - our invariant is that y calculates the dot product up to n*)
                  forward_loop (EX (n: Z),
                    PROP (0 <= n <= k)
                    (LOCALx (temp _n (Vint (Int.repr n)) :: 
                      temp _p (field_address0 (tarray (tarray tuchar 255) 128) 
                              [ArraySubsc n; ArraySubsc i] (gv _fec_weights)) ::
                      temp _y (Vubyte (dot_prod (F:=B) (submatrix (F:=B) (fec_n - 1) weight_mx h k)
                         (extend_mx (F:=B) k c packets) i j n)) :: LOCALS2)
                    (SEPx (iter_sepcon_arrays parity_ptrs mx' :: SEPS))))
                  break:
                   (PROP ()
                   (LOCALx (temp _p (field_address0 (tarray (tarray tuchar 255) 128) 
                              [ArraySubsc k; ArraySubsc i] (gv _fec_weights)) ::
                      temp _y (Vubyte (dot_prod (F:=B) (submatrix (F:=B) (fec_n - 1) weight_mx h k)
                         (extend_mx (F:=B) k c packets) i j k)) :: LOCALS2)
                   (SEPx (iter_sepcon_arrays parity_ptrs mx' :: SEPS)))).
                  { rewrite_eqs; forward. Exists 0%Z. rewrite_eqs; entailer!. }
                  { Intros n. rewrite_eqs; forward_if.
                    { assert_PROP (Zlength lengths = k) as Hlengths. { entailer!. list_solve. } 
                      (*body of innermost loop*) forward. rewrite H6 by lia.
                      (*we have 2 cases: either we are in bounds, so we do usual multiplication, or
                        we are out of bounds, so we are implicitly extending the matrix with zeroes (which of course
                        does not affect the sum). We need to handle each case separately. The important thing
                        is that the dot product is still preserved*)
                      (*Unfortunately, folding the definitions makes "forward_if" take forever*)
                      forward_if ((PROP ()
                        LOCAL (
                          temp _t'5 (Vint (Int.repr (Zlength (Znth n packets)))); temp _n (Vint (Int.repr n));
                          temp _p (field_address0 (tarray (tarray tuchar 255) 128) [ArraySubsc n; ArraySubsc i] 
                            (gv _fec_weights));
                          temp _y (Vubyte (dot_prod (F:=B) (submatrix (F:=B) (fec_n - 1) weight_mx h k)
                            (extend_mx (F:=B) k c packets) i j (n + 1)));
                          temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr i)); temp _z (Vint (Int.repr i));
                          temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd); 
                          gvars gv; temp _k (Vint (Int.repr k)); temp _h (Vint (Int.repr h)); 
                          temp _c (Vint (Int.repr c)); temp _pdata pd; temp _plen pl; temp _pstat ps)
                        SEP (iter_sepcon_arrays parity_ptrs mx';
                          data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
                          iter_sepcon_arrays packet_ptrs packets;
                          data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl;
                          data_at Ews (tarray tschar k) (zseq fec_n (Vint Int.zero)) ps; 
                          INDEX_TABLES gv;
                          data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) 
                            (gv _fec_weights)))).
                      { (*We need to pull out the specific packet from [iter_sepcon] so we have a [data_at]*)
                        assert (Hlens: Zlength packet_ptrs = Zlength packets) by list_solve.
                        assert (Hjbound : 0 <= n < Zlength packets) by lia.
                        sep_apply (iter_sepcon_arrays_remove_one _ _ _ Hlens Hjbound). Intros. 
                        forward.
                        { rewrite Znth_app1 by list_solve. entailer!. }
                        { assert (Hjlen: 0 <= j < Zlength (Znth n packets)). { rewrite Int.signed_repr in H13. lia.
                            inner_length. }
                          assert_PROP (force_val (sem_add_ptr_int tuchar Signed (Znth n (packet_ptrs ++ parity_ptrs)) 
                            (Vint (Int.repr j))) =
                            field_address (tarray tuchar (Zlength (Znth n packets))) (SUB j) (Znth n packet_ptrs)). {
                            entailer!. rewrite Znth_app1 by list_solve. solve_offset. }
                          forward.
                          { entailer!. simpl_repr_byte. }
                          { entailer!. rewrite !Znth_app1 by lia. auto. }
                          { forward.
                            assert_PROP (field_address0 (tarray (tarray tuchar 255) 128) 
                                [ArraySubsc n; ArraySubsc i] (gv _fec_weights) =
                              field_address (tarray (tarray tuchar (fec_n -1)) (fec_max_h)) 
                                [ArraySubsc n; ArraySubsc i] (gv _fec_weights)). { entailer!. solve_offset. }
                            pose proof (weight_mx_wf) as [Hwlen [Hnotneed Hinwlen]].
                            forward.
                            { entailer!. rewrite !(Znth_default Inhabitant_list). rewrite rev_mx_val_Znth. simpl_repr_byte.
                              lia. inner_length. rewrite rev_mx_val_length1; lia. }
                            { entailer!.  solve_offset. }
                            { rewrite !(Znth_default Inhabitant_list) by (rewrite rev_mx_val_length1; lia).
                              rewrite rev_mx_val_Znth; [|lia| inner_length]. rewrite Znth_map_Vubyte by inner_length.
                              rewrite force_val_byte.
                              (*TODO: why is this ridiculously slow?*)
                              forward_call (gv, (Znth (Zlength (Znth i weight_mx) - n - 1) (Znth i weight_mx)),
                                  (Znth j (Znth n packets))).
                              { forward. entailer!.
                              (*finally, need to prove that the postcondition is satisfied*) 
                                { unfold Int.xor. rewrite !Int.unsigned_repr by simpl_repr_byte.
                                  rewrite dot_prod_plus_1 by lia. rewrite submatrix_spec by rep_lia.
                                  rewrite extend_mx_spec by rep_lia. 
                                  simpl.
                                  destruct (Z_lt_le_dec j (Zlength (Znth n packets))); [simpl | lia].
                                  rewrite byte_xor_fold. simpl_repr_byte. rewrite <- byte_int_repr by rep_lia.
                                  rewrite Byte.repr_unsigned. unfold get.
                                  replace (Zlength (Znth i weight_mx)) with (fec_n - 1) by inner_length. reflexivity.
                                }
                                { rewrite <- iter_sepcon_arrays_remove_one. cancel. lia. lia. }
                              }
                            }
                          }
                        }
                      }
                      { (*other if condition (when we are past the end*)
                        forward. entailer!.
                        (*this time, the proof of the invariant is much simpler*)
                        rewrite dot_prod_plus_1 by lia. 
                        rewrite extend_mx_spec by rep_lia. simpl.
                        destruct (Z_lt_le_dec j (Zlength (Znth n packets))); simpl.
                        assert (Hlenbound: Zlength (Znth n packets) <= c) by inner_length. 
                        rewrite Int.signed_repr in H13; rep_lia. clear l. 
                        rewrite ssralg.GRing.mulr0. rewrite ssralg.GRing.addr0. reflexivity.
                      }
                      { (*increment ptr p*) forward.
                        { entailer!. solve_offset. } 
                        { (*innermost loop invariant preserved*) forward. Exists (n+1)%Z.
                          rewrite_eqs; entailer!. solve_offset. }
                      }
                    }
                    { (*end of inner loop*) forward. rewrite_eqs; entailer!. 
                      replace (Zlength packets) with n by lia. auto.
                    }
                  }
                  { (*write data back to parity*) rewrite_eqs.
                    (*need to remove the ith element of parities from iter_sepcon so we can access it*)
                    assert (Hwf: wf_lmatrix mx' h c) by (subst; apply pop_mx_mult_wf; lia). 
                    destruct Hwf as [Hlenmx' [_ Hinmx']].
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
                      { (*end of j loop*) forward. Exists (j+1)%Z. simpl_repr_byte.
                        rewrite_eqs. replace (Zlength (Znth i mx')) with c by inner_length.
                        rewrite <- !(byte_int_repr (Byte.unsigned _)) by rep_lia.
                        rewrite Byte.repr_unsigned. rewrite upd_Znth_map. entailer!.
                        rewrite <- pop_mx_mult_set by lia.  
                        remember (pop_mx_mult (Zlength parity_ptrs) c (Zlength packets)
                          (submatrix (F:=B) (fec_n - 1) weight_mx (Zlength parity_ptrs) (Zlength packets))
                          (extend_mx (F:=B) (Zlength packets) c packets) i j) as mx'.
                        remember (set (F:=B) mx' i j (dot_prod (F:=B)
                          (submatrix (F:=B) (fec_n - 1) weight_mx (Zlength parity_ptrs) (Zlength packets))
                          (extend_mx (F:=B) (Zlength packets) c packets) i j (Zlength packets))) as mx''.
                        assert (Hwf: wf_lmatrix mx'' (Zlength parity_ptrs) c). { subst. apply set_wf.
                          apply pop_mx_mult_wf; rep_lia. } destruct Hwf as [Hlenmx'' [_ Hinmx'']].
                        assert (Hlens: Zlength parity_ptrs = Zlength mx'') by lia. 
                        assert (Hith: 0 <= i < Zlength mx'') by lia. 
                        rewrite (iter_sepcon_arrays_remove_one _ _ _ Hlens Hith).
                        replace (Zlength (Znth i mx'')) with c by inner_length. rewrite Heqmx''. unfold set. 
                        simpl in *. rewrite remove_upd_Znth by lia. cancel. rewrite upd_Znth_same by lia. cancel.
                      }
                    }
                  }
                }
                { forward. (*end of j loop - postcondition*)
                  replace j with c by lia. rewrite_eqs. entailer!. replace j with c by lia. cancel.
                }
              }
              { rewrite_eqs. forward. Exists (i+1). (*invariant for i loop*)
                rewrite_eqs; entailer!. split. simpl_repr_byte.
                rewrite Z.mod_small by rep_lia. repeat f_equal; rep_lia. 
                rewrite pop_mx_mult_row_finish by rep_lia. cancel.
              }
            }
          }
        }
      }
      { (*end of outer loop*) forward. rewrite_eqs. entailer!.
        replace i with (Zlength parity_ptrs) by lia. rewrite pop_mx_mult_done by lia.
        unfold encode_list_mx. cancel.
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
  