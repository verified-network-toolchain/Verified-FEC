Require Import VST.floyd.proofauto.

Require Import fec.
Require Import MatrixTransform.
Require Import CommonVST.
Require Import VandermondeByte.
Require Import Specs.
Require Import ByteFacts.
Require Import ZSeq.
Require Import FECTactics.
Require Import ReedSolomonList.

Set Bullet Behavior "Strict Subproofs".



Section Decoder.

Opaque ByteField.byte_mul.

Lemma int_byte_zero: Vint (Int.repr 0) = Vubyte Byte.zero.
Proof.
  reflexivity.
Qed.
Check LOCALx_Permutation.

(*Let's see, may be harder this*)
Lemma sublist_nil'': forall {A: Type} (lo hi: Z),
  @sublist A lo hi [] = [].
Proof.
  intros A lo hi. destruct (sublist lo hi []) eqn : S.
  - reflexivity.
  - assert (In a []). apply (sublist_In lo hi). rewrite S. left. reflexivity.
    destruct H.
Qed.

Lemma delete_nth_bounds: forall {A: Type} (n: nat) (l: list A),
  (n >= length l)%nat ->
  delete_nth n l = l.
Proof.
  intros A n. induction n; intros l Hlen; simpl; destruct l; try reflexivity.
  - simpl in Hlen. lia. 
  - simpl in Hlen. rewrite IHn. reflexivity. lia.
Qed.

(*Can't use [sublist_len_1] bc we don't have Inhabitant*)
Lemma sublist_hd: forall {A: Type} (x: A) (l: list A),
  sublist 0 1 (x :: l) = [x].
Proof.
  intros A x l. assert (Hinhab: Inhabitant A). apply x.
  rewrite sublist_len_1. rewrite Znth_0_cons. reflexivity. list_solve.
Qed.

Lemma sublist_cons: forall {A: Type} (x: A) (l: list A) (lo hi: Z),
  0 <= lo ->
  sublist (lo + 1) (hi + 1) (x :: l) = sublist lo hi l.
Proof.
  intros A x l lo hi Hlo. replace (x :: l) with ([x] ++ l) by reflexivity.
  rewrite sublist_app2 by list_solve. f_equal; list_solve.
Qed.

(*[delete_nth] is used in the definition of [grab_nth_SEP], but [remove_nth] is easier to prove things about*)
Lemma delete_remove_nth: forall {A: Type} (n: nat) (l: list A),
  delete_nth n l = remove_nth (Z.of_nat n) l.
Proof.
  intros A n. induction n; intros l.
  - simpl. unfold remove_nth. simpl. destruct l; simpl. reflexivity.
    rewrite sublist_1_cons. symmetry. apply sublist_same; list_solve.
  - simpl delete_nth. destruct l.
    + unfold remove_nth. rewrite !sublist_nil''. reflexivity.
    + assert (0 <= Z.of_nat n < Zlength l \/ ~(0 <= Z.of_nat n < Zlength l)) as [Hin | Hout] by lia.
      * rewrite IHn. unfold remove_nth. rewrite (sublist_split 0 1 (Z.of_nat (S n))); [ | lia | list_solve].
        rewrite sublist_hd. rewrite sublist_1_cons. replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
        replace (Zlength (a :: l)) with (Zlength l + 1) by list_solve. rewrite sublist_cons by lia.
        replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. reflexivity.
      * rewrite delete_nth_bounds by (rewrite <- ZtoNat_Zlength; lia).
        unfold remove_nth. rewrite sublist_same_gen; [| lia | list_solve].
        rewrite sublist_nil_gen by list_solve. rewrite app_nil_r. reflexivity.
Qed.

Lemma grab_nth_LOCAL: forall (n: nat) (d: localdef) (Q: list localdef),
  0 <= Z.of_nat n < Zlength Q ->
  LOCALx Q = LOCALx (nth n Q d :: delete_nth n Q).
Proof.
  intros n d Q Hlen. rewrite delete_remove_nth. apply LOCALx_Permutation.
  unfold remove_nth. rewrite <- (sublist_same 0 (Zlength Q)) at 1; [| lia | list_solve].
  rewrite (sublist_split 0 (Z.of_nat n) (Zlength Q)) at 1; [| lia | list_solve].
  rewrite (sublist_split (Z.of_nat n) (Z.of_nat n + 1) (Zlength Q)); [|lia|list_solve].
  rewrite (@sublist_len_1 _ d) by lia. unfold Znth.
  destruct (zlt (Z.of_nat n) 0); [lia |]. clear g. rewrite Nat2Z.id. 
  eapply perm_trans. apply Permutation_app_comm. simpl. 
  apply perm_skip. apply Permutation_app_comm.
Qed.

(*TODO: maybe move somewhere*)
Lemma left_proj_sumbool_if: forall {A: Prop} {C: Type} (H: A) (x: {A} + {~ A}) (c1 c2: C),
   (if (proj_sumbool x) then c1 else c2) = c1.
Proof.
  intros A C Ha x c1 c2. destruct x; auto. contradiction.
Qed.

Lemma left_sumbool_if:  forall {A: Prop} {C: Type} (H: A) (x: {A} + {~ A}) (c1 c2: C),
   (if x then c1 else c2) = c1.
Proof.
  intros A C Ha x c1 c2. destruct x; auto. contradiction.
Qed.

Lemma right_proj_sumbool_if: forall {A: Prop} {C: Type} (H: ~A) (x: {A} + {~ A}) (c1 c2: C),
   (if (proj_sumbool x) then c1 else c2) = c2.
Proof.
  intros A C Ha x c1 c2. destruct x; auto. contradiction.
Qed.

Lemma right_sumbool_if:  forall {A: Prop} {C: Type} (H: ~A) (x: {A} + {~ A}) (c1 c2: C),
   (if x then c1 else c2) = c2.
Proof.
  intros A C Ha x c1 c2. destruct x; auto. contradiction.
Qed.

Ltac simpl_sum_if :=
  lazymatch goal with
  | [ |- context [ (if (proj_sumbool ?x) then ?c1 else ?c2) ]] => 
      try (rewrite left_proj_sumbool_if; [ | assumption]);
      try (rewrite right_proj_sumbool_if; [ | assumption])
  | [ |- context [ (if ?x then ?c1 else ?c2) ] ] => 
      try (rewrite left_sumbool_if; [ | assumption]);
      try (rewrite right_sumbool_if; [ | assumption])
  end.

Ltac solve_eval_vardesc :=
  try reflexivity;
  unfold eval_vardesc;
  match goal with
  |- match ?A with _ => _ end = _ => let x := fresh "X" in set (X := A); hnf in X; subst X
  end; cbv beta iota;
  match goal with
  |- match ?A with _ => _ end = _ => let x := fresh "X" in set (X := A); hnf in X; subst X
  end; cbv beta iota; rewrite -> (proj2 (eqb_type_spec _ _)) by (repeat f_equal; rep_lia);
  reflexivity.

Ltac solve_msubst_eval_LR ::=
  (unfold msubst_eval_LR; simpl; cbv[force_val2 force_val1];
    rewrite ?isptr_force_ptr, <- ?offset_val_force_ptr by auto; solve_eval_vardesc) ||
    match goal with
    | |- msubst_eval_LR _ _ _ _ ?e _ = _ =>
          fail "Cannot symbolically evaluate expression" e
           "given the information in your LOCAL clause; did you forget a 'temp' declaration?"
    end.

Ltac solve_msubst_eval_lvalue ::=
  (simpl; cbv[force_val2 force_val1]; rewrite ?isptr_force_ptr, <- ?offset_val_force_ptr by auto; solve_eval_vardesc) ||
    match goal with
    | |- msubst_eval_lvalue _ _ _ _ ?e = _ =>
          fail "Cannot symbolically evaluate expression" e
           "given the information in your LOCAL clause; did you forget a 'temp' declaration?"
    end.


Lemma body_fec_blk_decode : semax_body Vprog Gprog f_fec_blk_decode fec_blk_decode_spec.
Proof.
start_function. (*use better names to make proof cleaner, since there will be a lot of goals and hypotheses*)
rename H into Hknh. rename H0 into Hhh. rename H1 into Hccols. rename H2 into Hpacklen.
rename H3 into Hpackptrlen. rename H4 into Hparptrlen. rename H5 into Hparlen. rename H6 into Hstatlen.
rename H7 into Hlenbound. rename H8 into Hlenspec.
(*Lots of initializations*)
forward. forward. forward. forward. simpl_repr_byte. forward.
assert_PROP (force_val (sem_binary_operation' Oadd (tptr (tptr tuchar)) tint pd (Vint (Int.repr k))) =
    field_address0 (tarray (tptr (tuchar)) (k + h)) [ArraySubsc k] pd) as Hpd. { entailer!. solve_offset. } 
rewrite Hpd. clear Hpd. forward_if True; [contradiction | forward; entailer! |].
forward_if True; [contradiction | forward; entailer! |].
(*Clean up locals and seps*)
rewrite !int_byte_zero. 
match goal with
   |- semax _ _ ?c _ => set (C := c)
  end.
replace (16000) with fec_max_cols by rep_lia.
(*TODO: see if this causes issues - 128 refers to fec_max_h OR fec_max_n - fec_max_h, but for our
  purposes, it only matters that it is not unfolded ever*)
replace 128 with fec_max_h by rep_lia. replace 256 with (fec_max_h * 2) by rep_lia. subst C.
(*In the first loop, only "lost" and "found" are changing, so we bring them to the front, Likewise with
  "xh" and "xk"*)
rewrite (grab_nth_SEP 1). simpl. rewrite (grab_nth_SEP 2); simpl.
rewrite (grab_nth_LOCAL 2 (gvars gv)); simpl; [| list_solve]. 
rewrite (grab_nth_LOCAL 3 (gvars gv)); simpl; [| list_solve].
(*hide all of the non-changing local and sep variables*)
remember [temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd);
   temp _xr (Vubyte Byte.zero); temp _err (Vubyte Byte.zero); lvar _row (tarray tuchar fec_max_h) v_row;
   lvar _found (tarray tuchar fec_max_h) v_found; lvar _lost (tarray tuchar fec_max_h) v_lost;
   lvar _s (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s;
   lvar _v (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v; gvars gv;
   temp _k (Vint (Int.repr k)); temp _c (Vint (Int.repr c)); temp _pdata pd; 
   temp _plen pl; temp _pstat ps] as LOCALS.
remember [data_at_ Tsh (tarray tuchar fec_max_h) v_row;
       data_at_ Tsh (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s;
       data_at_ Tsh (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v;
       iter_sepcon_arrays packet_ptrs packets; iter_sepcon_options parity_ptrs parities;
       data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
       data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl;
       data_at Ews (tarray tschar k) (map Vbyte stats) ps; INDEX_TABLES gv;
       data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx)
         (gv _fec_weights)] as SEPS. 
(*First loop - populate lost/found packets*)
rewrite !data_at__tarray. rewrite !zseq_list_repeat by rep_lia.
replace (default_val tuchar) with Vundef by reflexivity.
forward_loop (EX (i: Z),
  PROP (0 <= i <= k)
  (LOCALx (temp _i (Vubyte (Byte.repr i)) :: temp _xh (Vubyte (Byte.repr (Zlength (find_lost stats i)))) 
    :: temp _xk (Vubyte (Byte.repr (Zlength (find_found stats i)))) :: LOCALS)
  (SEPx (data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats i fec_max_h) v_lost :: 
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_found stats i fec_max_h) v_found :: SEPS))))
  break: 
    (PROP ()
    (LOCALx (temp _xh (Vubyte (Byte.repr (Zlength (find_lost stats k)))) :: 
             temp _xk (Vubyte (Byte.repr (Zlength (find_found stats k)))) :: LOCALS)
    (SEPx (data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h)  v_lost :: 
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_found stats k fec_max_h)  v_found :: SEPS)))).
{ rewrite_eqs. forward. Exists 0. rewrite_eqs. entailer!.
  { (*What is this goal?*) rewrite !Zaux.Zeq_bool_true by auto.
    assert (Hattr: eqb_attr noattr noattr = true) by (rewrite eqb_attr_spec; auto). rewrite Hattr.
    simpl. auto.
  }
  { rewrite pop_find_lost_0. rewrite pop_find_found_0. cancel. }
}
{ Intros i. rewrite_eqs; forward_if.
  { rewrite Byte.unsigned_repr in H0 by rep_lia.
    assert (Hilen: (0 <= Byte.unsigned (Byte.repr i) < Zlength stats)) by simpl_repr_byte.
    forward. simpl_repr_byte. 
    forward_if (PROP ()
      (LOCALx (temp _i (Vubyte (Byte.repr i)) :: temp _xh (Vubyte (Byte.repr (Zlength (find_lost stats (i + 1))))) 
        :: temp _xk (Vubyte (Byte.repr (Zlength (find_found stats (i + 1))))) :: LOCALS)
      (SEPx (data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats (i + 1) fec_max_h) v_lost :: 
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_found stats (i + 1) fec_max_h) v_found :: SEPS)))).
    { (*xh case*) forward. assert (Zlength (find_lost stats i) <= i). { unfold find_lost.
      replace i with (Zlength (Ziota 0 i)) at 2 by (rewrite Zlength_Ziota; lia). apply find_lost_found_aux_Zlength. }
      forward. simpl_repr_byte. unfold Int.add. rewrite (Int.unsigned_repr (Zlength _)) by rep_lia.
      rewrite (Int.unsigned_repr 1) by rep_lia. rewrite Int.unsigned_repr by rep_lia. simpl_repr_byte.
      rewrite <- (byte_int_repr (Zlength (find_lost stats i))) by rep_lia.
      forward. (*TODO: this was the problematic one*)
      { entailer!. simpl_repr_byte. }
      { simpl_repr_byte. rewrite_eqs; entailer!.
        { rewrite !Zaux.Zeq_bool_true by auto. simpl. rewrite <- byte_int_repr by rep_lia.
          rewrite find_lost_plus_1 by lia. rewrite find_found_plus_1 by lia. repeat simpl_sum_if.
          repeat split; try reflexivity. f_equal; f_equal.  
          rewrite <- cat_app. list_solve.
        }
        { rewrite pop_find_lost_plus_1 by rep_lia.
          rewrite pop_find_found_plus_1 by rep_lia. repeat simpl_sum_if.
          rewrite <- byte_int_repr by rep_lia. cancel.
        }
      }
    }
    { (*xk case*) forward. assert (Zlength (find_found stats i) <= i). { unfold find_lost.
      replace i with (Zlength (Ziota 0 i)) at 2 by (rewrite Zlength_Ziota; lia). apply find_lost_found_aux_Zlength. }
      forward. simpl_repr_byte. unfold Int.add. rewrite (Int.unsigned_repr (Zlength _)) by rep_lia.
      rewrite (Int.unsigned_repr 1) by rep_lia. rewrite Int.unsigned_repr by rep_lia. simpl_repr_byte.
      rewrite <- (byte_int_repr (Zlength (find_found stats i))) by rep_lia.
      forward.
      { entailer!. simpl_repr_byte. }
      { simpl_repr_byte. rewrite_eqs; entailer!.
        { rewrite !Zaux.Zeq_bool_true by auto. simpl. rewrite <- byte_int_repr by rep_lia.
          rewrite find_lost_plus_1 by lia. rewrite find_found_plus_1 by lia. repeat simpl_sum_if.
          repeat split; try reflexivity. f_equal; f_equal.  
          rewrite <- cat_app. list_solve.
        }
        { rewrite pop_find_lost_plus_1 by rep_lia.
          rewrite pop_find_found_plus_1 by rep_lia. repeat simpl_sum_if.
          rewrite <- byte_int_repr by rep_lia. cancel.
        }
      }
    }
    { rewrite_eqs; forward. Exists (i+1). simpl_repr_byte. unfold Int.add.
      rewrite (Int.unsigned_repr 1) by rep_lia. rewrite (Int.unsigned_repr i) by rep_lia. simpl_repr_byte.
      rewrite_eqs; entailer!. rewrite !Zaux.Zeq_bool_true by auto; simpl.
      rewrite <- byte_int_repr by rep_lia; repeat split; reflexivity.
    }
  }
  { (*first loop postcondition*) forward. rewrite Byte.unsigned_repr in H0 by rep_lia.
    replace i with k by lia. rewrite_eqs; entailer!.
    rewrite !Zaux.Zeq_bool_true by auto; repeat split; reflexivity.
  }
}
{ remember (Zlength (find_lost stats k)) as xh.
  remember (Zlength (find_found stats k)) as xk.
  rewrite_eqs; forward_if.
  { rewrite_eqs.     replace fec_max_h with 128 by rep_lia.
    replace fec_max_cols with 16000 by rep_lia. forward. (*TODO: doesn't work ( in [solve_Forall2_fn_data_at])
      if the constants are opaque*)
    entailer!. (*TODO: go back to spec, add condition that there is at least 1 missing packet*)

(*Tactic debug stuff - first resturn



  apply semax_seq with FF; [  | apply semax_ff ]; clear_Delta_specs.
try fold_frame_function_body.
  match goal with
  | |- @semax ?CS _ ?Delta ?Pre (Sreturn ?oe) _ =>
    match oe with
    | None =>
        eapply semax_return_None;
        [ (reflexivity || fail 1000 "Error: return type is not Tvoid")
        | (solve_return_outer_gen || fail 1000 "unexpected failure in forward_return. Do not remove the stackframe")
        | (solve_canon_derives_stackframe || fail 1000 "stackframe is unfolded or modified.")
        | try match goal with Post := _ : ret_assert |- _ => subst Post; unfold abbreviate end;
          try change_compspecs CS;
          solve_return_inner_gen
        | entailer_for_return]
    | Some ?ret =>
        let v := fresh "v" in
        let H := fresh "HRE" in
        do_compute_expr1 Delta Pre constr:(Ecast ret (ret_type Delta));
        match goal with v' := _, H':_ |- _ => rename H' into H; rename v' into v end;
        subst v;
        eapply semax_return_Some;
        [ exact H
        | entailer_for_return
        | (solve_return_outer_gen|| fail 1000 "unexpected failure in forward_return. Do not remove the stackframe")
        | idtac "A"  (*(solve_canon_derives_stackframe

|| fail 1000 "stackframe is unfolded or modified.")*)
        | try match goal with Post := _ : ret_assert |- _ => subst Post; unfold abbreviate end;
          try change_compspecs CS;
          solve_return_inner_gen
        | entailer_for_return];
        clear H
        
    end
  end.
   try unfold stackframe_of. simple eapply canonicalize_stackframe.
     prove_local2ptree.
    replace fec_max_h with 128 by rep_lia.
    replace fec_max_cols with 16000 by rep_lia.
    solve_Forall2_fn_data_at.

 Print solve_Forall2_fn_data_at.

  solve
  [ simple apply canonicalize_stackframe_emp
  | try unfold stackframe_of; simple eapply canonicalize_stackframe;
     [ prove_local2ptree | solve_Forall2_fn_data_at ] ].
    Print Ltac solve_canon_derives_stackframe.


solve_canon_derives_stackframe.



    Print Ltac forward_return.

 forward_return.




 forward.
  {
    { 


 (*TODO: this was the problematic one*)


 forward.

 entailer!.


 (*TODO: prob make tactic*)
          rewrite find_found_plus_1 by lia. Check Z.eq_dec.  Check @left.

          rewrite Htest by assumption.


 f_equal. apply ProofIrrelevance.proof_irrelevance.


 Search (left). = left ?y).

 reflexivity.
            (sumbool 


          assert (Z.eq_dec (Byte.signed (Znth i stats)) 1 = left H1).


 with (@left _ _ H1) by auto.
          destruct (Z.eq_dec (Byte.signed (Znth i stats)) 1)



          Print sumbool.
          Check Z.eq_dec.

 Search find_lost.
      


rewrite semax_seq_skip. eapply semax_seq'. ensure_open_normal_ret_assert; hoist_later_in_pre.  
  match goal with
  | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e1 ?e2) _ =>
    check_expression_by_value e1;
    let T1 := fresh "T1" in evar (T1: PTree.t val);
    let T2 := fresh "T2" in evar (T2: PTree.t (type * val));
    let G := fresh "GV" in evar (G: option globals);
    let LOCAL2PTREE := fresh "LOCAL2PTREE" in
    assert (local2ptree Q = (T1, T2, nil, G)) as LOCAL2PTREE;
    [subst T1 T2 G; prove_local2ptree |];
    (*first [ store_tac_with_hint LOCAL2PTREE | store_tac_no_hint LOCAL2PTREE | SEP_type_contradict LOCAL2PTREE Delta e1 R | hint_msg LOCAL2PTREE Delta e1];
    clear T1 T2 LOCAL2PTREE*) idtac
  end.
Print store_tac_with_hint.

eapply semax_PTree_field_store_with_hint;
   [ exact
   LOCAL2PTREE
   | reflexivity
   | reflexivity
   | solve_msubst_eval_expr ||
       fail 1000
        "Cannot evaluate right-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)"
   (*| solve_msubst_eval_lvalue ||
       fail 1000
        "Cannot evaluate left-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)"
  *)| .. ].

Print solve_msubst_eval_lvalue.

  (simpl; cbv[force_val2 force_val1]; rewrite ?isptr_force_ptr, <- ?offset_val_force_ptr by auto). 
  solve_eval_vardesc.

; reflexivity) ||
    match goal with
    | |- msubst_eval_lvalue _ _ _ _ ?e = _ =>
          fail "Cannot symbolically evaluate expression" e
           "given the information in your LOCAL clause; did you forget a 'temp' declaration?"
    end.


 Print  solve_msubst_eval_lvalue.

| eassumption
   | check_hint_type
   | search_field_at_in_SEP ||
       fail 1000 "unexpected failure in store_tac_with_hint." "Required field_at does not exists in SEP"
   | auto || fail 1000 "unexpected failure in store_tac_with_hint." "Cannot prove writable_share"
   | convert_stored_value
   | first
   [ apply data_equal_congr; solve_store_rule_evaluation
   | fail 1000 "unexpected failure in store_tac_with_hint." "unexpected failure in computing stored result" ]
   | first
   [ entailer_for_store_tac
   | fail 1000 "unexpected failure in store_tac_with_hint." "unexpected failure in entailer_for_store_tac" ] ]
.
assert_fails (store_tac_with_hint LOCAL2PTREE).
eapply semax_PTree_field_store_with_hint.

store_tac_no_hint LOCAL2PTREE.
first [ store_tac_with_hint LOCAL2PTREE | store_tac_no_hint LOCAL2PTREE].

  eapply semax_PTree_field_store_with_hint;
   [ exact
   LOCAL2PTREE
   | reflexivity
   | reflexivity
   | solve_msubst_eval_expr ||
       fail 1000
        "Cannot evaluate right-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)"
   | solve_msubst_eval_lvalue ||
       fail 1000
        "Cannot evaluate left-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)"
   | eassumption
   | check_hint_type
   | search_field_at_in_SEP ||
       fail 1000 "unexpected failure in store_tac_with_hint." "Required field_at does not exists in SEP"
   | auto || fail 1000 "unexpected failure in store_tac_with_hint." "Cannot prove writable_share"
   | convert_stored_value
   | first
   [ apply data_equal_congr; solve_store_rule_evaluation
   | fail 1000 "unexpected failure in store_tac_with_hint." "unexpected failure in computing stored result" ]
   | first
   [ entailer_for_store_tac
   | fail 1000 "unexpected failure in store_tac_with_hint." "unexpected failure in entailer_for_store_tac" ] ]
.
  eapply semax_PTree_field_store_no_hint;
   [ exact
   LOCAL2PTREE
   | reflexivity
   | reflexivity
   | reflexivity
   | solve_msubst_eval_expr ||
       fail 1000
        "Cannot evaluate right-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)"
   | solve_msubst_eval_LR ||
       fail 1000
        "Cannot evaluate left-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)"
   | solve_msubst_efield_denote ||
       fail 1000
        "Cannot evaluate left-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)"
   | econstructor
   | solve_field_address_gen
   | search_field_at_in_SEP
   | auto || fail 1000 "unexpected failure in store_tac_no_hint." "Cannot prove writable_share"
   | convert_stored_value
   | first
   [ apply data_equal_congr; solve_store_rule_evaluation
   | fail 1000 "unexpected failure in store_tac_no_hint." "unexpected failure in computing stored result" ]
   | first
   [ entailer_for_store_tac
   | fail 1000 "unexpected failure in store_tac_no_hint." "unexpected failure in entailer_for_store_tac" ]
   | first
   [ solve_legal_nested_field_in_entailment
   | fail 1000 "unexpected failure in store_tac_no_hint."
      "unexpected failure in solve_legal_nested_field_in_entailment" ] ].

Print store_tac_no_hint. 


(*store_tac_no_hint LOCAL2PTREE.*)
  eapply semax_PTree_field_store_no_hint;
  [ exact LOCAL2PTREE
  | reflexivity
  | reflexivity
  | reflexivity
  | (solve_msubst_eval_expr                 || fail 1000 "Cannot evaluate right-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)")
 | .. ]. {

  (unfold msubst_eval_LR;
  simpl;
  cbv beta iota zeta delta [force_val2 force_val1];
  rewrite ?isptr_force_ptr, <- ?offset_val_force_ptr by auto). solve_eval_vardesc.

unfold eval_vardesc.
match goal with
|- match ?A with _ => _ end = _ => let x := fresh "X" in set (X := A); hnf in X; subst X
end. cbv beta iota.
match goal with
|- match ?A with _ => _ end = _ => let x := fresh "X" in set (X := A); hnf in X; subst X
end. cbv beta iota.
rewrite -> (proj2 (eqb_type_spec _ _)) by (repeat f_equal; rep_lia). reflexivity.

Search eqb_type.

rewrite eqb_type_refl.

 simpl.

  reflexivity).

Locate solve_msubst_eval_LR.
  solve_msubst_eval_LR.

 | (solve_msubst_eval_LR                   || fail 1000 "Cannot evaluate left-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)")
  | (solve_msubst_efield_denote             || fail 1000 "Cannot evaluate left-hand-side expression (sometimes this is caused by missing LOCALs in your precondition)")
  | econstructor
  | solve_field_address_gen
  | search_field_at_in_SEP (* This line can fail. If it does not, the following should not fail. *)
  | (auto                                   || fail 1000 "unexpected failure in store_tac_no_hint."
                                                         "Cannot prove writable_share")
  | convert_stored_value
  | first [apply data_equal_congr; solve_store_rule_evaluation
                                             | fail 1000 "unexpected failure in store_tac_no_hint."
                                                         "unexpected failure in computing stored result"]
  | first [entailer_for_store_tac            | fail 1000 "unexpected failure in store_tac_no_hint."
                                                         "unexpected failure in entailer_for_store_tac"]
  | first [solve_legal_nested_field_in_entailment
                                             | fail 1000 "unexpected failure in store_tac_no_hint."
                                                         "unexpected failure in solve_legal_nested_field_in_entailment"]
  ].

store_tac_no_hint LOCAL2PTREE.

Print Ltac store_tac.
  lazymatch goal with
  | |- ENTAIL _, _ |-- (_ * stackframe_of _)%logic => clean_up_stackframe; entailer_for_return
  | |- _ =>
        try apply semax_ff; check_Delta; check_POSTCONDITION; repeat rewrite <- seq_assoc;
         lazymatch goal with
         | |- semax _ _ (Sreturn _
                         _) _ =>
               apply semax_seq with FF; [  | apply semax_ff ]; clear_Delta_specs; forward_return
         | |- semax _ _ (Sreturn _) _ => clear_Delta_specs; forward_return
         | |- semax _ _ (break;
                         _) _ => apply semax_seq with FF; [  | apply semax_ff ]; forward_break
         | |- semax _ _ (continue;
                         _) _ => apply semax_seq with FF; [  | apply semax_ff ]; forward_continue
         | |- semax _ _ (break;) _ => forward_break
         | |- semax _ _ (continue;) _ => forward_continue
         | |- semax _ _ (/*skip*/;) _ => fwd_skip
         | |- semax _ _ ?c0 _ =>
               match c0 with
               | (_
                  _)%C => idtac
               | _ => rewrite semax_seq_skip
               end;
                match goal with
                | |- semax _ _ (?e1.?id1 = _;
                                ?s2) _ => try_forward_store_union_hack e1 s2 id1
                | |- semax _ _ (?c
                                _) _ =>
                      check_precondition; eapply semax_seq';
                       [ forward1 c
                       | fwd_result; Intros; abbreviate_semax; try (fwd_skip; try_clean_up_stackframe) ]
                end
         end
  end.
      Print Ltac forward.
      rewrite <- (byte_int_repr (Zlength (find_lost stats i))) by rep_lia. 
      forward.

 Search Share.top. forward.
      assert (Harrbound: 0 <= (Zlength (find_lost stats i)) < fec_max_h) by rep_lia. Print lvar.

 forward.
      rewrite_eqs; forward.

 simpl_repr_byte.  
      
      assert (Int.min_signed <= (Zlength (find_lost stats i)) <= Int.max_signed) by rep_lia.

 Search Zlength find_lost_found_aux. forward. simpl_repr_byte.

 forward.


 rewrite !eqb_attr_spec by auto. Search eqb_attr.


 Search Zeq_bool.


 auto.


 a. admit. (*rewrite_eqs; forward. Exists 0. rewrite_eqs; entailer!. Search data_at_ data_at.*)}
{ Intros i. rewrite_eqs; forward_if.
  { rewrite Byte.unsigned_repr in H0 by rep_lia.  assert (0 <= Byte.unsigned (Byte.repr i) < Zlength (map Byte.repr stats)).
   rewrite Zlength_map.
    simpl_repr_byte. rewrite Zlength_map in H1. forward. simpl_repr_byte. forward_if True.
    Search byte 1.

Byte.signed (Byte.repr (Znth i stats)) = 1


 rewrite Hstatlen. lia.
  


{ contradiction. }
{ forward. entailer!. }
{ 

 forward.*)