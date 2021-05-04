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
Require Import PopArrays.

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
(*
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
    end.*)

Lemma default_arr: forall z, 0 <= z ->
  default_val (tarray tuchar z) = @zseq (reptype tuchar) z Vundef.
Proof. 
  intros z Hz. unfold default_val. simpl. rewrite zseq_list_repeat by lia. reflexivity.
Qed.

Ltac prove_eqb_type :=
 match goal with |- context [eqb_type ?A ?B] => 
  try change (eqb_type A B) with true;
  rewrite (proj2 (eqb_type_spec A B))
     by (repeat f_equal; rep_lia)
 end;
 cbv beta iota.

Ltac simply_msubst_extract_locals ::=
  unfold msubst_extract_locals, msubst_extract_local, VST_floyd_map;
  cbv iota zeta beta;
  simpl_PTree_get; 
  try prove_eqb_type.

Ltac solve_msubst_eval_LR ::=
  (unfold msubst_eval_LR;
  simpl;
  cbv beta iota zeta delta [force_val2 force_val1];
  rewrite ?isptr_force_ptr, <- ?offset_val_force_ptr by auto;
  unfold eval_vardesc;
  repeat match goal with |- match PTree.get ?A ?B with _ => _ end = _ =>
         let x := fresh "x" in set (x := PTree.get A B); hnf in x; subst x;
          cbv beta iota
       end;
   try prove_eqb_type;
  reflexivity) ||
  match goal with 
  |- msubst_eval_LR _ _ _ _ ?e _ = _ =>
   fail "Cannot symbolically evaluate expression" e "given the information in your LOCAL clause; did you forget a 'temp' declaration?"
  end.

Ltac solve_msubst_eval_lvalue ::=
  (simpl;
  cbv beta iota zeta delta [force_val2 force_val1];
  rewrite ?isptr_force_ptr, <- ?offset_val_force_ptr by auto;
  unfold eval_vardesc;
  repeat match goal with |- match match PTree.get ?A ?B with _ => _ end with _ => _ end = _ =>
         let x := fresh "x" in set (x := PTree.get A B); hnf in x; subst x;
          cbv beta iota
       end;
   try prove_eqb_type;
  reflexivity) ||
  match goal with 
  |- msubst_eval_lvalue _ _ _ _ ?e = _ =>
   fail "Cannot symbolically evaluate expression" e "given the information in your LOCAL clause; did you forget a 'temp' declaration?"
  end.

Ltac solve_msubst_eval_lvar ::=
  (unfold msubst_eval_lvar;
   unfold eval_vardesc, eval_lvardesc;
  repeat match goal with |- match PTree.get ?A ?B with _ => _ end = _ =>
         let x := fresh "x" in set (x := PTree.get A B); hnf in x; subst x;
          cbv beta iota
       end;
   try prove_eqb_type;
   reflexivity) ||
  match goal with 
  |- msubst_eval_lvar _ _ ?id _ = _ =>
   fail "Cannot symbolically evaluate lvar" id "given the information in your LOCAL clause; did you forget an 'lvar' declaration?"
  end.

(*Due to bug in VST (TODO: remove this once I change to master branch or update VST) *)
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

Lemma body_fec_blk_decode : semax_body Vprog Gprog f_fec_blk_decode fec_blk_decode_spec.
Proof.
start_function. (*use better names to make proof cleaner, since there will be a lot of goals and hypotheses*)
rename H into Hknh. rename H0 into Hhh. rename H1 into Hccols. rename H2 into Hpacklen.
rename H3 into Hpackptrlen. rename H4 into Hparptrlen. rename H5 into Hparlen. rename H6 into Hstatlen.
rename H7 into Hlenbound. rename H8 into Hlenspec. rename H9 into Hnumpars.
rename H10 into Hparsconsist. rename H11 into Hparsomelen.
rewrite <- (@find_parity_rows_filter _ (Zlength parities)) in Hnumpars by lia.
rewrite <- (@find_lost_filter _ k) in Hnumpars by lia.
assert_PROP (Zlength lengths = k) as Hlenslen. { entailer!. rewrite !Zlength_map in H8. assumption. } 
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
rewrite (grab_nth_SEP 9); simpl.
rewrite (grab_nth_SEP 1); simpl. rewrite (grab_nth_SEP 2); simpl.
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
(*TODO: maybe nest freezer so we can just unfold 1 layer at a time*)
freeze FR1 := (data_at_ Tsh (tarray tuchar fec_max_h) v_row)
       (data_at_ Tsh (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s)
       (data_at_ Tsh (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v)
       (iter_sepcon_arrays packet_ptrs packets) (iter_sepcon_options parity_ptrs parities)
       (data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd)
       (data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl) (INDEX_TABLES gv)
       (data_at Ews tint (Vint Int.zero) (gv _trace))
       (data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx)
       (gv _fec_weights)).
freeze FR2 := (data_at Ews (tarray tschar k) (map Vbyte stats) ps) (FRZL FR1).
(*First loop - populate lost/found packets*)
rewrite !data_at__tarray. rewrite !zseq_list_repeat by rep_lia.
replace (default_val tuchar) with Vundef by reflexivity.
forward_loop (EX (i: Z),
  PROP (0 <= i <= k)
  (LOCALx (temp _i (Vubyte (Byte.repr i)) :: temp _xh (Vubyte (Byte.repr (Zlength (find_lost stats i)))) 
    :: temp _xk (Vubyte (Byte.repr (Zlength (find_found stats i)))) :: LOCALS)
  (SEP (FRZL FR2; data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats i fec_max_h) v_lost;
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_found stats i fec_max_h) v_found))%assert5))
  break: 
    (PROP ()
    (LOCALx (temp _xh (Vubyte (Byte.repr (Zlength (find_lost stats k)))) :: 
             temp _xk (Vubyte (Byte.repr (Zlength (find_found stats k)))) :: LOCALS)
    (SEP (FRZL FR2; data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h)  v_lost;
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_found stats k fec_max_h)  v_found )%assert5))).
{ rewrite_eqs. forward. Exists 0. rewrite_eqs. entailer!.
  { rewrite !eqb_type_refl; split; reflexivity.
    (*Search eqb_type. (*What is this goal?*) rewrite !Zaux.Zeq_bool_true by auto.
    assert (Hattr: eqb_attr noattr noattr = true) by (rewrite eqb_attr_spec; auto). rewrite Hattr.
    simpl. auto.*)
  }
  { rewrite pop_find_lost_0. rewrite pop_find_found_0. cancel. }
}
{ Intros i. rewrite_eqs; forward_if.
  { rewrite Byte.unsigned_repr in H0 by rep_lia.
    assert (Hilen: (0 <= Byte.unsigned (Byte.repr i) < Zlength stats)) by simpl_repr_byte.
    thaw FR2.
    forward. simpl_repr_byte. freeze FR2 := (data_at Ews (tarray tschar k) (map Vbyte stats) ps) (FRZL FR1).
    forward_if (PROP ()
      (LOCALx (temp _i (Vubyte (Byte.repr i)) :: temp _xh (Vubyte (Byte.repr (Zlength (find_lost stats (i + 1))))) 
        :: temp _xk (Vubyte (Byte.repr (Zlength (find_found stats (i + 1))))) :: LOCALS)
      (SEP (FRZL FR2; data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats (i + 1) fec_max_h) v_lost; 
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_found stats (i + 1) fec_max_h) v_found)%assert5))).
    { (*xh case*) forward. pose proof (@find_lost_Zlength stats i (proj1 H)) as Hlostlen.
      forward. simpl_repr_byte. unfold Int.add. rewrite (Int.unsigned_repr (Zlength _)) by rep_lia.
      rewrite (Int.unsigned_repr 1) by rep_lia. rewrite Int.unsigned_repr by rep_lia. simpl_repr_byte.
      rewrite <- (byte_int_repr (Zlength (find_lost stats i))) by rep_lia.
      forward. (*TODO: this was the problematic one*)
      { entailer!. simpl_repr_byte. }
      { simpl_repr_byte. rewrite_eqs; entailer!.
        { rewrite !eqb_type_refl. (*rewrite !Zaux.Zeq_bool_true by auto. simpl.*) rewrite <- byte_int_repr by rep_lia.
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
    { (*xk case*) forward. pose proof (@find_found_Zlength stats i (proj1 H)) as Hfoundlen.
      forward. simpl_repr_byte. unfold Int.add. rewrite (Int.unsigned_repr (Zlength _)) by rep_lia.
      rewrite (Int.unsigned_repr 1) by rep_lia. rewrite Int.unsigned_repr by rep_lia. simpl_repr_byte.
      rewrite <- (byte_int_repr (Zlength (find_found stats i))) by rep_lia.
      forward.
      { entailer!. simpl_repr_byte. }
      { simpl_repr_byte. rewrite_eqs; entailer!.
        { rewrite !eqb_type_refl. (*rewrite !Zaux.Zeq_bool_true by auto. simpl.*) rewrite <- byte_int_repr by rep_lia.
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
      rewrite_eqs; entailer!. rewrite !eqb_type_refl. (*rewrite !Zaux.Zeq_bool_true by auto; simpl.*)
      rewrite <- byte_int_repr by rep_lia; repeat split; reflexivity. thaw FR2. cancel.
    }
  }
  { (*first loop postcondition*) forward. rewrite Byte.unsigned_repr in H0 by rep_lia.
    replace i with k by lia. rewrite_eqs; entailer!. rewrite !eqb_type_refl; split; reflexivity.
    (*rewrite !Zaux.Zeq_bool_true by auto; repeat split; reflexivity.*)
  }
}
{ remember (Zlength (find_lost stats k)) as xh.
  remember (Zlength (find_found stats k)) as xk. assert (Hk: 0 <= k) by lia.
  pose proof (@find_lost_Zlength stats k Hk) as Hxh. rewrite <-Heqxh in Hxh.
  pose proof (@find_found_Zlength stats k Hk) as Hxk. rewrite <-Heqxk in Hxk. clear Hk.
  rewrite_eqs; forward_if.
  { rewrite_eqs. (*replace fec_max_h with 128 by rep_lia.
    replace fec_max_cols with 16000 by rep_lia.*) forward.
    thaw FR2. thaw FR1. (*TODO: doesn't work ( in [solve_Forall2_fn_data_at])
      if the constants are opaque*)
    entailer!. replace 256 with (fec_max_h * 2) by rep_lia. replace 16000 with fec_max_cols by rep_lia.
    replace 128 with fec_max_h by rep_lia. cancel.
    (*If xh = 0, the result is trivial*)
    rewrite Int_repr_zero in H by rep_lia.
    rewrite Byte.unsigned_repr in H by rep_lia.
    rewrite decoder_list_correct_0; auto; try lia.
    rewrite <- (find_lost_filter (k:=(Zlength packets))); auto.
  }
  { forward. unfold Int.sub. rewrite !Int.unsigned_repr by rep_lia. simpl_repr_byte.
    (*Second loop - populate parity packet row/found*) 
    clear HeqLOCALS. clear LOCALS. 
    rewrite (grab_nth_LOCAL 6 (gvars gv)); simpl; [| list_solve]. 
    rewrite (grab_nth_LOCAL 7 (gvars gv)); simpl; [| list_solve].
    rewrite (grab_nth_LOCAL 2 (gvars gv)); simpl; [| list_solve]. 
    rewrite (grab_nth_LOCAL 4 (gvars gv)); simpl; [| list_solve]. 
    rewrite (grab_nth_LOCAL 6 (gvars gv)); simpl; [| list_solve].
    (*dont need LOCALS in the loop*)
    remember [temp _err (Vubyte Byte.zero); lvar _lost (tarray tuchar fec_max_h) v_lost;
       lvar _s (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s;
       lvar _v (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v; gvars gv;
       temp _k (Vint (Int.repr k)); temp _c (Vint (Int.repr c)); temp _pdata pd; 
       temp _plen pl; temp _pstat ps] as LOCALS.
    (*we do need these in the loop, but they are not changing*)
    remember (lvar _found (tarray tuchar fec_max_h) v_found :: lvar _row (tarray tuchar fec_max_h) v_row
              :: temp _xh (Vubyte (Byte.repr xh))
              :: temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd):: LOCALS) as LOCALS1.
    thaw FR2. thaw FR1.
    freeze FR1 := (data_at Ews (tarray tschar k) (map Vbyte stats) ps)
       (data_at_ Tsh (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s)
       (data_at_ Tsh (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v)
       (iter_sepcon_arrays packet_ptrs packets)
       (data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl) (INDEX_TABLES gv)
       (data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx)
         (gv _fec_weights)) (data_at Ews tint (Vint Int.zero) (gv _trace))
       (data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost).
    freeze FR2 := (FRZL FR1) (data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd)
        (iter_sepcon_options parity_ptrs parities).
    rewrite !data_at__tarray. rewrite !zseq_list_repeat by rep_lia.
    replace (default_val tuchar) with Vundef by reflexivity.
    (*The loop invariant - TODO : need to know that i <= fec_max_h - we know this
      idea is that xh valid parity ptrs exist - but probably easiest way to say this is that
      whole length is at most fec_max_h - technically, however, this doesnt always need to be true
      (but it will be, parities should be subset of encoder results) - see about this

in actuator - it knows h and only considers the first h - so this is an OK assumption to make - TODO
  change spec to include this, also put in result for i
  
  but we will also need condition that xh valid pointers exist - use filter for this and add it, or else
  this loop will access invalid memory - think about this with spec

  also also - need to fill in sepcon_array_option - most likely just add emp w None,
  dat_at with some, say pts is nullvall iff parity is None, then would neeed a result
  that if (pparity[i]) evaluates to false iff this is a nullval - is this true?
  need to see how if statement works first

  summary
  -need bound of fec_max_h on Zlength parities
  - need condition that number lost packets <= (myabe =) number parity packets
  - need to see about how if works, then fill it iter_sepcon_array_options

 need some result about bound of i, probably with bound of fec_max_h
      maybe - assume length of parities is <= fec_max_h? This should be OK*)
    forward_loop (EX (i: Z),
      PROP (0 <= i <= Zlength parities; 0 <= Zlength (find_parity_rows parities i) <= xh)
      (LOCALx (temp _i (Vint (Int.repr i)) :: temp _xr (Vubyte (Byte.repr (Zlength (find_parity_rows parities i)))) ::
        temp _xk (Vubyte (Byte.repr (xk + Zlength (find_parity_found parities (fec_n - 1) i)))) ::
        temp _q (Vint (Int.repr (fec_n - 2 - i))) :: LOCALS1)
      (SEP (FRZL FR2; data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row;
            data_at Tsh (tarray tuchar fec_max_h)  
              (pop_find_parity_found stats parities i fec_max_h k (fec_n - 1)) v_found))%assert5))
     break: ( EX (i: Z), PROP (0 <= i <= Zlength parities; Zlength (find_parity_rows parities i) = xh)
       (LOCALx (temp _xr (Vubyte (Byte.repr (Zlength (find_parity_rows parities i)))) ::
        temp _xk (Vubyte (Byte.repr (xk + Zlength (find_parity_found parities (fec_n - 1) i)))) ::
        temp _q (Vint (Int.repr (fec_n - 2 - i))) :: LOCALS1)
      (SEP (FRZL FR2; data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row;
            data_at Tsh (tarray tuchar fec_max_h)  
              (pop_find_parity_found stats parities i fec_max_h k (fec_n - 1)) v_found))%assert5)).
      (*TODO: see about postcondition*)
    { rewrite_eqs; forward. Exists 0. rewrite_eqs; entailer!.
      { rewrite !eqb_type_refl.
        pose proof (@find_parity_rows_Zlength parities 0). 
        repeat split; try reflexivity; try repeat f_equal; try rep_lia.
      }
      { rewrite pop_find_parity_found_0. rewrite pop_find_parity_rows_0. cancel. }
    }
    { Intros i. rewrite_eqs; forward_if.
      { rewrite !Byte.unsigned_repr in H2 by rep_lia.
        assert (Hi: i < Zlength parities). {
          assert (Hparbound: 
            Zlength (find_parity_rows parities i) < Zlength (find_parity_rows parities (Zlength parities))) by lia.
          apply find_parity_rows_inj in Hparbound; lia. }
        thaw FR2.
        assert_PROP (force_val (sem_add_ptr_int (tptr tuchar) Signed 
            (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd)
            (Vint (Int.repr i))) = field_address (tarray (tptr tuchar) (k + h)) (SUB (k + i)) pd) as Hpari. {
            entailer!. solve_offset. }
        (*It makes more sense to case of whether the ith entry is Some or None, then go through the VST proof 
          separately for each one. We remember the postcondition so we don't need to write it twice*)
        remember (PROP ()
            (LOCALx (temp _i (Vint (Int.repr i)) :: temp _xr (Vubyte (Byte.repr (Zlength (find_parity_rows parities (i + 1))))) ::
              temp _xk (Vubyte (Byte.repr (xk + Zlength (find_parity_found parities (fec_n - 1) (i + 1))))) ::
              temp _q (Vint (Int.repr (fec_n - 2 - i))) :: LOCALS1)
            (SEP (FRZL FR1; data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
              iter_sepcon_options parity_ptrs parities;
              data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities (i+1) fec_max_h) v_row;
              data_at Tsh (tarray tuchar fec_max_h)  
                (pop_find_parity_found stats parities (i+1) fec_max_h k (fec_n - 1)) v_found))%assert5)) as Ifpost.
        assert (Hlen: Zlength parity_ptrs = Zlength parities) by lia.
        assert (Hibound: 0 <= i < Zlength parities) by lia.
        destruct (Znth i parities) as [l |] eqn : Hparith.
        { rewrite (iter_sepcon_options_remove_one _ _ _ _ Hlen Hibound Hparith). Intros. forward.
          { rewrite Znth_app2 by lia. replace (k + i - Zlength packet_ptrs) with i by lia.
             entailer!.
          }
          { entailer!. solve_offset. }
          { forward_if Ifpost; try(rewrite Znth_app2 by lia); 
            try (replace (Zlength packets + i - Zlength packet_ptrs) with i by lia).
            { apply denote_tc_test_eq_split. rewrite !sepcon_assoc. rewrite sepcon_comm.
              rewrite !sepcon_assoc. rewrite sepcon_comm. rewrite !sepcon_assoc.
              apply sepcon_valid_pointer1. apply data_at_valid_ptr; auto.
              simpl. rewrite (Hparsomelen i) by (auto; rep_lia). lia.
              apply valid_pointer_zero64; auto.
            }
            { forward.
              pose proof (@find_parity_found_Zlength parities i (fec_n - 1)) as Hparfoundlen.
              simpl_repr_byte. forward. unfold Int.add. simpl_repr_byte.
              forward.
              { entailer!. split; try rep_lia.
                assert (Hpackbound: 0 <= Zlength packets <= Byte.max_unsigned) by rep_lia.
                pose proof (find_lost_found_Zlength stats Hpackbound) as Hxhxk.
                rewrite find_parity_rows_found_Zlength. rep_lia.
              }
              { forward. simpl_repr_byte. forward. unfold Int.add; simpl_repr_byte.
                forward.
                { entailer!. }
                { rewrite HeqIfpost. rewrite_eqs; entailer!.
                  { rewrite !eqb_type_refl. rewrite find_parity_rows_plus_1 by lia.
                    rewrite find_parity_found_plus_1 by lia. rewrite Hparith. 
                    rewrite <- !byte_int_repr by rep_lia. repeat split; f_equal; f_equal;
                    rewrite Zlength_app; list_solve.
                  }
                  { rewrite pop_find_parity_rows_plus_1 by rep_lia.
                    rewrite pop_find_parity_found_plus_1; try rep_lia.
                    2: { assert (Hpackbound: 0 <= Zlength packets <= Byte.max_unsigned) by rep_lia.
                        pose proof (find_lost_found_Zlength stats Hpackbound) as Hxhxk.
                        rewrite find_parity_rows_found_Zlength. rep_lia. }
                    rewrite Hparith. replace (fec_n - 1 - 1 - i) with (fec_n - 2 - i) by lia.
                    (*need to put [iter_sepcon_options] back together*)
                    rewrite (iter_sepcon_options_remove_one _ _ _ _ Hlen Hibound Hparith).
                    rewrite <- !byte_int_repr by rep_lia. cancel.
                  }
                }
              }
            }
            { (*contradiction*) rewrite Znth_app2 in H3 by lia.
               replace (k + i - Zlength packet_ptrs) with i in H3 by lia.
               rewrite <- Hparsconsist in H3 by lia. rewrite H3 in Hparith; inversion Hparith.
            }
            { (*TODO: it would be nice to not have to repeat this part, but not sure how
                except by doing cases in all the above*) rewrite HeqIfpost. rewrite_eqs; forward.
              unfold Int.sub. simpl_repr_byte. forward_if True.
              { forward. entailer!. rewrite !eqb_type_refl; auto. }
              { rep_lia. }
              { forward. unfold Int.add. simpl_repr_byte. Exists (i+1). rewrite_eqs; entailer!.
                { rewrite find_parity_rows_plus_1 by lia. rewrite Hparith. rewrite Zlength_app.
                  rewrite !eqb_type_refl. repeat split; try reflexivity. rep_lia. list_solve.
                  f_equal; f_equal; lia.
                }
                {  rewrite (iter_sepcon_options_remove_one _ _ _ _ Hlen Hibound Hparith). cancel. }
            }
          }
        }
      }
      { (*Now, we have the case where there is no parity packet. This will be simpler.*)
        assert (Hnull: @Znth _ Vundef i parity_ptrs = nullval) by (apply Hparsconsist; [ lia | assumption]).
        rewrite_eqs; forward.
        { rewrite Znth_app2 by lia. replace (k + i - Zlength packet_ptrs) with i by lia.
          entailer!. rewrite Hnull. auto.
        }
        { entailer!. solve_offset. }
        { forward_if Ifpost; try(rewrite Znth_app2 by lia); 
          try (replace (Zlength packets + i - Zlength packet_ptrs) with i by lia).
          { rewrite Hnull. apply denote_tc_test_eq_split. apply valid_pointer_null.
            apply valid_pointer_zero64; auto.
          }
          { forward. rewrite Znth_app2 in H3 by lia.
            replace (k + i - Zlength packet_ptrs) with i in H3 by lia.
            rewrite Hnull in H3. inversion H3.
          }
          { (*The actual null case*) forward. rewrite HeqIfpost. rewrite_eqs; entailer!.
            { rewrite find_parity_rows_plus_1 by lia. rewrite find_parity_found_plus_1 by lia.
              rewrite Hparith. rewrite !eqb_type_refl. auto.
            }
            { rewrite pop_find_parity_rows_plus_1 by rep_lia.
              rewrite pop_find_parity_found_plus_1; try rep_lia. (*TODO: maybe assert this before destruct*)
              2: { assert (Hpackbound: 0 <= Zlength packets <= Byte.max_unsigned) by rep_lia.
                        pose proof (find_lost_found_Zlength stats Hpackbound) as Hxhxk.
                        rewrite find_parity_rows_found_Zlength. rep_lia. }
              rewrite Hparith. cancel.
            }
          }
          { rewrite HeqIfpost. rewrite_eqs; forward. unfold Int.sub. simpl_repr_byte.
            forward_if True.
            { forward. entailer!. rewrite !eqb_type_refl; auto. }
            { rep_lia. }
            { forward. unfold Int.add; simpl_repr_byte. Exists (i+1). entailer!.
              rewrite find_parity_rows_plus_1 by lia. rewrite Hparith. rewrite !eqb_type_refl.
              repeat split; try rep_lia. f_equal; f_equal; lia.
            }
          }
        }
      }
    }
    { rewrite !Byte.unsigned_repr in H2 by rep_lia. forward. Exists i. rewrite_eqs; entailer!.
      rewrite !eqb_type_refl; auto.
    }
  }
  { Intros i. (*done with 2nd loop*) rewrite_eqs. thaw FR2. thaw FR1.
    forward. forward_if True; [contradiction | forward; entailer!; rewrite !eqb_type_refl; auto |].
    (*Start of matrix inversion loop*)
    (*Only things we need are v, lost, fec_weights, row*)
    freeze FR1 := (data_at Ews (tarray tschar k) (map Vbyte stats) ps)
      (data_at_ Tsh (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s)
      (iter_sepcon_arrays packet_ptrs packets)
      (data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl) (INDEX_TABLES gv)
      (data_at Ews tint (Vint Int.zero) (gv _trace))
      (data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd)
      (iter_sepcon_options parity_ptrs parities)
      (data_at Tsh (tarray tuchar fec_max_h)
            (pop_find_parity_found stats parities i fec_max_h k (fec_n - 1)) v_found).
    (*Things we need in the loop but aren't changing*)
    freeze FR2 := (FRZL FR1) 
       (data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights))
       (data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost)
       (data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row).
    clear HeqLOCALS1 LOCALS1 HeqLOCALS LOCALS.
    rewrite (grab_nth_LOCAL 12 (gvars gv)); simpl; [| list_solve]. 
    rewrite (grab_nth_LOCAL 6 (gvars gv)); simpl; [| list_solve]. 
    rewrite (grab_nth_LOCAL 7 (gvars gv)); simpl; [| list_solve]. 
    rewrite (grab_nth_LOCAL 10 (gvars gv)); simpl; [| list_solve]. 
    rewrite (grab_nth_LOCAL 12 (gvars gv)); simpl; [| list_solve]. 
    (*Locals we don't need in this loop*)
    remember [temp _t'29 (Vint Int.zero);
     temp _xr (Vubyte (Byte.repr (Zlength (find_parity_rows parities i))));
     temp _xk (Vubyte (Byte.repr (xk + Zlength (find_parity_found parities (fec_n - 1) i))));
     temp _q (Vint (Int.repr (fec_n - 2 - i))); lvar _found (tarray tuchar fec_max_h) v_found;
     temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd);
     temp _err (Vubyte Byte.zero); lvar _s (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s;
     temp _k (Vint (Int.repr k)); temp _c (Vint (Int.repr c)); temp _pdata pd; 
     temp _plen pl; temp _pstat ps] as LOCALS.
    (*Locals we need but aren't changing*)
    remember (lvar _v (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v
       :: lvar _lost (tarray tuchar fec_max_h) v_lost
          :: temp _xh (Vubyte (Byte.repr xh))
             :: lvar _row (tarray tuchar fec_max_h) v_row :: gvars gv :: LOCALS) as LOCALS1.
    assert (Hxh0: 0 < xh). { assert (Hxh0: 0 = xh \/ 0 < xh) by list_solve. destruct Hxh0 as [Hxh0 | Hxh0]; try lia.
      rewrite <- Hxh0 in H. rewrite !Byte.unsigned_repr in H by rep_lia. contradiction. } clear H.
    forward_loop (EX (j : Z),
      PROP (0 <= j <= xh)
      (LOCALx ((temp _j (Vint (Int.repr j))) :: LOCALS1)
      (SEP (FRZL FR2; data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h))
        (pop_find_inv xh (map_2d_rev id weight_mx) (find_parity_rows parities i) (find_lost stats k) j 0) v_v)%assert5)))
     break: (PROP () (LOCALx LOCALS1 (SEP (FRZL FR2; data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h))
         (pop_find_inv xh (map_2d_rev id weight_mx) (find_parity_rows parities i) (find_lost stats k) xh 0) v_v)%assert5))).
    { rewrite_eqs; forward. Exists 0. rewrite_eqs; entailer!.
      rewrite !eqb_type_refl; auto. rewrite data_at__tarray. (*Need to go 2D-1D array for loop and Gaussian elim*)
      rewrite data_at_2darray_concat. 
      { replace (fec_max_h * (fec_max_h * 2)) with (2 * fec_max_h * fec_max_h) by lia. apply derives_refl'.
        f_equal. rewrite pop_find_inv_0 by rep_lia. rewrite zseq_list_repeat by lia. 
        rewrite default_arr by lia. rewrite (@zseq_concat (reptype tuchar)) by lia. f_equal. lia.
      }
      { rewrite Zlength_list_repeat'; rep_lia. }
      { rewrite Forall_Znth. rewrite Zlength_list_repeat'; try rep_lia. intros y Hy.
        rewrite Znth_list_repeat_inrange by lia. rewrite default_arr by lia. rewrite zseq_Zlength; lia. }
      { auto. }
    }
    { Intros j. rewrite_eqs; forward_if.
      { rewrite Byte.unsigned_repr in H2 by rep_lia. thaw FR2. forward.
        { entailer!. }
        { entailer!. simpl_repr_byte. rewrite pop_find_parity_rows_Znth by rep_lia. simpl_repr_byte. }
        { rewrite pop_find_parity_rows_Znth by rep_lia.
          (*TODO: look at encoder to see how I handled the partially indexed 2D array*)
          assert (Hrowjbound: 0 <= Byte.unsigned (Znth j (find_parity_rows parities i)) < i). {
            assert (Hi: 0 <= i <= Byte.max_unsigned) by rep_lia.
            pose proof (find_parity_rows_bound parities Hi) as Hall. rewrite Forall_Znth in Hall.
            apply Hall. rep_lia. }
          assert_PROP (force_val (sem_add_ptr_int (tarray tuchar 255) Signed (gv _fec_weights)
                    (Vubyte (Znth j (find_parity_rows parities i)))) =
            field_address (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (SUB 
            (Byte.unsigned ((Znth j (find_parity_rows parities i))))) (gv _fec_weights)) as Hn. {
                  entailer!. solve_offset. rewrite <- (Byte.repr_unsigned (Znth j (find_parity_rows parities i))).
            solve_offset. } forward. clear Hn.
          replace (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) with (tarray (tarray tuchar 256) 128) by
           (repeat f_equal; repeat rep_lia). forward.
          { entailer!. rewrite !Byte.unsigned_repr by rep_lia.
            assert (Zlength (find_lost stats (Zlength packets)) <= 128) by rep_lia.
            assert (Int.min_signed <= j * Zlength (find_lost stats (Zlength packets)) <= Int.max_signed). {
              assert (j * Zlength (find_lost stats (Zlength packets)) <= 128 * 128) by nia. rep_lia. }
            assert (Int.min_signed <= j * Zlength (find_lost stats (Zlength packets)) * 2 <= Int.max_signed). {
               assert (j * Zlength (find_lost stats (Zlength packets)) * 2 <= 2 * 128 * 128) by nia. rep_lia. }
            rewrite !Int.signed_repr; rep_lia.
          }
          { replace (tarray (tarray tuchar 256) 128) with (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h)
            by (repeat f_equal; repeat rep_lia).
            rewrite <- HeqLOCALS. rewrite <- HeqLOCALS1.
            remember (temp _r (force_val (sem_binary_operation' Oadd (tarray tuchar 256) tint v_v
               (eval_binop Omul tint tint (eval_binop Omul tint tuchar (Vint (Int.repr j)) (Vubyte (Byte.repr xh)))
                (Vint (Int.repr 2))))) :: temp _n  (force_val
                (sem_binary_operation' Oadd (tarray (tarray tuchar 255) 128) tuchar 
                (gv _fec_weights) (Vubyte (Znth j (find_parity_rows parities i)))))
                :: temp _t'28 (Vubyte (Znth j (find_parity_rows parities i)))
                :: temp _j (Vint (Int.repr j)) :: LOCALS1) as LOCALS2.
            freeze FR2 := (FRZL FR1)
              (data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row).
            forward_loop (EX (ctr : Z),
              PROP (0 <= ctr <= xh)
              (LOCALx ((temp _i (Vint (Int.repr ctr))) :: LOCALS2)
              (SEP (FRZL FR2;
                 data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx)(gv _fec_weights);
                 data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost;
                 data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h))
                   (pop_find_inv xh (map_2d_rev id weight_mx) (find_parity_rows parities i) (find_lost stats k) j ctr) v_v))%assert5))
            break: (PROP () (LOCALx LOCALS2 
               (SEP (FRZL FR2;
                 data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights);
                 data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost;
                 data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h))
                   (pop_find_inv xh (map_2d_rev id weight_mx) (find_parity_rows parities i) (find_lost stats k) j xh) v_v))%assert5)).
            { rewrite_eqs; forward. Exists 0. rewrite_eqs; entailer!.
              rewrite !eqb_type_refl; auto.
            }
            { Intros i'. (*Need for both branches*)
              assert_PROP (force_val (sem_add_ptr_int tuchar Signed (force_val
                (sem_add_ptr_int tuchar Signed v_v (Vint
                (Int.mul (Int.mul (Int.repr j) (Int.repr (Byte.unsigned (Byte.repr xh)))) (Int.repr 2)))))
                (Vint (Int.repr i'))) = field_address (tarray tuchar (2 * fec_max_h * fec_max_h)) 
                (SUB (j * xh * 2 + i')) v_v) as Hri'. {
                  rewrite_eqs; entailer!.
                  assert (Zlength (find_lost stats (Zlength packets)) < 128) by rep_lia.
                  assert (Int.min_signed <= j * Zlength (find_lost stats (Zlength packets)) * 2 <= Int.max_signed). {
                  assert (j * Zlength (find_lost stats (Zlength packets)) * 2 <= 2 * 128 * 128) by nia. rep_lia. }
                  assert (0 <= j * Zlength (find_lost stats (Zlength packets)) * 2 + i' < 2 * fec_max_h * fec_max_h). {
                    rewrite !fec_max_h_eq; nia. }
                  solve_offset. }
              rewrite_eqs; forward_if.
              { rewrite Byte.unsigned_repr in H4 by rep_lia.
                rewrite_eqs; forward_if (PROP () (LOCALx ((temp _i (Vint (Int.repr i'))) :: LOCALS2)
                  (SEP (FRZL FR2;
                    data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights);
                    data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost;
                    data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h))
                      (upd_Znth (j * xh * 2 + i') (pop_find_inv xh (map_2d_rev id weight_mx) (find_parity_rows parities i) (find_lost stats k) j i')
                        (if (Z.eq_dec (i' + j + 1) xh) then Vubyte Byte.one else Vubyte Byte.zero)) v_v))%assert5)).
                { (*simplify if condition*) 
                  unfold Int.add in H5. rewrite !Byte.unsigned_repr in H5 by rep_lia. 
                  rewrite (Int.unsigned_repr i') in H5 by rep_lia. rewrite (Int.unsigned_repr j) in H5 by rep_lia.
                  rewrite !Int.unsigned_repr in H5 by rep_lia. apply (f_equal Int.unsigned) in H5.
                  rewrite !Int.unsigned_repr in H5 by rep_lia. 
                  forward. rewrite_eqs; entailer!.
                  rewrite !eqb_type_refl; auto. rewrite H5. rewrite left_sumbool_if by reflexivity.
                  simpl_repr_byte. rewrite field_at_data_at_cancel'. entailer!.
                }
                { (*Other case*)
                  unfold Int.add in H5. rewrite !Byte.unsigned_repr in H5 by rep_lia. 
                  rewrite (Int.unsigned_repr i') in H5 by rep_lia. rewrite (Int.unsigned_repr j) in H5 by rep_lia.
                  rewrite !Int.unsigned_repr in H5 by rep_lia. 
                  assert (Hijxh: i' + j + 1 <> xh). intro C. rewrite C in H5. contradiction. clear H5.
                  forward. rewrite_eqs; entailer!.
                  rewrite !eqb_type_refl; auto. rewrite right_sumbool_if by auto.
                  simpl_repr_byte. rewrite field_at_data_at_cancel'. entailer!.
                }
                { (*After the if condition*) rewrite_eqs; forward.
                  { entailer!. }
                  { rewrite pop_find_lost_Znth by rep_lia. entailer!. simpl_repr_byte. }
                  { rewrite pop_find_lost_Znth by rep_lia. 
                    assert_PROP (force_val (sem_add_ptr_int tuchar Signed (force_val
                      (sem_add_ptr_int (tarray tuchar 255) Signed (gv _fec_weights)
                      (Vubyte (Znth j (find_parity_rows parities i))))) (Vubyte (Znth i' (find_lost stats k)))) =
                    field_address (tarray (tarray tuchar (fec_n - 1)) fec_max_h) 
                      [ArraySubsc (Byte.unsigned (Znth i' (find_lost stats k)));
                       ArraySubsc (Byte.unsigned (Znth j (find_parity_rows parities i)))] (gv _fec_weights)). {
                    entailer!. rewrite <- (Byte.repr_unsigned (Znth j (find_parity_rows parities i))).
                    rewrite <- (Byte.repr_unsigned (Znth i' (find_lost stats (Zlength packets)))).
                    assert (Byte.unsigned (Znth i' (find_lost stats (Zlength packets))) < 255). {
                      assert (Hlostbound: Forall (fun x => 0 <= Byte.unsigned x < Zlength packets) (find_lost stats (Zlength packets))). {
                        apply find_lost_bound; rep_lia. }
                      rewrite Forall_Znth in Hlostbound. specialize (Hlostbound i'). rep_lia. } solve_offset. }
                    forward.
                    { entailer!. assert (0 <= Byte.unsigned (Znth j (find_parity_rows parities i)) < fec_max_h) by rep_lia.
                      pose proof (weight_mx_wf) as [Hwh [_ Hwn]].
                      rewrite !(@Znth_default _  Inhabitant_list). 2: { rewrite rev_mx_val_length1; rep_lia. }
                      rewrite rev_mx_val_Znth; try rep_lia. 2: { inner_length.
                        assert (Hlostbound: Forall (fun x => 0 <= Byte.unsigned x < Zlength packets) (find_lost stats (Zlength packets))). {
                        apply find_lost_bound; rep_lia. }
                        rewrite Forall_Znth in Hlostbound. specialize (Hlostbound i'). rep_lia. }
                      simpl_repr_byte.
                    }
                    { (*Need to simplify r + i + xh before dereference*)
                      assert_PROP (force_val (sem_add_ptr_int tuchar Signed (force_val
                       (sem_add_ptr_int tuchar Signed (force_val (sem_add_ptr_int tuchar Signed v_v
                       (Vint (Int.mul (Int.mul (Int.repr j) (Int.repr (Byte.unsigned (Byte.repr xh))))
                       (Int.repr 2))))) (Vint (Int.repr i')))) (Vubyte (Byte.repr xh))) =
                      field_address (tarray tuchar (2 * fec_max_h * fec_max_h)) 
                      (SUB (j * xh * 2 + i' + xh)) v_v) as Hrixh. { entailer!.
                        assert (Zlength (find_lost stats (Zlength packets)) < 128) by rep_lia.
                        assert (Int.min_signed <= j * Zlength (find_lost stats (Zlength packets)) * 2 <= Int.max_signed). {
                          assert (j * Zlength (find_lost stats (Zlength packets)) * 2 <= 2 * 128 * 128) by nia. rep_lia. }
                        assert (0 <= j * Zlength (find_lost stats (Zlength packets)) * 2 + i' + Zlength (find_lost stats (Zlength packets)) <
                                2 * fec_max_h * fec_max_h). {
                          assert (j * Zlength (find_lost stats (Zlength packets)) * 2 + i' + Zlength (find_lost stats (Zlength packets))<=
                              126 * 127 * 2 + 126 + 127) by nia. rep_lia. }
                        solve_offset. }
                      forward. forward. Exists (i' + 1). rewrite_eqs; entailer!.
                      { simpl_repr_byte. rewrite !eqb_type_refl; auto. }
                      { rewrite pop_find_inv_set by rep_lia. rewrite field_at_data_at_cancel'.
                        apply derives_refl'. repeat f_equal.
                        - destruct (Z.eq_dec (j + i' + 1) (Zlength (find_lost stats (Zlength packets)))); simpl;
                          destruct (Z.eq_dec (i' + j + 1) (Zlength (find_lost stats (Zlength packets)))); try reflexivity;
                          try lia.
                        - unfold get. assert (0 <= Byte.unsigned (Znth j (find_parity_rows parities i)) < fec_max_h) by rep_lia.
                          pose proof (weight_mx_wf) as [Hwh [_ Hwn]].
                          assert (0 <= Byte.unsigned (Znth i' (find_lost stats (Zlength packets))) <
                            Zlength (Znth (Byte.unsigned (Znth j (find_parity_rows parities i))) weight_mx)). {
                            inner_length. assert (Hlostbound: Forall (fun x => 0 <= Byte.unsigned x < Zlength packets) (find_lost stats (Zlength packets))). {
                              apply find_lost_bound; rep_lia. }
                            rewrite Forall_Znth in Hlostbound. specialize (Hlostbound i'). rep_lia. }
                          rewrite !(@Znth_default _  Inhabitant_list). 2: { rewrite rev_mx_val_length1; rep_lia. }
                          rewrite rev_mx_val_Znth by rep_lia.
                          rewrite map_2d_rev_Znth by rep_lia. reflexivity.
                      }
                    }
                  }
                }
              }
              { (*end of inner loop*) forward. rewrite_eqs; entailer!. rewrite !eqb_type_refl; auto.
                rewrite Byte.unsigned_repr in H4 by rep_lia.
                replace i' with (Zlength (find_lost stats (Zlength packets))) by rep_lia.
                rewrite pop_find_inv_finish by rep_lia. cancel.
              }
            }
            { (*inv preservation outer loop*) rewrite_eqs; forward. Exists (j+1). rewrite_eqs; entailer!.
              rewrite !eqb_type_refl; auto. rewrite pop_find_inv_finish by rep_lia. thaw FR2. cancel.
            }
          }
        }
      }
      { (*end of outer loop*) forward. rewrite Byte.unsigned_repr in H2 by rep_lia. rewrite_eqs; entailer!.
        rewrite !eqb_type_refl; auto. replace j with (Zlength (find_lost stats (Zlength packets))) by lia.
        cancel.
      }
    }
    { (*Inverse loop is done! Next step is Gaussian elim, small err, then mx mult loop
        (a bit more complicated bc whole array is not used - this one is 2D though, may need other "pop"*)


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