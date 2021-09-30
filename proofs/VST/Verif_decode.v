(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

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

(*small lemmas that are helpful*)
Lemma get_inhab: forall l i j, @get byte (inhabitant_F B) l i j = 
   @get (ssralg.GRing.Field.sort B) (inhabitant_F B) l i j.
Proof.
  reflexivity.
Qed.


Lemma body_fec_blk_decode : semax_body Vprog Gprog f_fec_blk_decode fec_blk_decode_spec.
Proof.
start_function. (*use better names to make proof cleaner, since there will be a lot of goals and hypotheses*)
rename H into Hknh. rename H0 into Hhh. rename H1 into Hccols. rename H2 into Hbp. rename H3 into Hpacklen.
rename H4 into Hpackptrlen. rename H5 into Hparptrlen. rename H6 into Hparlen. rename H7 into Hstatlen.
rename H8 into Hlenbound. rename H9 into Hlenspec. rename H10 into Hnumpars.
rename H11 into Hparsconsist. rename H12 into Hparsomelen. rename H13 into Hstatsvals.
rewrite <- (@find_parity_rows_filter _ parbound) in Hnumpars by lia.
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
(*Note: 128 refers to fec_max_h OR fec_max_n - fec_max_h, but for our purposes, we just need it to be opaque*)
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
freeze FR1 := (data_at_ Tsh (tarray tuchar fec_max_h) v_row)
       (data_at_ Tsh (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s)
       (data_at_ Tsh (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v)
       (iter_sepcon_arrays packet_ptrs packets) (iter_sepcon_options parity_ptrs parities)
       (data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd)
       (data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl) (FIELD_TABLES gv)
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
  { rewrite !eqb_type_refl; split; reflexivity.  }
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
        { rewrite !eqb_type_refl. rewrite <- byte_int_repr by rep_lia.
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
        { rewrite !eqb_type_refl. rewrite <- byte_int_repr by rep_lia.
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
      rewrite_eqs; entailer!. rewrite !eqb_type_refl.
      rewrite <- byte_int_repr by rep_lia; repeat split; reflexivity. thaw FR2. cancel.
    }
  }
  { (*first loop postcondition*) forward. rewrite Byte.unsigned_repr in H0 by rep_lia.
    replace i with k by lia. rewrite_eqs; entailer!. rewrite !eqb_type_refl; split; reflexivity.
  }
}
{ remember (Zlength (find_lost stats k)) as xh.
  remember (Zlength (find_found stats k)) as xk. assert (Hk: 0 <= k) by lia.
  pose proof (@find_lost_Zlength stats k Hk) as Hxh. rewrite <-Heqxh in Hxh.
  pose proof (@find_found_Zlength stats k Hk) as Hxk. rewrite <-Heqxk in Hxk. clear Hk.
  rewrite_eqs; forward_if.
  { rewrite_eqs. forward.
    thaw FR2. thaw FR1. (*TODO: this didn't doesn't work ( in [solve_Forall2_fn_data_at]) with opaque constants*)
    rewrite Byte.unsigned_repr in H by rep_lia. rewrite Int_repr_zero in H by rep_lia.
    entailer!.
    { rewrite <- (@find_lost_filter _ (Zlength packets)). rewrite H. reflexivity. lia. }
    { replace 256 with (fec_max_h * 2) by rep_lia. replace 16000 with fec_max_cols by rep_lia.
      replace 128 with fec_max_h by rep_lia. cancel.
      (*If xh = 0, the result is trivial*)
      rewrite decoder_list_correct_0; auto; try lia. cancel.
      2 : { rewrite <- (find_lost_filter (k:=(Zlength packets))); auto. }
      apply derives_refl'. repeat f_equal. apply Znth_eq_ext. 
      - rewrite zseq_Zlength; list_solve.
      - rewrite Zlength_map. intros i Hi. rewrite Znth_map by auto.
        rewrite zseq_Znth; try lia. f_equal.
        destruct (Byte.eq_dec (Znth i stats) (Byte.zero)); auto.
        assert (Hinlost: In (Byte.repr i) (find_lost stats (Zlength packets))). {
          apply find_lost_found_aux_in_spec. rewrite Forall_Znth => x. rewrite Zlength_Ziota by lia.
          intros Hx. rewrite Znth_Ziota by lia. rep_lia. right. rewrite !Byte.unsigned_repr by rep_lia.
          split. apply Ziota_In; lia. assert (Hith: Znth i stats = Byte.one). {
            rewrite Forall_Znth in Hstatsvals. specialize (Hstatsvals _ Hi). destruct Hstatsvals; subst; auto. 
            contradiction. }
          rewrite Hith. destruct (Z.eq_dec (Byte.signed Byte.one) 1); auto. }
        apply Zlength_nil_inv in H. rewrite H in Hinlost. contradiction.
    }
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
       (data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl) (FIELD_TABLES gv)
       (data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx)
         (gv _fec_weights)) (data_at Ews tint (Vint Int.zero) (gv _trace))
       (data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost).
    freeze FR2 := (FRZL FR1) (data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd)
        (iter_sepcon_options parity_ptrs parities).
    rewrite !data_at__tarray. rewrite !zseq_list_repeat by rep_lia.
    replace (default_val tuchar) with Vundef by reflexivity.
    (*In this loop, we exit once we have found xh valid parity pointers, so the
      postcondition involves an EX quantifier - we don't know exactly how many steps it will take*)
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
            Zlength (find_parity_rows parities i) < Zlength (find_parity_rows parities parbound)) by lia.
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
            { (*it would be nice to not have to repeat this part, but not sure how
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
              rewrite pop_find_parity_found_plus_1; try rep_lia.
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
  { Intros i. assert (Hroweq: (find_parity_rows parities i) = (find_parity_rows parities parbound)). {
      apply find_parity_rows_eq; lia. }
    assert (Hfoundeq: (find_parity_found parities (fec_n - 1) i) = (find_parity_found parities (fec_n - 1) parbound)). {
      apply find_parity_found_eq; try lia. rewrite !find_parity_rows_found_Zlength. lia. }
  (*done with 2nd loop*) rewrite_eqs. thaw FR2. thaw FR1.
    forward. forward_if True; [contradiction | forward; entailer!; rewrite !eqb_type_refl; auto |].
    (*Start of matrix inversion loop*)
    (*Only things we need are v, lost, fec_weights, row*)
    freeze FR1 := (data_at Ews (tarray tschar k) (map Vbyte stats) ps)
      (data_at_ Tsh (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s)
      (iter_sepcon_arrays packet_ptrs packets)
      (data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl) (FIELD_TABLES gv)
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
    { (*Inverse loop is done! Now need pre/postconditions of gaussian elim*)
      rewrite_eqs. (*issue: ptree does not evaluate bc of opaque constants*)
      replace (tarray (tarray tuchar fec_max_cols) fec_max_h) with
        (tarray (tarray tuchar 16000) 128) by (repeat f_equal; rep_lia).
      replace (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) with
         (tarray (tarray tuchar 256) 128) by (repeat f_equal; rep_lia). 
      rewrite pop_find_inv_post; try lia. rewrite <- cat_app. rewrite CommonSSR.map_map_equiv.
      2 : { apply weight_mx_wf. }
      2 : { eapply forall_lt_leq_trans. 2 : apply find_parity_rows_bound. all: rep_lia. }
      2 : { eapply forall_lt_leq_trans. 2 : apply find_lost_bound. all: rep_lia. }
      (*We don't fill up the whole array, so we need to split it*)
      rewrite (split2_data_at_Tarray_app (2 * xh * xh)).
      2 : { rewrite Zlength_map. rewrite (@flatten_mx_Zlength _ xh (xh + xh)). lia.
            apply row_mx_list_wf; lia. }
      2 : { rewrite zseq_Zlength; try rep_lia. assert (xh <= fec_max_h) by rep_lia. nia. }
      replace (tarray tuchar (2 * xh * xh)) with (tarray tuchar (xh * (xh + xh))) by  (f_equal; lia).
      thaw FR2. thaw FR1.
      forward_call(gv, xh, xh + xh, (concat_mx_id (F:=B)
              (submx_rows_cols_rev_list (F:=B) weight_mx xh xh (fec_n - 1)
                 (seq.map Byte.unsigned (find_parity_rows parities i))
                 (seq.map Byte.unsigned (seq.rev (find_lost stats k)))) xh), v_v, Tsh).
      { entailer!. simpl. simpl_repr_byte. f_equal. rewrite !byte_int_repr by rep_lia. f_equal.
        f_equal. f_equal. f_equal. lia. }
      { replace (xh * (xh + xh)) with (2 * xh * xh) by lia. entailer!.
      }
      { split; [lia | split; [ rep_lia |split]].
        - apply row_mx_list_wf; lia.
        - split; auto.  apply strong_inv_row_mx_list. apply strong_inv_list_partial; lia.
      }
      { forward. forward_if True; [contradiction | forward; entailer! |].
        (*start of syndrome mx (multiplication) loop*)
        clear HeqLOCALS1 LOCALS1 HeqLOCALS LOCALS. 
        replace (Zlength (find_lost stats (Zlength packets))) with xh by (subst; lia).
        freeze FR1 := (data_at _ _ _ v_v) (data_at _ (tarray tuchar (2 * fec_max_h * fec_max_h - 2 * xh * xh)) _ _)
          (data_at _ _ _ ps) (data_at _ _ _ (gv _trace))
          (data_at _ _ _ v_lost).
        (*All local variables are unchanging in the loop*) (*q is redefined, so we don't want to remember it*)
        rewrite (grab_nth_LOCAL 10 (gvars gv)); simpl; [| list_solve]. 
        remember [temp _err (Vint Int.zero); temp _t'6 (Vint Int.zero);
         lvar _v (tarray (tarray tuchar 256) 128) v_v; lvar _lost (tarray tuchar fec_max_h) v_lost;
         temp _xh (Vubyte (Byte.repr xh)); lvar _row (tarray tuchar fec_max_h) v_row; 
         gvars gv; temp _t'29 (Vint Int.zero);
         temp _xr (Vubyte (Byte.repr (Zlength (find_parity_rows parities i))));
         temp _xk (Vubyte (Byte.repr (xk + Zlength (find_parity_found parities (fec_n - 1) i))));
         lvar _found (tarray tuchar fec_max_h) v_found;
         temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd);
         lvar _s (tarray (tarray tuchar 16000) 128) v_s; temp _k (Vint (Int.repr k));
         temp _c (Vint (Int.repr c)); temp _pdata pd; temp _plen pl; temp _pstat ps] as LOCALS.
        (*We have lots of items in the SEP clause that are not changing, but we need them. So we can't
          freeze then, but it's helpful to remember them so we dont need to constantly write them out*)
        rewrite (grab_nth_SEP 2); simpl.
        remember [FRZL FR1; FIELD_TABLES gv; iter_sepcon_arrays packet_ptrs packets;
           data_at Ews (tarray tint (Zlength packets)) (map Vint (map Int.repr lengths)) pl;
           data_at Ews (tarray (tptr tuchar) (Zlength packets + Zlength parity_ptrs))
             (packet_ptrs ++ parity_ptrs) pd; iter_sepcon_options parity_ptrs parities;
           data_at Tsh (tarray tuchar fec_max_h)
             (pop_find_parity_found stats parities i fec_max_h (Zlength packets) (fec_n - 1)) v_found;
           data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx)
             (gv _fec_weights);
           data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row] as SEPS.
        remember (find_parity_rows parities i) as row.
        remember (find_found stats k) as found1.
        remember (find_parity_found parities (fec_n - 1) i) as found2.
        remember (found1 ++ found2) as found.
        forward_loop (EX (i' : Z),
          PROP (0 <= i' <= xh)
          (LOCALx ((temp _i (Vint (Int.repr i'))) :: LOCALS)
          (SEPx (
            (*This matrix is quite complicated to describe, also opaque constants give dependent type issues when
                  trying to rewrite*)
             (data_at Tsh (tarray (tarray tuchar 16000) 128) 
              (pop_mx_mult_part xh c k fec_max_h fec_max_cols 
                (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) (map Byte.unsigned row) 
                    (map Byte.unsigned found))
                (col_mx_list (submx_rows_cols_list (F:=B) packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                    (submx_rows_cols_list (fill_missing  c parities) xh c (map Byte.unsigned row) (Ziota 0 c)) (k-xh) xh c)
                i' 0) v_s) :: SEPS))))
        break: (PROP () (LOCALx LOCALS (SEPx(
          (data_at Tsh (tarray (tarray tuchar 16000) 128) 
            (pop_mx_mult_part xh c k fec_max_h fec_max_cols 
              (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) (map Byte.unsigned row) 
                  (map Byte.unsigned found))
              (col_mx_list (submx_rows_cols_list (F:=B) packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                  (submx_rows_cols_list (fill_missing  c parities) xh c (map Byte.unsigned row) (Ziota 0 c)) (k-xh) xh c)
              xh 0) v_s) :: SEPS)))).
          { rewrite_eqs; forward. Exists 0. rewrite_eqs; entailer!.
            rewrite pop_mx_mult_part_zero by rep_lia.
            rewrite data_at__tarray. rewrite zseq_list_repeat by lia. rewrite default_arr by lia.
            rewrite fec_max_cols_eq. rewrite fec_max_h_eq. cancel.
          }
          { Intros i'. rewrite_eqs; forward_if.
            { (*outer loop body*) rewrite Byte.unsigned_repr in H2 by rep_lia.
              forward.
              { entailer!. }
              { rewrite pop_find_parity_rows_Znth by (subst; lia). entailer!. simpl_repr_byte. }
              { rewrite pop_find_parity_rows_Znth by (subst; lia). forward.
              (*NOTE: Again, get C-language expression error, can't directly work with arrays due to
                  dependent type issues, not using opaque constants here*)
              forward. rewrite <- HeqLOCALS. rewrite <- HeqSEPS.
              remember (temp _t (force_val
                (sem_binary_operation' Oadd (tarray (tarray tuchar 16000) 128) tuchar v_s (Vint (Int.repr i'))))
              :: temp _p (force_val (sem_binary_operation' Oadd (tarray (tarray tuchar 255) 128) tuchar 
                  (gv _fec_weights) (Vubyte (Znth i' (find_parity_rows parities i)))))
              :: temp _t'24 (Vubyte (Znth i' (find_parity_rows parities i)))
              :: temp _i (Vint (Int.repr i')) :: LOCALS) as LOCALS1.
              forward_loop (EX (j: Z),
                PROP (0 <= j <= c)
                (LOCALx ((temp _j (Vint (Int.repr j))) :: LOCALS1)
                (SEPx (
                   (data_at Tsh (tarray (tarray tuchar 16000) 128)
                     (pop_mx_mult_part xh c k fec_max_h fec_max_cols
                        (submx_rows_cols_rev_list (F:=B) weight_mx xh k (fec_n - 1) (map Byte.unsigned row)
                           (map Byte.unsigned found))
                        (col_mx_list (F:=B)
                           (submx_rows_cols_list (F:=B) packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                           (submx_rows_cols_list (F:=B) (fill_missing c parities) xh c 
                              (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' j) v_s) :: SEPS))))
              break: (PROP () (LOCALx LOCALS1 (SEPx (
                (data_at Tsh (tarray (tarray tuchar 16000) 128)
                     (pop_mx_mult_part xh c k fec_max_h fec_max_cols
                        (submx_rows_cols_rev_list (F:=B) weight_mx xh k (fec_n - 1) (map Byte.unsigned row)
                           (map Byte.unsigned found))
                        (col_mx_list (F:=B)
                           (submx_rows_cols_list (F:=B) packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                           (submx_rows_cols_list (F:=B) (fill_missing c parities) xh c 
                              (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' c) v_s) :: SEPS)))).
                { rewrite_eqs; forward. Exists 0. rewrite_eqs; entailer!. }
                { Intros j. rewrite_eqs; forward_if. (*inner (j) loop body*)
                  { forward. simpl_repr_byte.
                    rewrite <- HeqLOCALS. rewrite <- HeqLOCALS1. rewrite <- HeqSEPS.
                    (*In this loop, we only change y, so the seps are constant*)
                    remember (data_at Tsh (tarray (tarray tuchar 16000) 128)
                      (pop_mx_mult_part xh c k fec_max_h fec_max_cols
                         (submx_rows_cols_rev_list (F:=B) weight_mx xh k (fec_n - 1) 
                            (map Byte.unsigned row) (map Byte.unsigned found))
                         (col_mx_list (F:=B)
                            (submx_rows_cols_list (F:=B) packets (k - xh) c (map Byte.unsigned found1)
                               (Ziota 0 c))
                            (submx_rows_cols_list (F:=B) (fill_missing c parities) xh c 
                               (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' j) v_s :: SEPS) as SEPS1.
                    forward_loop (EX (q: Z),
                      PROP (0 <= q <= k)
                      (LOCALx (temp _y (Vubyte (dot_prod (F:=B) 
                        (submx_rows_cols_rev_list (F:=B) weight_mx xh k (fec_n - 1) 
                            (map Byte.unsigned row) (map Byte.unsigned found))
                        (col_mx_list (F:=B)
                           (submx_rows_cols_list (F:=B) packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                           (submx_rows_cols_list (F:=B) (fill_missing c parities) xh c
                              (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' j q)) 
                        :: temp _q (Vint (Int.repr q)) :: temp _j (Vint (Int.repr j)) :: LOCALS1) (SEPx SEPS1)))
                    break: (PROP () 
                      (LOCALx (temp _y (Vubyte (dot_prod (F:=B) 
                        (submx_rows_cols_rev_list (F:=B) weight_mx xh k (fec_n - 1) 
                            (map Byte.unsigned row) (map Byte.unsigned found))
                        (col_mx_list (F:=B)
                           (submx_rows_cols_list (F:=B) packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                           (submx_rows_cols_list (F:=B) (fill_missing c parities) xh c
                              (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' j k)) 
                        :: temp _j (Vint (Int.repr j)) :: LOCALS1) (SEPx SEPS1))).
                    { rewrite_eqs; forward. simpl_repr_byte. Exists 0.
                      rewrite dot_prod_zero. rewrite_eqs; entailer. }
                    { Intros q. rewrite_eqs; forward_if.
                      { (*In innermost loop - dot prod*)
                        assert (Hfoundlen: Zlength found1 + Zlength found2 = k). { 
                          assert (Hkbyte: 0 <= k <= Byte.max_unsigned) by rep_lia.
                          pose proof (find_lost_found_Zlength stats Hkbyte) as Hlostfound.
                          subst; rewrite find_parity_rows_found_Zlength; rep_lia. }
                        forward.
                        { entailer!. }
                        { rewrite pop_find_parity_found_Znth by (subst; rep_lia). entailer!. simpl_repr_byte. }
                        { rewrite pop_find_parity_found_Znth by (subst; rep_lia). forward.
                          simpl_repr_byte. rewrite <- byte_int_repr at 1 by rep_lia. 
                          rewrite Byte.repr_unsigned. 
                          (*simplify *(p + z) which is really fec_weights[row[i]][found[q]]*)
                          (*we need some bounds first, which will also be needed later*)
                          assert (Byte.unsigned (Znth i' (find_parity_rows parities i)) < fec_max_h). {
                              assert (Hibyte: 0 <= i <= Byte.max_unsigned) by rep_lia.
                              pose proof (find_parity_rows_bound parities Hibyte) as Hrowbound.
                              assert (0 <= Byte.unsigned (Znth i' (find_parity_rows parities i)) < i) by
                                (rewrite Forall_Znth in Hrowbound; apply Hrowbound; list_solve). rep_lia. }
                          remember (if proj_sumbool (range_le_lt_dec 0 q (Zlength (find_found stats (Zlength packets))))
                            then Znth q (find_found stats (Zlength packets))
                            else
                             Znth (q - Zlength (find_found stats (Zlength packets)))
                               (find_parity_found parities (fec_n - 1) i)) as foundnth.
                          assert (Byte.unsigned foundnth < fec_n - 1). { subst.
                              destruct (range_le_lt_dec 0 q (Zlength (find_found stats (Zlength packets)))); simpl.
                              - assert (Hkbyte: 0 <= Zlength packets <= Byte.max_unsigned) by rep_lia.
                                pose proof (find_found_bound stats Hkbyte) as Hfoundbound.
                                assert (0 <= Byte.unsigned (Znth q (find_found stats (Zlength packets))) < Zlength packets) by
                                  (rewrite Forall_Znth in Hfoundbound; apply Hfoundbound; rep_lia). rep_lia.
                              - assert (Hin: 0 <= i < fec_n - 1) by rep_lia.
                                assert (Hnbyte: fec_n - 1 <= Byte.max_unsigned) by rep_lia.
                                pose proof (find_parity_found_bound parities Hin Hnbyte).
                                rewrite Forall_Znth in H8. apply H8. lia. }
                          assert_PROP (force_val (sem_add_ptr_int tuchar Signed
                            (force_val (sem_add_ptr_int (tarray tuchar 255) Signed (gv _fec_weights)
                            (Vubyte (Znth i' (find_parity_rows parities i)))))
                            (Vubyte foundnth)) = 
                          field_address (tarray (tarray tuchar (fec_n -1)) fec_max_h)
                            [ArraySubsc (Byte.unsigned foundnth);
                             ArraySubsc (Byte.unsigned (Znth i' (find_parity_rows parities i)))] (gv _fec_weights)). {
                              rewrite <- (Byte.repr_unsigned (Znth i' _)). rewrite <- (Byte.repr_unsigned foundnth).  
                              entailer!. solve_offset. }
                          forward.
                          { entailer!. pose proof (weight_mx_wf) as [Hwh [_ Hwn]].
                            rewrite !(@Znth_default _  Inhabitant_list). 2: { rewrite rev_mx_val_length1; rep_lia. }
                            rewrite rev_mx_val_Znth; try rep_lia. 2: { inner_length. } simpl_repr_byte.
                          }
                          { forward. pose proof (weight_mx_wf) as [Hwh [_ Hwn]].
                            rewrite !(@Znth_default _  Inhabitant_list). 2: { rewrite rev_mx_val_length1; rep_lia. }
                            rewrite rev_mx_val_Znth; try rep_lia. 2: { inner_length. } inner_length.
                            rewrite force_val_byte.
                            (*Now we are at if statement. Depends on if we are in packets part or parities part*)
                            forward_if (PROP () 
                              (LOCALx (temp _y (Vubyte (dot_prod (F:=B) 
                                (submx_rows_cols_rev_list (F:=B) weight_mx xh k (fec_n - 1) 
                                    (map Byte.unsigned row) (map Byte.unsigned found))
                                (col_mx_list (F:=B)
                                   (submx_rows_cols_list (F:=B) packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                                   (submx_rows_cols_list (F:=B) (fill_missing c parities) xh c
                                      (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' j (q + 1))) 
                                :: temp _q (Vint (Int.repr q)) :: temp _j (Vint (Int.repr j)) :: LOCALS1) (SEPx SEPS1))).
                            { (*In this case, we know we are in the packets part and that q is small*)
                              destruct (range_le_lt_dec 0 q (Zlength (find_found stats (Zlength packets)))); simpl in Heqfoundnth.
                              2 : { rewrite Heqfoundnth in H10.
                                assert (Hin: 0 <= i < fec_n - 1) by rep_lia.
                                assert (Hnbyte: fec_n - 1 <= Byte.max_unsigned) by rep_lia.
                                pose proof (find_parity_found_bound' parities Hin Hnbyte) as Hfoundb.
                                rewrite Forall_Znth in Hfoundb.
                                assert (fec_n - 1 - i <= Byte.unsigned 
                                  (Znth (q - Zlength (find_found stats (Zlength packets))) (find_parity_found parities 
                                  (fec_n - 1) i)) < fec_n - 1). { apply Hfoundb; subst; rep_lia. } rep_lia. }
                              rewrite Heqfoundnth. 
                              (*need for forward*)
                              assert (Hqlen: 0 <= Byte.unsigned (Znth q (find_found stats (Zlength packets))) < Zlength (map Int.repr lengths)). {
                                rewrite Zlength_map. replace (Zlength lengths) with (Zlength packets) by lia.
                                assert (Hkbyte: 0 <= Zlength packets <= Byte.max_unsigned) by rep_lia.
                                pose proof (find_found_bound stats Hkbyte) as Hfoundb. rewrite Forall_Znth in Hfoundb.
                                apply Hfoundb. lia. } rewrite Zlength_map in Hqlen.
                              forward. forward_if.
                              { assert (Hjlen: j < Zlength (Znth (Byte.unsigned (Znth q (find_found stats (Zlength packets)))) packets)). {
                                  rewrite Hlenspec in H11; try rep_lia. rewrite Int.signed_repr in H11; try lia.
                                  inner_length. } clear H11.
                                (*We are going to be accessing pdata, so we need to unfold the iter_sepcon*)
                                assert (Hlens: Zlength packet_ptrs = Zlength packets) by lia. 
                                assert (Hpackbound: 0 <= Byte.unsigned (Znth q (find_found stats (Zlength packets))) < Zlength packets) by lia.
                                rewrite (iter_sepcon_arrays_remove_one _  _ _ Hlens Hpackbound). Intros.
                                forward; rewrite Znth_app1 by lia.
                                { entailer!. }
                                { forward.
                                  { entailer!. simpl_repr_byte. }
                                  { rewrite Znth_map by lia. forward. simpl_repr_byte.
                                    rewrite <- byte_int_repr by rep_lia. rewrite Byte.repr_unsigned.
                                    unfold FIELD_TABLES. Intros. 
                                    forward_call(gv, (Znth (fec_n - 1 - Byte.unsigned (Znth q (find_found stats (Zlength packets))) - 1)
                                      (Znth (Byte.unsigned (Znth i' (find_parity_rows parities i))) weight_mx)),
                                      (Znth j (Znth (Byte.unsigned (Znth q (find_found stats (Zlength packets)))) packets))).
                                    forward. rewrite_eqs; unfold FIELD_TABLES; entailer!.
                                    { unfold Int.xor. rewrite !Int.unsigned_repr by simpl_repr_byte.
                                      rewrite ByteFacts.byte_xor_fold.
                                      simpl_repr_byte. unfold Vubyte. f_equal. f_equal. f_equal.
                                      rewrite dot_prod_plus_1 by lia.
                                      replace (ssralg.GRing.add (V:=ssralg.GRing.Field.zmodType B)) with
                                        Byte.xor by reflexivity. f_equal.
                                      replace (ssralg.GRing.mul (R:=ssralg.GRing.Field.ringType B)) with
                                        ByteField.byte_mul by reflexivity. f_equal.
                                      - unfold submx_rows_cols_rev_list.
                                        unfold submx_rows_cols_list. rewrite mk_lmatrix_get by lia.
                                        unfold get. rewrite !Znth_map by list_solve.
                                        rewrite Znth_app1 by lia. reflexivity.
                                      - unfold col_mx_list. rewrite mk_lmatrix_get by lia.
                                        destruct (Z_lt_ge_dec q (Zlength packets - Zlength (find_lost stats (Zlength packets)))); simpl.
                                        + (*real case*)
                                          unfold submx_rows_cols_list.
                                          rewrite get_inhab. rewrite mk_lmatrix_get by lia.
                                          rewrite Znth_Ziota by lia. unfold get. rewrite Znth_map by list_solve. f_equal.
                                        + (*contradiction case*)
                                          assert (Hkbyte: 0 <= (Zlength packets) <= Byte.max_unsigned) by rep_lia.
                                          pose proof (find_lost_found_Zlength stats Hkbyte). rep_lia.
                                    }
                                    { rewrite (iter_sepcon_arrays_remove_one _  _ _ Hlens Hpackbound).
                                      cancel.
                                    }
                                  }
                                }
                              }
                              { (*if we are outside the range of the original bound - really count as a zero*)
                                assert (Hjlen: j >= Zlength (Znth (Byte.unsigned (Znth q (find_found stats (Zlength packets)))) packets)). {
                                  rewrite Hlenspec in H11; try rep_lia. rewrite Int.signed_repr in H11; try lia.
                                  inner_length. } clear H11.
                                forward. rewrite_eqs; entailer!. f_equal. rewrite dot_prod_plus_1 by lia. simpl.
                                unfold col_mx_list at 2. assert (Hget: forall l i j,
                                  @get byte (inhabitant_F B) l i j = @get (ssralg.GRing.Field.sort B) (inhabitant_F B) l i j). {
                                  reflexivity. } rewrite (get_inhab _ q j). rewrite mk_lmatrix_get by rep_lia.
                                destruct (Z_lt_ge_dec q (Zlength packets - Zlength (find_lost stats (Zlength packets)))); simpl.
                                2 : { assert (Hkbyte: 0 <= (Zlength packets) <= Byte.max_unsigned) by rep_lia.
                                      pose proof (find_lost_found_Zlength stats Hkbyte). rep_lia. }
                                assert (Hzero: @get byte (inhabitant_F B) (submx_rows_cols_list (F:=B) packets
                                 (Zlength packets - Zlength (find_lost stats (Zlength packets))) c
                                 (map Byte.unsigned (find_found stats (Zlength packets))) (Ziota 0 c)) q j = Byte.zero). {
                                  unfold submx_rows_cols_list. rewrite (get_inhab _ q j). rewrite mk_lmatrix_get by lia.
                                  rewrite Znth_Ziota by lia. unfold get. rewrite Znth_overflow by list_solve. reflexivity. }
                                rewrite Hzero. rewrite ssralg.GRing.mulr0. rewrite ssralg.GRing.addr0. reflexivity.
                              }
                            }
                            { (*Other case - we are in parities*)
                              destruct (range_le_lt_dec 0 q (Zlength (find_found stats (Zlength packets)))); simpl in Heqfoundnth.
                              (*contradiction case*) rewrite Heqfoundnth in H10.
                              assert (Hkbyte: 0 <= Zlength packets <= Byte.max_unsigned) by rep_lia.
                              pose proof (find_found_bound stats Hkbyte) as Hfoundb. rewrite Forall_Znth in Hfoundb.
                              assert (0 <= Byte.unsigned (Znth q (find_found stats (Zlength packets))) < Zlength packets) by 
                                (apply Hfoundb; lia). rep_lia. (*accessing parity - need to split [iter_sepcon_option]*)
                              assert (Hkbyte: 0 <= (Zlength packets) <= Byte.max_unsigned) by rep_lia.
                              pose proof (find_lost_found_Zlength stats Hkbyte) as Hxhxk. 
                              assert (Hnthsome: exists l, (Znth (fec_n - 2 - Byte.unsigned foundnth) parities) = Some l). {
                                rewrite Heqfoundnth. replace (fec_n - 2) with ((fec_n - 1) - 1) by lia.
                                apply find_parity_found_Znth_some; try rep_lia. subst; rep_lia. }
                              destruct Hnthsome as [l Hsome].
                              assert (Hqlen: 0 <= (fec_n - 2 - Byte.unsigned foundnth) < Zlength parities). {
                                subst. assert (Hin: 0 <= i < fec_n - 1) by rep_lia.
                                assert (Hbyte: fec_n - 1 <= Byte.max_unsigned) by rep_lia.
                                pose proof (find_parity_found_bound' parities Hin Hbyte) as Hparb.
                                rewrite Forall_Znth in Hparb. 
                                specialize (Hparb (q - Zlength (find_found stats (Zlength packets)))); rep_lia. }
                              assert (Hparlenseq: Zlength parity_ptrs = Zlength parities) by lia.
                              rewrite (iter_sepcon_options_remove_one _ _ _ _ Hparlenseq Hqlen Hsome). Intros.
                              assert (Hlenl: Zlength l = c). { apply (Hparsomelen (fec_n - 2 - Byte.unsigned foundnth)); auto. lia. }
                              rewrite Hlenl.
                              replace (Zlength l) with c by (rewrite Hparsomelen; auto).
                              (*Now we can express the field_address*)
                              assert_PROP (force_val
                               (sem_add_ptr_int (tptr tuchar) Signed (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd)
                                  (Vint (Int.sub (Int.sub (Int.repr 256) (Int.repr 2)) (Int.repr (Byte.unsigned foundnth))))) =
                                field_address (tarray (tptr tuchar) (Zlength packets + Zlength parity_ptrs)) (SUB (k + (fec_n - 2 - Byte.unsigned foundnth))) pd). {
                                  entailer!. solve_offset. } subst foundnth.
                              forward.
                              { rewrite Znth_app2 by lia. 
                                assert (Hremk: forall x, k + x - Zlength packet_ptrs = x) by (intros x; lia).
                                rewrite Hremk. entailer!. }
                              { entailer!. rewrite H11. solve_offset. }
                              { rewrite Znth_app2 by lia. 
                                assert (Hremk: forall x, k + x - Zlength packet_ptrs = x) by (intros x; lia).
                                rewrite Hremk. forward.
                                { rewrite Znth_map by lia. entailer!. simpl_repr_byte. }
                                { forward. rewrite Znth_map by lia. rewrite force_val_byte.
                                  (*at multiplication*) unfold FIELD_TABLES; Intros.
                                  forward_call (gv, (Znth (fec_n - 1 - Byte.unsigned
                                      (Znth (q - Zlength (find_found stats (Zlength packets)))
                                      (find_parity_found parities (fec_n - 1) i)) - 1)
                                      (Znth (Byte.unsigned (Znth i' (find_parity_rows parities i))) weight_mx)), 
                                    (Znth j l)).
                                  forward.  rewrite_eqs; unfold FIELD_TABLES; entailer!.
                                  { unfold Int.xor. rewrite !Int.unsigned_repr by simpl_repr_byte.
                                    rewrite ByteFacts.byte_xor_fold.
                                    simpl_repr_byte. unfold Vubyte. f_equal. f_equal. f_equal.
                                    rewrite dot_prod_plus_1 by lia.
                                    replace (ssralg.GRing.add (V:=ssralg.GRing.Field.zmodType B)) with
                                      Byte.xor by reflexivity. f_equal.
                                    replace (ssralg.GRing.mul (R:=ssralg.GRing.Field.ringType B)) with
                                      ByteField.byte_mul by reflexivity. f_equal.
                                    - unfold submx_rows_cols_rev_list.
                                      unfold submx_rows_cols_list. rewrite mk_lmatrix_get by lia.
                                      unfold get. rewrite !Znth_map by list_solve.
                                      rewrite Znth_app2 by lia. reflexivity.
                                    - unfold col_mx_list. rewrite mk_lmatrix_get by lia.
                                      destruct (Z_lt_ge_dec q (Zlength packets - Zlength (find_lost stats (Zlength packets)))); simpl.
                                      + (*contradiction case*) rep_lia.
                                      + (*real case*)
                                        unfold submx_rows_cols_list.
                                        rewrite get_inhab. rewrite mk_lmatrix_get by lia.
                                        rewrite Znth_Ziota by lia. apply fill_missing_mx_some; try lia; auto. 
                                        rewrite <- Hsome. f_equal. rewrite Znth_map by lia.
                                        rewrite find_parity_rows_found_Znth by rep_lia.
                                        pose proof find_lost_found_Zlength stats Hkbyte.
                                        replace (Zlength packets - Zlength (find_lost stats (Zlength packets))) with
                                           (Zlength (find_found stats (Zlength packets))) by lia. lia. 
                                        rewrite Znth_map by lia. 
                                        assert (Hibyte: 0 <= i <= Byte.max_unsigned) by rep_lia.
                                        pose proof (find_parity_rows_bound parities Hibyte) as Hrowb.
                                        rewrite Forall_Znth in Hrowb. 
                                        specialize (Hrowb (q - (Zlength packets - Zlength (find_lost stats (Zlength packets))))). rep_lia.
                                  }
                                  { rewrite (iter_sepcon_options_remove_one _ _ _ _ Hparlenseq Hqlen Hsome). cancel.
                                  }
                                }
                              }
                            }
                            { (*invariant pres for dot prod loop*) rewrite_eqs; forward.
                              Exists (q+1). rewrite_eqs; entailer!. simpl_repr_byte.
                            }
                          }
                        }
                      }
                      { (*end of dot prod loop*) forward. rewrite_eqs; entailer!.
                        replace q with (Zlength packets) by lia. reflexivity.
                      }
                    }
                    { (*put the value in the matrix*) rewrite_eqs.
                      replace (lvar _s (tarray (tarray tuchar 16000) 128) v_s) with
                              (lvar _s (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s)
                        by (repeat f_equal; rep_lia).
                      assert (Htemp: forall x, data_at Tsh (tarray (tarray tuchar 16000) 128) x v_s =
                        data_at Tsh (tarray (tarray tuchar fec_max_cols) fec_max_h) x v_s). { intros x.
                        rewrite fec_max_cols_eq. rewrite fec_max_h_eq. reflexivity. }
                     rewrite Htemp.
                      assert_PROP (force_val
                       (sem_add_ptr_int tuchar Signed
                          (force_val (sem_add_ptr_int (tarray tuchar 16000) Signed v_s (Vint (Int.repr i'))))
                          (Vint (Int.repr j))) = field_address (tarray (tarray tuchar fec_max_cols) fec_max_h)
                             [ArraySubsc j; ArraySubsc i'] v_s). {
                      entailer!. solve_offset. } (*We needed opaque constants otherwise this takes forever*)
                      rewrite_eqs; forward.
                      simpl_repr_byte. forward. Exists (j+1). rewrite_eqs; entailer!.
                      { rewrite fec_max_h_eq. rewrite fec_max_cols_eq. rewrite eqb_type_refl. auto. }
                      { rewrite <- fec_max_cols_eq. rewrite <- fec_max_h_eq. rewrite field_at_data_at_cancel'.
                        apply derives_refl'. f_equal. rewrite <- pop_mx_mult_part_set by rep_lia.
                        unfold set. f_equal. f_equal. apply Znth_default.
                        rewrite pop_mx_mult_part_Zlength; rep_lia.
                      }
                    }
                  }
                  { (*end of j loop*) replace j with c by lia. forward. rewrite_eqs; entailer!. }
                }
                { (*preservation of outer loop invar*) rewrite_eqs; forward. Exists (i'+1). 
                  unfold Int.add. simpl_repr_byte. rewrite_eqs; entailer!.
                  rewrite <- pop_mx_mult_part_row_finish by lia. cancel.
                }
              }
            }
            { (*end of outer loop*) rewrite Byte.unsigned_repr in H2 by rep_lia. replace i' with xh by lia.
              forward. rewrite_eqs; entailer!.
            }
          }
          { (*Final loop (multiplication and regenerate data)*)
            rewrite_eqs; forward. unfold Int.sub. simpl_repr_byte.
            (*TODO: cannot rewrite opaque constants, get C parser error*)
            forward.
            clear HeqLOCALS LOCALS HeqSEPS SEPS. thaw FR1.
            (*unfortunately, we need almost everything in this loop*)
            freeze FR1 := (data_at _ _ _
              (field_address0 (tarray tuchar (2 * fec_max_h * fec_max_h)) (SUB (2 * xh * xh)) v_v))
              (data_at _ _ _ (gv _trace)) (iter_sepcon_options parity_ptrs parities) 
              (data_at _ _ _ v_found) (data_at _ _ _ (gv _fec_weights)) (data_at _ _ _ v_row).
            (*remember matrices to make the loop invariants nicer. The names match those in [decode_list_mx]*)
            remember (submx_rows_cols_rev_list (F:=B) weight_mx xh k (fec_n - 1) (map Byte.unsigned row)
              (map Byte.unsigned found)) as w''.
            remember (col_mx_list (F:=B)
             (submx_rows_cols_list (F:=B) packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
             (submx_rows_cols_list (F:=B) (fill_missing c parities) xh c (map Byte.unsigned row)
                (Ziota 0 c)) (k - xh) xh c) as d'.
            remember (submx_rows_cols_rev_list (F:=B) weight_mx xh xh (fec_n - 1)
                    (seq.map Byte.unsigned row) (seq.map Byte.unsigned (seq.rev (find_lost stats k)))) as w'.
            (*remember local variables - none are changing in loop*)
            remember [temp _u (force_val (sem_binary_operation' Oadd (tarray (tarray tuchar 16000) 128) tuchar v_s
                (Vint (Int.repr (xh - 1))))); temp _x (Vint (Int.repr (xh - 1)));
               temp _err (Vint Int.zero); temp _t'6 (Vint Int.zero); lvar _v (tarray (tarray tuchar 256) 128) v_v;
               lvar _lost (tarray tuchar fec_max_h) v_lost; temp _xh (Vubyte (Byte.repr xh));
               lvar _row (tarray tuchar fec_max_h) v_row; gvars gv; temp _t'29 (Vint Int.zero);
               temp _xr (Vubyte (Byte.repr (Zlength row))); temp _xk (Vubyte (Byte.repr (xk + Zlength found2)));
               lvar _found (tarray tuchar fec_max_h) v_found;
               temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd);
               lvar _s (tarray (tarray tuchar 16000) 128) v_s; temp _k (Vint (Int.repr k));
               temp _c (Vint (Int.repr c)); temp _pdata pd; temp _plen pl; temp _pstat ps] as LOCALS.
            (*Only item actually changing in the SEP clause in what is stats and pdata, so all rest can be remembered*)
            rewrite (grab_nth_SEP 3); simpl.
            rewrite (grab_nth_SEP 6); simpl.
            remember [FRZL FR1; data_at Tsh (tarray (tarray tuchar 16000) 128)
              (pop_mx_mult_part xh c k fec_max_h fec_max_cols w'' d' xh 0) v_s;
              data_at Tsh (tarray tuchar (xh * (xh + xh)))
              (map Vubyte (flatten_mx (gauss_restrict_list (F:=B) xh (xh + xh) (concat_mx_id (F:=B) w' xh)))) v_v;
             data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats (Zlength packets) fec_max_h) v_lost;
             FIELD_TABLES gv;
             data_at Ews (tarray tint (Zlength packets)) (map Vint (map Int.repr lengths)) pl;
             data_at Ews (tarray (tptr tuchar) (Zlength packets + Zlength parity_ptrs))
               (packet_ptrs ++ parity_ptrs) pd] as SEPS.
            forward_loop (EX (i: Z),
              PROP (0 <= i <= xh)
              (LOCALx ((temp _i (Vint (Int.repr i))) :: LOCALS)
              (SEPx (iter_sepcon_arrays packet_ptrs 
                (pop_fill_rows_list packets (lmatrix_multiply xh xh c (find_invmx_list w' xh)
                    (lmatrix_multiply xh k c w'' d')) (map Byte.unsigned (rev (find_lost stats k))) i 0) ::
                data_at Ews (tarray tschar (Zlength packets)) 
                  (map Vbyte (pop_stats stats (map Byte.unsigned (rev (find_lost stats k))) i)) ps :: SEPS))))
            break: (PROP () (LOCALx LOCALS
              (SEPx (iter_sepcon_arrays packet_ptrs 
                (pop_fill_rows_list packets (lmatrix_multiply xh xh c (find_invmx_list w' xh)
                    (lmatrix_multiply xh k c w'' d')) (map Byte.unsigned (rev (find_lost stats k))) xh 0) ::
                data_at Ews (tarray tschar (Zlength packets)) 
                  (map Vbyte (pop_stats stats (map Byte.unsigned (rev (find_lost stats k))) xh)) ps :: SEPS)))).
            { rewrite_eqs; forward. Exists 0. rewrite_eqs; entailer!.
              rewrite pop_fill_rows_list_0. rewrite pop_stats_0. cancel. }
            { Intros i'. rewrite_eqs; forward_if.
              { (*need in multiple places*) rewrite Byte.unsigned_repr in H2 by rep_lia.
                assert (Hixh2: Int.min_signed <= i' * Zlength (find_lost stats (Zlength packets)) * 2 <= Int.max_signed). {
                  split; try rep_lia. 
                  assert (i' * Zlength (find_lost stats (Zlength packets)) * 2 <= 
                  Zlength (find_lost stats (Zlength packets)) * Zlength (find_lost stats (Zlength packets)) * 2) by (subst; nia).
                  assert ( Zlength (find_lost stats (Zlength packets)) <= 127) by (subst; rep_lia).
                  assert (i' * Zlength (find_lost stats (Zlength packets)) * 2 <= 127 * 127 * 2) by nia. rep_lia. }
                forward.
                { entailer!. rewrite !Byte.unsigned_repr by rep_lia. rewrite !Int.signed_repr by rep_lia. lia. }
                { assert_PROP (force_val (sem_binary_operation' Oadd (tarray tuchar 256) tint v_v
                  (eval_binop Omul tint tint
                     (eval_binop Omul tuchar tuchar (Vint (Int.repr i')) (Vubyte (Byte.repr xh)))
                     (Vint (Int.repr 2)))) = field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2)) v_v) as Hp. {
                  entailer!. solve_offset. }
                  rewrite Hp; clear Hp.
                  forward. (*now simplify m*)
                  assert_PROP (force_val (sem_binary_operation' Oadd (tptr tuchar) tuchar
                    (field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2)) v_v)
                    (Vubyte (Byte.repr xh))) = field_address (tarray tuchar (xh * (xh + xh)))
                    (SUB (i' * xh * 2 + xh)) v_v) as Hm. { entailer!. solve_offset. }
                  rewrite Hm; clear Hm.
                  forward; try (rewrite pop_find_lost_Znth by (subst; lia)); [entailer! | entailer!; simpl_repr_byte|].
                  forward.
                  { entailer!. assert (Hkbyte: 0 <= Zlength packets <= Byte.max_unsigned) by rep_lia.
                    apply (find_lost_bound stats) in Hkbyte. rewrite Forall_Znth in Hkbyte. apply Hkbyte; rep_lia.
                  }
                  { (*might as well do the stats postcondition here*)
                    replace (upd_Znth (Byte.unsigned (Znth (xh - 1 - i') (find_lost stats (Zlength packets))))
                      (map Vbyte (pop_stats stats (map Byte.unsigned (rev (find_lost stats k))) i'))
                      (Vint (Int.repr 0))) 
                      with (map Vbyte (pop_stats stats (map Byte.unsigned (rev (find_lost stats k))) (i' + 1))).
                    2 : { rewrite pop_stats_plus_1.
                          - rewrite <- upd_Znth_map. rewrite Znth_map by (rewrite Zlength_rev; lia).
                            rewrite Znth_rev by lia. subst. f_equal. f_equal. f_equal. lia.
                          - apply FinFun.Injective_map_NoDup. intros b1 b2. apply byte_unsigned_inj.
                            apply NoDup_rev. apply find_lost_NoDup. rep_lia.
                          - rewrite Forall_map. apply Forall_rev. 
                            assert (Hkbyte: 0 <= k <= Byte.max_unsigned) by rep_lia. 
                            apply (find_lost_bound stats) in Hkbyte. rewrite Forall_Znth in Hkbyte.
                            rewrite Forall_Znth. intros x Hx. simpl. replace (Zlength stats) with k by lia.
                            apply Hkbyte; auto.
                          - rewrite Zlength_map. rewrite Zlength_rev. lia.
                        }
                    (*Now we are at the j loop*)
                    rewrite <- HeqLOCALS. rewrite <- HeqSEPS.
                    (*None of the new locals are changing either*)
                    remember (temp _t'16 (Vubyte (Znth (xh - 1 - i') (find_lost stats (Zlength packets))))
                      :: temp _m (field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + xh)) v_v)
                      :: temp _p (field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2)) v_v)
                      :: temp _i (Vint (Int.repr i')) :: LOCALS) as LOCALS1.
                    (*We are also done with the stats list*)
                    remember (data_at Ews (tarray tschar (Zlength packets))
                      (map Vbyte (pop_stats stats (map Byte.unsigned (rev (find_lost stats k))) (i' + 1))) ps
                      :: SEPS) as SEPS1.
                    forward_loop (EX (j: Z),
                      (PROP (0 <= j <= c)
                      (LOCALx ((temp _j (Vint (Int.repr j))) :: LOCALS1)
                      (SEPx (iter_sepcon_arrays packet_ptrs (pop_fill_rows_list packets
                          (lmatrix_multiply (F:=B) xh xh c (find_invmx_list (F:=B) w' xh)
                          (lmatrix_multiply (F:=B) xh k c w'' d')) 
                          (map Byte.unsigned (rev (find_lost stats k))) i' j) :: SEPS1)))))
                      break: (PROP () (LOCALx LOCALS1 (SEPx 
                        (iter_sepcon_arrays packet_ptrs (pop_fill_rows_list packets
                          (lmatrix_multiply (F:=B) xh xh c (find_invmx_list (F:=B) w' xh)
                          (lmatrix_multiply (F:=B) xh k c w'' d')) 
                          (map Byte.unsigned (rev (find_lost stats k))) i' c) :: SEPS1)))).
                    { rewrite_eqs; forward. Exists 0. rewrite_eqs; entailer!. }
                    { Intros j. rewrite_eqs; forward_if.
                      { forward. simpl_repr_byte. forward.
                        (*simplify r*)
                        assert_PROP (force_val (sem_binary_operation' Oadd (tptr tuchar) tint
                          (force_val (sem_binary_operation' Oadd (tarray (tarray tuchar 16000) 128) tuchar v_s
                          (Vint (Int.repr (xh - 1))))) (Vint (Int.repr j))) = 
                          field_address (tarray (tarray tuchar fec_max_cols) fec_max_h) 
                          [ArraySubsc j; ArraySubsc (xh - 1)] v_s) as Hr. {
                          entailer!. solve_offset. }
                        rewrite Hr; clear Hr.
                        (*inner loop (dot prod loop). This is a bit annoying because they iterate with
                          pointers for some unknown reason*)
                        rewrite <- HeqLOCALS. rewrite <- HeqLOCALS1. rewrite <- HeqSEPS. rewrite <- HeqSEPS1.
                        (*We don't change anything in SEPS here*)
                        remember (iter_sepcon_arrays packet_ptrs (pop_fill_rows_list packets
                          (lmatrix_multiply (F:=B) xh xh c (find_invmx_list (F:=B) w' xh)
                          (lmatrix_multiply (F:=B) xh k c w'' d'))
                          (map Byte.unsigned (rev (find_lost stats k))) i' j) :: SEPS1) as SEPS2.
                        remember (temp _j (Vint (Int.repr j)) :: LOCALS1) as LOCALS2.
                        (*r is annoying. It is not always a field_address, because when we end, it is invalid. This
                          is not a problem because we don't access it then, but we need to use offset_val*) 
                        forward_loop (EX (n : Z),
                          PROP (0 <= n <= xh)
                          (LOCALx (temp _n (field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + n)) v_v)
                            :: (temp _y (Vubyte (dot_prod (F:=B) (rev_cols_list xh xh (find_invmx_list w' xh)) (*dot prod is reversed*)
                                        (rev_rows_list xh c (lmatrix_multiply xh k c w'' d')) i' j n))) :: 
                            (temp _r (offset_val (((xh - 1 - n) * fec_max_cols) + j) v_s))  :: LOCALS2)
                          (SEPx SEPS2)))
                        break: (PROP () 
                          (LOCALx (temp _y (Vubyte (dot_prod (F:=B) (find_invmx_list w' xh) (*dont need other locals*)
                                        (lmatrix_multiply xh k c w'' d') i' j xh)) :: LOCALS2)
                          (SEPx SEPS2))).
                        { rewrite_eqs; forward. Exists 0. rewrite_eqs; entailer!. solve_offset. }
                        { Intros n. rewrite_eqs; forward_if.
                          { (*pointer access in condition is valid*) entailer!.
                            rewrite isptr_denote_tc_test_order by solve_offset.
                            unfold test_order_ptrs. remember (Zlength (find_lost stats (Zlength packets))) as xh.
                            (*need to go from field_address -> offset_val*)
                            assert_PROP ((field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + n)) v_v) =
                              offset_val (i' * xh * 2 + n) v_v) as Hptr1. { entailer!; solve_offset. }
                            assert_PROP ((field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + xh)) v_v) =
                              offset_val (i' * xh * 2 + xh) v_v) as Hptr2. { entailer!; solve_offset. }
                            rewrite Hptr1. rewrite Hptr2. rewrite sameblock_offset_val by auto.
                            repeat(sep_apply data_at_memory_block).
                            assert (Hptrbound: 0 <= i' * xh * 2 + xh <= (xh * (xh + xh))) by nia.
                            apply andp_right.
                            - sep_eapply (memory_block_weak_valid_pointer Tsh (sizeof (tarray tuchar (xh * (xh + xh)))) v_v); auto; try(simpl; lia).
                              instantiate (1 := (i' * xh * 2 + n)). simpl. nia. entailer!.
                            - sep_eapply (memory_block_weak_valid_pointer Tsh (sizeof (tarray tuchar (xh * (xh + xh)))) v_v); auto; try(simpl; lia).
                              instantiate (1 := (i' * xh * 2 + xh)). simpl. nia. entailer!.
                          }
                          { (*Get the condition into a usable form*)
                            assert_PROP ((field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + n)) v_v) =
                              (field_address0 (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + n)) v_v)) as Hntemp. {
                              entailer!; solve_offset. }
                            assert_PROP ((field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + xh)) v_v) =
                              (field_address0 (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + xh)) v_v)) as Hmtemp. {
                              entailer!; solve_offset. }
                            assert_PROP (n < xh) as Hxnxh. { entailer!. rewrite Hntemp in H6. rewrite Hmtemp in H6.
                              rewrite ptr_comparison_lt_iff in H6; auto; try lia; try nia. simpl. lia. }
                            clear Hntemp Hmtemp H6.
                            forward.
                            { entailer!; nia. }
                            { rewrite Znth_map. 2: { rewrite (flatten_mx_Zlength _ xh (xh + xh)). nia.
                              apply gauss_restrict_list_wf. apply row_mx_list_wf; lia. }
                              entailer!. simpl_repr_byte.
                            }
                            { rewrite Znth_map. 2 : { rewrite (flatten_mx_Zlength _ xh (xh + xh)). nia.
                              apply gauss_restrict_list_wf. apply row_mx_list_wf; lia. }
                              (*Takes forever with literals, need opaque constants*)
                              replace (lvar _s (tarray (tarray tuchar 16000) 128) v_s) with
                                (lvar _s (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s) by
                                (rewrite fec_max_cols_eq; rewrite fec_max_h_eq; reflexivity).
                              replace (data_at Tsh (tarray (tarray tuchar 16000) 128)
                                  (pop_mx_mult_part xh c k fec_max_h fec_max_cols w'' d' xh 0) v_s) with
                                (data_at Tsh (tarray (tarray tuchar fec_max_cols) fec_max_h)
                                  (pop_mx_mult_part xh c k fec_max_h fec_max_cols w'' d' xh 0) v_s) by
                                (rewrite fec_max_cols_eq; rewrite fec_max_h_eq; reflexivity).
                              (*Will need this in both cases. Defaults for Znth are annoying*)
                              assert (Hpopnth: forall (v: val) (l: list val),
                                (@Znth val v j (@Znth (list val) l (xh - 1 - n) 
                                (pop_mx_mult_part xh c k fec_max_h fec_max_cols w'' d' xh 0))) =
                                (Vubyte (get (lmatrix_multiply (F:=B) xh k c w'' d') (xh - 1 - n) j))). {
                                intros v l. rewrite !(@Znth_default _ Inhabitant_val). 
                                rewrite !(@Znth_default _  Inhabitant_list).
                                rewrite pop_mx_mult_part_done; try rep_lia. reflexivity.
                                rewrite pop_mx_mult_part_Zlength; rep_lia.
                                assert (rect (pop_mx_mult_part xh c k fec_max_h fec_max_cols w'' d' xh 0) fec_max_h fec_max_cols) as 
                                  [Hpartlen [_ Hpartall]]. {
                                  apply pop_mx_mult_part_wf; rep_lia. }
                                rewrite Forall_Znth in Hpartall.
                                rewrite !(@Znth_default _  Inhabitant_list) by rep_lia. rewrite Hpartall; rep_lia. }
                              (*Now we need the [field_address] for r*)
                              assert_PROP  (offset_val ((xh - 1 - n) * fec_max_cols + j) v_s = 
                                (field_address (tarray (tarray tuchar fec_max_cols) fec_max_h)
                              [ArraySubsc j; ArraySubsc (xh - 1 - n)] v_s)). { entailer!. solve_offset. }
                              forward.
                              { rewrite Hpopnth. entailer!; simpl_repr_byte. }
                              { rewrite Hpopnth. unfold FIELD_TABLES. Intros.
                                forward_call(gv, (Znth (i' * xh * 2 + n)
                                    (flatten_mx (gauss_restrict_list (F:=B) xh (xh + xh) (concat_mx_id (F:=B) w' xh)))),
                                    (get (lmatrix_multiply (F:=B) xh k c w'' d') (xh - 1 - n) j)).
                                forward. (*simplify y*) unfold Int.xor. rewrite !Int.unsigned_repr by rep_lia.
                                rewrite byte_xor_fold. simpl_repr_byte. rewrite <- byte_int_repr by rep_lia.
                                rewrite Byte.repr_unsigned.
                                forward. (*to avoid any issues with unfolding constants:*)
                                replace (Int.repr 16000) with (Int.repr fec_max_cols) by (f_equal; rep_lia).
                                forward. (*restore loop invar (dot prod)*)
                                Exists (n+1).
                                rewrite_eqs; unfold FIELD_TABLES; entailer!.
                                repeat split. (*lots of equivalences because of pointers*)
                                - solve_offset.
                                - f_equal. rewrite dot_prod_plus_1 by lia.
                                  replace (ssralg.GRing.add (V:=ssralg.GRing.Field.zmodType B)) with Byte.xor by auto.
                                  f_equal.
                                  replace (ssralg.GRing.mul (R:=ssralg.GRing.Field.ringType B)) with ByteField.byte_mul by auto.
                                  f_equal.
                                  + unfold rev_cols_list. rewrite mk_lmatrix_get by lia. 
                                    unfold find_invmx_list. unfold right_submx. rewrite mk_lmatrix_get by lia.
                                    remember (Zlength (find_lost stats (Zlength packets))) as xh.
                                    rewrite (@flatten_mx_Znth' xh (xh + xh)). 3: nia. 
                                    2 : apply gauss_restrict_list_wf; apply row_mx_list_wf; lia.
                                    replace (i' * xh * 2) with (i' * (xh + xh)) by nia.
                                    f_equal.
                                    * rewrite idx_div; lia.
                                    * rewrite idx_mod; lia.
                                  + unfold rev_rows_list. rewrite mk_lmatrix_get by lia. f_equal. lia.
                                - solve_offset.
                                - rewrite fec_max_cols_eq. rewrite fec_max_h_eq. rewrite eqb_type_refl; auto.
                                - rewrite fec_max_cols_eq. rewrite fec_max_h_eq. cancel.
                              }
                            }
                          }
                          { (*end of dot prod loop*) forward.
                            assert_PROP ((field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + n)) v_v) =
                              (field_address0 (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + n)) v_v)) as Hntemp. {
                              entailer!; solve_offset. }
                            assert_PROP ((field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + xh)) v_v) =
                              (field_address0 (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + xh)) v_v)) as Hmtemp. {
                              entailer!; solve_offset. }
                            assert_PROP (xh <= n) as Hxnxh. { entailer!. rewrite Hntemp in H6. rewrite Hmtemp in H6.
                              apply typed_false_not_true in H6. 
                              rewrite ptr_comparison_lt_iff in H6; auto; try lia; try nia.  simpl. lia. }
                            clear Hntemp Hmtemp H6.
                            assert (Hnxh: n = xh) by lia. rewrite_eqs; entailer!. 
                            rewrite dot_prod_rev; try lia. reflexivity. apply right_submx_wf; lia.
                            apply lmatrix_multiply_wf; lia.
                          }
                        }
                        { (*write to data - need to unfold iter_sepcon*)
                          rewrite_eqs; forward; rewrite !Byte.unsigned_repr by rep_lia.
                          { entailer!. }
                          { rewrite pop_find_lost_Znth by (subst; lia). entailer!. simpl_repr_byte. }
                          { rewrite pop_find_lost_Znth by (subst; lia). 
                            (*need for forward*)
                            assert (0 <= Byte.unsigned (Znth (xh - i' - 1) (find_lost stats (Zlength packets))) <
                               Zlength lengths). {
                              replace (Zlength lengths) with (Zlength packets) by lia.
                              assert (Hkbyte: 0 <= Zlength packets <= Byte.max_unsigned) by rep_lia.
                              apply (find_lost_bound stats) in Hkbyte. rewrite Forall_Znth in Hkbyte.
                              apply Hkbyte. subst; lia. }
                            forward.
                            (*need invariant for if statement*)
                            rewrite <- HeqLOCALS. rewrite <- HeqLOCALS1. rewrite <- HeqLOCALS2.
                            rewrite <- HeqSEPS. rewrite <- HeqSEPS1.
                            remember (temp _t'12 (Vint (Int.repr
                              (Znth (Byte.unsigned (Znth (xh - i' - 1) (find_lost stats (Zlength packets)))) lengths)))
                              :: temp _data_lost_row (Vubyte (Znth (xh - i' - 1) (find_lost stats (Zlength packets))))
                              :: temp _y (Vubyte (dot_prod (F:=B) (find_invmx_list (F:=B) w' xh)
                              (lmatrix_multiply (F:=B) xh k c w'' d') i' j xh)) :: LOCALS2) as LOCALS3.
                            rewrite_eqs;
                            forward_if (PROP () (LOCALx LOCALS3 (SEPx 
                              (iter_sepcon_arrays packet_ptrs
                              (pop_fill_rows_list packets
                                 (lmatrix_multiply (F:=B) xh xh c (find_invmx_list (F:=B) w' xh)
                                    (lmatrix_multiply (F:=B) xh k c w'' d'))
                                 (map Byte.unsigned (rev (find_lost stats k))) i' (j + 1)) :: SEPS1)))).
                            { assert (Hilenb: 0 <= (Znth (Byte.unsigned (Znth (xh - i' - 1)
                                 (find_lost stats (Zlength packets)))) lengths) <= c). {
                               rewrite Hlenspec by rep_lia. split; [list_solve |].
                               rewrite Forall_Znth in Hlenbound. apply Hlenbound. lia. }
                              rewrite Int.signed_repr in H6 by rep_lia.
                              rewrite Hlenspec in H6 by lia.
                              (*Need to unfold the [iter_sepcon_arrays]*)
                              remember (pop_fill_rows_list packets
                               (lmatrix_multiply (F:=B) xh xh c (find_invmx_list (F:=B) w' xh)
                                  (lmatrix_multiply (F:=B) xh k c w'' d'))
                               (map Byte.unsigned (rev (find_lost stats k))) i' j) as poppack.
                              assert (Hleneq: Zlength packet_ptrs = Zlength poppack). { subst.
                                unfold pop_fill_rows_list. rewrite mkseqZ_Zlength; lia. }
                              assert (Hibound: 0 <= Byte.unsigned (Znth (xh - i' - 1) 
                                  (find_lost stats (Zlength packets))) < Zlength poppack) by lia.
                              rewrite (iter_sepcon_arrays_remove_one _ _ _ Hleneq Hibound). Intros.
                              forward.
                              { rewrite Znth_app1 by rep_lia. entailer!. }
                              { rewrite Znth_app1 by rep_lia. forward.
                                { entailer!. unfold pop_fill_rows_list.
                                  rewrite mkseqZ_Znth by lia. rewrite mkseqZ_Zlength; lia. }
                                { simpl_repr_byte. rewrite <- (byte_int_repr (Byte.unsigned _)) by rep_lia.
                                  rewrite Byte.repr_unsigned.
                                  (*rewrite before entailer because everything gets subst'ed and it's impossible
                                    to read*)
                                  remember (pop_fill_rows_list packets
                                   (lmatrix_multiply (F:=B) xh xh c (find_invmx_list (F:=B) w' xh)
                                      (lmatrix_multiply (F:=B) xh k c w'' d'))
                                   (map Byte.unsigned (rev (find_lost stats k))) i' (j + 1)) as poppack'.
                                  assert (Hleneq': Zlength packet_ptrs = Zlength poppack'). { subst.
                                    unfold pop_fill_rows_list. rewrite mkseqZ_Zlength; lia. }
                                  assert (Hibound': 0 <= Byte.unsigned (Znth (xh - i' - 1) 
                                      (find_lost stats (Zlength packets))) < Zlength poppack') by lia.
                                  rewrite (iter_sepcon_arrays_remove_one _ _ _ Hleneq' Hibound'). 
                                  rewrite_eqs; entailer!.
                                  rewrite !pop_fill_rows_list_set.
                                  - (*unfold set.*) (*ugh why does entailer ruin all this*)
                                    remember (find_found stats (Zlength packets)) as found.
                                    remember (find_lost stats (Zlength packets)) as lost.
                                    remember (find_parity_rows parities i) as row.
                                    remember (Zlength lost) as xh.
                                    remember (Zlength packets) as k.
                                    remember (submx_rows_cols_rev_list (F:=B) weight_mx xh xh (fec_n - 1)
                                      (seq.map Byte.unsigned row) (seq.map Byte.unsigned (seq.rev lost))) as w'.
                                    remember (submx_rows_cols_rev_list (F:=B) weight_mx xh k (fec_n - 1)
                                      (map Byte.unsigned row)
                                      (map Byte.unsigned (found ++ find_parity_found parities (fec_n - 1) i))) as w''.
                                    remember (col_mx_list (F:=B)
                                     (submx_rows_cols_list (F:=B) packets (k - xh) c (map Byte.unsigned found)
                                        (Ziota 0 c))
                                     (submx_rows_cols_list (F:=B) (fill_missing c parities) xh c
                                        (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) as d'.
                                    remember (lmatrix_multiply (F:=B) xh k c w'' d') as s.
                                    remember (lmatrix_multiply (F:=B) xh xh c (find_invmx_list (F:=B) w' xh) s) as d.
                                    rewrite Znth_map. 2: { rewrite Zlength_rev. list_solve. }
                                    rewrite Znth_rev by lia. replace (Zlength lost) with xh by lia.
                                    unfold set at 3.
                                    rewrite remove_upd_Znth by lia. cancel. apply derives_refl'.
                                    rewrite set_Zlength2. f_equal. unfold set. rewrite !upd_Znth_map.
                                    f_equal. rewrite upd_Znth_same by lia. f_equal. rewrite Heqd.
                                    unfold lmatrix_multiply. rewrite (@mk_lmatrix_get B) by lia.
                                    reflexivity.
                                  - apply FinFun.Injective_map_NoDup. intros b1 b2. apply byte_unsigned_inj.
                                    apply NoDup_rev. apply find_lost_NoDup. rep_lia.
                                  - rewrite Forall_map. apply Forall_rev.
                                    assert (Hlostb: 0 <= Zlength packets <= Byte.max_unsigned) by rep_lia.
                                    apply (find_lost_bound stats) in Hlostb. rewrite Forall_Znth in Hlostb.
                                    rewrite Forall_Znth; intros x Hx. simpl. apply Hlostb. apply Hx.
                                  - rewrite Zlength_map. rewrite Zlength_rev. lia.
                                  - rewrite Znth_map. rewrite Znth_rev by lia. lia. rewrite Zlength_rev; lia.
                                }
                              }
                            }
                            { (*Other case: j bigger than length*)
                              assert (Hilenb: 0 <= (Znth (Byte.unsigned (Znth (xh - i' - 1)
                                 (find_lost stats (Zlength packets)))) lengths) <= c). {
                               rewrite Hlenspec by rep_lia. split; [list_solve |].
                               rewrite Forall_Znth in Hlenbound. apply Hlenbound. lia. }
                              rewrite Int.signed_repr in H6 by rep_lia.
                              rewrite Hlenspec in H6 by lia.
                              forward. rewrite pop_fill_rows_list_set_over.
                              2 : { rewrite Zlength_map. rewrite Zlength_rev. lia. }
                              2 : { rewrite Znth_map. rewrite Znth_rev; subst; lia.
                                    rewrite Zlength_rev. lia. }
                              rewrite_eqs; entailer!.
                            }
                            { rewrite_eqs; forward. (*end of j loop - invar preservation*)
                              Exists (j+1). rewrite_eqs; entailer!.
                            }
                          }
                        }
                      }
                      { (*postcondition for j loop*) assert (Hjc: j = c) by lia. subst. forward.
                        entailer!.
                      }
                    }
                    { (*end of i loop - invar preservation*)
                      rewrite_eqs; forward. Exists (i'+1). rewrite_eqs; entailer!.
                      simpl_repr_byte.
                      rewrite pop_fill_rows_list_finish. cancel. assumption.
                    }
                  }
                }
              }
              { (*postcondition for i loop*) forward. rewrite Byte.unsigned_repr in H2 by rep_lia.
                assert (Hixh: i' = xh) by lia. rewrite_eqs; entailer!.
              }
            }
            { rewrite_eqs; forward_if True. contradiction. forward; entailer!.
              forward_if True; [contradiction | forward; entailer! |].
              forward. simpl_repr_byte. 
              rewrite <- CommonSSR.filter_filter.
              rewrite <- (@find_lost_filter stats (Zlength packets)) by lia. thaw FR1. entailer!.
              unfold decoder_list.
              assert (Hrevlen: Zlength (find_lost stats (Zlength packets)) =
                (Zlength (map Byte.unsigned (rev (find_lost stats (Zlength packets)))))). {
                rewrite Zlength_map. rewrite Zlength_rev. reflexivity. }
              rewrite Hrevlen at 12.
              rewrite (@pop_fill_rows_list_done packets _ (map Byte.unsigned (rev (find_lost stats (Zlength packets))))
                lengths 0 (Zlength packets) c (Zlength (find_lost stats (Zlength packets)))); try lia; try assumption.
              2 : { apply (@lmatrix_multiply_wf B (Zlength (find_lost stats (Zlength packets)))); lia. }
              (*do matrix part last so we can derives_refl'*)
              rewrite !sepcon_assoc.
              apply sepcon_derives.
              - apply derives_refl'. f_equal. f_equal. unfold decode_list_mx.
                rewrite (@fill_rows_list_extend _ _ _ _ _ _ _ c); try lia.
                rewrite Hroweq. rewrite Hfoundeq.
                rewrite !cat_app. rewrite !CommonSSR.map_map_equiv. 
                rewrite (@submx_rows_cols_list_extend _ _ _ _ _ _ c); try lia; try assumption. f_equal.
                rewrite CommonSSR.rev_rev. reflexivity.
                + rewrite Forall_map. eapply Forall_impl. 2:  apply find_found_bound; rep_lia.
                  simpl. lia.
                + rewrite Forall_Znth. rewrite Zlength_Ziota by lia. intros x Hx. rewrite Znth_Ziota; lia. 
                + rewrite Zlength_map. assert (Hkbyte: 0 <= Zlength packets <= Byte.max_unsigned) by rep_lia.
                  apply (find_lost_found_Zlength stats) in Hkbyte. lia.
                + rewrite Zlength_Ziota; lia.
            - apply sepcon_derives.
              + replace (Zlength (find_lost stats (Zlength packets))) with
                  (Zlength (map Byte.unsigned (rev (find_lost stats (Zlength packets))))) by
                (rewrite Zlength_map; rewrite Zlength_rev; reflexivity).
                rewrite pop_stats_done. rewrite zseq_map. replace (Zlength stats) with (Zlength packets) by lia.
                cancel. intros x Hxlen Hx.
                assert (Znth x stats = Byte.zero \/ Znth x stats = Byte.one) as [Hbz | Hbo].  {
                  rewrite Forall_Znth in Hstatsvals. apply Hstatsvals. lia. }
                apply Hbz. rewrite in_map_iff in Hx.
                exfalso. apply Hx. exists (Byte.repr x). split. rewrite Byte.unsigned_repr; rep_lia.
                unfold find_lost. rewrite <- in_rev.
                rewrite find_lost_found_aux_in_spec. right. rewrite !Byte.unsigned_repr by rep_lia.
                split.
                rewrite Ziota_In; lia. rewrite Hbo. auto.
                rewrite Forall_Znth. rewrite Zlength_Ziota by lia. intros y Hy. 
                rewrite Znth_Ziota; rep_lia.
              + rewrite fec_max_h_eq. entailer!. rewrite sepcon_comm.
                remember (Zlength (find_lost stats (Zlength packets))) as xh.
                replace (xh * (xh + xh)) with (2 * xh * xh) by lia.
                rewrite <- (split2_data_at_Tarray_app).
                (*Now have to go 1D - 2D array*)
                rewrite <- (concat_unconcat _ 128 256); try lia.
                replace (2 * 128 * 128) with (128 * 256) by lia.
                rewrite <- data_at_2darray_concat; auto. entailer!.
                * apply unconcat_length2; lia.
                * rewrite Zlength_app. rewrite Zlength_map.
                  rewrite (@flatten_mx_Zlength _ xh (xh + xh)).
                  rewrite zseq_Zlength. nia. assert (xh <= 128) by rep_lia. nia.
                  apply gauss_restrict_list_wf. apply row_mx_list_wf; lia.
                * rewrite Zlength_map. rewrite (@flatten_mx_Zlength _ xh (xh + xh)). lia.
                  apply gauss_restrict_list_wf. apply row_mx_list_wf; lia.
                * rewrite zseq_Zlength. nia. assert (xh <= 128) by rep_lia. nia.
            }
          }
        }
      }
    }
  }
}
Qed.

End Decoder.