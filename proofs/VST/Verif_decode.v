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

Opaque ByteField.byte_mul.

Local Open Scope list_scope.

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
  destruct (Z_lt_dec (Z.of_nat n) 0); [lia |]. clear n0. rewrite Nat2Z.id. 
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
  intros z Hz. unfold default_val. simpl. rewrite zseq_Zrepeat by lia. reflexivity.
Qed.

Definition fec_blk_decode_loop1 :=
              Sfor 
                (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tuchar))
                (Ebinop Olt (Etempvar _i tuchar) (Etempvar _k tint) tint)
                (Ssequence
                        (Sset _t'42
                          (Ederef
                            (Ebinop Oadd (Etempvar _pstat (tptr tschar))
                              (Etempvar _i tuchar) (tptr tschar)) tschar))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'42 tschar)
                                       (Econst_int (Int.repr 1) tint) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'1 (Etempvar _xh tuchar))
                              (Sset _xh
                                (Ecast
                                  (Ebinop Oadd (Etempvar _t'1 tuchar)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tuchar)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _lost (tarray tuchar 128))
                                  (Etempvar _t'1 tuchar) (tptr tuchar))
                                tuchar) (Etempvar _i tuchar)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'2 (Etempvar _xk tuchar))
                              (Sset _xk
                                (Ecast
                                  (Ebinop Oadd (Etempvar _t'2 tuchar)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tuchar)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _found (tarray tuchar 128))
                                  (Etempvar _t'2 tuchar) (tptr tuchar))
                                tuchar) (Etempvar _i tuchar)))))
                (Sset _i (Ecast (Ebinop Oadd (Etempvar _i tuchar)
                          (Econst_int (Int.repr 1) tint) tint) tuchar)).

Lemma body_fec_blk_decode_loop1: 
 forall (Espec: OracleKind) (k : Z)
   (pd pl ps : val)
   (stats : list byte)
  (v_v v_s v_lost v_found v_row : val)
  (Hknh : 0 < k < fec_n - fec_max_h)
  (Hstatsvals : Forall (fun x : byte => x = Byte.zero \/ x = Byte.one) stats)
  (Hstatlen : Zlength stats = k),
semax (func_tycontext f_fec_blk_decode Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _xh (Vubyte Byte.zero); temp _xk (Vubyte Byte.zero);
   temp _k (Vint (Int.repr k)); temp _pstat ps; lvar _found (tarray tuchar fec_max_h) v_found;
   lvar _lost (tarray tuchar fec_max_h) v_lost)
   SEP (data_at Ews (tarray tschar k) (map Vbyte stats) ps;
   data_at Tsh (tarray tuchar fec_max_h) (zseq fec_max_h Vundef) v_found;
   data_at Tsh (tarray tuchar fec_max_h) (zseq fec_max_h Vundef) v_lost))
  fec_blk_decode_loop1
  (normal_ret_assert
     (PROP ( )
      LOCAL (temp _xh (Vubyte (Byte.repr (Zlength (find_lost stats k))));
      temp _xk (Vubyte (Byte.repr (Zlength (find_found stats k))));
      temp _k (Vint (Int.repr k)); temp _pstat ps;
      lvar _found (tarray tuchar fec_max_h) v_found;
      lvar _lost (tarray tuchar fec_max_h) v_lost)
      SEP (data_at Ews (tarray tschar k) (map Vbyte stats) ps;
      data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost;
      data_at Tsh (tarray tuchar fec_max_h) (pop_find_found stats k fec_max_h) v_found))).
Proof.
intros.
unfold fec_blk_decode_loop1.
abbreviate_semax.

forward_loop (EX (i: Z),
  PROP (0 <= i <= k)
  LOCAL (temp _i (Vubyte (Byte.repr i)); 
               temp _xh (Vubyte (Byte.repr (Zlength (find_lost stats i))));
               temp _xk (Vubyte (Byte.repr (Zlength (find_found stats i))));
               temp _k (Vint (Int.repr k)); temp _pstat ps;
               lvar _found (tarray tuchar fec_max_h) v_found;
               lvar _lost (tarray tuchar fec_max_h) v_lost)
  SEP (data_at Ews (tarray tschar k) (map Vbyte stats) ps;
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats i fec_max_h) v_lost;
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_found stats i fec_max_h) v_found))%assert5.

{ forward. Exists 0. entailer!.
  { rewrite pop_find_lost_0. rewrite pop_find_found_0. cancel. }
}
{ (*unfold app. rewrite_eqs.*) 
   Intros i. forward_if.
  { rewrite Byte.unsigned_repr in H0 by rep_lia.
    assert (Hilen: (0 <= Byte.unsigned (Byte.repr i) < Zlength stats)) by simpl_repr_byte.
    forward. simpl_repr_byte.
    forward_if (PROP ()
      LOCAL (temp _i (Vubyte (Byte.repr i));
             temp _xh (Vubyte (Byte.repr (Zlength (find_lost stats (i + 1)))));
             temp _xk (Vubyte (Byte.repr (Zlength (find_found stats (i + 1)))));
             temp _k (Vint (Int.repr k)); temp _pstat ps;
             lvar _found (tarray tuchar fec_max_h) v_found;
             lvar _lost (tarray tuchar fec_max_h) v_lost)
      SEP (data_at Ews (tarray tschar k) (map Vbyte stats) ps; 
           data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats (i + 1) fec_max_h) v_lost; 
           data_at Tsh (tarray tuchar fec_max_h) (pop_find_found stats (i + 1) fec_max_h) v_found)%assert5).
    { (*xh case*) forward. pose proof (@find_lost_Zlength stats i (proj1 H)) as Hlostlen.
      forward. unfold Int.add. rewrite !Int.unsigned_repr; simpl_repr_byte.
      rewrite <- (byte_int_repr (Zlength (find_lost stats i))) by rep_lia.
      forward. (*TODO: this was the problematic one*)
      { entailer!. simpl_repr_byte. }
      { simpl_repr_byte. entailer!.
        { rewrite <- byte_int_repr by rep_lia.
          rewrite find_lost_plus_1 by lia. rewrite find_found_plus_1 by lia. repeat simpl_sum_if.
          split; [f_equal; f_equal|reflexivity]. list_solve. 
        }
        { rewrite pop_find_lost_plus_1 by rep_lia.
          rewrite pop_find_found_plus_1 by rep_lia. repeat simpl_sum_if.
          rewrite <- byte_int_repr by rep_lia. cancel.
        }
      }
    }
    { (*xk case*) forward. pose proof (@find_found_Zlength stats i (proj1 H)) as Hfoundlen.
      forward. unfold Int.add. rewrite !Int.unsigned_repr; simpl_repr_byte.
      rewrite <- (byte_int_repr (Zlength (find_found stats i))) by rep_lia.
      forward.
      { entailer!. simpl_repr_byte. }
      { simpl_repr_byte. rewrite_eqs; entailer!.
        { rewrite <- byte_int_repr by rep_lia.
          rewrite find_lost_plus_1 by lia. rewrite find_found_plus_1 by lia. repeat simpl_sum_if.
          split; [reflexivity| f_equal; f_equal]. list_solve.
        }
        { rewrite pop_find_lost_plus_1 by rep_lia.
          rewrite pop_find_found_plus_1 by rep_lia. repeat simpl_sum_if.
          rewrite <- byte_int_repr by rep_lia. cancel.
        }
      }
    }
    { forward. Exists (i+1). unfold Int.add. rewrite !Int.unsigned_repr; simpl_repr_byte.
      entailer!. rewrite <- byte_int_repr by rep_lia. reflexivity.
    }
  }
  { (*first loop postcondition*) forward. rewrite Byte.unsigned_repr in H0 by rep_lia.
    replace i with k by lia. entailer!. 
  }
}
Qed.

(*A frame rule for mpreds with EX*)
Lemma semax_frame_ex: forall `{Espec: OracleKind} {A: Type} (QFrame : list localdef) (Frame : list mpred) (Delta Delta1 : tycontext) 
         (P : list Prop) (Q : list localdef) (c : statement) (R : list mpred) 
         (P1 : list Prop) (Q1 : list localdef) (R1 : list mpred) (P2 : A -> list Prop) 
         (Q2 : A -> list localdef) (R2 : A -> list mpred),
       semax Delta1 (PROPx P1 (LOCALx Q1 (SEPx R1))) c
         (normal_ret_assert (EX i : A, (PROPx (P2 i) (LOCALx (Q2 i) (SEPx (R2 i))))))->Delta1 = Delta->
       (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
        |-- PROPx P1 (LOCALx (Q1 ++ QFrame) (SEPx (R1 ++ Frame))))->closed_wrt_modvars c
                                                                      (LOCALx QFrame (SEPx Frame))->
       semax Delta (PROPx P (LOCALx Q (SEPx R))) c
         (normal_ret_assert (EX i : A, (PROPx (P2 i) (LOCALx ((Q2 i) ++ QFrame) (SEPx ((R2 i) ++ Frame)))))).
Proof.
  intros. 
  eapply semax_pre. apply H1.
  replace (PROPx P1 (LOCALx (Q1 ++ QFrame) (SEPx (R1 ++ Frame)))) with
    ((PROPx P1 (LOCALx Q1 (SEPx R1))) * (LOCALx QFrame (SEPx Frame)))%logic
  by (rewrite <- (app_nil_r P1) at 2; rewrite <- PROP_combine; f_equal; unfold PROPx; normalize).
  apply (semax_frame _ _ _ _ _ H2) in H. rewrite frame_normal in H.
  replace (EX i : A, PROPx (P2 i) (LOCALx (Q2 i ++ QFrame) (SEPx (R2 i ++ Frame))))%argsassert
    with ((EX i : A, PROPx (P2 i) (LOCALx (Q2 i) (SEPx (R2 i))))%argsassert
             * LOCALx QFrame (SEPx Frame))%logic. subst; apply H.
  normalize.
  assert (forall (f: A -> mpred) (g: A -> mpred),
    (forall a, f a = g a) ->
    (EX y : A, f y) = (EX y : A, g y)). { intros. apply pred_ext;
    apply exp_left; intros x;
    apply (exp_right x); rewrite H3; cancel. }
  simpl. apply functional_extensionality. intros y.
  apply H3. intros. rewrite <- (app_nil_r (P2 a)) at 2. rewrite <- PROP_combine. simpl. f_equal.
  unfold PROPx. simpl. normalize.
Qed.


(*More useful version of this*)
Lemma semax_frame_seq_ex: forall `{Espec: OracleKind} {A: Type} 
        (QFrame : list localdef) (Frame : list mpred) (Delta : tycontext) 
         (P : list Prop) (Q : list localdef) (c1 c2 : statement) (R : list mpred) 
         (P1 : list Prop) (Q1 : list localdef) (R1 : list mpred) (P2 : A -> list Prop) 
         (Q2 : A -> list localdef) (R2 : A -> list mpred) (R3: ret_assert),
       semax Delta (PROPx P1 (LOCALx Q1 (SEPx R1))) c1
         (normal_ret_assert (EX i : A, (PROPx (P2 i) (LOCALx (Q2 i) (SEPx (R2 i))))))->
       (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
        |-- PROPx P1 (LOCALx (Q1 ++ QFrame) (SEPx (R1 ++ Frame))))->closed_wrt_modvars c1
                                                                      (LOCALx QFrame (SEPx Frame))->
        semax Delta (EX i : A, (PROPx (P2 i) (LOCALx ((Q2 i) ++ QFrame) (SEPx ((R2 i) ++ Frame))))) c2 R3 ->
       semax Delta (PROPx P (LOCALx Q (SEPx R))) (Ssequence c1 c2) R3.
Proof.
  intros. eapply semax_seq. 2: apply H2.
  eapply semax_frame_ex in H. 2: reflexivity.  2: apply H0. 2: assumption.
  apply sequential'. apply H.
Qed.


(*Second loop*)
Definition fec_blk_decode_loop2 :=
(Sfor (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tuchar))
        (Ebinop Olt (Etempvar _xr tuchar) (Etempvar _xh tuchar) tint)
        (Ssequence
           (Ssequence
              (Sset _t'41
                 (Ederef
                    (Ebinop Oadd (Etempvar _pparity (tptr (tptr tuchar))) (Etempvar _i tuchar)
                       (tptr (tptr tuchar))) (tptr tuchar)))
              (Sifthenelse (Etempvar _t'41 (tptr tuchar))
                 (Ssequence
                    (Ssequence
                       (Ssequence (Sset _t'3 (Etempvar _xk tuchar))
                          (Sset _xk
                             (Ecast
                                (Ebinop Oadd (Etempvar _t'3 tuchar) (Econst_int (Int.repr 1) tint) tint)
                                tuchar)))
                       (Sassign
                          (Ederef
                             (Ebinop Oadd (Evar _found (tarray tuchar 128)) 
                                (Etempvar _t'3 tuchar) (tptr tuchar)) tuchar) 
                          (Etempvar _q tuchar)))
                    (Ssequence
                       (Ssequence (Sset _t'4 (Etempvar _xr tuchar))
                          (Sset _xr
                             (Ecast
                                (Ebinop Oadd (Etempvar _t'4 tuchar) (Econst_int (Int.repr 1) tint) tint)
                                tuchar)))
                       (Sassign
                          (Ederef
                             (Ebinop Oadd (Evar _row (tarray tuchar 128)) (Etempvar _t'4 tuchar)
                                (tptr tuchar)) tuchar) (Etempvar _i tuchar)))) Sskip))
           (Ssequence
              (Sset _q
                 (Ecast (Ebinop Osub (Etempvar _q tuchar) (Econst_int (Int.repr 1) tint) tint) tuchar))
              (Sifthenelse (Ebinop Olt (Etempvar _i tuchar) (Econst_int (Int.repr 128) tint) tint) Sskip
                 (Scall None
                    (Evar ___assert_fail
                       (Tfunction
                          (Tcons (tptr tschar)
                             (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
                          cc_default))
                    (cons (Evar ___stringlit_14 (tarray tschar 14))
                       (cons (Evar ___stringlit_6 (tarray tschar 6))
                          (cons (Econst_int (Int.repr 329) tint)
                             (cons (Evar ___func____2 (tarray tschar 15)) nil))))))))
        (Sset _i (Ecast (Ebinop Oadd (Etempvar _i tuchar) (Econst_int (Int.repr 1) tint) tint) tuchar))).

(*This needs a lot of preconditions, mainly relating to bounds. It is possible to simplify some of these bounds
  which will give additional subgoals in the main proof*)
Lemma body_fec_blk_decode_loop2: forall (Espec: OracleKind) (k h c xk xh parbound: Z) (v_found v_row: val)
  (pd: val) (packet_ptrs parity_ptrs: list val) (parities: list (option (list byte))) (stats: list byte)
  (Hknh : 0 < k < fec_n - fec_max_h)
  (Hhh : 0 <= h <= fec_max_h)
  (Hccols : 0 < c <= fec_max_cols) (*Technically only need the first part*)
  (Hpackptrlen : Zlength packet_ptrs = k)
  (Hparlen : Zlength parities = h)
  (Heqxh : xh = Zlength (find_lost stats k))
  (Hnumpars : xh = Zlength (find_parity_rows parities parbound))
  (Hparsconsist : forall i : Z, 0 <= i < h->Znth i parities = None <-> Znth i parity_ptrs = nullval)
  (Hparsomelen : forall (i : Z) (l : list byte), 0 <= i < h->Znth i parities = Some l->Zlength l = c)
  (Hparptrlen : Zlength parity_ptrs = h)
  (Heqxk : xk = Zlength (find_found stats k))
  (Hxh : xh <= k)
  (Hxk : xk <= k)
  (Hbp: 0 <= parbound <= h),
semax (func_tycontext f_fec_blk_decode Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _xr (Vubyte Byte.zero); temp _xk (Vubyte (Byte.repr xk));
   temp _q (Vint (Int.repr (256 - 2))); lvar _found (tarray tuchar fec_max_h) v_found;
   lvar _row (tarray tuchar fec_max_h) v_row; temp _xh (Vubyte (Byte.repr xh));
   temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd))
   SEP (data_at Tsh (tarray tuchar fec_max_h) (pop_find_found stats k fec_max_h) v_found;
   data_at Tsh (tarray tuchar fec_max_h) (zseq fec_max_h Vundef) v_row;
   data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
   iter_sepcon_options parity_ptrs parities))
  fec_blk_decode_loop2
  (normal_ret_assert
     (EX i : Z,
      PROP (0 <= i <= Zlength parities; Zlength (find_parity_rows parities i) = xh)
      LOCAL (temp _xr (Vubyte (Byte.repr (Zlength (find_parity_rows parities i))));
      temp _xk (Vubyte (Byte.repr (xk + Zlength (find_parity_found parities (fec_n - 1) i))));
      temp _q (Vint (Int.repr (fec_n - 2 - i))); lvar _found (tarray tuchar fec_max_h) v_found;
      lvar _row (tarray tuchar fec_max_h) v_row; temp _xh (Vubyte (Byte.repr xh));
      temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd))
      SEP (data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row;
      data_at Tsh (tarray tuchar fec_max_h)
        (pop_find_parity_found stats parities i fec_max_h k (fec_n - 1)) v_found;
      data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
      iter_sepcon_options parity_ptrs parities))).
Proof.
  intros.
  unfold fec_blk_decode_loop2.
  abbreviate_semax.
  (*In this loop, we exit once we have found xh valid parity pointers, so the
      postcondition involves an EX quantifier - we don't know exactly how many steps it will take*)
    forward_loop (EX (i: Z),
      PROP (0 <= i <= Zlength parities; 0 <= Zlength (find_parity_rows parities i) <= xh)
      LOCAL (temp _i (Vint (Int.repr i)); temp _xr (Vubyte (Byte.repr (Zlength (find_parity_rows parities i))));
        temp _xk (Vubyte (Byte.repr (xk + Zlength (find_parity_found parities (fec_n - 1) i))));
        temp _q (Vint (Int.repr (fec_n - 2 - i)));
        lvar _found (tarray tuchar fec_max_h) v_found;
        lvar _row (tarray tuchar fec_max_h) v_row; temp _xh (Vubyte (Byte.repr xh));
        temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd))
      SEP (data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row;
           data_at Tsh (tarray tuchar fec_max_h)  
              (pop_find_parity_found stats parities i fec_max_h k (fec_n - 1)) v_found;
           data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
           iter_sepcon_options parity_ptrs parities)).
    { forward. Exists 0. entailer!.
      { pose proof (@find_parity_rows_Zlength parities 0). 
        repeat split; try reflexivity; try repeat f_equal; try rep_lia.
      }
      { rewrite pop_find_parity_found_0. rewrite pop_find_parity_rows_0. cancel. }
    }
    { Intros i. forward_if.
      { rewrite !Byte.unsigned_repr in H1 by rep_lia.
        assert (Hi: i < Zlength parities). {
          assert (Hparbound: 
            Zlength (find_parity_rows parities i) < Zlength (find_parity_rows parities parbound)) by lia.
          apply find_parity_rows_inj in Hparbound; lia. }
        assert_PROP (force_val (sem_add_ptr_int (tptr tuchar) Signed 
            (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd)
            (Vint (Int.repr i))) = field_address (tarray (tptr tuchar) (k + h)) (SUB (k + i)) pd) as Hpari. {
            entailer!. solve_offset. } 
        (*It makes more sense to case of whether the ith entry is Some or None, then go through the VST proof 
          separately for each one. We remember the postcondition so we don't need to write it twice*)
        set (IFPost := (PROP ()
            LOCAL (temp _i (Vint (Int.repr i));
              temp _xr (Vubyte (Byte.repr (Zlength (find_parity_rows parities (i + 1)))));
              temp _xk (Vubyte (Byte.repr (xk + Zlength (find_parity_found parities (fec_n - 1) (i + 1)))));
              temp _q (Vint (Int.repr (fec_n - 2 - i)));
              lvar _found (tarray tuchar fec_max_h) v_found;
              lvar _row (tarray tuchar fec_max_h) v_row; temp _xh (Vubyte (Byte.repr xh));
              temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd))
            SEP (data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
              iter_sepcon_options parity_ptrs parities;
              data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities (i+1) fec_max_h) v_row;
              data_at Tsh (tarray tuchar fec_max_h)  
                (pop_find_parity_found stats parities (i+1) fec_max_h k (fec_n - 1)) v_found))%assert5).
        assert (Hlen: Zlength parity_ptrs = Zlength parities) by lia.
        assert (Hibound: 0 <= i < Zlength parities) by lia.
        destruct (Znth i parities) as [l |] eqn : Hparith.
        { rewrite (iter_sepcon_options_remove_one _ _ _ _ Hlen Hibound Hparith). Intros. forward.
          { rewrite Znth_app2 by lia. replace (k + i - Zlength packet_ptrs) with i by lia.
             entailer!.
          }
          { entailer!. solve_offset. }
          { forward_if IFPost; try(rewrite Znth_app2 by lia); 
            try (replace (Zlength packet_ptrs + i - Zlength packet_ptrs) with i by lia).
            { apply denote_tc_test_eq_split. do 3 (rewrite !sepcon_assoc, sepcon_comm).
              rewrite !sepcon_assoc. apply sepcon_valid_pointer1. apply data_at_valid_ptr; auto.
              simpl. rewrite (Hparsomelen i) by (auto; rep_lia). lia.
              apply valid_pointer_zero64; auto.
            }
            { forward.
              pose proof (@find_parity_found_Zlength parities i (fec_n - 1)) as Hparfoundlen.
              simpl_repr_byte. forward. unfold Int.add. simpl_repr_byte.
              forward.
              { entailer!. split; try rep_lia.
                assert (Hpackbound: 0 <= Zlength packet_ptrs <= Byte.max_unsigned) by rep_lia.
                pose proof (find_lost_found_Zlength stats Hpackbound) as Hxhxk.
                rewrite find_parity_rows_found_Zlength. rep_lia.
              }
              { forward. simpl_repr_byte. forward. unfold Int.add; simpl_repr_byte.
                forward.
                { entailer!. }
                { subst IFPost. entailer!.
                  { rewrite find_parity_rows_plus_1, find_parity_found_plus_1, Hparith, <-!byte_int_repr by rep_lia.
                    repeat split; f_equal; f_equal; rewrite Zlength_app; list_solve.
                  }
                  { (*rewrite pop_find_parity_rows_plus_1 by rep_lia.*)
                    rewrite pop_find_parity_rows_plus_1, pop_find_parity_found_plus_1; try rep_lia.
                    2: { assert (Hpackbound: 0 <= Zlength packet_ptrs <= Byte.max_unsigned) by rep_lia.
                        pose proof (find_lost_found_Zlength stats Hpackbound) as Hxhxk.
                        rewrite find_parity_rows_found_Zlength. rep_lia. }
                    rewrite Hparith. replace (fec_n - 1 - 1 - i) with (fec_n - 2 - i) by lia.
                    (*need to put [iter_sepcon_options] back together*)
                    rewrite (iter_sepcon_options_remove_one _ _ _ _ Hlen Hibound Hparith), <-!byte_int_repr by rep_lia.
                    cancel.
                  }
                }
              }
            }
            { (*contradiction*) 
              (*TODO: why is Znth unfolding?*)
              pose proof (Znth_app2 val Vundef) as Happ.
              unfold Znth at 1 in Happ.
              rewrite Happ in H2 by lia.
              (*rewrite Znth_app2 in H2 by lia.*)
               replace (k + i - Zlength packet_ptrs) with i in H2 by lia.
               rewrite <- Hparsconsist in H2 by lia. rewrite H2 in Hparith; inversion Hparith.
            }
            { (*it would be nice to not have to repeat this part, but not sure how
                except by doing cases in all the above*) subst IFPost. forward.
              unfold Int.sub. simpl_repr_byte. forward_if True.
              { forward. entailer!. }
              { rep_lia. }
              { forward. unfold Int.add. simpl_repr_byte. Exists (i+1). entailer!.
                { rewrite find_parity_rows_plus_1, Hparith, Zlength_app by lia. repeat split.
                  rep_lia. list_solve. f_equal; f_equal; lia.
                }
                { rewrite (iter_sepcon_options_remove_one _ _ _ _ Hlen Hibound Hparith). cancel. }
            }
          }
        }
      }
      { (*Now, we have the case where there is no parity packet. This will be simpler.*)
        assert (Hnull: @Znth _ Vundef i parity_ptrs = nullval) by (apply Hparsconsist; [ lia | assumption]).
        forward.
        { rewrite Znth_app2 by lia. replace (k + i - Zlength packet_ptrs) with i by lia.
          entailer!. rewrite Hnull. reflexivity. 
        }
        { entailer!. solve_offset. }
        { forward_if IFPost; try(rewrite Znth_app2 by lia); 
          try (replace (Zlength packet_ptrs + i - Zlength packet_ptrs) with i by lia).
          { rewrite Hnull. apply denote_tc_test_eq_split. apply valid_pointer_null.
            apply valid_pointer_zero64; auto.
          }
          { forward.
            (*TODO: again Znth is unfolded*)
            pose proof (Znth_app2 val Vundef) as Happ.
            unfold Znth at 1 in Happ.
            rewrite Happ in H2 by lia. 
            (*rewrite Znth_app2 in H2 by lia.*)
            replace (k + i - Zlength packet_ptrs) with i in H2 by lia.
            rewrite Hnull in H2. inversion H2.
          }
          { (*The actual null case*) forward. subst IFPost. entailer!.
            { rewrite find_parity_rows_plus_1, find_parity_found_plus_1,Hparith by lia. auto. }
            { rewrite pop_find_parity_rows_plus_1, pop_find_parity_found_plus_1; try rep_lia.
                rewrite Hparith. cancel.
              assert (Hpackbound: 0 <= Zlength packet_ptrs <= Byte.max_unsigned) by rep_lia.
              pose proof (find_lost_found_Zlength stats Hpackbound) as Hxhxk.
              rewrite find_parity_rows_found_Zlength. rep_lia. 
            }
          }
          { subst IFPost. forward. unfold Int.sub. simpl_repr_byte.
            forward_if True.
            { forward. entailer!. }
            { rep_lia. }
            { forward. unfold Int.add; simpl_repr_byte. Exists (i+1). entailer!.
              rewrite find_parity_rows_plus_1, Hparith by lia.
              repeat split; try rep_lia. f_equal; f_equal; lia.
            }
          }
        }
      }
    }
    { rewrite !Byte.unsigned_repr in H1 by rep_lia. forward. Exists i. entailer!.
    }
  }
Qed.

(*Third loop*)
Definition fec_blk_decode_loop3 :=
(Sfor (Sset _j (Econst_int (Int.repr 0) tint))
     (Ebinop Olt (Etempvar _j tint) (Etempvar _xh tuchar) tint)
     (Ssequence
        (Ssequence
           (Sset _t'28
              (Ederef (Ebinop Oadd (Evar _row (tarray tuchar 128)) (Etempvar _j tint) (tptr tuchar))
                 tuchar))
           (Sset _n
              (Ecast
                 (Ederef
                    (Ebinop Oadd (Evar _fec_weights (tarray (tarray tuchar 255) 128))
                       (Etempvar _t'28 tuchar) (tptr (tarray tuchar 255))) (tarray tuchar 255))
                 (tptr tuchar))))
        (Ssequence
           (Sset _r
              (Ebinop Oadd (Ederef (Evar _v (tarray (tarray tuchar 256) 128)) (tarray tuchar 256))
                 (Ebinop Omul (Ebinop Omul (Etempvar _j tint) (Etempvar _xh tuchar) tint)
                    (Econst_int (Int.repr 2) tint) tint) (tptr tuchar)))
           (Sfor (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tuchar))
              (Ebinop Olt (Etempvar _i tuchar) (Etempvar _xh tuchar) tint)
              (Ssequence
                 (Sifthenelse
                    (Ebinop Oeq
                       (Ebinop Oadd (Ebinop Oadd (Etempvar _i tuchar) (Etempvar _j tint) tint)
                          (Econst_int (Int.repr 1) tint) tint) (Etempvar _xh tuchar) tint)
                    (Sassign
                       (Ederef
                          (Ebinop Oadd (Etempvar _r (tptr tuchar)) (Etempvar _i tuchar) (tptr tuchar))
                          tuchar) (Econst_int (Int.repr 1) tint))
                    (Sassign
                       (Ederef
                          (Ebinop Oadd (Etempvar _r (tptr tuchar)) (Etempvar _i tuchar) (tptr tuchar))
                          tuchar) (Econst_int (Int.repr 0) tint)))
                 (Ssequence
                    (Sset _t'26
                       (Ederef
                          (Ebinop Oadd (Evar _lost (tarray tuchar 128)) (Etempvar _i tuchar)
                             (tptr tuchar)) tuchar))
                    (Ssequence
                       (Sset _t'27
                          (Ederef
                             (Ebinop Oadd (Etempvar _n (tptr tuchar)) (Etempvar _t'26 tuchar)
                                (tptr tuchar)) tuchar))
                       (Sassign
                          (Ederef
                             (Ebinop Oadd
                                (Ebinop Oadd (Etempvar _r (tptr tuchar)) (Etempvar _i tuchar)
                                   (tptr tuchar)) (Etempvar _xh tuchar) (tptr tuchar)) tuchar)
                          (Etempvar _t'27 tuchar)))))
              (Sset _i
                 (Ecast (Ebinop Oadd (Etempvar _i tuchar) (Econst_int (Int.repr 1) tint) tint) tuchar)))))
     (Sset _j (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint) tint))).

Ltac rep_nia := rep_lia_setup; rep_lia_setup2; nia.

(*This proof has a decent amount of repetition in it, seems like it can be automated more*)
Lemma body_fec_blk_decode_loop3: forall (Espec: OracleKind) (k xh i: Z) (stats: list byte)
  (parities: list (option (list byte)))
  (v_v v_lost v_row : val) (gv: globals)
(Hknh : 0 < k < fec_n - fec_max_h)
(Heqxh : xh = Zlength (find_lost stats k))
(Hxh : xh <= k)
(Hixh : Zlength (find_parity_rows parities i) = xh)
(Hxh0: 0 < xh)
(Hih: 0 <= i <= fec_max_h) (*simplifes a bunch of them*),
semax (func_tycontext f_fec_blk_decode Vprog Gprog [])
  (PROP ( )
   LOCAL (lvar _v (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v;
   lvar _lost (tarray tuchar fec_max_h) v_lost; temp _xh (Vubyte (Byte.repr xh));
   lvar _row (tarray tuchar fec_max_h) v_row; gvars gv)
   SEP (data_at_ Tsh (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v;
   data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights);
   data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost;
   data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row))
  fec_blk_decode_loop3
  (normal_ret_assert
     (PROP ( )
      LOCAL (lvar _v (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v;
      lvar _lost (tarray tuchar fec_max_h) v_lost; temp _xh (Vubyte (Byte.repr xh));
      lvar _row (tarray tuchar fec_max_h) v_row; gvars gv)
      SEP (data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h))
             (pop_find_inv xh (map_2d_rev id weight_mx) (find_parity_rows parities i)
                (find_lost stats k) xh 0) v_v;
      data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx)
        (gv _fec_weights);
      data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost;
      data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row))).
Proof.
  intros.
  unfold fec_blk_decode_loop3.
  abbreviate_semax.
  forward_loop (EX (j : Z),
    PROP (0 <= j <= xh)
    LOCAL (temp _j (Vint (Int.repr j)); lvar _v (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v;
      lvar _lost (tarray tuchar fec_max_h) v_lost; temp _xh (Vubyte (Byte.repr xh));
      lvar _row (tarray tuchar fec_max_h) v_row; gvars gv)
    SEP (data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h))
          (pop_find_inv xh (map_2d_rev id weight_mx) (find_parity_rows parities i) (find_lost stats k) j 0) v_v;
         data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights);
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost;
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row)).
  { forward. Exists 0. entailer!.
     (*Need to go 2D-1D array for loop and Gaussian elim*) rewrite data_at__tarray, data_at_2darray_concat. 
    { replace (fec_max_h * (fec_max_h * 2)) with (2 * fec_max_h * fec_max_h) by lia. apply derives_refl'.
      f_equal. rewrite pop_find_inv_0, zseq_Zrepeat,default_arr,(@zseq_concat (reptype tuchar))  by rep_lia.
      f_equal. lia.
    }
    { rewrite Zlength_Zrepeat; rep_lia. }
    { rewrite Forall_Znth, Zlength_Zrepeat by rep_lia. intros y Hy.
      rewrite Znth_Zrepeat,default_arr,zseq_Zlength; lia. }
    { auto. }
  }
  { Intros j. forward_if.
    { rewrite Byte.unsigned_repr in H0 by rep_lia. forward.
      { entailer!. }
      { entailer!. rewrite pop_find_parity_rows_Znth by rep_lia. simpl_repr_byte. }
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
          rewrite !Int.signed_repr; rep_nia.
        }
        { replace (tarray (tarray tuchar 256) 128) with (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h)
          by (repeat f_equal; repeat rep_lia).
          (*donesn't technically need frame rule but makes things a bit nicer, and should be much better
            with automation*)
          (*To cut down on repetition*)
          set (loc := [temp _r (force_val (sem_binary_operation' Oadd (tarray tuchar 256) tint v_v
                  (eval_binop Omul tint tint (eval_binop Omul tint tuchar (Vint (Int.repr j)) (Vubyte (Byte.repr xh)))
                  (Vint (Int.repr 2)))));
                 temp _n (force_val (sem_binary_operation' Oadd (tarray (tarray tuchar 255) 128) tuchar 
                  (gv _fec_weights) (Vubyte (Znth j (find_parity_rows parities i)))));
                 temp _j (Vint (Int.repr j)); lvar _lost (tarray tuchar fec_max_h) v_lost;
                 temp _xh (Vubyte (Byte.repr xh));
                 gvars gv]).
          apply (semax_frame_seq 
                  [ temp _t'28 (Vubyte (Znth j (find_parity_rows parities i)));
                    lvar _v (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v;
                    lvar _row (tarray tuchar fec_max_h) v_row ]
                  [ data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row])
          with (P1 := [])(P2 := [])
          (Q1 := loc)
          (Q2 := loc)
          (R1 := [data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h))
                  (pop_find_inv xh (map_2d_rev id weight_mx) (find_parity_rows parities i) 
                  (find_lost stats k) j 0) v_v;
                  data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights);
                  data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost])
          (R2 := [ data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h)) (pop_find_inv xh 
                    (map_2d_rev id weight_mx) (find_parity_rows parities i) (find_lost stats k) j xh) v_v;
                   data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights);
                   data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost ]);
          [ | solve [ subst loc; unfold app; entailer!; auto]
            | solve [auto 50 with closed]
            | ].
          { abbreviate_semax.
            (*TODO: lots of repetition in here*)
            forward_loop (EX (ctr : Z),
              PROP (0 <= ctr <= xh)
              (LOCALx ((temp _i (Vint (Int.repr ctr))) :: loc)
              (SEP (data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx)(gv _fec_weights);
                    data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost;
                    data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h))
                      (pop_find_inv xh (map_2d_rev id weight_mx) 
                          (find_parity_rows parities i) (find_lost stats k) j ctr) v_v))%assert5)).
            { subst loc; forward. Exists 0. entailer!. }
            { Intros i'. (*Need for both branches*)
              assert_PROP (force_val (sem_add_ptr_int tuchar Signed (force_val
                (sem_add_ptr_int tuchar Signed v_v (Vint
                (Int.mul (Int.mul (Int.repr j) (Int.repr (Byte.unsigned (Byte.repr xh)))) (Int.repr 2)))))
                (Vint (Int.repr i'))) = field_address (tarray tuchar (2 * fec_max_h * fec_max_h)) 
                (SUB (j * xh * 2 + i')) v_v) as Hri'. { 
                  subst loc; entailer!. solve_offset; rep_nia. }
              forward_if.
              { abbreviate_semax. rewrite Byte.unsigned_repr in H2 by rep_lia. 
                subst loc. (*TODO: a way without getting rid of loc - if I do this, forward_if doesn't work
                 maybe substitute in entailer!*)
                forward_if (PROP ()    
                  LOCAL (temp _i (Vint (Int.repr i'));
                     temp _r (force_val (sem_binary_operation' Oadd (tarray tuchar 256) tint v_v
                       (eval_binop Omul tint tint (eval_binop Omul tint tuchar (Vint (Int.repr j)) 
                       (Vubyte (Byte.repr xh))) (Vint (Int.repr 2)))));
                     temp _n (force_val (sem_binary_operation' Oadd (tarray (tarray tuchar 255) 128) tuchar 
                       (gv _fec_weights) (Vubyte (Znth j (find_parity_rows parities i)))));
                      temp _j (Vint (Int.repr j)); lvar _lost (tarray tuchar fec_max_h) v_lost;
                      temp _xh (Vubyte (Byte.repr xh)); gvars gv)
                  SEP (
                    data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights);
                    data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost;
                    data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h))
                      (upd_Znth (j * xh * 2 + i') (pop_find_inv xh (map_2d_rev id weight_mx) (find_parity_rows parities i) (find_lost stats k) j i')
                        (if (Z.eq_dec (i' + j + 1) xh) then Vubyte Byte.one else Vubyte Byte.zero)) v_v)).
                { (*simplify if condition*) 
                  unfold Int.add in H3. 
                  rewrite !Byte.unsigned_repr, (Int.unsigned_repr i'),(Int.unsigned_repr j),
                    !Int.unsigned_repr in H3 by rep_lia. 
                  apply (f_equal Int.unsigned) in H3. rewrite !Int.unsigned_repr in H3 by rep_lia. 
                  forward. entailer!.
                  rewrite left_sumbool_if by auto.
                  simpl_repr_byte. rewrite field_at_data_at_cancel'. entailer!.
                }
                { (*Other case*)
                  unfold Int.add in H3. 
                  rewrite !Byte.unsigned_repr, (Int.unsigned_repr i'), (Int.unsigned_repr j), 
                    !Int.unsigned_repr in H3 by rep_lia. 
                  assert (Hijxh: i' + j + 1 <> xh). intro C. rewrite C in H3. contradiction. clear H3.
                  forward. entailer!.
                  rewrite right_sumbool_if by auto.
                  simpl_repr_byte. rewrite field_at_data_at_cancel'. entailer!.
                }
                { (*After the if condition*) forward.
                  { entailer!. }
                  { rewrite pop_find_lost_Znth by rep_lia. entailer!. simpl_repr_byte. }
                  { rewrite pop_find_lost_Znth by rep_lia. 
                    assert_PROP (force_val (sem_add_ptr_int tuchar Signed (force_val
                      (sem_add_ptr_int (tarray tuchar 255) Signed (gv _fec_weights)
                      (Vubyte (Znth j (find_parity_rows parities i))))) (Vubyte (Znth i' (find_lost stats k)))) =
                    field_address (tarray (tarray tuchar (fec_n - 1)) fec_max_h) 
                      [ArraySubsc (Byte.unsigned (Znth i' (find_lost stats k)));
                       ArraySubsc (Byte.unsigned (Znth j (find_parity_rows parities i)))] (gv _fec_weights)). {
                    entailer!. rewrite <- (Byte.repr_unsigned (Znth j (find_parity_rows parities i))),
                      <- (Byte.repr_unsigned (Znth i' (find_lost stats k))). 
                    assert (Byte.unsigned (Znth i' (find_lost stats k)) < 255). {
                      assert (Hlostbound: Forall (fun x => 0 <= Byte.unsigned x < k) (find_lost stats k)). {
                        apply find_lost_bound; rep_lia. }
                      rewrite Forall_Znth in Hlostbound. specialize (Hlostbound i'). rep_lia. } solve_offset. }
                    forward.
                    { entailer!. assert (0 <= Byte.unsigned (Znth j (find_parity_rows parities i)) < fec_max_h) by rep_lia.
                      pose proof (weight_mx_wf) as [Hwh [_ Hwn]].
                      rewrite !(@Znth_default _  Inhabitant_list). 2: { rewrite rev_mx_val_length1; rep_lia. }
                      rewrite rev_mx_val_Znth; try rep_lia. 2: { inner_length.
                        assert (Hlostbound: Forall (fun x => 0 <= Byte.unsigned x < k) (find_lost stats k)). {
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
                      (SUB (j * xh * 2 + i' + xh)) v_v) as Hrixh. { entailer!. solve_offset; rep_nia. }
                      forward. forward. Exists (i' + 1). entailer!.
                      { simpl_repr_byte. }
                      { rewrite pop_find_inv_set by rep_lia. rewrite field_at_data_at_cancel'.
                        apply derives_refl'. repeat f_equal.
                        - destruct (Z.eq_dec (j + i' + 1) (Zlength (find_lost stats k))); simpl;
                          destruct (Z.eq_dec (i' + j + 1) (Zlength (find_lost stats k))); try reflexivity;
                          try lia.
                        - unfold get. assert (0 <= Byte.unsigned (Znth j (find_parity_rows parities i)) < fec_max_h) by rep_lia.
                          pose proof (weight_mx_wf) as [Hwh [_ Hwn]].
                          assert (0 <= Byte.unsigned (Znth i' (find_lost stats k)) <
                            Zlength (Znth (Byte.unsigned (Znth j (find_parity_rows parities i))) weight_mx)). {
                            inner_length. assert (Hlostbound: Forall (fun x => 0 <= Byte.unsigned x < k) (find_lost stats k)). {
                              apply find_lost_bound; rep_lia. }
                            rewrite Forall_Znth in Hlostbound. specialize (Hlostbound i'). rep_lia. }
                          rewrite !(@Znth_default _  Inhabitant_list). 2: { rewrite rev_mx_val_length1; rep_lia. }
                          rewrite rev_mx_val_Znth, map_2d_rev_Znth by rep_lia. reflexivity.
                      }
                    }
                  }
                }
              }
              { (*end of inner loop*) forward. subst loc; entailer!. 
                rewrite Byte.unsigned_repr in H2 by rep_lia.
                replace i' with (Zlength (find_lost stats k)) by rep_lia.
                rewrite pop_find_inv_finish by rep_lia. cancel.
              }
            }
          }
          { (*After the frame*)
            subst loc; unfold app; abbreviate_semax. forward.
            (*inv preservation outer loop*) Exists (j+1). entailer!.
            rewrite pop_find_inv_finish by rep_lia. cancel.
          }
        }
      }
    }
    { (*end of outer loop*) forward. rewrite Byte.unsigned_repr in H0 by rep_lia. entailer!.
      replace j with (Zlength (find_lost stats k)) by lia.
      cancel.
    }
  }
Qed.

(*4th loop: matrix multiplication*)
Definition fec_blk_decode_loop4 :=
(Sfor (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tuchar))
     (Ebinop Olt (Etempvar _i tuchar) (Etempvar _xh tuchar) tint)
     (Ssequence
        (Ssequence
           (Sset _t'24
              (Ederef (Ebinop Oadd (Evar _row (tarray tuchar 128)) (Etempvar _i tuchar) (tptr tuchar))
                 tuchar))
           (Sset _p
              (Ederef
                 (Ebinop Oadd (Evar _fec_weights (tarray (tarray tuchar 255) 128))
                    (Etempvar _t'24 tuchar) (tptr (tarray tuchar 255))) (tarray tuchar 255))))
        (Ssequence
           (Sset _t
              (Ederef
                 (Ebinop Oadd (Evar _s (tarray (tarray tuchar 16000) 128)) (Etempvar _i tuchar)
                    (tptr (tarray tuchar 16000))) (tarray tuchar 16000)))
           (Sfor (Sset _j (Econst_int (Int.repr 0) tint))
              (Ebinop Olt (Etempvar _j tint) (Etempvar _c tint) tint)
              (Ssequence (Sset _y (Ecast (Econst_int (Int.repr 0) tint) tuchar))
                 (Ssequence
                    (Sfor (Sset _q (Ecast (Econst_int (Int.repr 0) tint) tuchar))
                       (Ebinop Olt (Etempvar _q tuchar) (Etempvar _k tint) tint)
                       (Ssequence
                          (Ssequence
                             (Sset _t'23
                                (Ederef
                                   (Ebinop Oadd (Evar _found (tarray tuchar 128)) 
                                      (Etempvar _q tuchar) (tptr tuchar)) tuchar))
                             (Sset _z (Ecast (Etempvar _t'23 tuchar) tuchar)))
                          (Ssequence
                             (Ssequence
                                (Sset _t'22
                                   (Ederef
                                      (Ebinop Oadd (Etempvar _p (tptr tuchar)) 
                                         (Etempvar _z tuchar) (tptr tuchar)) tuchar))
                                (Sset _weight (Ecast (Etempvar _t'22 tuchar) tuchar)))
                             (Sifthenelse (Ebinop Olt (Etempvar _z tuchar) (Etempvar _k tint) tint)
                                (Ssequence
                                   (Sset _t'19
                                      (Ederef
                                         (Ebinop Oadd (Etempvar _plen (tptr tint)) 
                                            (Etempvar _z tuchar) (tptr tint)) tint))
                                   (Sifthenelse
                                      (Ebinop Ogt (Etempvar _t'19 tint) (Etempvar _j tint) tint)
                                      (Ssequence
                                         (Ssequence
                                            (Sset _t'20
                                               (Ederef
                                                  (Ebinop Oadd (Etempvar _pdata (tptr (tptr tuchar)))
                                                     (Etempvar _z tuchar) (tptr (tptr tuchar)))
                                                  (tptr tuchar)))
                                            (Ssequence
                                               (Sset _t'21
                                                  (Ederef
                                                     (Ebinop Oadd (Etempvar _t'20 (tptr tuchar))
                                                        (Etempvar _j tint) (tptr tuchar)) tuchar))
                                               (Sset _data (Ecast (Etempvar _t'21 tuchar) tuchar))))
                                         (Ssequence
                                            (Scall (Some _t'7)
                                               (Evar _fec_gf_mult
                                                  (Tfunction (Tcons tuchar (Tcons tuchar Tnil)) tuchar
                                                     cc_default))
                                               (cons (Etempvar _weight tuchar)
                                                  (cons (Etempvar _data tuchar) nil)))
                                            (Sset _y
                                               (Ecast
                                                  (Ebinop Oxor (Etempvar _y tuchar)
                                                     (Etempvar _t'7 tuchar) tint) tuchar)))) Sskip))
                                (Ssequence
                                   (Ssequence
                                      (Sset _t'17
                                         (Ederef
                                            (Ebinop Oadd (Etempvar _pparity (tptr (tptr tuchar)))
                                               (Ebinop Osub
                                                  (Ebinop Osub (Econst_int (Int.repr 256) tint)
                                                     (Econst_int (Int.repr 2) tint) tint)
                                                  (Etempvar _z tuchar) tint) 
                                               (tptr (tptr tuchar))) (tptr tuchar)))
                                      (Ssequence
                                         (Sset _t'18
                                            (Ederef
                                               (Ebinop Oadd (Etempvar _t'17 (tptr tuchar))
                                                  (Etempvar _j tint) (tptr tuchar)) tuchar))
                                         (Sset _data (Ecast (Etempvar _t'18 tuchar) tuchar))))
                                   (Ssequence
                                      (Scall (Some _t'8)
                                         (Evar _fec_gf_mult
                                            (Tfunction (Tcons tuchar (Tcons tuchar Tnil)) tuchar
                                               cc_default))
                                         (cons (Etempvar _weight tuchar)
                                            (cons (Etempvar _data tuchar) nil)))
                                      (Sset _y
                                         (Ecast
                                            (Ebinop Oxor (Etempvar _y tuchar) 
                                               (Etempvar _t'8 tuchar) tint) tuchar)))))))
                       (Sset _q
                          (Ecast (Ebinop Oadd (Etempvar _q tuchar) (Econst_int (Int.repr 1) tint) tint)
                             tuchar)))
                    (Sassign
                       (Ederef
                          (Ebinop Oadd (Etempvar _t (tptr tuchar)) (Etempvar _j tint) (tptr tuchar))
                          tuchar) (Etempvar _y tuchar))))
              (Sset _j (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint) tint)))))
     (Sset _i (Ecast (Ebinop Oadd (Etempvar _i tuchar) (Econst_int (Int.repr 1) tint) tint) tuchar))).

(*TODO: move*)
From HB Require structures.
From mathcomp Require ssralg.
Section RowsCols.

Import structures ssralg ByteField.

Definition bsubmx_rows_cols_list : list (list byte) -> Z -> Z ->
  list Z -> list Z -> lmatrix byte := 
  fun m z1 z2 l1 l2 => submx_rows_cols_list m z1 z2 l1 l2.

End RowsCols.
(*TODO: from Verif_field*)
From mathcomp Require all_ssreflect ssralg.
Section ByteZero.

Import structures.
Import all_ssreflect ssralg ByteField.

Lemma byte_mul_0_b: forall b, 
  byte_mul 0%R b = 0%R.
Proof.
  move=> b. apply (@GRing.mul0r byte).
Qed. 

Lemma byte_mul_b_0: forall b,
  byte_mul b 0%R = 0%R.
Proof.
  apply (@GRing.mulr0 byte).
Qed.

Lemma byte_add_b_0: forall b,
  Byte.xor b 0%R = b.
Proof.
  apply (@GRing.addr0 byte).
Qed.

End ByteZero.


(*TODO: this proof is long and tedious (some is unavoidable bc its a triply-nested loop with an if statement
  inside) - can it be automated more*)
Lemma body_fec_blk_decode_loop4: forall (Espec: OracleKind) (k c h xh i: Z) (v_row v_found v_s: val) 
  (gv: globals) (pl pd: val) (row found1 found2: list byte)
  (packets: list (list byte)) (parities: list (option (list byte))) (lengths: list Z) (stats: list byte)
  (packet_ptrs parity_ptrs : list val)
  (Hknh : 0 < k < fec_n - fec_max_h)
  (Hhh : 0 <= h <= fec_max_h)
  (Hccols : 0 < c <= fec_max_cols)
  (Hpackptrlen : Zlength packet_ptrs = k)
  (Hparlen : Zlength parities = h)
  (Hlenbound : Forall (fun x : list byte => Zlength x <= c) packets)
  (Heqxh : xh = Zlength (find_lost stats k))
  (Hparsomelen : forall (i : Z) (l : list byte), 0 <= i < h->Znth i parities = Some l->Zlength l = c)
  (Hpacklen : Zlength packets = k)
  (Hparptrlen : Zlength parity_ptrs = h)
  (Hstatlen : Zlength stats = k)
  (Hlenspec : forall i : Z, 0 <= i < k->Znth i lengths = Zlength (Znth i packets)) (*TODO: why do we have this and Hlenmap*)
  (Hlenslen : Zlength lengths = k)
  (Hxh : xh <= k) 
  (H0 : 0 <= i <= Zlength parities)
  (H1 : Zlength (find_parity_rows parities i)= xh)
  (Hrow: row = find_parity_rows parities i) 
  (Hfound1: found1 = find_found stats k) 
  (Hfound2: found2 = find_parity_found parities (fec_n - 1) i),
semax (func_tycontext f_fec_blk_decode Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _xh (Vubyte (Byte.repr xh)); lvar _row (tarray tuchar fec_max_h) v_row; 
   gvars gv; lvar _s (tarray (tarray tuchar 16000) 128) v_s; temp _c (Vint (Int.repr c));
   temp _k (Vint (Int.repr k)); lvar _found (tarray tuchar fec_max_h) v_found; 
   temp _plen pl; temp _pdata pd;
   temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd))
   SEP (data_at_ Tsh (tarray (tarray tuchar 16000) 128) v_s; FIELD_TABLES gv;
   iter_sepcon_arrays packet_ptrs packets;
   data_at Ews (tarray tint (Zlength packet_ptrs)) (map Vint (map Int.repr lengths)) pl;
   data_at Ews (tarray (tptr tuchar) (Zlength packet_ptrs + Zlength parities))
     (packet_ptrs ++ parity_ptrs) pd; iter_sepcon_options parity_ptrs parities;
   data_at Tsh (tarray tuchar fec_max_h)
     (pop_find_parity_found stats parities i fec_max_h (Zlength packet_ptrs) (fec_n - 1)) v_found;
   data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights);
   data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row))
  fec_blk_decode_loop4
  (normal_ret_assert
     (PROP ( )
      LOCAL (temp _xh (Vubyte (Byte.repr xh)); lvar _row (tarray tuchar fec_max_h) v_row; 
      gvars gv; lvar _s (tarray (tarray tuchar 16000) 128) v_s; temp _c (Vint (Int.repr c));
      temp _k (Vint (Int.repr k)); lvar _found (tarray tuchar fec_max_h) v_found; 
      temp _plen pl; temp _pdata pd;
      temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd))
      SEP (data_at Tsh (tarray (tarray tuchar 16000) 128)
             (pop_mx_mult_part xh c k fec_max_h fec_max_cols
                (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) 
                   (map Byte.unsigned row) (map Byte.unsigned (found1 ++ found2)))
                (col_mx_list
                   (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1)
                      (Ziota 0 c))
                   (submx_rows_cols_list (fill_missing c parities) xh c 
                      (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) xh 0) v_s; 
      FIELD_TABLES gv; iter_sepcon_arrays packet_ptrs packets;
      data_at Ews (tarray tint (Zlength packet_ptrs)) (map Vint (map Int.repr lengths)) pl;
      data_at Ews (tarray (tptr tuchar) (Zlength packet_ptrs + Zlength parities))
        (packet_ptrs ++ parity_ptrs) pd; iter_sepcon_options parity_ptrs parities;
      data_at Tsh (tarray tuchar fec_max_h)
        (pop_find_parity_found stats parities i fec_max_h (Zlength packet_ptrs) (fec_n - 1)) v_found;
      data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx)
        (gv _fec_weights);
      data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row))).
Proof.
  intros.
  unfold fec_blk_decode_loop4.
  abbreviate_semax.
  (*No locals change throughout the loop; only the first SEP clause changes*)
  match goal with
  | [ |- semax _ (PROPx _ (LOCALx ?l (SEPx (?h :: ?t)))) _ _ ] => set (locs := l); set (seps := t)
  end.
  forward_loop (EX (i' : Z),
    PROP (0 <= i' <= xh)
    (LOCALx ((temp _i (Vint (Int.repr i'))) :: locs)
    (SEPx (
      (*This matrix is quite complicated to describe, also opaque constants give dependent type issues when
            trying to rewrite*)
       (data_at Tsh (tarray (tarray tuchar 16000) 128) 
        (pop_mx_mult_part xh c k fec_max_h fec_max_cols 
          (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) (map Byte.unsigned row) 
              (map Byte.unsigned (found1 ++ found2)))
          (col_mx_list (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
              (submx_rows_cols_list (fill_missing  c parities) xh c (map Byte.unsigned row) (Ziota 0 c)) (k-xh) xh c)
          i' 0) v_s) :: seps)))); subst locs; subst seps.
  { forward. Exists 0. replace 16000 with fec_max_cols by rep_lia.
    replace 128 with fec_max_h by rep_lia. (*need to avoid stack overflow*)
    entailer!.
    rewrite pop_mx_mult_part_zero by rep_lia.
    rewrite data_at__tarray, zseq_Zrepeat, default_arr, fec_max_cols_eq, fec_max_h_eq by lia. cancel.
  }
  { Intros i'. forward_if.
    { (*outer loop body*) rewrite Byte.unsigned_repr in H2 by rep_lia.
      forward.
      { entailer!. }
      { rewrite pop_find_parity_rows_Znth by lia. entailer!. simpl_repr_byte. }
      { rewrite pop_find_parity_rows_Znth by lia. forward.
      (*NOTE: Again, get C-language expression error, can't directly work with arrays due to
          dependent type issues, not using opaque constants here*)
      forward. 
      (*let's use the frame rule again*)
      (*this time, I don't think that we need the row array (v_row) or its local var, but we need everything else*)
      (*TODO: make this better*)
      rewrite (grab_nth_LOCAL 5 (gvars gv)) by list_solve. simpl.
      rewrite (grab_nth_SEP 8), (grab_nth_SEP 1). simpl.
      match goal with
      | [ |- semax _ (PROPx _ (LOCALx (?l1 :: ?l2) (SEPx (?h1 :: ?h2 :: ?t)))) _ _ ] => 
        set (locs := l2); set (seps := t)
      end.
      (*frame rule might be overkill here - but with better automation, better*)
      apply (semax_frame_seq [lvar _row (tarray tuchar fec_max_h) v_row]
        [data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row])
      with (P1 := []) (P2 := [])
        (Q1 := locs) (Q2 := locs) 
        (R1 := data_at Tsh (tarray (tarray tuchar 16000) 128)
            (pop_mx_mult_part xh c k fec_max_h fec_max_cols
               (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) (map Byte.unsigned row)
                  (map Byte.unsigned (found1 ++ found2)))
               (col_mx_list
                  (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                  (submx_rows_cols_list (fill_missing c parities) xh c 
                     (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' 0) v_s :: seps)
        (R2 := (data_at Tsh (tarray (tarray tuchar 16000) 128)
             (pop_mx_mult_part xh c k fec_max_h fec_max_cols
                (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) (map Byte.unsigned row)
                   (map Byte.unsigned (found1 ++ found2)))
                (col_mx_list
                   (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                   (submx_rows_cols_list (fill_missing c parities) xh c 
                      (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' c) v_s) :: seps); 
      [ | solve[ subst locs; subst seps; simpl app; entailer! ] | solve [auto 50 with closed ] |]; abbreviate_semax.
      { forward_loop (EX (j: Z),
        PROP (0 <= j <= c)
        (LOCALx ((temp _j (Vint (Int.repr j))) :: locs)
        (SEPx (
           (data_at Tsh (tarray (tarray tuchar 16000) 128)
             (pop_mx_mult_part xh c k fec_max_h fec_max_cols
                (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) (map Byte.unsigned row)
                   (map Byte.unsigned (found1 ++ found2)))
                (col_mx_list 
                   (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                   (submx_rows_cols_list (fill_missing c parities) xh c 
                      (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' j) v_s) :: seps)))).
        { forward. Exists 0. subst locs seps; entailer!. }
        { Intros j. forward_if.  (*inner (j) loop body*)
          { forward. simpl_repr_byte.
            (*In this loop, we only change y, so the seps are constant*)
            match goal with
            | [ |- semax _ (PROPx _ (LOCALx _ (SEPx ?s))) _ _ ] => 
              set (seps1 := s)
            end.
            (*no point in frame rule because we need everything*)
            forward_loop (EX (q: Z),
              PROP (0 <= q <= k)
              (LOCALx (temp _y (Vubyte (dot_prod 
                (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) 
                    (map Byte.unsigned row) (map Byte.unsigned (found1 ++ found2)))
                (col_mx_list
                   (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                   (submx_rows_cols_list (fill_missing c parities) xh c
                      (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' j q)) 
                :: temp _q (Vint (Int.repr q)) :: temp _j (Vint (Int.repr j)) :: locs) (SEPx seps1)))
            break: (PROP () 
              (LOCALx (temp _y (Vubyte (dot_prod 
                (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) 
                    (map Byte.unsigned row) (map Byte.unsigned (found1 ++ found2)))
                (col_mx_list
                   (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                   (submx_rows_cols_list (fill_missing c parities) xh c
                      (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' j k)) 
                :: temp _j (Vint (Int.repr j)) :: locs) (SEPx seps1))).
            { forward. simpl_repr_byte. Exists 0.
              rewrite dot_prod_zero. subst seps seps1 locs; entailer!. }
            { Intros q. forward_if.
              { (*In innermost loop - dot prod*)
                subst seps seps1 locs.
                assert (Hfoundlen: Zlength found1 + Zlength found2 = k). { 
                  assert (Hkbyte: 0 <= k <= Byte.max_unsigned) by rep_lia.
                  pose proof (find_lost_found_Zlength stats Hkbyte) as Hlostfound.
                  subst; rewrite find_parity_rows_found_Zlength. rep_lia. }
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
                  remember (if proj_sumbool (range_le_lt_dec 0 q (Zlength (find_found stats (Zlength packet_ptrs))))
                    then Znth q (find_found stats (Zlength packet_ptrs))
                    else
                     Znth (q - Zlength (find_found stats (Zlength packet_ptrs)))
                       (find_parity_found parities (fec_n - 1) i)) as foundnth.
                  assert (Byte.unsigned foundnth < fec_n - 1). { subst.
                      destruct (range_le_lt_dec 0 q (Zlength (find_found stats (Zlength packet_ptrs)))); simpl.
                      - assert (Hkbyte: 0 <= Zlength packet_ptrs <= Byte.max_unsigned) by rep_lia.
                        pose proof (find_found_bound stats Hkbyte) as Hfoundbound.
                        assert (0 <= Byte.unsigned (Znth q (find_found stats (Zlength packet_ptrs))) < Zlength packet_ptrs) by
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
                      rewrite <- (Byte.repr_unsigned (Znth i' _)),  <- (Byte.repr_unsigned foundnth).  
                      entailer!. solve_offset. }
                  forward.
                  { entailer!. pose proof (weight_mx_wf) as [Hwh [_ Hwn]].
                    rewrite !(@Znth_default _  Inhabitant_list); [| solve [rewrite rev_mx_val_length1; rep_lia]].
                    rewrite rev_mx_val_Znth; [simpl_repr_byte|rep_lia|inner_length]. 
                  }
                  { forward. pose proof (weight_mx_wf) as [Hwh [_ Hwn]].
                    rewrite !(@Znth_default _  Inhabitant_list); [| solve[ rewrite rev_mx_val_length1; rep_lia]].
                    rewrite rev_mx_val_Znth; [|rep_lia|inner_length]. 
                    rewrite force_val_byte.
                    (*Now we are at if statement. Depends on if we are in packets part or parities part*)

                    (*let's use the frame rule again bc we have lots of extra garbage in the context*)
                    set (locs := [ temp _k (Vint (Int.repr k)); temp _plen pl; temp _j (Vint (Int.repr j));
                        temp _pdata pd; 
                        temp _weight(Vubyte(Znth
                          (Zlength (Znth (Byte.unsigned (Znth i' (find_parity_rows parities i))) weight_mx)
                             - Byte.unsigned foundnth
                             - 1) (Znth (Byte.unsigned (Znth i' (find_parity_rows parities i))) weight_mx)));
                        temp _z (Vubyte foundnth); gvars gv;
                        temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd);
                        temp _t'24 (Vubyte (Znth i' (find_parity_rows parities i)))]).
                    set (seps := [FIELD_TABLES gv; iter_sepcon_arrays packet_ptrs packets;
                     data_at Ews (tarray tint (Zlength packet_ptrs)) (map Vint (map Int.repr lengths)) pl;
                     data_at Ews (tarray (tptr tuchar) (Zlength packet_ptrs + Zlength parities))
                       (packet_ptrs ++ parity_ptrs) pd; iter_sepcon_options parity_ptrs parities]).
                    apply (semax_frame_seq
                       [ temp _t (force_val (sem_add_ptr_int (tarray tuchar 16000) Signed v_s (Vint (Int.repr i'))));
                         temp _i (Vint (Int.repr i')); temp _c (Vint (Int.repr c));
                         lvar _found (tarray tuchar fec_max_h) v_found;
                         temp _p (force_val (sem_add_ptr_int (tarray tuchar 255) Signed (gv _fec_weights)
                            (Vubyte (Znth i' (find_parity_rows parities i)))));
                         temp _xh (Vubyte (Byte.repr xh)); lvar _s (tarray (tarray tuchar 16000) 128) v_s;
                         temp _q (Vint (Int.repr q))]
                      [ data_at Tsh (tarray (tarray tuchar 16000) 128)
                        (pop_mx_mult_part xh c k fec_max_h fec_max_cols
                         (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) (map Byte.unsigned row)
                            (map Byte.unsigned (found1 ++ found2)))
                         (col_mx_list
                            (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                            (submx_rows_cols_list (fill_missing c parities) xh c 
                               (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' j) v_s;
                        data_at Tsh (tarray tuchar fec_max_h)
                          (pop_find_parity_found stats parities i fec_max_h (Zlength packet_ptrs) (fec_n - 1)) v_found;
                        data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) 
                          (rev_mx_val weight_mx) (gv _fec_weights)])
                      with (P1 := []) (P2 := [])
                      (Q1 := temp _y (Vubyte (dot_prod
                           (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) (map Byte.unsigned row)
                              (map Byte.unsigned (found1 ++ found2)))
                           (col_mx_list
                              (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                              (submx_rows_cols_list (fill_missing c parities) xh c (map Byte.unsigned row)
                                 (Ziota 0 c)) (k - xh) xh c) i' j q)) :: locs) 
                      (Q2 := temp _y (Vubyte (dot_prod 
                        (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) 
                            (map Byte.unsigned row) (map Byte.unsigned (found1 ++ found2)))
                        (col_mx_list
                           (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                           (submx_rows_cols_list (fill_missing c parities) xh c
                              (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) i' j (q + 1))) :: locs)
                      (R1 := seps) (R2 := seps);
                      [ | solve [ subst locs seps; simpl app; entailer!] | solve [auto 50 with closed ] |].
                    { abbreviate_semax. subst locs seps. forward_if. (*because we used the frame rule, we don't need a postcondtion anymore*)
                      { (*In this case, we know we are in the packets part and that q is small*)
                        destruct (range_le_lt_dec 0 q (Zlength (find_found stats (Zlength packet_ptrs)))); simpl in Heqfoundnth.
                        2 : { rewrite Heqfoundnth in H10.
                          assert (Hin: 0 <= i < fec_n - 1) by rep_lia.
                          assert (Hnbyte: fec_n - 1 <= Byte.max_unsigned) by rep_lia.
                          pose proof (find_parity_found_bound' parities Hin Hnbyte) as Hfoundb.
                          rewrite Forall_Znth in Hfoundb.
                          assert (fec_n - 1 - i <= Byte.unsigned 
                            (Znth (q - Zlength (find_found stats (Zlength packet_ptrs))) (find_parity_found parities 
                            (fec_n - 1) i)) < fec_n - 1). { apply Hfoundb; subst; rep_lia. } rep_lia. }
                        rewrite Heqfoundnth. 
                        (*need for forward*)
                        assert (Hqlen: 0 <= Byte.unsigned (Znth q (find_found stats (Zlength packet_ptrs))) < Zlength (map Int.repr lengths)). {
                          rewrite Zlength_map. replace (Zlength lengths) with (Zlength packet_ptrs) by lia.
                          assert (Hkbyte: 0 <= Zlength packet_ptrs <= Byte.max_unsigned) by rep_lia.
                          pose proof (find_found_bound stats Hkbyte) as Hfoundb. rewrite Forall_Znth in Hfoundb.
                          apply Hfoundb. lia. } rewrite Zlength_map in Hqlen.
                        forward. forward_if.
                        { assert (Hjlen: j < Zlength (Znth (Byte.unsigned (Znth q (find_found stats (Zlength packet_ptrs)))) packets)). {
                            rewrite Hlenspec in H11; try rep_lia. rewrite Int.signed_repr in H11; try lia.
                            inner_length. } clear H11.
                          (*We are going to be accessing pdata, so we need to unfold the iter_sepcon*)
                          assert (Hlens: Zlength packet_ptrs = Zlength packets) by lia. 
                          assert (Hpackbound: 0 <= Byte.unsigned (Znth q (find_found stats (Zlength packet_ptrs))) < Zlength packets) by lia.
                          rewrite (iter_sepcon_arrays_remove_one _  _ _ Hlens Hpackbound). Intros.
                          forward; rewrite Znth_app1 by lia.
                          { entailer!. }
                          { forward.
                            { entailer!. simpl_repr_byte. }
                            { rewrite Znth_map by lia. forward. simpl_repr_byte.
                              rewrite <- byte_int_repr,Byte.repr_unsigned by rep_lia.
                              unfold FIELD_TABLES. Intros. 
                              forward_call(gv, (Znth (fec_n - 1 - Byte.unsigned (Znth q (find_found stats (Zlength packet_ptrs))) - 1)
                                (Znth (Byte.unsigned (Znth i' (find_parity_rows parities i))) weight_mx)),
                                (Znth j (Znth (Byte.unsigned (Znth q (find_found stats (Zlength packet_ptrs)))) packets))).
                              { entailer!. (*TODO:why didn't we need this before?*)
                                replace (Zlength (Znth (Byte.unsigned (Znth i' (find_parity_rows parities i))) weight_mx))
                                  with (fec_n -1). simpl. simpl_repr_byte.
                                rewrite Forall_Znth in Hwn. symmetry. apply Hwn. rep_lia. }
                              { forward. unfold FIELD_TABLES; entailer!.
                                { unfold Int.xor. rewrite !Int.unsigned_repr, ByteFacts.byte_xor_fold by simpl_repr_byte.
                                  simpl_repr_byte. unfold Vubyte. f_equal. f_equal. f_equal.
                                  rewrite dot_prod_plus_1 by lia.
                                  unfold ssralg.GRing.add. simpl.
                                  f_equal.
                                  unfold ssralg.GRing.mul; simpl.
                                  f_equal.
                                  - unfold submx_rows_cols_rev_list, submx_rows_cols_list.
                                    (*TODO: bad*)
                                    rewrite (@mk_lmatrix_get ByteField.Byte_int__canonical__GRing_Field) by lia.
                                    unfold get. rewrite !Znth_map by list_solve.
                                    rewrite Znth_app1 by lia. reflexivity.
                                  - unfold col_mx_list. 
                                    rewrite (@mk_lmatrix_get ByteField.Byte_int__canonical__GRing_Field) by lia.
                                    destruct (Z_lt_ge_dec q (Zlength packet_ptrs - Zlength (find_lost stats (Zlength packet_ptrs)))); simpl.
                                    + (*real case*)
                                      unfold bsubmx_rows_cols_list.
                                      unfold submx_rows_cols_list.
                                      rewrite (@mk_lmatrix_get ByteField.Byte_int__canonical__GRing_Field),
                                      Znth_Ziota by lia.
                                      unfold get. rewrite Znth_map by list_solve. reflexivity.
                                    + (*contradiction case*)
                                      assert (Hkbyte: 0 <= (Zlength packet_ptrs) <= Byte.max_unsigned) by rep_lia.
                                      pose proof (find_lost_found_Zlength stats Hkbyte). rep_lia.
                                }
                                { rewrite (iter_sepcon_arrays_remove_one _  _ _ Hlens Hpackbound).
                                  cancel.
                                }
                              }
                            }
                          }
                        }
                        { (*if we are outside the range of the original bound - really count as a zero*)
                          assert (Hjlen: j >= Zlength (Znth (Byte.unsigned (Znth q (find_found stats (Zlength packet_ptrs)))) packets)). {
                            rewrite Hlenspec,Int.signed_repr in H11; try rep_lia. inner_length. } clear H11.
                          forward. entailer!. f_equal. rewrite dot_prod_plus_1 by lia. simpl.
                          unfold col_mx_list at 2. (*assert (Hget: forall l i j,
                            @get byte (inhabitant_F B) l i j = @get (ssralg.GRing.Field.sort B) (inhabitant_F B) l i j). {
                            reflexivity. }*) 
                          rewrite (@mk_lmatrix_get ByteField.Byte_int__canonical__GRing_Field) by rep_lia.
                          destruct (Z_lt_ge_dec q (Zlength packet_ptrs - Zlength (find_lost stats (Zlength packet_ptrs)))); simpl.
                          2 : { assert (Hkbyte: 0 <= (Zlength packet_ptrs) <= Byte.max_unsigned) by rep_lia.
                                pose proof (find_lost_found_Zlength stats Hkbyte). rep_lia. }
                          assert (Hzero: get (bsubmx_rows_cols_list packets
                           (Zlength packet_ptrs - Zlength (find_lost stats (Zlength packet_ptrs))) c
                           (map Byte.unsigned (find_found stats (Zlength packet_ptrs))) (Ziota 0 c)) q j = Byte.zero). {
                            unfold bsubmx_rows_cols_list, submx_rows_cols_list. 
                            rewrite mk_lmatrix_get, Znth_Ziota by lia.
                            unfold get. rewrite Znth_overflow by list_solve. reflexivity. }
                          match goal with
                          | |- context [get (bsubmx_rows_cols_list ?packets ?a ?b ?c ?d) ?i ?j] =>
                            replace (get (bsubmx_rows_cols_list packets a b c d) i j) with Byte.zero
                            by apply Hzero
                          end.
                          rewrite byte_mul_b_0, byte_add_b_0. reflexivity.
                        }
                      }
                      { (*Other case - we are in parities*)
                        destruct (range_le_lt_dec 0 q (Zlength (find_found stats (Zlength packet_ptrs)))); simpl in Heqfoundnth.
                        { (*contradiction case*) rewrite Heqfoundnth in H10.
                          assert (Hkbyte: 0 <= Zlength packet_ptrs <= Byte.max_unsigned) by rep_lia.
                          pose proof (find_found_bound stats Hkbyte) as Hfoundb. rewrite Forall_Znth in Hfoundb.
                          assert (0 <= Byte.unsigned (Znth q (find_found stats (Zlength packet_ptrs))) < Zlength packet_ptrs) by 
                            (apply Hfoundb; lia). rep_lia. 
                        }
                        { (*accessing parity - need to split [iter_sepcon_option]*)
                          assert (Hkbyte: 0 <= (Zlength packet_ptrs) <= Byte.max_unsigned) by rep_lia.
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
                            specialize (Hparb (q - Zlength (find_found stats (Zlength packet_ptrs)))); rep_lia. }
                          assert (Hparlenseq: Zlength parity_ptrs = Zlength parities) by lia.
                          rewrite (iter_sepcon_options_remove_one _ _ _ _ Hparlenseq Hqlen Hsome). Intros.
                          assert (Hlenl: Zlength l = c). { apply (Hparsomelen (fec_n - 2 - Byte.unsigned foundnth)); auto. lia. }
                          rewrite Hlenl.
                          replace (Zlength l) with c by (rewrite Hparsomelen; auto). 
                          (*Now we can express the field_address*)
                          assert_PROP (force_val
                           (sem_add_ptr_int (tptr tuchar) Signed (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd)
                              (Vint (Int.sub (Int.sub (Int.repr 256) (Int.repr 2)) (Int.repr (Byte.unsigned foundnth))))) =
                            field_address (tarray (tptr tuchar) (Zlength packet_ptrs + Zlength parities)) (SUB (k + (fec_n - 2 - Byte.unsigned foundnth))) pd). {
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
                            { forward. rewrite Znth_map,force_val_byte by lia. 
                              (*at multiplication*) unfold FIELD_TABLES; Intros.
                              forward_call (gv, (Znth (fec_n - 1 - Byte.unsigned
                                  (Znth (q - Zlength (find_found stats (Zlength packet_ptrs)))
                                  (find_parity_found parities (fec_n - 1) i)) - 1)
                                  (Znth (Byte.unsigned (Znth i' (find_parity_rows parities i))) weight_mx)), 
                                (Znth j l)).
                              { (*TODO: again: why did we get this goal?*)
                                rewrite Forall_Znth in Hwn. rewrite Hwn by rep_lia. entailer!. simpl. simpl_repr_byte. }
                              { forward. unfold FIELD_TABLES; entailer!.
                                { unfold Int.xor. rewrite !Int.unsigned_repr, ByteFacts.byte_xor_fold; simpl_repr_byte.
                                  unfold Vubyte. do 3 f_equal.
                                  rewrite dot_prod_plus_1 by lia.
                                  unfold ssralg.GRing.add; simpl.
                                  f_equal.
                                  unfold ssralg.GRing.mul; simpl.
                                  f_equal.
                                  - unfold submx_rows_cols_rev_list, submx_rows_cols_list.
                                    rewrite (@mk_lmatrix_get ByteField.Byte_int__canonical__GRing_Field) by lia.
                                    unfold get. rewrite !Znth_map by list_solve.
                                    rewrite Znth_app2 by lia. reflexivity.
                                  - unfold col_mx_list. rewrite (@mk_lmatrix_get ByteField.Byte_int__canonical__GRing_Field) by lia.
                                    destruct (Z_lt_ge_dec q (Zlength packet_ptrs - Zlength (find_lost stats (Zlength packet_ptrs)))); simpl.
                                    + (*contradiction case*) rep_lia.
                                    + (*real case*)
                                      unfold submx_rows_cols_list.
                                      rewrite (@mk_lmatrix_get ByteField.Byte_int__canonical__GRing_Field), Znth_Ziota by lia.
                                      apply fill_missing_mx_some; try lia; auto. 
                                      rewrite <- Hsome. f_equal. rewrite Znth_map, find_parity_rows_found_Znth by rep_lia.
                                      pose proof find_lost_found_Zlength stats Hkbyte.
                                      replace (Zlength packet_ptrs - Zlength (find_lost stats (Zlength packet_ptrs))) with
                                         (Zlength (find_found stats (Zlength packet_ptrs))) by lia. lia. 
                                      rewrite Znth_map by lia. 
                                      assert (Hibyte: 0 <= i <= Byte.max_unsigned) by rep_lia.
                                      pose proof (find_parity_rows_bound parities Hibyte) as Hrowb.
                                      rewrite Forall_Znth in Hrowb. 
                                      specialize (Hrowb (q - (Zlength packet_ptrs - Zlength (find_lost stats (Zlength packet_ptrs))))). rep_lia.
                                }
                                { rewrite (iter_sepcon_options_remove_one _ _ _ _ Hparlenseq Hqlen Hsome). cancel.
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                    { (*invariant pres for dot prod loop*) subst locs seps. simpl app; abbreviate_semax. forward.
                      Exists (q+1). entailer!. simpl_repr_byte. 
                    }
                  }
                }
              }
              { (*end of dot prod loop*) forward. subst seps seps1 locs; entailer!.
                replace q with (Zlength packet_ptrs) by lia. reflexivity.
              }
            }
            { (*put the value in the matrix*) subst seps seps1 locs.
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
              forward.
              simpl_repr_byte. forward. Exists (j+1). entailer!.
              rewrite <- fec_max_cols_eq,<- fec_max_h_eq, field_at_data_at_cancel'.
              apply derives_refl'. f_equal. rewrite <- pop_mx_mult_part_set by rep_lia.
              unfold set. f_equal. f_equal. apply Znth_default.
              rewrite pop_mx_mult_part_Zlength; rep_lia.
            }
          }
          { (*end of j loop*) replace j with c by lia. forward. subst locs seps; entailer!. }
        }
      }
      { (*preservation of outer loop invar*) subst locs seps; simpl app. forward. Exists (i'+1). 
        unfold Int.add. simpl_repr_byte.
        rewrite <- fec_max_cols_eq, <- fec_max_h_eq.
        replace 255 with (fec_n - 1) by rep_lia.
         entailer!.
        rewrite <- pop_mx_mult_part_row_finish by lia. cancel.
      }
    }
  }
  { (*end of outer loop*) rewrite Byte.unsigned_repr in H2 by rep_lia. replace i' with xh by lia.
    forward. entailer!.
  }
}
Qed.

Definition fec_blk_decode_loop5 :=
  (Sfor (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tuchar))
     (Ebinop Olt (Etempvar _i tuchar) (Etempvar _xh tuchar) tint)
     (Ssequence
        (Sset _p
           (Ebinop Oadd (Ederef (Evar _v (tarray (tarray tuchar 256) 128)) (tarray tuchar 256))
              (Ebinop Omul (Ebinop Omul (Etempvar _i tuchar) (Etempvar _xh tuchar) tint)
                 (Econst_int (Int.repr 2) tint) tint) (tptr tuchar)))
        (Ssequence
           (Sset _m (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _xh tuchar) (tptr tuchar)))
           (Ssequence
              (Ssequence
                 (Sset _t'16
                    (Ederef
                       (Ebinop Oadd (Evar _lost (tarray tuchar 128))
                          (Ebinop Osub (Etempvar _x tuchar) (Etempvar _i tuchar) tint) 
                          (tptr tuchar)) tuchar))
                 (Sassign
                    (Ederef
                       (Ebinop Oadd (Etempvar _pstat (tptr tschar)) (Etempvar _t'16 tuchar) (tptr tschar))
                       tschar) (Econst_int (Int.repr 0) tint)))
              (Sfor (Sset _j (Econst_int (Int.repr 0) tint))
                 (Ebinop Olt (Etempvar _j tint) (Etempvar _c tint) tint)
                 (Ssequence (Sset _y (Ecast (Econst_int (Int.repr 0) tint) tuchar))
                    (Ssequence
                       (Sset _r
                          (Ebinop Oadd (Etempvar _u (tptr tuchar)) (Etempvar _j tint) (tptr tuchar)))
                       (Ssequence
                          (Sfor (Sset _n (Etempvar _p (tptr tuchar)))
                             (Ebinop Olt (Etempvar _n (tptr tuchar)) (Etempvar _m (tptr tuchar)) tint)
                             (Ssequence
                                (Ssequence
                                   (Ssequence (Sset _t'14 (Ederef (Etempvar _n (tptr tuchar)) tuchar))
                                      (Ssequence (Sset _t'15 (Ederef (Etempvar _r (tptr tuchar)) tuchar))
                                         (Scall (Some _t'9)
                                            (Evar _fec_gf_mult
                                               (Tfunction (Tcons tuchar (Tcons tuchar Tnil)) tuchar
                                                  cc_default))
                                            (cons (Etempvar _t'14 tuchar)
                                               (cons (Etempvar _t'15 tuchar) nil)))))
                                   (Sset _y
                                      (Ecast
                                         (Ebinop Oxor (Etempvar _y tuchar) (Etempvar _t'9 tuchar) tint)
                                         tuchar)))
                                (Sset _r
                                   (Ebinop Osub (Etempvar _r (tptr tuchar))
                                      (Econst_int (Int.repr 16000) tint) (tptr tuchar))))
                             (Sset _n
                                (Ebinop Oadd (Etempvar _n (tptr tuchar)) (Econst_int (Int.repr 1) tint)
                                   (tptr tuchar))))
                          (Ssequence
                             (Sset _data_lost_row
                                (Ederef
                                   (Ebinop Oadd (Evar _lost (tarray tuchar 128))
                                      (Ebinop Osub
                                         (Ebinop Osub (Etempvar _xh tuchar) (Etempvar _i tuchar) tint)
                                         (Econst_int (Int.repr 1) tint) tint) 
                                      (tptr tuchar)) tuchar))
                             (Ssequence
                                (Sset _t'12
                                   (Ederef
                                      (Ebinop Oadd (Etempvar _plen (tptr tint))
                                         (Etempvar _data_lost_row tint) (tptr tint)) tint))
                                (Sifthenelse (Ebinop Ogt (Etempvar _t'12 tint) (Etempvar _j tint) tint)
                                   (Ssequence
                                      (Sset _t'13
                                         (Ederef
                                            (Ebinop Oadd (Etempvar _pdata (tptr (tptr tuchar)))
                                               (Etempvar _data_lost_row tint) 
                                               (tptr (tptr tuchar))) (tptr tuchar)))
                                      (Sassign
                                         (Ederef
                                            (Ebinop Oadd (Etempvar _t'13 (tptr tuchar))
                                               (Etempvar _j tint) (tptr tuchar)) tuchar)
                                         (Etempvar _y tuchar))) Sskip))))))
                 (Sset _j (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint) tint))))))
     (Sset _i (Ecast (Ebinop Oadd (Etempvar _i tuchar) (Econst_int (Int.repr 1) tint) tint) tuchar))).

Lemma body_fec_blk_decode_loop5: forall (Espec: OracleKind) (k (*h*) c xh i: Z) (v_s v_v v_lost: val) 
  (gv: globals) (pl pd ps: val) (packet_ptrs parity_ptrs: list val) (stats: list byte)
  (packets: list (list byte)) (parities: list (option (list byte))) (lengths: list Z)
  d' w' w'' (row found1 found2: list byte)

(*TODO: what do we need? Do we need h?*)
  (Hknh : 0 < k < fec_n - fec_max_h)
  (Hccols : 0 < c <= fec_max_cols)
  (Hpackptrlen : Zlength packet_ptrs = k)
  (Hlenbound : Forall (fun x : list byte => Zlength x <= c) packets)
  (Heqxh : xh = Zlength (find_lost stats k))
  (Hpacklen : Zlength packets = k)
  (Hstatlen : Zlength stats = k)
  (Hlenspec : forall i : Z, 0 <= i < k->Znth i lengths = Zlength (Znth i packets))
  (Hlenslen : Zlength lengths = k)
  (Hxh : xh <= k)
  (Hxh0 : 0 < xh)
  (Hrow: row = find_parity_rows parities i)
  (Hfound1: found1 = find_found stats k) 
  (Hfound2: found2 = find_parity_found parities (fec_n - 1) i)
  (Hw'': w'' = submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) (map Byte.unsigned row)
         (map Byte.unsigned (found1 ++ found2)))
  (Hd': d' = col_mx_list
        (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
        (submx_rows_cols_list (fill_missing c parities) xh c (map Byte.unsigned row) (Ziota 0 c))
        (k - xh) xh c)
  (Hw': w' = submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1) (seq.map Byte.unsigned row)
        (seq.map Byte.unsigned (seq.rev (find_lost stats k)))),
semax (func_tycontext f_fec_blk_decode Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _u
            (force_val
               (sem_binary_operation' Oadd (tarray (tarray tuchar 16000) 128) tuchar v_s
                  (Vint (Int.repr (xh - 1))))); temp _x (Vint (Int.repr (xh - 1)));
   temp _xh (Vubyte (Byte.repr xh)); temp _c (Vint (Int.repr c)); gvars gv; 
   temp _plen pl; temp _pdata pd;
   lvar _v (tarray (tarray tuchar 256) 128) v_v; lvar _lost (tarray tuchar fec_max_h) v_lost;
   temp _pstat ps)
   SEP (iter_sepcon_arrays packet_ptrs packets;
   data_at Ews (tarray tschar (Zlength packet_ptrs)) (map Vbyte stats) ps;
   data_at Tsh (tarray (tarray tuchar 16000) 128)
     (pop_mx_mult_part xh c k fec_max_h fec_max_cols w'' d' xh 0) v_s; FIELD_TABLES gv;
   data_at Ews (tarray tint (Zlength packet_ptrs)) (map Vint (map Int.repr lengths)) pl;
   data_at Ews (tarray (tptr tuchar) (Zlength packet_ptrs + Zlength parities))
     (packet_ptrs ++ parity_ptrs) pd;
   data_at Tsh (tarray tuchar (xh * (xh + xh)))
     (map Vubyte
        (flatten_mx
           (gauss_restrict_list xh (xh + xh)
              (concat_mx_id
                 (submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1)
                    (seq.map Byte.unsigned (find_parity_rows parities i))
                    (seq.map Byte.unsigned (seq.rev (find_lost stats k)))) xh)))) v_v;
   data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats (Zlength packet_ptrs) fec_max_h) v_lost))
   fec_blk_decode_loop5
  (normal_ret_assert
     (PROP ( )
      LOCAL (temp _u
               (force_val
                  (sem_binary_operation' Oadd (tarray (tarray tuchar 16000) 128) tuchar v_s
                     (Vint (Int.repr (xh - 1))))); temp _x (Vint (Int.repr (xh - 1)));
      temp _xh (Vubyte (Byte.repr xh)); temp _c (Vint (Int.repr c)); gvars gv; 
      temp _plen pl; temp _pdata pd;
      lvar _v (tarray (tarray tuchar 256) 128) v_v; lvar _lost (tarray tuchar fec_max_h) v_lost;
      temp _pstat ps)
      SEP (iter_sepcon_arrays packet_ptrs
             (pop_fill_rows_list packets
                (lmatrix_multiply xh xh c (find_invmx_list w' xh)
                   (lmatrix_multiply xh k c w'' d')) (map Byte.unsigned (rev (find_lost stats k)))
                xh 0);
      data_at Ews (tarray tschar (Zlength packet_ptrs))
        (map Vbyte (pop_stats stats (map Byte.unsigned (rev (find_lost stats k))) xh)) ps;
      data_at Tsh (tarray (tarray tuchar 16000) 128)
        (pop_mx_mult_part xh c k fec_max_h fec_max_cols w'' d' xh 0) v_s; FIELD_TABLES gv;
      data_at Ews (tarray tint (Zlength packet_ptrs)) (map Vint (map Int.repr lengths)) pl;
      data_at Ews (tarray (tptr tuchar) (Zlength packet_ptrs + Zlength parities))
        (packet_ptrs ++ parity_ptrs) pd;
      data_at Tsh (tarray tuchar (xh * (xh + xh)))
        (map Vubyte
           (flatten_mx
              (gauss_restrict_list xh (xh + xh)
                 (concat_mx_id
                    (submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1)
                       (seq.map Byte.unsigned (find_parity_rows parities i))
                       (seq.map Byte.unsigned (seq.rev (find_lost stats k)))) xh)))) v_v;
      data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats (Zlength packet_ptrs) fec_max_h) v_lost))).
Proof.
intros.
unfold fec_blk_decode_loop5.
abbreviate_semax.
(*no locals change in loop, only 1st 2 sep clauses do*)
match goal with
| [ |- semax _ (PROPx _ (LOCALx ?l (SEPx (?h :: ?h1 :: ?t)))) _ _ ] => set (locs := l); set (seps := t)
end.

forward_loop (EX (i: Z),
  PROP (0 <= i <= xh)
  (LOCALx ((temp _i (Vint (Int.repr i))) :: locs)
  (SEPx (iter_sepcon_arrays packet_ptrs 
    (pop_fill_rows_list packets (lmatrix_multiply xh xh c (find_invmx_list w' xh)
        (lmatrix_multiply xh k c w'' d')) (map Byte.unsigned (rev (find_lost stats k))) i 0) ::
    data_at Ews (tarray tschar (Zlength packet_ptrs)) 
      (map Vbyte (pop_stats stats (map Byte.unsigned (rev (find_lost stats k))) i)) ps :: seps)))).
{ forward. Exists 0. subst locs seps; entailer!. rewrite pop_fill_rows_list_0, pop_stats_0. cancel. }
{ Intros i'. subst locs seps; forward_if.
  { (*need in multiple places*) rewrite Byte.unsigned_repr in H0 by rep_lia.
    assert (Hixh2: Int.min_signed <= i' * Zlength (find_lost stats (Zlength packet_ptrs)) * 2 <= Int.max_signed) by (subst; rep_nia). 
    forward.
    { entailer!. rewrite !Byte.unsigned_repr, !Int.signed_repr; rep_lia. }
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
      { entailer!. assert (Hkbyte: 0 <= Zlength packet_ptrs <= Byte.max_unsigned) by rep_lia.
        apply (find_lost_bound stats) in Hkbyte. rewrite Forall_Znth in Hkbyte. apply Hkbyte; rep_lia.
      }
      { (*might as well do the stats postcondition here*)
        replace (upd_Znth (Byte.unsigned (Znth (xh - 1 - i') (find_lost stats (Zlength packet_ptrs))))
          (map Vbyte (pop_stats stats (map Byte.unsigned (rev (find_lost stats k))) i'))
          (Vint (Int.repr 0))) 
          with (map Vbyte (pop_stats stats (map Byte.unsigned (rev (find_lost stats k))) (i' + 1))).
        2 : { rewrite pop_stats_plus_1.
              - rewrite <- upd_Znth_map. rewrite Znth_map by (rewrite Zlength_rev; lia).
                rewrite Znth_rev by lia. subst. do 3 f_equal. lia.
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
        (*Probably not worth using frame rule  only 3 local vars (_t'16, _pstat, _v) and 1 sep clause (pstat) 
          but good for now*)
        rewrite (grab_nth_LOCAL 13 (gvars gv)) by list_solve. simpl.
        rewrite (grab_nth_LOCAL 12 (gvars gv)) by list_solve. simpl.
        match goal with
        | [ |- semax _ (PROPx _ (LOCALx (?l1 :: ?l2 :: ?l3 :: ?tl) (SEPx (?h :: ?h1 :: ?t)))) _ _ ] => 
          set (locs := tl); set (seps := t)
        end.
        apply (semax_frame_seq [lvar _v (tarray (tarray tuchar 256) 128) v_v; temp _pstat ps;
          temp _t'16 (Vubyte (Znth (xh - 1 - i') (find_lost stats (Zlength packet_ptrs))))]
          [ data_at Ews (tarray tschar (Zlength packet_ptrs))
               (map Vbyte (pop_stats stats (map Byte.unsigned (rev (find_lost stats k))) (i' + 1))) ps])
        with (P1 := []) (P2 := []) (Q1 := locs) (Q2 := locs)
        (R1 := iter_sepcon_arrays packet_ptrs
            (pop_fill_rows_list packets
               (lmatrix_multiply xh xh c (find_invmx_list w' xh)
                  (lmatrix_multiply xh k c w'' d')) (map Byte.unsigned (rev (find_lost stats k)))
               i' 0) :: seps)
        (R2 := iter_sepcon_arrays packet_ptrs (pop_fill_rows_list packets
              (lmatrix_multiply xh xh c (find_invmx_list w' xh)
              (lmatrix_multiply xh k c w'' d')) 
              (map Byte.unsigned (rev (find_lost stats k))) i' c) :: seps);
        [ | subst locs seps; simpl app; entailer! | solve[ auto 50 with closed ] |];
        abbreviate_semax.
        { forward_loop (EX (j: Z),
            (PROP (0 <= j <= c)
            (LOCALx ((temp _j (Vint (Int.repr j))) :: locs)
            (SEPx (iter_sepcon_arrays packet_ptrs (pop_fill_rows_list packets
                (lmatrix_multiply xh xh c (find_invmx_list w' xh)
                (lmatrix_multiply xh k c w'' d')) 
                (map Byte.unsigned (rev (find_lost stats k))) i' j) :: seps))))).
          { forward. Exists 0. subst locs seps; entailer!. }
          { Intros j. subst locs seps; forward_if.
            { forward. simpl_repr_byte. forward. 
              (*simplify r*)
              assert_PROP (force_val (sem_binary_operation' Oadd (tptr tuchar) tint
                  (force_val(sem_add_ptr_int (tarray tuchar 16000) Signed v_s (Vint (Int.repr (xh - 1)))))
                  (Vint (Int.repr j))) = 
                field_address (tarray (tarray tuchar fec_max_cols) fec_max_h) 
                [ArraySubsc j; ArraySubsc (xh - 1)] v_s) as Hr. {
                entailer!. solve_offset. }
              rewrite Hr; clear Hr.
              (*inner loop (dot prod loop). This is a bit annoying because they iterate with
                pointers for some unknown reason. But we can frame out a lot, and no SEPS change*)
              set (locs := 
                [temp _m (field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + xh)) v_v);
                 temp _p (field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2)) v_v);
                 gvars gv]).
              set (seps :=
                [ data_at Tsh (tarray (tarray tuchar 16000) 128)
                 (pop_mx_mult_part xh c k fec_max_h fec_max_cols w'' d' xh 0) v_s; FIELD_TABLES gv;
                 data_at Tsh (tarray tuchar (xh * (xh + xh)))
                 (map Vubyte
                    (flatten_mx
                       (gauss_restrict_list xh (xh + xh)
                          (concat_mx_id
                             (submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1)
                                (seq.map Byte.unsigned (find_parity_rows parities i))
                                (seq.map Byte.unsigned (seq.rev (find_lost stats k)))) xh)))) v_v]).
              rewrite <- seq_assoc. 
              apply (semax_frame_seq
                [ temp _j (Vint (Int.repr j)); temp _i (Vint (Int.repr i'));
                  temp _u (force_val (sem_add_ptr_int (tarray tuchar 16000) Signed v_s (Vint (Int.repr (xh - 1)))));
                  temp _x (Vint (Int.repr (xh - 1))); temp _xh (Vubyte (Byte.repr xh)); temp _c (Vint (Int.repr c));
                  temp _plen pl; temp _pdata pd; lvar _lost (tarray tuchar fec_max_h) v_lost]
                [ iter_sepcon_arrays packet_ptrs
                  (pop_fill_rows_list packets
                     (lmatrix_multiply xh xh c (find_invmx_list w' xh)
                        (lmatrix_multiply xh k c w'' d')) (map Byte.unsigned (rev (find_lost stats k)))
                     i' j);
                   data_at Ews (tarray tint (Zlength packet_ptrs)) (map Vint (map Int.repr lengths)) pl;
                   data_at Ews (tarray (tptr tuchar) (Zlength packet_ptrs + Zlength parities))
                     (packet_ptrs ++ parity_ptrs) pd;
                   data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats (Zlength packet_ptrs) fec_max_h) v_lost])
              with (P1 := []) (P2 := []) 
              (Q1 := temp _y (Vint (Int.repr 0)) :: temp _r
                (field_address (tarray (tarray tuchar fec_max_cols) fec_max_h)
                   [ArraySubsc j; ArraySubsc (xh - 1)] v_s) :: locs)
              (Q2 := temp _y (Vubyte (dot_prod (find_invmx_list w' xh) (*dont need other locals*)
                              (lmatrix_multiply xh k c w'' d') i' j xh)) :: locs)
              (R1 := seps) (R2 := seps);
              [ | subst locs seps; simpl app; entailer! | solve [ auto 50 with closed ] |]; abbreviate_semax.
              { (*r is annoying. It is not always a field_address, because when we end, it is invalid. This
                  is not a problem because we don't access it then, but we need to use offset_val*) 
                forward_loop (EX (n : Z),
                  PROP (0 <= n <= xh)
                  (LOCALx (temp _n (field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + n)) v_v)
                    :: (temp _y (Vubyte (dot_prod (rev_cols_list xh xh (find_invmx_list w' xh)) (*dot prod is reversed*)
                                (rev_rows_list xh c (lmatrix_multiply xh k c w'' d')) i' j n))) :: 
                    (temp _r (offset_val (((xh - 1 - n) * fec_max_cols) + j) v_s))  :: locs)
                  (SEPx seps))).
                { forward. Exists 0. subst locs seps; entailer!. solve_offset. }
                { Intros n. subst locs seps; forward_if. 
                  { (*pointer access in condition is valid*) entailer!.
                    rewrite isptr_denote_tc_test_order by solve_offset.
                    unfold test_order_ptrs. remember (Zlength (find_lost stats (Zlength packet_ptrs))) as xh.
                    (*need to go from field_address -> offset_val*)
                    assert_PROP ((field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + n)) v_v) =
                      offset_val (i' * xh * 2 + n) v_v) as Hptr1. { entailer!; solve_offset. }
                    assert_PROP ((field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + xh)) v_v) =
                      offset_val (i' * xh * 2 + xh) v_v) as Hptr2. { entailer!; solve_offset. }
                    rewrite Hptr1, Hptr2, sameblock_offset_val by auto.
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
                    assert_PROP (n < xh) as Hxnxh. { entailer!. 
                      rewrite Hntemp, Hmtemp in H4.
                      setoid_rewrite ptr_comparison_lt_iff in H4; auto; try lia; try nia.
                      simpl; lia. }
                    clear Hntemp Hmtemp H4.
                    forward.
                    { entailer!; nia. }
                    { rewrite Znth_map. entailer!. simpl_repr_byte. 
                      rewrite (flatten_mx_Zlength _ xh (xh + xh)). nia.
                      apply gauss_restrict_list_wf. apply row_mx_list_wf; lia.
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
                        (Vubyte (get (lmatrix_multiply xh k c w'' d') (xh - 1 - n) j))). {
                        intros v l. rewrite !(@Znth_default _ Inhabitant_val),!(@Znth_default _  Inhabitant_list),
                          pop_mx_mult_part_done; try rep_lia. reflexivity. 
                        rewrite pop_mx_mult_part_Zlength; rep_lia.
                        assert (rect (pop_mx_mult_part xh c k fec_max_h fec_max_cols w'' d' xh 0) fec_max_h fec_max_cols) as 
                          [Hpartlen [_ Hpartall]]. {
                          apply pop_mx_mult_part_wf; rep_lia. }
                        rewrite Forall_Znth in Hpartall.
                        rewrite !(@Znth_default _  Inhabitant_list), Hpartall; rep_lia. }
                      (*Now we need the [field_address] for r*)
                      assert_PROP  (offset_val ((xh - 1 - n) * fec_max_cols + j) v_s = 
                        (field_address (tarray (tarray tuchar fec_max_cols) fec_max_h)
                      [ArraySubsc j; ArraySubsc (xh - 1 - n)] v_s)). { entailer!. solve_offset. }
                      forward; rewrite Hpopnth.
                      { entailer!; simpl_repr_byte. }
                      { unfold FIELD_TABLES. Intros.
                        forward_call(gv, (Znth (i' * xh * 2 + n)
                            (flatten_mx (gauss_restrict_list xh (xh + xh) (concat_mx_id w' xh)))),
                            (get (lmatrix_multiply xh k c w'' d') (xh - 1 - n) j)).
                        (*TODO: why do I get this extra goal?*)
                        { entailer!. simpl. unfold Vubyte. simpl_repr_byte. } 
                        { forward. (*simplify y*) unfold Int.xor. 
                          rewrite !Int.unsigned_repr, byte_xor_fold by rep_lia. simpl_repr_byte.
                          rewrite <- byte_int_repr, Byte.repr_unsigned by rep_lia.
                          forward. (*to avoid any issues with unfolding constants:*)
                          replace (Int.repr 16000) with (Int.repr fec_max_cols) by (f_equal; rep_lia).
                          forward. (*restore loop invar (dot prod)*)
                          Exists (n+1).
                          unfold FIELD_TABLES; entailer!.
                          repeat split. (*lots of equivalences because of pointers*)
                          - solve_offset.
                          - f_equal. rewrite dot_prod_plus_1 by lia.
                            unfold ssralg.GRing.add; simpl.
                            f_equal.
                            unfold ssralg.GRing.mul; simpl.
                            f_equal.
                            + unfold rev_cols_list.
                              rewrite (@mk_lmatrix_get ByteField.Byte_int__canonical__GRing_Field) by lia. 
                              unfold find_invmx_list, right_submx. rewrite mk_lmatrix_get by lia.
                              set (xh := Zlength (find_lost stats (Zlength packet_ptrs))) in *.
                              rewrite (@flatten_mx_Znth' xh (xh + xh)); 
                              [| apply gauss_restrict_list_wf; apply row_mx_list_wf; lia | nia].
                              replace (i' * xh * 2) with (i' * (xh + xh)) by nia.
                              f_equal.
                              * rewrite idx_div; lia.
                              * rewrite idx_mod; lia.
                            + unfold rev_rows_list. rewrite (@mk_lmatrix_get ByteField.Byte_int__canonical__GRing_Field) by lia. f_equal. lia.
                          - solve_offset.
                          - rewrite fec_max_cols_eq, fec_max_h_eq; auto. 
                        }
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
                    assert_PROP (xh <= n) as Hxnxh. { entailer!. rewrite Hntemp, Hmtemp in H4.
                      apply typed_false_not_true in H4. 
                      setoid_rewrite ptr_comparison_lt_iff in H4; auto; try lia; try nia.  simpl. lia. }
                    clear Hntemp Hmtemp H4.
                    assert (Hnxh: n = xh) by lia. entailer!. 
                    rewrite dot_prod_rev; try lia. reflexivity. apply right_submx_wf; lia.
                    apply lmatrix_multiply_wf; lia.
                  }
                }
              }
              { (*write to data - need to unfold iter_sepcon*)
                subst locs seps; simpl app; forward; rewrite !Byte.unsigned_repr by rep_lia.
                { entailer!. }
                { rewrite pop_find_lost_Znth by (subst; lia). entailer!. simpl_repr_byte. }
                { rewrite pop_find_lost_Znth by (subst; lia). 
                  (*need for forward*)
                  assert (0 <= Byte.unsigned (Znth (xh - i' - 1) (find_lost stats (Zlength packet_ptrs))) <
                     Zlength lengths). {
                    replace (Zlength lengths) with (Zlength packet_ptrs) by lia.
                    assert (Hkbyte: 0 <= Zlength packet_ptrs <= Byte.max_unsigned) by rep_lia.
                    apply (find_lost_bound stats) in Hkbyte. rewrite Forall_Znth in Hkbyte.
                    apply Hkbyte. subst; lia. }
                  forward.
                  (*for if statement, use frame rule 1 more time (don't need most things)*)
                  set (locs := 
                    [ temp _t'12 (Vint (Int.repr
                      (Znth (Byte.unsigned (Znth (xh - i' - 1) (find_lost stats (Zlength packet_ptrs))))
                         lengths)));
                      temp _j (Vint (Int.repr j)); temp _pdata pd;
                       temp _data_lost_row (Vubyte (Znth (xh - i' - 1) (find_lost stats (Zlength packet_ptrs))));
                      temp _y (Vubyte
                        (dot_prod (find_invmx_list w' xh) 
                          (lmatrix_multiply xh k c w'' d') i' j xh))]).
                  set (seps :=
                    [ data_at Ews (tarray (tptr tuchar) (Zlength packet_ptrs + Zlength parities))
                        (packet_ptrs ++ parity_ptrs) pd]).
                  apply (semax_frame_seq 
                    [ temp _m (field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2 + xh)) v_v);
                      temp _p (field_address (tarray tuchar (xh * (xh + xh))) (SUB (i' * xh * 2)) v_v); 
                      gvars gv; temp _i (Vint (Int.repr i'));
                      temp _u (force_val (sem_add_ptr_int (tarray tuchar 16000) Signed v_s (Vint (Int.repr (xh - 1)))));
                      temp _x (Vint (Int.repr (xh - 1))); temp _xh (Vubyte (Byte.repr xh)); temp _c (Vint (Int.repr c));
                      temp _plen pl; temp _pdata pd; lvar _lost (tarray tuchar fec_max_h) v_lost]
                    [ data_at Tsh (tarray (tarray tuchar 16000) 128)
                        (pop_mx_mult_part xh c k fec_max_h fec_max_cols w'' d' xh 0) v_s; 
                      FIELD_TABLES gv;
                      data_at Tsh (tarray tuchar (xh * (xh + xh)))
                       (map Vubyte
                          (flatten_mx
                             (gauss_restrict_list xh (xh + xh)
                                (concat_mx_id
                                   (submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1)
                                      (seq.map Byte.unsigned (find_parity_rows parities i))
                                      (seq.map Byte.unsigned (seq.rev (find_lost stats k)))) xh)))) v_v;
                      data_at Ews (tarray tint (Zlength packet_ptrs)) (map Vint (map Int.repr lengths)) pl;
                      data_at Tsh (tarray tuchar fec_max_h) 
                        (pop_find_lost stats (Zlength packet_ptrs) fec_max_h) v_lost])
                  with (P1 := []) (P2 := []) (Q1 := locs) (Q2 := locs)
                    (R1 := iter_sepcon_arrays packet_ptrs
                       (pop_fill_rows_list packets
                          (lmatrix_multiply xh xh c (find_invmx_list w' xh)
                             (lmatrix_multiply xh k c w'' d')) 
                          (map Byte.unsigned (rev (find_lost stats k))) i' j) :: seps)
                    (R2 := iter_sepcon_arrays packet_ptrs
                        (pop_fill_rows_list packets
                           (lmatrix_multiply xh xh c (find_invmx_list w' xh)
                              (lmatrix_multiply xh k c w'' d'))
                           (map Byte.unsigned (rev (find_lost stats k))) i' (j + 1)) :: seps);
                  [ | subst locs seps; simpl app; entailer! | solve [ auto 50 with closed ] |]; abbreviate_semax.
                  { subst locs seps. forward_if.
                    { assert (Hilenb: 0 <= (Znth (Byte.unsigned (Znth (xh - i' - 1)
                         (find_lost stats (Zlength packet_ptrs)))) lengths) <= c). {
                       rewrite Hlenspec by rep_lia. split; [list_solve |].
                       rewrite Forall_Znth in Hlenbound. apply Hlenbound. lia. }
                      rewrite Int.signed_repr, Hlenspec in H4 by rep_lia.
                      (*Need to unfold the [iter_sepcon_arrays]*)
                      set (poppack := pop_fill_rows_list packets
                       (lmatrix_multiply xh xh c (find_invmx_list w' xh)
                          (lmatrix_multiply xh k c w'' d'))
                       (map Byte.unsigned (rev (find_lost stats k))) i' j) in *.
                      assert (Hleneq: Zlength packet_ptrs = Zlength poppack). { subst poppack.
                        unfold pop_fill_rows_list. rewrite mkseqZ_Zlength; lia. }
                      assert (Hibound: 0 <= Byte.unsigned (Znth (xh - i' - 1) 
                          (find_lost stats (Zlength packet_ptrs))) < Zlength poppack) by lia.
                      rewrite (iter_sepcon_arrays_remove_one _ _ _ Hleneq Hibound). Intros.
                      forward.
                      { entailer!. }
                      { rewrite Znth_app1 by rep_lia. entailer!. }
                      { rewrite Znth_app1 by rep_lia. forward.
                        { entailer!. subst poppack. unfold pop_fill_rows_list.
                          rewrite mkseqZ_Znth, mkseqZ_Zlength; lia. }
                        { simpl_repr_byte. rewrite <- (byte_int_repr (Byte.unsigned _)) by rep_lia.
                          rewrite Byte.repr_unsigned.
                          (*rewrite before entailer because everything gets subst'ed and it's impossible
                            to read*)
                          set (poppack' := pop_fill_rows_list packets
                           (lmatrix_multiply xh xh c (find_invmx_list w' xh)
                              (lmatrix_multiply xh k c w'' d'))
                           (map Byte.unsigned (rev (find_lost stats k))) i' (j + 1)) in *.
                          assert (Hleneq': Zlength packet_ptrs = Zlength poppack'). { subst poppack'.
                            unfold pop_fill_rows_list. rewrite mkseqZ_Zlength; lia. }
                          assert (Hibound': 0 <= Byte.unsigned (Znth (xh - i' - 1) 
                              (find_lost stats (Zlength packet_ptrs))) < Zlength poppack') by lia.
                          rewrite (iter_sepcon_arrays_remove_one _ _ _ Hleneq' Hibound'). 
                          entailer!. subst poppack poppack'.
                          rewrite !pop_fill_rows_list_set.
                          - (*unfold set.*) (*ugh why does entailer ruin all this*)
                            set (found := find_found stats (Zlength packet_ptrs)) in *.
                            set (lost := find_lost stats (Zlength packet_ptrs)) in *.
                            set (row := find_parity_rows parities i) in *.
                            set (xh := Zlength lost) in *.
                            set (k := Zlength packet_ptrs) in *.
                            set (w' := submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1)
                              (seq.map Byte.unsigned row) (seq.map Byte.unsigned (seq.rev lost))) in *.
                            set (w'' := submx_rows_cols_rev_list weight_mx xh k (fec_n - 1)
                              (map Byte.unsigned row)
                              (map Byte.unsigned (found ++ find_parity_found parities (fec_n - 1) i))) in *.
                            set (d' := col_mx_list
                             (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found)
                                (Ziota 0 c))
                             (submx_rows_cols_list (fill_missing c parities) xh c
                                (map Byte.unsigned row) (Ziota 0 c)) (k - xh) xh c) in *.
                            set (s := lmatrix_multiply xh k c w'' d') in *.
                            set (d := lmatrix_multiply xh xh c (find_invmx_list w' xh) s) in *.
                            rewrite Znth_map; [| rewrite Zlength_rev; list_solve ].
                            rewrite Znth_rev by lia. replace (Zlength lost) with xh by lia.
                            unfold set at 3.
                            rewrite remove_upd_Znth by lia. cancel. apply derives_refl'.
                            rewrite set_Zlength2. f_equal. unfold set. rewrite !upd_Znth_map.
                            f_equal. rewrite upd_Znth_same by lia. f_equal. subst d.
                            unfold lmatrix_multiply. rewrite (@mk_lmatrix_get ByteField.Byte_int__canonical__GRing_Field) by lia.
                            reflexivity.
                          - apply FinFun.Injective_map_NoDup. intros b1 b2. apply byte_unsigned_inj.
                            apply NoDup_rev. apply find_lost_NoDup. rep_lia.
                          - rewrite Forall_map. apply Forall_rev.
                            assert (Hlostb: 0 <= Zlength packet_ptrs <= Byte.max_unsigned) by rep_lia.
                            apply (find_lost_bound stats) in Hlostb. rewrite Forall_Znth in Hlostb.
                            rewrite Forall_Znth; intros x Hx. simpl.
                            replace (Zlength packets) with (Zlength packet_ptrs) by lia.
                            apply Hlostb. apply Hx.
                          - rewrite Zlength_map,Zlength_rev. lia.
                          - rewrite Znth_map. rewrite Znth_rev by lia. lia. rewrite Zlength_rev; lia.
                        }
                      }
                    }
                    { (*Other case: j bigger than length*)
                      assert (Hilenb: 0 <= (Znth (Byte.unsigned (Znth (xh - i' - 1)
                         (find_lost stats (Zlength packet_ptrs)))) lengths) <= c). {
                       rewrite Hlenspec by rep_lia. split; [list_solve |].
                       rewrite Forall_Znth in Hlenbound. apply Hlenbound. lia. }
                      rewrite Int.signed_repr, Hlenspec in H4 by rep_lia.
                      forward. rewrite pop_fill_rows_list_set_over;
                      [ entailer! | rewrite Zlength_map; rewrite Zlength_rev; lia |]. 
                      rewrite Znth_map. rewrite Znth_rev; subst; lia.
                            rewrite Zlength_rev. lia. 
                    }
                  }
                  { subst locs seps; simpl app. deadvars!. forward. (*why do we need deadvars here?*)
                    (*end of j loop - invar preservation*)
                     Exists (j+1). entailer!.
                  }
                }
              }
            }
            { (*postcondition for j loop*) assert (Hjc: j = c) by lia. subst. forward.
              entailer!.
            }
          }
        }
        { (*end of i loop - invar preservation*)
          subst locs seps; forward. Exists (i'+1). entailer!.
          simpl_repr_byte.
          rewrite pop_fill_rows_list_finish. simpl. cancel. assumption.
        }
      }
    }
  }
  { (*postcondition for i loop*) forward. rewrite Byte.unsigned_repr in H0 by rep_lia.
    assert (Hixh: i' = xh) by lia. entailer!.
  }
}
Qed.

Lemma body_fec_blk_decode : semax_body Vprog Gprog f_fec_blk_decode fec_blk_decode_spec.
Proof.
start_function. (*use better names to make proof cleaner, since there will be a lot of goals and hypotheses*)
rename H into Hknh. rename H0 into Hhh. rename H1 into Hccols. rename H2 into Hbp.
assert_PROP (Zlength packets = k) as Hpacklen. { entailer!. list_solve. } 
rename H3 into Hpackptrlen.
assert_PROP (Zlength parity_ptrs = h) as Hparptrlen. { entailer!. list_solve. }
rename H4 into Hparlen.
assert_PROP (Zlength stats = k) as Hstatlen. { entailer!. list_solve. }
rename H5 into Hlenbound.
assert (forall (i: Z), 0 <= i < k -> Znth i lengths = Zlength (Znth i packets)) as Hlenspec. { 
  intros i Hi. subst. list_solve. }
rename H6 into Hlenmap. rename H7 into Hnumpars.
rename H8 into Hparsconsist. rename H9 into Hparsomelen. rename H10 into Hstatsvals.
rewrite <- (@find_parity_rows_filter _ parbound) in Hnumpars by lia.
rewrite <- (@find_lost_filter _ k) in Hnumpars by lia.
assert_PROP (Zlength lengths = k) as Hlenslen. { entailer!. list_solve. } 
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
(*First loop - populate lost/found packets*)
rewrite !data_at__tarray. rewrite !zseq_Zrepeat by rep_lia.
change (default_val tuchar) with Vundef.
apply (semax_frame_seq 
                    [temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd);
                     temp _xr (Vubyte Byte.zero); temp _err (Vubyte Byte.zero);
                     lvar _row (tarray tuchar fec_max_h) v_row;
                     lvar _s (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s;
                     lvar _v (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v; 
                     gvars gv; temp _c (Vint (Int.repr c));
                     temp _pdata pd; temp _plen pl]
                    [data_at_ Tsh (tarray tuchar fec_max_h) v_row;
                     data_at_ Tsh (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s;
                     data_at_ Tsh (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v;
                     iter_sepcon_arrays packet_ptrs packets; iter_sepcon_options parity_ptrs parities;
                     data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
                     data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl; FEC_TABLES gv])
  with (P1 := []) (P2 := [])
 (Q1 := [temp _xh (Vubyte Byte.zero); temp _xk (Vubyte Byte.zero);
                   temp _k (Vint (Int.repr k)); temp _pstat ps;
                     lvar _found (tarray tuchar fec_max_h) v_found;
                     lvar _lost (tarray tuchar fec_max_h) v_lost  ])
 (Q2 := [temp _xh (Vubyte (Byte.repr (Zlength (find_lost stats k))));
             temp _xk (Vubyte (Byte.repr (Zlength (find_found stats k))));
                 temp _k (Vint (Int.repr k)); temp _pstat ps;
                     lvar _found (tarray tuchar fec_max_h) v_found;
                     lvar _lost (tarray tuchar fec_max_h) v_lost  ])
 (R1 := [ data_at Ews (tarray tschar k) (map Vbyte stats) ps;
            data_at Tsh (tarray tuchar fec_max_h) (zseq fec_max_h Vundef) v_found;
       data_at Tsh (tarray tuchar fec_max_h) (zseq fec_max_h Vundef) v_lost])
 (R2 := [ data_at Ews (tarray tschar k) (map Vbyte stats) ps;
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h)  v_lost;
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_found stats k fec_max_h)  v_found]);
  [ | solve [unfold app; entailer!]
    | solve [auto 50 with closed]
    | ].
  apply body_fec_blk_decode_loop1; auto.

  abbreviate_semax.
  remember (Zlength (find_lost stats k)) as xh.
  remember (Zlength (find_found stats k)) as xk. assert (Hk: 0 <= k) by lia.
  pose proof (@find_lost_Zlength stats k Hk) as Hxh. rewrite <-Heqxh in Hxh.
  pose proof (@find_found_Zlength stats k Hk) as Hxk. rewrite <-Heqxk in Hxk. clear Hk.
  unfold app at 1 2. forward_if.
 + forward.
    (*TODO: this didn't doesn't work ( in [solve_Forall2_fn_data_at]) with opaque constants*)
    rewrite Byte.unsigned_repr in H by rep_lia. rewrite Int_repr_zero in H by rep_lia.
    entailer!.
    { rewrite <- (@find_lost_filter _ (Zlength packet_ptrs)). rewrite H. reflexivity. lia. }
    { replace 256 with (fec_max_h * 2) by rep_lia. replace 16000 with fec_max_cols by rep_lia.
      replace 128 with fec_max_h by rep_lia. cancel.
      (*If xh = 0, the result is trivial*) (*TODO: maybe do this in separate lemma (just list equality)*)
      rewrite decoder_list_correct_0; auto; try lia; 
        [cancel | rewrite <- (find_lost_filter (k:=(Zlength packet_ptrs))); auto].
      apply derives_refl'. repeat f_equal. apply Znth_eq_ext. 
      - rewrite zseq_Zlength; list_solve.
      - rewrite Zlength_map. intros i Hi. rewrite Znth_map by auto.
        rewrite zseq_Znth by lia. f_equal.
        destruct (Byte.eq_dec (Znth i stats) (Byte.zero)); auto.
        assert (Hinlost: In (Byte.repr i) (find_lost stats (Zlength packet_ptrs))). {
          apply find_lost_found_aux_in_spec. rewrite Forall_Znth; intros x. rewrite Zlength_Ziota by lia.
          intros Hx. rewrite Znth_Ziota by lia. rep_lia. right. rewrite !Byte.unsigned_repr by rep_lia.
          split. apply Ziota_In; lia. assert (Hith: Znth i stats = Byte.one). {
            rewrite Forall_Znth in Hstatsvals. specialize (Hstatsvals _ Hi). destruct Hstatsvals; subst; auto. 
            contradiction. }
          rewrite Hith. destruct (Z.eq_dec (Byte.signed Byte.one) 1); auto. }
        apply Zlength_nil_inv in H. rewrite H in Hinlost. contradiction.
    }
 + forward. unfold Int.sub. rewrite !Int.unsigned_repr by rep_lia. simpl_repr_byte.
    (*Second loop - populate parity packet row/found*) 
    rewrite !data_at__tarray. rewrite !zseq_Zrepeat by rep_lia.
    replace (default_val tuchar) with Vundef by reflexivity.
    apply (semax_frame_seq_ex
                    [temp _err (Vubyte Byte.zero); lvar _lost (tarray tuchar fec_max_h) v_lost;
                     lvar _s (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s;
                     lvar _v (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v; gvars gv;
                     temp _k (Vint (Int.repr k)); temp _c (Vint (Int.repr c)); temp _pdata pd; 
                     temp _plen pl; temp _pstat ps]
                    [data_at Ews (tarray tschar k) (map Vbyte stats) ps;
                     data_at_ Tsh (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s;
                     data_at_ Tsh (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v;
                     iter_sepcon_arrays packet_ptrs packets;
                     data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl;
                     FEC_TABLES gv;
                     data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost])
    with (P1 := []) (P2 := fun i => [0 <= i <= Zlength parities; Zlength (find_parity_rows parities i) = xh])
    (Q1 := [temp _xr (Vubyte Byte.zero); temp _xk (Vubyte (Byte.repr xk));
         temp _q (Vint (Int.repr (256 - 2)));
         lvar _found (tarray tuchar fec_max_h) v_found; lvar _row (tarray tuchar fec_max_h) v_row;
         temp _xh (Vubyte (Byte.repr xh)); temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd)])
    (Q2 := fun i => 
        [temp _xr (Vubyte (Byte.repr (Zlength (find_parity_rows parities i))));
         temp _xk (Vubyte (Byte.repr (xk + Zlength (find_parity_found parities (fec_n - 1) i))));
         temp _q (Vint (Int.repr (fec_n - 2 - i)));
         lvar _found (tarray tuchar fec_max_h) v_found; lvar _row (tarray tuchar fec_max_h) v_row;
         temp _xh (Vubyte (Byte.repr xh));
         temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd)])
    (R1 := [ data_at Tsh (tarray tuchar fec_max_h) (pop_find_found stats k fec_max_h) v_found;
          data_at Tsh (tarray tuchar fec_max_h) (zseq fec_max_h Vundef) v_row;
          data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
          iter_sepcon_options parity_ptrs parities])
    (R2 := fun i => 
        [ data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row;
          data_at Tsh (tarray tuchar fec_max_h) 
            (pop_find_parity_found stats parities i fec_max_h k (fec_n - 1)) v_found;
          data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
          iter_sepcon_options parity_ptrs parities]); 
      [ | solve [unfold app; entailer!]
        | solve [auto 50 with closed]
        | ].
    eapply body_fec_blk_decode_loop2; auto. apply Hccols. apply Hnumpars. all: auto.
    abbreviate_semax.
    (*After 2nd loop*)
    Intros i. assert (Hroweq: (find_parity_rows parities i) = (find_parity_rows parities parbound)). {
      apply find_parity_rows_eq; lia. }
    assert (Hfoundeq: (find_parity_found parities (fec_n - 1) i) = (find_parity_found parities (fec_n - 1) parbound)). {
      apply find_parity_found_eq; try lia. rewrite !find_parity_rows_found_Zlength. lia. }
    unfold FEC_TABLES. unfold app at 1 2. Intros.
    forward. forward_if True; [discriminate | solve[forward; entailer!] |].
    assert (Hxh0: 0 < xh). { assert (Hxh0: 0 = xh \/ 0 < xh) by list_solve. destruct Hxh0 as [Hxh0 | Hxh0]; try lia.
      rewrite <- Hxh0 in H. rewrite !Byte.unsigned_repr in H by rep_lia. contradiction. } clear H.
    apply (semax_frame_seq
            [temp _t'29 (Vint Int.zero);
             temp _xr (Vubyte (Byte.repr (Zlength (find_parity_rows parities i))));
             temp _xk (Vubyte (Byte.repr (xk + Zlength (find_parity_found parities (fec_n - 1) i))));
             temp _q (Vint (Int.repr (fec_n - 2 - i))); lvar _found (tarray tuchar fec_max_h) v_found;
             temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd);
             temp _err (Vubyte Byte.zero); lvar _s (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s;
             temp _k (Vint (Int.repr k)); temp _c (Vint (Int.repr c)); temp _pdata pd; 
             temp _plen pl; temp _pstat ps]
           [ data_at Ews (tarray tschar k) (map Vbyte stats) ps;
             data_at_ Tsh (tarray (tarray tuchar fec_max_cols) fec_max_h) v_s;
             iter_sepcon_arrays packet_ptrs packets;
             data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl; FIELD_TABLES gv;
             data_at Ews tint (Vint Int.zero) (gv _trace);
             data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
             iter_sepcon_options parity_ptrs parities;
             data_at Tsh (tarray tuchar fec_max_h)
                (pop_find_parity_found stats parities i fec_max_h k (fec_n - 1)) v_found])
    with (P1 := []) (P2 := [])
    (Q1 := [lvar _v (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v;
            lvar _lost (tarray tuchar fec_max_h) v_lost;
            temp _xh (Vubyte (Byte.repr xh));
            lvar _row (tarray tuchar fec_max_h) v_row; gvars gv])
    (Q2 := [lvar _v (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v;
            lvar _lost (tarray tuchar fec_max_h) v_lost;
            temp _xh (Vubyte (Byte.repr xh));
            lvar _row (tarray tuchar fec_max_h) v_row; gvars gv])
    (R1 := [ data_at_ Tsh (tarray (tarray tuchar (fec_max_h * 2)) fec_max_h) v_v;
             data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights);
             data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost;
             data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row])
    (R2 := [ data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h))
              (pop_find_inv xh (map_2d_rev id weight_mx) (find_parity_rows parities i) (find_lost stats k) xh 0) v_v;
             data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights);
             data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats k fec_max_h) v_lost;
             data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row]);
    [ | solve [unfold app; entailer!]
        | solve [auto 50 with closed ]
        | ].
    apply body_fec_blk_decode_loop3; auto. lia.
    unfold app at 1 2.
    abbreviate_semax.
    (*After third loop, Now need pre/postconditions of gaussian elim*)
    (*issue: ptree does not evaluate bc of opaque constants*)
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
    2 : { rewrite zseq_Zlength; rep_nia. }
    replace (tarray tuchar (2 * xh * xh)) with (tarray tuchar (xh * (xh + xh))) by  (f_equal; lia).
    forward_call(gv, xh, xh + xh, (concat_mx_id
            (submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1)
               (seq.map Byte.unsigned (find_parity_rows parities i))
               (seq.map Byte.unsigned (seq.rev (find_lost stats k)))) xh), v_v, Tsh).
    { entailer!. simpl. simpl_repr_byte. f_equal. rewrite !byte_int_repr by rep_lia. do 4 f_equal. lia. }
    { replace (xh * (xh + xh)) with (2 * xh * xh) by lia. entailer!. }
    { split.
      - apply row_mx_list_wf; lia.
      - apply strong_inv_row_mx_list. apply strong_inv_list_partial; lia.
    }
    { forward. forward_if True; [contradiction | forward; entailer! |].
      (*start of syndrome mx (multiplication) loop*)
      replace (Zlength (find_lost stats (Zlength packet_ptrs))) with xh by (subst; lia).
      (*To reduce duplication, we store the things in common for LOCALS and SEP - TODO: automate*)

      set (locs := [ temp _xh (Vubyte (Byte.repr xh)); lvar _row (tarray tuchar fec_max_h) v_row; 
                   gvars gv; lvar _s (tarray (tarray tuchar 16000) 128) v_s; 
                   temp _c (Vint (Int.repr c)); temp _k (Vint (Int.repr k));
                   lvar _found (tarray tuchar fec_max_h) v_found;
                   temp _plen pl; temp _pdata pd;
                   temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd) ]).
      set (seps := [FIELD_TABLES gv; iter_sepcon_arrays packet_ptrs packets;
         data_at Ews (tarray tint (Zlength packet_ptrs)) (map Vint (map Int.repr lengths)) pl;
         data_at Ews (tarray (tptr tuchar) (Zlength packet_ptrs + Zlength parities))
           (packet_ptrs ++ parity_ptrs) pd; iter_sepcon_options parity_ptrs parities;
         data_at Tsh (tarray tuchar fec_max_h)
           (pop_find_parity_found stats parities i fec_max_h (Zlength packet_ptrs) (fec_n - 1)) v_found;
         data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx)
           (gv _fec_weights);
         data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row]).
      set (row := (find_parity_rows parities i)).
      set (found1 := (find_found stats k)).
      set (found2 := find_parity_found parities (fec_n - 1) i).
      apply (semax_frame_seq 
        [ temp _err (Vint Int.zero);
          temp _t'6 (Vint Int.zero);
          lvar _v (tarray (tarray tuchar 256) 128) v_v; lvar _lost (tarray tuchar fec_max_h) v_lost;
          temp _t'29 (Vint Int.zero);
          temp _xr (Vubyte (Byte.repr (Zlength (find_parity_rows parities i))));
          temp _xk (Vubyte (Byte.repr (xk + Zlength (find_parity_found parities (fec_n - 1) i))));
          temp _pstat ps]
        [ data_at Tsh (tarray tuchar (xh * (xh + xh))) (map Vubyte (flatten_mx
           (gauss_restrict_list xh (xh + xh) (concat_mx_id
                 (submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1)
                    (seq.map Byte.unsigned (find_parity_rows parities i)) (*a pattern would be REALLY helpful*)
                    (seq.map Byte.unsigned (seq.rev (find_lost stats k)))) xh)))) v_v;
          data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h - 2 * xh * xh))
            (zseq (2 * fec_max_h * fec_max_h - 2 * xh * xh) Vundef)
            (field_address0 (tarray tuchar (2 * fec_max_h * fec_max_h)) (SUB (2 * xh * xh)) v_v);
          data_at Ews (tarray tschar (Zlength packet_ptrs)) (map Vbyte stats) ps;
          data_at Ews tint (Vint Int.zero) (gv _trace);
          data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats (Zlength packet_ptrs) fec_max_h) v_lost])
        with (P1 := []) (P2 := [])
          (Q1 := locs)
          (Q2 := locs)
          (R1 := data_at_ Tsh (tarray (tarray tuchar 16000) 128) v_s :: seps)
          (R2 := (data_at Tsh (tarray (tarray tuchar 16000) 128) 
            (pop_mx_mult_part xh c k fec_max_h fec_max_cols 
              (submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) (map Byte.unsigned row) 
                  (map Byte.unsigned (found1 ++ found2)))
              (col_mx_list (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
                  (submx_rows_cols_list (fill_missing  c parities) xh c (map Byte.unsigned row) (Ziota 0 c)) (k-xh) xh c)
              xh 0) v_s) (*this is quite ugly*) :: seps);
        [ | solve [ simpl app; entailer! ] | solve [ auto 50 with closed ]|] .
      apply body_fec_blk_decode_loop4; auto.
      subst locs seps; simpl app; abbreviate_semax.
      (*Final loop (multiplication and regenerate data)*)
      forward. unfold Int.sub. simpl_repr_byte.
      (*TODO: cannot rewrite opaque constants, get C parser error*)
      forward.

      (*remember matrices to make the loop invariants nicer. The names match those in [decode_list_mx]*)
      set (w'' := submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) (map Byte.unsigned row)
        (map Byte.unsigned (found1 ++ found2))) in *.
      set (d' := col_mx_list
       (bsubmx_rows_cols_list packets (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
       (submx_rows_cols_list (fill_missing c parities) xh c (map Byte.unsigned row)
          (Ziota 0 c)) (k - xh) xh c) in *.
      set (w' := submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1)
              (seq.map Byte.unsigned row) (seq.map Byte.unsigned 
              (seq.rev (find_lost stats k)))) in *.

      (*Local variables we need, but are not changing*)
      set (locs := 
        [temp _u (force_val
          (sem_binary_operation' Oadd (tarray (tarray tuchar 16000) 128) tuchar v_s
              (Vint (Int.repr (xh - 1))))); temp _x (Vint (Int.repr (xh - 1)));
        temp _xh (Vubyte (Byte.repr xh)); temp _c (Vint (Int.repr c));  gvars gv; 
        temp _plen pl; temp _pdata pd;
        lvar _v (tarray (tarray tuchar 256) 128) v_v;
        lvar _lost (tarray tuchar fec_max_h) v_lost; temp _pstat ps]).

      (*SEPs we need, but are not changing*)
      set (seps := [data_at Tsh (tarray (tarray tuchar 16000) 128)
      (pop_mx_mult_part xh c k fec_max_h fec_max_cols w'' d' xh 0) v_s; 
      FIELD_TABLES gv;
      data_at Ews (tarray tint (Zlength packet_ptrs)) (map Vint (map Int.repr lengths)) pl;
      data_at Ews (tarray (tptr tuchar) (Zlength packet_ptrs + Zlength parities))
        (packet_ptrs ++ parity_ptrs) pd;
      data_at Tsh (tarray tuchar (xh * (xh + xh)))
        (map Vubyte
            (flatten_mx
              (gauss_restrict_list xh (xh + xh)
                  (concat_mx_id
                    (submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1)
                        (seq.map Byte.unsigned (find_parity_rows parities i))
                        (seq.map Byte.unsigned (seq.rev (find_lost stats k)))) xh)))) v_v;
                        data_at Tsh (tarray tuchar fec_max_h) (pop_find_lost stats (Zlength packet_ptrs) fec_max_h) v_lost]).

      apply (semax_frame_seq 
        [ lvar _row (tarray tuchar fec_max_h) v_row; 
          lvar _s (tarray (tarray tuchar 16000) 128) v_s;
          temp _k (Vint (Int.repr k));
          lvar _found (tarray tuchar fec_max_h) v_found; 
          temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd); 
          temp _err (Vint Int.zero); temp _t'6 (Vint Int.zero); 
          temp _t'29 (Vint Int.zero);
          temp _xr (Vubyte (Byte.repr (Zlength (find_parity_rows parities i))));
          temp _xk (Vubyte (Byte.repr (xk + Zlength 
            (find_parity_found parities (fec_n - 1) i))))]
        [   data_at Tsh (tarray tuchar (2 * fec_max_h * fec_max_h - 2 * xh * xh))
              (zseq (2 * fec_max_h * fec_max_h - 2 * xh * xh) Vundef)
              (field_address0 (tarray tuchar (2 * fec_max_h * fec_max_h)) (SUB (2 * xh * xh)) v_v);
            data_at Ews tint (Vint Int.zero) (gv _trace);
            iter_sepcon_options parity_ptrs parities;
            data_at Tsh (tarray tuchar fec_max_h)
              (pop_find_parity_found stats parities i fec_max_h (Zlength packet_ptrs) (fec_n - 1)) v_found;
            data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights);
            data_at Tsh (tarray tuchar fec_max_h) (pop_find_parity_rows parities i fec_max_h) v_row] )
      with (P1 := []) (P2 := [])
      (Q1 := locs) (Q2 := locs)
      (R1 := iter_sepcon_arrays packet_ptrs packets ::
             data_at Ews (tarray tschar (Zlength packet_ptrs)) (map Vbyte stats) ps ::
             seps)
      (R2 := (iter_sepcon_arrays packet_ptrs 
        (pop_fill_rows_list packets (lmatrix_multiply xh xh c (find_invmx_list w' xh)
            (lmatrix_multiply xh k c w'' d')) (map Byte.unsigned (rev (find_lost stats k))) xh 0) ::
        data_at Ews (tarray tschar (Zlength packet_ptrs)) 
          (map Vbyte (pop_stats stats (map Byte.unsigned (rev (find_lost stats k))) xh)) ps :: seps));
      [ | subst locs seps; simpl app; entailer! | solve [ auto 50 with closed ] |].
      apply (body_fec_blk_decode_loop5) with (row := row) (found1 := found1) (found2 := found2); auto.
      subst locs seps; simpl app. abbreviate_semax. 
      forward_if True; [contradiction | forward; entailer! |].
      forward_if True; [contradiction | forward; entailer! |].
      forward. (*prove postcondition*)
      simpl_repr_byte. 
      rewrite <- CommonSSR.filter_filter, <- (@find_lost_filter stats (Zlength packet_ptrs)) by lia.
      rewrite <- fec_max_h_eq, <- fec_max_cols_eq.
      entailer!.
      {
        unfold Vubyte. simpl. simpl_repr_byte.
      }
      unfold decoder_list.
      assert (Hrevlen: Zlength (find_lost stats (Zlength packet_ptrs)) =
        (Zlength (map Byte.unsigned (rev (find_lost stats (Zlength packet_ptrs)))))). {
        rewrite Zlength_map. rewrite Zlength_rev. reflexivity. }
      rewrite Hrevlen at 12.
      replace (Zlength (find_lost stats (Zlength packet_ptrs))) with
        (Zlength (map Byte.unsigned (rev (find_lost stats (Zlength packet_ptrs))))) at 5 
        by (rewrite Zlength_map, Zlength_rev; reflexivity).
      rewrite (@pop_fill_rows_list_done packets _ (map Byte.unsigned (rev (find_lost stats (Zlength packet_ptrs))))
        (map (Zlength (A:=byte)) packets) 0 (Zlength packet_ptrs) c (Zlength (find_lost stats (Zlength packet_ptrs)))); 
      try lia; try assumption; [| apply (@lmatrix_multiply_wf ByteField.Byte_int__canonical__GRing_Field (Zlength (find_lost stats (Zlength packet_ptrs)))); 
        lia | rewrite Zlength_map, Zlength_rev; reflexivity |].
      unfold FEC_TABLES.
      (*do matrix part last so we can derives_refl'*)
      rewrite !sepcon_assoc.
      apply sepcon_derives.
      - subst w' d' w'' row found1 found2. apply derives_refl'. f_equal. f_equal. unfold decode_list_mx.
        rewrite (@fill_rows_list_extend _ (Zlength packet_ptrs) _ _ _ _ _ c); try lia. 
        rewrite Hroweq, Hfoundeq, !cat_app, !CommonSSR.map_map_equiv.
        match goal with
        | |- fill_rows_list (F:=ByteField.Byte_int__canonical__GRing_Field)  ?l ?c ?l2 ?e ?x ?t1 =
          fill_rows_list (F:=ByteField.Byte_int__canonical__GRing_Field)  ?l ?c ?l2 ?e ?y ?t2 =>
          replace t1 with t2 by
            (rewrite CommonSSR.rev_rev; apply CommonSSR.map_map_equiv);
          replace x with y; [reflexivity |]
        end.
        f_equal.
        f_equal.
        f_equal.
        unfold bsubmx_rows_cols_list.
        symmetry.
        rewrite (@submx_rows_cols_list_extend _ _ _ _ _  _ c); try lia; try assumption.
        + f_equal. apply extend_mx_length; try lia; solve[list_solve].
        + rewrite Forall_map. eapply Forall_impl. 2:  apply find_found_bound; rep_lia.
          simpl. lia.
        + rewrite Forall_Znth,Zlength_Ziota by lia. intros x Hx. rewrite Znth_Ziota; lia. 
        + rewrite Zlength_map. assert (Hkbyte: 0 <= Zlength packet_ptrs <= Byte.max_unsigned) by rep_lia.
          apply (find_lost_found_Zlength stats) in Hkbyte. lia.
        + rewrite Zlength_Ziota; lia.
    - rewrite fec_max_h_eq; entailer!. rewrite sepcon_assoc. 
      apply sepcon_derives.
      + replace (Zlength (find_lost stats (Zlength packet_ptrs))) with
        (Zlength (map Byte.unsigned (rev (find_lost stats (Zlength packet_ptrs))))) by
        (rewrite Zlength_map; rewrite Zlength_rev; reflexivity).
        rewrite pop_stats_done, zseq_map. replace (Zlength stats) with (Zlength packet_ptrs) by lia.
        cancel. intros x Hxlen Hx.
        assert (Znth x stats = Byte.zero \/ Znth x stats = Byte.one) as [Hbz | Hbo].  {
          rewrite Forall_Znth in Hstatsvals. apply Hstatsvals. lia. }
        apply Hbz. rewrite in_map_iff in Hx.
        exfalso. apply Hx. exists (Byte.repr x). split. rewrite Byte.unsigned_repr; rep_lia.
        unfold find_lost. rewrite <- in_rev,find_lost_found_aux_in_spec.
        right. rewrite !Byte.unsigned_repr by rep_lia.
        split.
        rewrite Ziota_In; lia. rewrite Hbo. auto.
        rewrite Forall_Znth, Zlength_Ziota by lia. intros y Hy. 
        rewrite Znth_Ziota; rep_lia.
      + (*rewrite fec_max_h_eq. entailer!. rewrite sepcon_comm.*)
        remember (Zlength (find_lost stats (Zlength packet_ptrs))) as xh.
        replace (xh * (xh + xh)) with (2 * xh * xh) by lia.
        (*Now have to go 1D - 2D array*)
        rewrite <- (split2_data_at_Tarray_app), <- (concat_unconcat _ 128 256); try lia.
        replace (2 * 128 * 128) with (128 * 256) by lia.
        rewrite <- data_at_2darray_concat; auto.
        rewrite <- fec_n_eq, <- fec_max_h_eq. entailer!.
        * apply unconcat_length2; lia.
        * rewrite Zlength_app,  Zlength_map, (@flatten_mx_Zlength _ xh (xh + xh)), zseq_Zlength; 
            [nia | rep_nia |]. 
          replace (Zlength (map Byte.unsigned (rev (find_lost stats (Zlength packet_ptrs))))) with xh by lia.
          apply gauss_restrict_list_wf. apply row_mx_list_wf; lia.
        * rewrite zseq_Zlength; rep_nia.
    - intros i' Hi'. apply Hlenspec. lia.
    }
Qed.
