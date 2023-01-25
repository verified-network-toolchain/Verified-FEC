(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
(*Functions for working with arrays and memory in VST that are generic*)

(*These first two are not directly related to VST but are used in the later proofs*)
Lemma Zlength_concat: forall {A: Type} (n m : Z) (l: list (list A)),
  Zlength l = n ->
  Forall (fun x => Zlength x = m) l ->
  Zlength (concat l) = n * m.
Proof.
  intros A m n l. revert m. induction l; intros.
  - list_solve.
  - simpl. rewrite Zlength_app. rewrite (IHl (m-1)). 2: list_solve.
    assert (Zlength a = n). inversion H0; subst; reflexivity. rewrite H1. lia. inversion H0; auto.
Qed. 

Lemma lt_plus_lt: forall z1 z2 z3, 
  0 <= z1 -> 
  z1 + z2 < z3 -> 
  z2 < z3.
Proof.
  intros z1 z2 z3 Hz1 Hz12. rewrite Z.lt_add_lt_sub_r in Hz12. lia.
Qed.

Lemma typed_false_not_true: forall a b, typed_false a b -> ~(typed_true a b).
Proof.
  intros a b F T.
  unfold typed_true in T; unfold typed_false in F; rewrite T in F; inversion F.
Qed. 

(** Facts about [combine]*)
(*This function is in the standard library, but we need a few results about how functions like Znth, Zlength,
  and sublist work with combine*)
Lemma combine_Zlength: forall {A B : Type} (l1: list A) (l2: list B),
  Zlength l1 = Zlength l2 ->
  Zlength (combine l1 l2) = Zlength l1.
Proof.
  intros A B l1 l2 Hlen. rewrite !Zlength_correct in *. rewrite combine_length. lia.
Qed.

Lemma combine_Znth: forall {A B: Type} `{Inhabitant A} `{Inhabitant B} (l1 : list A) (l2: list B) i,
  Zlength l1 = Zlength l2 ->
  0 <= i < Zlength l1 ->
  Znth i (combine l1 l2) = (Znth i l1, Znth i l2).
Proof.
  intros. rewrite <- !nth_Znth. apply combine_nth. rewrite <- !ZtoNat_Zlength; lia.
  lia. lia. rewrite combine_Zlength; lia.
Qed. 

Lemma combine_sublist: forall {A B: Type} `{Inhabitant A} `{Inhabitant B} (lo hi : Z) (l1 : list A) (l2: list B),
  Zlength l1 = Zlength l2 ->
  0 <= lo <= hi ->
  hi <= Zlength l1 ->
  combine (sublist lo hi l1) (sublist lo hi l2) = sublist lo hi (combine l1 l2).
Proof.
  intros A B Hinh1 Hinh2 lo hi l1 l2 Hlen Hhilo Hhi.
  assert (Hsublen: Zlength (combine (sublist lo hi l1) (sublist lo hi l2)) = hi - lo). {
   rewrite combine_Zlength by (rewrite !Zlength_sublist; lia). list_solve. }
  apply Znth_eq_ext. rewrite Hsublen. rewrite Zlength_sublist; try lia.
  rewrite combine_Zlength; lia.
  intros i Hi. rewrite Hsublen in Hi. rewrite combine_Znth by list_solve.
  rewrite !Znth_sublist by lia. rewrite combine_Znth by lia. reflexivity.
Qed.

Lemma combine_app: forall {A B: Type} `{Inhabitant A} `{Inhabitant B} (l1 l3: list A) (l2 l4: list B),
  Zlength l1 = Zlength l2 ->
  Zlength l3 = Zlength l4 ->
  combine (l1 ++ l3) (l2 ++ l4) = combine l1 l2 ++ combine l3 l4.
Proof.
  intros A B Hin1 Hin2 l1 l3 l2 l4 Hlen1 Hlen3.
  apply Znth_eq_ext.
  - rewrite !combine_Zlength by list_solve. rewrite !Zlength_app. rewrite !combine_Zlength; list_solve.
  - intros i Hilen. rewrite combine_Zlength in Hilen by list_solve. rewrite combine_Znth by list_solve.
    assert (0 <= i < Zlength l1 \/ Zlength l1 <= i < Zlength l1 + Zlength l3) by list_solve.
    destruct H as [Hfst | Hsnd].
    + rewrite !Znth_app1; try lia. rewrite combine_Znth by lia. reflexivity.
      rewrite combine_Zlength; lia.
    + rewrite !Znth_app2; try lia. rewrite combine_Znth; try lia. all: rewrite combine_Zlength; try lia.
      rewrite Hlen1. reflexivity.
Qed.

Section VSTFacts.

Context {Comp : compspecs}.

(** Working with pointers that we treat as arrays*)

(*For simplifying pointer arithmetic*)
Lemma sem_sub_pi_offset: forall ty s off n,
  isptr s ->
  complete_type cenv_cs ty = true ->
  Int.min_signed <= n <= Int.max_signed ->
  force_val (sem_sub_pi ty Signed (offset_val off s) (Vint (Int.repr n))) =
  offset_val (off - (sizeof ty) * n) s.
Proof.
  intros ty s off n Hptr Hty Hn.
  replace (off - (sizeof ty) * n) with (off + (- (sizeof ty) * n)) by lia. rewrite <- offset_offset_val.
  assert (Hptr' : isptr (offset_val off s)). rewrite isptr_offset_val; auto.
  destruct (offset_val off s) eqn : Hoff; inversion Hptr'. simpl.
  unfold sem_sub_pi. rewrite Hty. simpl. f_equal. unfold sizeof.
  assert ((Ptrofs.of_ints (Int.repr n)) = Ptrofs.repr n). unfold Ptrofs.of_ints.
  f_equal. apply Int.signed_repr; auto. rewrite H. rewrite ptrofs_mul_repr.
  rewrite Ptrofs.sub_add_opp. f_equal. replace (- Ctypes.sizeof ty * n) with (-(Ctypes.sizeof ty * n)) by lia.
  rewrite <- (Ptrofs.neg_repr). reflexivity.
Qed.

(*Indexing into arrays*)

Lemma arr_field_compatible0 : forall t size p i, 
  field_compatible (tarray t size) [] p ->
  0 <= i <= size ->
  field_compatible0 (tarray t size) (SUB i) p.
Proof.
  intros t size p i Hcomp Hsz.
  unfold field_compatible in *. unfold field_compatible0. destruct Hcomp as [Hptr [Hleg [Hsz_comp [Hal Hnest]]]].
  repeat(split; auto).
Qed.

Lemma arr_field_address0: forall t size p i, 
  field_compatible (tarray t size) [] p ->
  0 <= i <= size ->
  field_address0 (tarray t size) (SUB i) p = offset_val (sizeof t * i) p.
Proof.
  intros t size p i Hcomp Hi.
  unfold field_address0. destruct (field_compatible0_dec (tarray t size) [ArraySubsc i] p).
  simpl. auto. exfalso. apply n. apply arr_field_compatible0; auto.
Qed.

Lemma arr_field_compatible : forall t size p i, 
  field_compatible (tarray t size) [] p ->
  0 <= i < size ->
  field_compatible (tarray t size) (SUB i) p.
Proof.
  intros t size p i Hcomp Hsz.
  unfold field_compatible in *. unfold field_compatible0. destruct Hcomp as [Hptr [Hleg [Hsz_comp [Hal Hnest]]]].
  repeat(split; auto).
Qed.

Lemma arr_field_address: forall t size p i, 
  field_compatible (tarray t size) [] p ->
  0 <= i < size ->
  field_address (tarray t size) (SUB i) p = offset_val (sizeof t * i) p.
Proof.
  intros t size p i Hcomp Hi.
  unfold field_address. destruct (field_compatible_dec (tarray t size) [ArraySubsc i] p).
  simpl. auto. exfalso. apply n. apply arr_field_compatible; auto.
Qed.

(*Useful for proving that pointers are valid for conditionals*)
Lemma isptr_denote_tc_test_order: forall p1 p2,
  isptr p1 ->
  isptr p2 ->
  denote_tc_test_order p1 p2 = test_order_ptrs p1 p2.
Proof.
  intros p1 p2 Hptr1 Hptr2. destruct p1; destruct Hptr1. destruct p2; destruct Hptr2. reflexivity.
Qed.

Lemma isptr_offset_val_sameblock : forall p i,
  isptr p ->
  sameblock p (offset_val i p) = true.
Proof.
  intros. destruct p; destruct H.
  simpl. unfold proj_sumbool. apply peq_true.
Qed.

Lemma sameblock_refl : forall p,
  isptr p ->
  sameblock p p = true.
Proof.
  intros.
  destruct p; destruct H. apply peq_true.
Qed.

Lemma sameblock_symm : forall p1 p2,
  sameblock p1 p2 = true ->
  sameblock p2 p1 = true.
Proof.
  intros.
  destruct p1; destruct p2; try discriminate.
  simpl in *. destruct (peq b b0); try discriminate.
  subst.
  apply peq_true.
Qed.

Lemma sameblock_trans : forall p1 p2 p3,
  sameblock p1 p2 = true ->
  sameblock p2 p3 = true->
  sameblock p1 p3 = true.
Proof.
  intros.
  destruct p1; try discriminate.
  destruct p2; try discriminate.
  destruct p3; try discriminate.
  simpl in *.
  destruct (peq b b0); try discriminate.
  destruct (peq b0 b1); try discriminate.
  subst.
  apply peq_true.
Qed.

Lemma sameblock_offset_val: forall p n1 n2,
  isptr p ->
  sameblock (offset_val n1 p) (offset_val n2 p) = true.
Proof.
  intros p n1 n2 Hptr. eapply sameblock_trans. eapply sameblock_symm. 
  all: apply isptr_offset_val_sameblock; auto.
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

(*Switch Cgt and Clt*)
Lemma cgt_clt_ptr: forall p1 p2,
  sem_cmp_pp Cgt p1 p2 = sem_cmp_pp Clt p2 p1.
Proof.
  intros p1 p2. unfold sem_cmp_pp. simpl. f_equal. unfold Val.cmplu_bool.
  destruct p1; destruct p2; auto. destruct (Archi.ptr64); auto; simpl.
  destruct (eq_block b b0). subst. destruct (eq_block b0 b0); try contradiction.
  reflexivity. destruct (eq_block b0 b); subst; auto. contradiction.
Qed.

(*Same for the lt case. This is an easy corollary of the above 2 lemmas*)
Lemma ptr_comparison_lt_iff: forall t size p i j,
  field_compatible (tarray t size) [] p ->
  0 <= i <= size ->
  0 <= j <= size ->
  0 < sizeof t ->
  isptr p ->
  typed_true tint (force_val (sem_cmp_pp Clt (field_address0 (tarray t size) (SUB i) p)
    (field_address0 (tarray t size) (SUB j) p))) <-> i < j. 
Proof.
  intros t sz p i j Hcompat Hi Hj Ht Hptr. rewrite <- cgt_clt_ptr.
  rewrite ptr_comparison_gt_iff by auto. lia.
Qed.


(** Working with 2D Arrays*)

(*We can consider an instance of t at position p to be a valid array of length 1 at p*)
Lemma data_at_array_len_1: forall sh t a p,
data_at sh t a p |-- !! field_compatible (tarray t 1) [] p.
Proof.
  intros. erewrite <- data_at_singleton_array_eq. 2: reflexivity. entailer!.
Qed.

(*The crucial lemma for showing the relationship between 1D and 2D arrays: if we move over 1 array (in the 2D array)
  or m places (in the 1D array), the result is still compatible*)
Lemma field_compatible0_1d_2d: forall n m t p,
  0 <= m ->
  0 < n ->
  field_compatible (Tarray t m noattr) [] p ->
  (field_compatible0 (tarray (tarray t m) n)) [ArraySubsc 1] p <->
  (field_compatible0 (tarray t (n * m)) [ArraySubsc m] p).
Proof.
  intros n m t p Hm Hn Hfst.
  unfold field_compatible in Hfst. unfold field_compatible0.
  simpl in *. destruct Hfst as [Hptr1 [Hleg1 [Hszc1 [Hal1 Hlegn1]]]].
  clear Hlegn1.
  (*The interesting part*)
  assert (size_compatible (tarray (tarray t m) n) p /\ align_compatible (tarray (tarray t m) n) p <->
    size_compatible (tarray t (n * m)) p /\ align_compatible (tarray t (n * m)) p ). {
   unfold size_compatible. destruct p; inversion Hptr1. simpl in *.
    replace (Z.max 0 m) with m by lia.
    replace (Z.max 0 n) with n by lia.
    replace (Z.max 0 (n * m)) with (m * n) by lia.
    rewrite Z.mul_assoc. split; intros [Hszc2 Hal2].
    - split. assumption. inversion Hal2; subst. inversion H.
      inversion Hal1; subst. inversion H.
      apply align_compatible_rec_Tarray. intros j Hj.
      assert (m = 0 \/ m > 0) by lia. destruct H as [H | Hm0]. subst. lia.
      assert (0 <= j < m \/ m <= j < n * m) by lia. destruct H as [Hfst | Hrest].
      + specialize (H4 _ Hfst). apply H4.
      + (*To index into the rest of the array, we need to use j/ m and j %m, which gives lots of annoying proof obligations*)
        assert (0 <= j / m  < n). { split. assert (1 <= j / m). rewrite <- (Z_div_same _ Hm0).
        apply Z_div_le; lia. lia. apply Z.div_lt_upper_bound; lia. }
        specialize (H3 _ H). clear H4. inversion H3; subst. inversion H0.
        assert (0 <= j mod m < m). { apply Z.mod_pos_bound; lia. }
        specialize (H5 _ H0). replace (Ptrofs.unsigned i + Ctypes.sizeof t * j) with
        (Ptrofs.unsigned i + Ctypes.sizeof (tarray t m) * (j / m) + Ctypes.sizeof t * (j mod m)). apply H5.
        rewrite <- !Z.add_assoc. f_equal. simpl Ctypes.sizeof. replace (Z.max 0 m) with m by lia.
        rewrite <- Z.mul_assoc. rewrite <- Z.mul_add_distr_l. f_equal.
        replace (Z.max 0 m) with m by lia.
        rewrite <- Z_div_mod_eq. reflexivity. lia.
    - split. assumption. inversion Hal2; subst. inversion H.
      inversion Hal1; subst. inversion H.  apply align_compatible_rec_Tarray. intros j Hj.
      apply align_compatible_rec_Tarray. intros k Hk.
      assert (0 = j \/ 1 <= j) by lia. destruct H as [Hfst | Hrest].
      + subst. rewrite Z.mul_0_r. rewrite Z.add_0_r. apply H4. apply Hk.
      + assert (0 = m \/ 0 < m) by lia. destruct H as [H | Hm0]. lia.
        assert (0 <= j * m + k < n * m). { split; try lia.
        assert (j * m + k < j * m + m) by lia. replace (j * m + m) with ((j+1) * m) in H by lia.
        assert ((j+1) * m <= n * m). apply Zmult_le_compat_r; lia. lia. } 
        specialize (H3 _ H). simpl. replace ( Z.max 0 m ) with m by lia.
        replace (Ptrofs.unsigned i + Ctypes.sizeof t * m * j + Ctypes.sizeof t * k) with 
        (Ptrofs.unsigned i + Ctypes.sizeof t * (j * m + k)). apply H3. rewrite <- !Z.add_assoc. f_equal.
        rewrite <- Z.mul_assoc. rewrite <- Z.mul_add_distr_l. f_equal. lia. }
  split; intros [Hptr2 [Hleg2 [Hszc2 [Hal2 [Hlegn2 Hbound2]]]]].
  repeat(split; auto). apply H. split; auto.
  apply H. split; auto. replace m with (1 * m) at 1 by lia. apply Z.mul_le_mono_nonneg_r; lia.
  repeat(split; auto). apply H. split; auto. apply H; split; auto. lia. lia.
Qed.

(*The full relationship between 1D and 2D arrays*)
Lemma data_at_2darray_concat : forall sh t n m (al : list (list (reptype t))) p,
  Zlength al = n ->
  Forall (fun l => Zlength l = m) al ->
  complete_legal_cosu_type t = true ->
  data_at sh (tarray (tarray t m) n) al p
    = data_at sh (tarray t (n * m)) (concat al) p.
Proof.
  intros.
  generalize dependent n; generalize dependent p; induction al; intros.
  - simpl. replace n with 0 by list_solve. rewrite Z.mul_0_l. 
    apply pred_ext; entailer!; rewrite !data_at_zero_array_eq; auto.
  - rewrite Zlength_cons in H. simpl. assert (Hmlen: Zlength a = m) by (inversion H0; subst; reflexivity).
    apply pred_ext.
    + (*We will need these later, when we have transformed the [data_at] predicates, so they are harder to prove*)
      assert_PROP (field_compatible (tarray (tarray t m) (Z.succ (Zlength al))) [] p). { entailer!. }
      assert_PROP (field_compatible0 (tarray (tarray t m) n) [ArraySubsc 1] p). { entailer!.
        apply arr_field_compatible0. auto. list_solve. }
      change (a :: al) with ([a] ++ al). 
      change (list (reptype t)) with (reptype (tarray t m)) in a.
      rewrite (split2_data_at_Tarray_app 1 _ _ _ [a]). 2: Zlength_solve.
      change (reptype (tarray t m)) with  (list (reptype t)) in a. 2: { rewrite <- H.
      assert (forall x, x = Z.succ x - 1). intros; lia. apply H4. }
      rewrite (split2_data_at_Tarray_app m).
      replace (n * m - m) with ((n-1) * m) by lia.
      erewrite data_at_singleton_array_eq. 2: reflexivity.
      assert (Hm: 0 <= m). rewrite <- Hmlen. list_solve.
      entailer!. rewrite !field_address0_clarify; auto.
      simpl. unfold sizeof. rewrite <- Z.mul_assoc.
      replace (Z.max 0 (Zlength a) * 1) with (Zlength a) by lia. rewrite IHal. cancel.
      inversion H0; subst; auto. lia. unfold field_address0.
      rewrite field_compatible0_1d_2d in H3.
      destruct (field_compatible0_dec (tarray t (Z.succ (Zlength al) * Zlength a)) [ArraySubsc (Zlength a)] p); [| contradiction].
    apply isptr_is_pointer_or_null; auto. list_solve. list_solve. auto.
    inversion H0; subst; reflexivity.
    rewrite (Zlength_concat (n-1) m). lia. list_solve. inversion H0; auto.
    + assert_PROP ((field_compatible0 (tarray t (n * m)) [ArraySubsc m] p)). { entailer!.
      apply arr_field_compatible0. apply H2.
       split. list_solve. rewrite <- (Z.mul_1_l (Zlength a)) at 1. apply Z.mul_le_mono_nonneg_r; list_solve. }
      change (a :: al) with ([a] ++ al). 
      change (list (reptype t)) with (reptype (tarray t m)) in a.
      rewrite (split2_data_at_Tarray_app 1 _ _ _ [a]). 2: Zlength_solve.
      change (reptype (tarray t m)) with  (list (reptype t)) in a. 2: { rewrite <- H.
      assert (forall x, x = Z.succ x - 1). intros; lia. apply H3. }
      rewrite (split2_data_at_Tarray_app m). 2: auto.
      replace (n * m - m) with ((n-1) * m) by lia.
      erewrite data_at_singleton_array_eq. 2: reflexivity.
      assert (Hm: 0 <= m). rewrite <- Hmlen. list_solve.
      entailer!. rewrite !field_address0_clarify; auto.
      simpl. unfold sizeof. rewrite <- Z.mul_assoc.
      replace (Z.max 0 (Zlength a) * 1) with (Zlength a) by lia. rewrite IHal. cancel.
      inversion H0; subst; auto. lia. unfold field_address0.
      rewrite <- field_compatible0_1d_2d in H2.
      destruct (field_compatible0_dec (tarray (tarray t (Zlength a)) (Z.succ (Zlength al))) [ArraySubsc 1] p); [| contradiction].
      apply isptr_is_pointer_or_null; auto. list_solve. list_solve. auto.
      rewrite (Zlength_concat (n-1) m). lia. list_solve. inversion H0; auto.
Qed.

(** Working with Arrays of Pointers*)

(*Represents the fact that there is a list of pointers (ptrs), and the contents of those pointers
  are described by contents - in essence, a 2D array with possibly different lengths*)
(*For now, only defined for tuchar, could extend to other int types*)
Definition iter_sepcon_arrays (ptrs : list val) (contents: list (list byte)) := 
  iter_sepcon (fun (x: (list byte * val)) => let (l, ptr) := x in 
            data_at Ews (tarray tuchar (Zlength l)) (map Vubyte l) ptr) (combine contents ptrs).

Lemma iter_sepcon_arrays_Znth: forall ptrs contents i,
  Zlength ptrs = Zlength contents ->
  0 <= i < Zlength contents ->
  iter_sepcon_arrays ptrs contents |-- 
    data_at Ews (tarray tuchar (Zlength (Znth i contents))) (map Vubyte (Znth i contents)) (Znth i ptrs) * TT.
Proof.
  intros ptrs contents i Hlen Hi. unfold iter_sepcon_arrays. 
  sep_apply (iter_sepcon_in_true (fun x : list byte * val => let (l, ptr) := x in 
    data_at Ews (tarray tuchar (Zlength l)) (map Vubyte l) ptr) (combine contents ptrs) 
    (Znth i contents, Znth i ptrs)); [|cancel].
  rewrite In_Znth_iff. exists i. split. rewrite combine_Zlength; lia.
  apply combine_Znth; lia.
Qed.

Lemma remove_lead_eq: forall {A: Type} (P: Prop) (x: A),
  (x = x -> P) <-> P.
Proof.
  intros. tauto.
Qed.


(*We don't actually use this, but we prove a [local_facts] so that we could use this with entailer! if we wanted*)
Lemma iter_sepcon_arrays_local_facts: forall ptrs contents,
  iter_sepcon_arrays ptrs contents |-- !! (Zlength ptrs = Zlength contents -> 
        forall i, 0 <= i < Zlength contents ->
         field_compatible (tarray tuchar (Zlength (Znth i contents))) [] (Znth i ptrs) /\
         Forall (value_fits tuchar) (map Vubyte (Znth i contents))).
Proof.
  intros ptrs contents. 
  assert (Zlength ptrs = Zlength contents \/ Zlength ptrs <> Zlength contents) as [Heq | Hneq] by lia; 
  [ | entailer!]. rewrite Heq. rewrite remove_lead_eq. eapply derives_trans. 2:
  apply (@allp_prop_left _ _ Z (fun (i: Z) => 0 <= i < Zlength contents ->
        field_compatible (tarray tuchar (Zlength (Znth i contents))) [] (Znth i ptrs) /\
        Forall (value_fits tuchar) (map Vubyte (Znth i contents)))).
  apply allp_right. intros i.
  (*This is not particularly elegant; is there a way to get an implication out directly?*)
  assert (0 <= i < Zlength contents \/ ~ (0 <= i < Zlength contents)) as [Hlt | Hgt] by lia; [| entailer ].
  (*why doesn't entailer! work?*)
  sep_apply (iter_sepcon_arrays_Znth _ _ _ Heq Hlt).
  assert (forall m P Q, P -> (m |-- !! Q) -> (m |-- !! (P -> Q))). { intros. sep_apply H. entailer!. }
  apply H. assumption. entailer!.
Qed.

(*We would also like another, more general fact. For [iter_sepcon] that gives an mpred 
  as well as [iter_sepcon_arrays]), we can remove
  the nth element and keep the rest*)

(*An easier definition than [delete_nth], since it uses Z and there are lots of lemmas/automation about sublist*)
Definition remove_nth {A: Type} (n: Z) (l: list A): list A :=
  sublist 0 n l ++ sublist (n+1) (Zlength l) l.

Lemma iter_sepcon_remove_one: forall {B : Type} `{Inhabitant B} (p: B -> mpred) (l: list B) (n: Z),
  0 <= n < Zlength l ->
  iter_sepcon p l = ((p (Znth n l)) * iter_sepcon p (remove_nth n l))%logic.
Proof.
  intros B Hinhab p l n Hn. unfold remove_nth. rewrite <- (sublist_same 0 (Zlength l) l) at 1 by auto.
  rewrite (sublist_split 0 n (Zlength l) l) by lia.
  rewrite (sublist_split n (n+1) (Zlength l) l) by lia. rewrite !iter_sepcon_app.
  rewrite sublist_len_1 by lia. simpl. apply pred_ext; cancel.
Qed.

Lemma combine_remove_nth: forall {A B: Type} `{Inhabitant A} `{Inhabitant B} n (l1: list A) (l2: list B),
  Zlength l1 = Zlength l2 ->
  0 <= n < Zlength l1 ->
  combine (remove_nth n l1) (remove_nth n l2) = remove_nth n (combine l1 l2).
Proof.
  intros A B Hinh1 Hinh2 n l1 l2 Hlens Hn.
  unfold remove_nth. rewrite combine_app by list_solve. rewrite Hlens. rewrite !combine_sublist by lia.
  rewrite combine_Zlength by lia. rewrite Hlens. reflexivity.
Qed.

Lemma iter_sepcon_arrays_remove_one: forall ptrs contents i,
  Zlength ptrs = Zlength contents ->
  0 <= i < Zlength contents ->
  iter_sepcon_arrays ptrs contents = 
    (data_at Ews (tarray tuchar (Zlength (Znth i contents))) (map Vubyte (Znth i contents)) (Znth i ptrs) *
    iter_sepcon_arrays (remove_nth i ptrs) (remove_nth i contents))%logic.
Proof.
  intros ptrs contents i Hlens Hi. unfold iter_sepcon_arrays. rewrite (iter_sepcon_remove_one _ _ i).
  rewrite combine_Znth by auto. f_equal. rewrite combine_remove_nth by lia. reflexivity.
  rewrite combine_Zlength; lia.
Qed.

Lemma remove_upd_Znth: forall {A: Type} (l: list A) (i : Z) (x: A),
  0 <= i < Zlength l ->
  remove_nth i (upd_Znth i l x) = remove_nth i l.
Proof. 
  intros. unfold remove_nth.  
  rewrite sublist_upd_Znth_l; try lia.
  rewrite !sublist_upd_Znth_r; try lia; list_solve.
Qed. 

(* We want a similar definition for when only some of the data exists, and the others are null pointers*)

Definition iter_sepcon_options (ptrs: list val) (contents: list (option (list byte))) : mpred :=
  iter_sepcon (fun (x: option (list byte) * val) => let (o, ptr) := x in
    match o with
      | None => emp
      | Some l => data_at Ews (tarray tuchar (Zlength l)) (map Vubyte l) ptr
    end) (combine contents ptrs).

Lemma iter_sepcon_options_remove_one: forall ptrs contents i l,
  Zlength ptrs = Zlength contents ->
  0 <= i < Zlength contents ->
  Znth i contents = Some l ->
  iter_sepcon_options ptrs contents = 
    (data_at Ews (tarray tuchar (Zlength l)) (map Vubyte l) (Znth i ptrs) *
    iter_sepcon_options (remove_nth i ptrs) (remove_nth i contents))%logic.
Proof.
  intros ptrs contents i l Hlens Hi Hnth. unfold iter_sepcon_options. rewrite (iter_sepcon_remove_one _ _ i).
  destruct (Znth i (combine contents ptrs)) as [o ptr] eqn : Hnth'.
  rewrite combine_Znth in Hnth' by auto. inversion Hnth'; subst. rewrite Hnth.
  rewrite combine_remove_nth by lia. reflexivity. rewrite combine_Zlength; lia.
Qed.

End VSTFacts.
