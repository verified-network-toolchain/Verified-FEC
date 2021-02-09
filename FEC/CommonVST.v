Require Import VST.floyd.proofauto.
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
        rewrite <- !Z.add_assoc. f_equal. simpl. rewrite <- Z.mul_assoc. rewrite <- Z.mul_add_distr_l. f_equal.
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

End VSTFacts. 