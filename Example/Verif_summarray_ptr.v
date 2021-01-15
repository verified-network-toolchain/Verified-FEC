Require Import VST.floyd.proofauto.
Require Import sumarray_ptr.

Open Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs.
make_compspecs prog. Defined.

Definition Vprog : varspecs.
mk_varspecs prog. Defined.

Definition sum_Z : list Z -> Z := fold_right Z.add 0.

Lemma sum_Z_app:
  forall a b, sum_Z (a++b) = sum_Z a + sum_Z b.
Proof.
  intros. induction a; simpl; lia.
Qed.

Definition sumarray_spec :=
  DECLARE _sumarray
  WITH a: val, sh : share, contents : list Z, size: Z
  PRE [ tptr tuint, tint ]
    PROP (readable_share sh; 0 <= size <= Int.max_signed;
         Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
    PARAMS (a; Vint (Int.repr size))
    SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
 POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (sum_Z contents)))
    SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

Definition Gprog := [sumarray_spec].

Print denote_tc_test_order.

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

Lemma clt_ptr_antirefl: forall p,
  isptr p ->
~typed_true tint
        (force_val
           (sem_cmp_pp Clt p p)).
Proof.
  intros p Hptr. rewrite force_sem_cmp_pp; auto.
  unfold compare_pp. destruct p; try inversion Hptr. simpl.
  destruct (eq_block b b). assert (Hlu: Ptrofs.ltu i i = false). unfold Ptrofs.ltu.
  destruct (zlt (Ptrofs.unsigned i) (Ptrofs.unsigned i)). lia. reflexivity. rewrite Hlu.
  unfold typed_true. simpl. intro C; inversion C. auto.
Qed.

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

Lemma lt_plus_lt: forall z1 z2 z3, 
  0 <= z1 -> 
  z1 + z2 < z3 -> 
  z2 < z3.
Proof.
  intros z1 z2 z3 Hz1 Hz12. rewrite Z.lt_add_lt_sub_r in Hz12. lia.
Qed.

(*Very annoying to prove. TODO: maybe make more general ; ie, for general offset_val?*)
Lemma ptr_comparison_iff: forall t size p i j,
  field_compatible (tarray t size) [] p ->
  0 <= i <= size ->
  0 <= j <= size ->
  0 < sizeof t -> 
  isptr p ->
  typed_true tint
        (force_val
           (sem_cmp_pp Clt (field_address0 (tarray t size) (SUB i) p)
              (field_address0 (tarray t size) (SUB j) p))) <-> i < j.
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
  assert (sameblock (Vptr b i0) (Vptr b0 i1) = true). rewrite <- Fi. rewrite <- Fj.
  rewrite !arr_field_address0; auto. eapply sameblock_trans.
  2: apply isptr_offset_val_sameblock. apply sameblock_symm. apply isptr_offset_val_sameblock.
  all: auto. simpl in H. unfold eq_block. destruct (peq b b0); try inversion H. subst.
  simpl. rewrite arr_field_address0 in Fi; auto. rewrite arr_field_address0 in Fj; auto.
  destruct p; inversion Hptr. simpl in *. inversion Fi; subst. inversion Fj; subst.
  clear Fi Fj H Hptr. unfold Ptrofs.ltu.
  assert (Hi2 : 0 <= Ptrofs.unsigned i2) by rep_lia. unfold field_compatible in Hcomp. simpl in Hcomp. 
  destruct Hcomp as [Ht [Hcomp [HHsz Hrest]]].
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
    destruct (zlt (Ptrofs.unsigned i2 + Ptrofs.unsigned (Ptrofs.repr (sizeof t * i)))
          (Ptrofs.unsigned i2 + Ptrofs.unsigned (Ptrofs.repr (sizeof t * j)))).
    - assert (Hptrlt: Ptrofs.unsigned (Ptrofs.repr (sizeof t * i)) < Ptrofs.unsigned (Ptrofs.repr (sizeof t * j))) by lia.
      clear l. unfold Ptrofs.unsigned in Hptrlt. simpl in Hptrlt. rewrite !Ptrofs.Z_mod_modulus_eq in Hptrlt.
      rewrite !Zmod_small in Hptrlt. rewrite <- Z.mul_lt_mono_pos_l in Hptrlt; auto. all: try apply Hij; auto.
      split; intros; auto. reflexivity.
    - assert (Hptrlt: Ptrofs.unsigned (Ptrofs.repr (sizeof t * j)) <= Ptrofs.unsigned (Ptrofs.repr (sizeof t * i))) by lia.
      clear g. unfold Ptrofs.unsigned in Hptrlt. simpl in Hptrlt. rewrite !Ptrofs.Z_mod_modulus_eq in Hptrlt.
      rewrite !Zmod_small in Hptrlt. rewrite <- Z.mul_le_mono_pos_l in Hptrlt; auto. all: try apply Hij; auto.
      split; intros; try lia. inversion H.
Qed.

Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
  start_function. forward. forward. forward. Search valid_pointer.
  assert (0 < size) by admit. (*I think we need this because we do reference the pointer a, so it cannot 
    point to a 0 length array (unlike the array version, which just compares indices*)
  forward_while
  (EX (i: Z),
   PROP (0 <= i <= size)
   LOCAL (temp _end (field_address0 (tarray tuint size) (SUB size) a);
      temp _curr (field_address0 (tarray tuint size) (SUB i) a);
      temp _a a; temp _n (Vint (Int.repr size));
      temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
   SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).
  - Exists 0. entailer!. split. simpl. apply arr_field_address0; auto. list_solve.
    rewrite arr_field_address0; auto. simpl. rewrite isptr_offset_val_zero; auto. list_solve.
  - entailer!. rewrite !arr_field_address0; auto. simpl.
    rewrite isptr_denote_tc_test_order; auto. unfold test_order_ptrs.
    assert (Hsame: sameblock (offset_val (4 * i) a) 
        (offset_val (4 * Zlength (map Vint (map Int.repr contents))) a) = true). {
    eapply sameblock_trans. 2: apply isptr_offset_val_sameblock. apply sameblock_symm.
    apply isptr_offset_val_sameblock. all: auto. } simpl_reptype. rewrite Hsame.
    sep_apply data_at_memory_block.
    apply andp_right.
    + sep_eapply memory_block_weak_valid_pointer. 4: apply derives_refl.
      simpl. list_solve. simpl. list_solve. auto.
    + sep_eapply memory_block_weak_valid_pointer. 4: eapply derives_refl.
      simpl. list_solve. simpl. list_solve. auto.
    +  list_solve.
  - assert_PROP ((0 <= i < Zlength (map Int.repr contents))). {
    entailer!. simpl_reptype. rewrite ptr_comparison_iff in HRE; auto; try lia.
    list_solve. simpl. lia. }
    assert_PROP ((field_address0 (tarray tuint size) [ArraySubsc i] a) = (field_address (tarray tuint size) [ArraySubsc i] a)).
    entailer!. rewrite arr_field_address0; auto. rewrite arr_field_address; auto. list_solve.
    assert (Hlen: 0 <= i < Zlength contents) by list_solve. 
    forward. entailer!. rewrite arr_field_address0; auto. 
    forward. forward. entailer!. rewrite arr_field_address0; auto. Exists (i+1). entailer!.
    split. list_solve. split. rewrite !arr_field_address0; auto. simpl. rewrite sem_add_pi_ptr_special; auto; try rep_lia.
    simpl. rewrite offset_offset_val. f_equal. lia. list_solve. 
    f_equal. f_equal. rewrite sublist_last_1; try lia. rewrite sum_Z_app. simpl. lia.
  - forward. assert ( ~(i <  Zlength (map Vint (map Int.repr contents)))). intro C.
    rewrite <- ptr_comparison_iff in C; auto. unfold typed_false in HRE. unfold typed_true in C.
    rewrite C in HRE. inversion HRE. all: auto. list_solve. simpl; lia. 
    assert (Hi: i = Zlength (map Vint (map Int.repr contents))). simpl_reptype; lia. clear H7.
    rewrite Hi. entailer!. rewrite sublist_same; try reflexivity. list_solve.
Admitted.

  
(*(Partial) alternate version that uses [offset_val] rather than [field_address]*)
(*
Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
  start_function. forward. forward. forward.
  (*Is this the right way to refer to curr?*)
  assert (0 < size) by admit.
  forward_while
  (EX (i: Z),
   PROP (0 <= i <= size)
   LOCAL (temp _end (offset_val (size * 4) a);
      temp _curr (offset_val (i * 4) a);
      temp _a a; temp _n (Vint (Int.repr size));
      temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
   SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).
  - Exists 0%Z. entailer!. simpl sizeof. list_solve.
  - entailer!. rewrite isptr_denote_tc_test_order; auto.
    unfold test_order_ptrs. simpl.
    assert (Hsameblock : sameblock (offset_val (i * 4) a)
      (offset_val (Zlength (map Vint (map Int.repr contents)) * 4) a) = true). {
      apply sameblock_trans with a.
      apply sameblock_symm. apply isptr_offset_val_sameblock. apply H5.
      apply isptr_offset_val_sameblock. apply H5.
    }
    simpl_reptype.
    rewrite Hsameblock.
    sep_apply data_at_memory_block.
    apply andp_right.
    + sep_eapply memory_block_weak_valid_pointer.
      * instantiate (1 := (i * 4)).
        simpl. list_solve.
      * simpl. list_solve.
      * apply readable_nonidentity; auto.
      * auto.
    + sep_eapply memory_block_weak_valid_pointer.
      * instantiate (1 := (Zlength contents) * 4).
        simpl. list_solve.
      * simpl. list_solve.
      * apply readable_nonidentity; auto.
      * list_solve.
  - assert_PROP ((0 <= i < Zlength (map Int.repr contents))). {
    entailer!. simpl_reptype. remember (Zlength (map Vint (map Int.repr contents))) as size.
    assert (i = size \/ i < size) by lia. destruct H7.
    subst. exfalso. eapply (clt_ptr_antirefl). 2: apply HRE. auto. list_solve. } 
    assert_PROP (field_compatible (tarray tuint size) (SUB i) a). { entailer!.
    unfold field_compatible in *. destruct H6 as [Hptr [Hleg [Hsz [Hal Hnest]]]].
    repeat(split; try auto). lia. list_solve. }
    assert (offset_val (i * 4) a = field_address (tarray tuint size) (SUB i) a). {
    unfold field_address. destruct (field_compatible_dec (tarray tuint size) [ArraySubsc i] a).
    2: contradiction. simpl. f_equal. lia. }
    assert (0 <= i < Zlength contents) by list_solve.
    forward. forward. forward. Exists (i+1). entailer!. split. list_solve. split. simpl. f_equal. lia.
    f_equal. f_equal. rewrite sublist_last_1; try lia. rewrite sum_Z_app. simpl. lia.
  - forward. entailer!. rewrite sublist_same; try lia. reflexivity.
    (*Come back to this if [field_address] method doesn't work as well*)
*)
