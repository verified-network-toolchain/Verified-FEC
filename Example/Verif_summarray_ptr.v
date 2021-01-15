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
  destruct p; destruct H.
  simpl.
  apply peq_true.
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
Admitted.