Require Import VST.floyd.proofauto.
Require Import sumarray_ptr.

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

Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
  start_function. forward. forward. forward.
  
  forward_while
  (EX i: Z,
   PROP (0 <= i <= size)
   LOCAL (temp _end (force_val (sem_binary_operation' Oadd (tptr tuint) tint a (Vint (Int.repr size))));
      temp _curr (force_val (sem_binary_operation' Oadd (tptr tuint) tint a (Vint (Int.repr i))));
      temp _a a; temp _n (Vint (Int.repr size));
      temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
   SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).
  - Exists 0%Z. entailer!.
  - (*entailer!. simpl. Search denote_tc_test_order. rewrite isptr_denote_tc_test_order. *) 
Admitted.