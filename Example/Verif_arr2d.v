Require Import VST.floyd.proofauto.
Require Import arr2d.
Open Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs.
make_compspecs prog. Defined.

Definition Vprog : varspecs.
mk_varspecs prog. Defined.

Definition ith_spec :=
  DECLARE _ith
  WITH a: val, sh : share, contents : list Z, size: Z, i : Z
  PRE [ tptr tint, tint, tint ]
    PROP (readable_share sh; 0 <= size <= Int.max_signed;
         Forall (fun x => 0 <= x <= Int.max_unsigned) contents; 0 <= i < size)
    PARAMS (a; Vint (Int.repr i); Vint (Int.repr size))
    SEP (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a)
 POST [ tint ]
    PROP () RETURN (Vint (Int.repr (Znth i contents)))
    SEP (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a).

Definition main_spec :=
  DECLARE _main
  WITH gv : globals
  PRE [ ] main_pre prog tt gv
  POST [tint]
    PROP ()
    RETURN (Vint (Int.repr 5))
    SEP (TT).
  

Definition Gprog := [ith_spec; main_spec].

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  forward. unfold default_val; simpl. unfold Znth; simpl. unfold upd_Znth; simpl.
  unfold sublist; simpl.
  replace (Vundef) with (Vint Int.zero) by admit.
 forward_call (gv _arr, Ews, [0; 0; 0; 0; 0; 0; 5; 0; 0; 0; 0] , 12, 6).
  - entailer!.
    (*key step*)
 unfold field_compatible in H.
    destruct H as [Hptr [Hleg [Hsz [Hal Hnest]]]].
    simpl in *.
    (*This is the core of the problem - how to go from 2D array to 1D array?*)

 Search value_fits.
    Print ArraySubsc. tarray.
    Search (tarray (tarray ?t ?i) ?j).