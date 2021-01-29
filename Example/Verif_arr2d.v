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

Require Import VST.msl.iter_sepcon.

Ltac list_solve_preprocess ::=
  fold_Vbyte; autounfold with list_solve_unfold in *; autorewrite with
   list_solve_rewrite in *; repeat match goal with
                                   | |- _ /\ _ => split
                                   end; intros.

Fixpoint array_pointers_nat t p n :=
  match n with
  | O => []
  | S n' => p :: (array_pointers_nat t (offset_val (sizeof t) p) n')
  end.

Definition array_pointers t p n :=
  array_pointers_nat t p (Z.to_nat n).

Lemma array_pointers_unfold t p n :
  0 < n ->
  array_pointers t p n = p :: (array_pointers t (offset_val (sizeof t) p) (n-1)).
Admitted.

Lemma data_at_array_iter_sepcon : forall sh t n al p,
  0 <= n ->
  complete_legal_cosu_type t = true ->
  data_at sh (tarray t n) al p
    = iter_sepcon (fun (vp : reptype t * val) => let (v, p) := vp in data_at sh t v p)
          (combine al (array_pointers t p n)).
Proof.
  intros.
  change (reptype (tarray t n)) with (list (reptype t)) in al.
  apply pred_ext.
  - generalize dependent n; generalize dependent p; induction al; intros.
    + entailer!. rewrite Zlength_nil.
      sep_apply data_at_zero_array_inv.
      auto.
    + assert_PROP (Zlength (a :: al) = n). { entailer!. }
      assert_PROP (field_address0 (tarray t n) [ArraySubsc 1] p
          = offset_val (sizeof t) p).
      {
        entailer!.
        unfold field_address0.
        destruct (field_compatible0_dec _ _).
        admit. admit.
      }
      rewrite Zlength_cons in H1.
      change (a :: al) with ([a] ++ al).
      rewrite (split2_data_at_Tarray_app 1) by Zlength_solve.
      assert (Zlength al >= 0) by Zlength_solve.
      rewrite array_pointers_unfold by lia.
      simpl iter_sepcon.
      sep_apply data_at_singleton_array_eq. cancel.
      rewrite H2.
      apply IHal.
      lia.
  - admit.
Admitted.

Lemma data_at_2darray_concat : forall sh t n m (al : list (list (reptype t))) p,
  0 <= n ->
  0 <= m ->
  Zlength al = n ->
  Forall (fun l => Zlength l = m) al ->
  complete_legal_cosu_type t = true ->
  data_at sh (tarray (tarray t m) n) al p
    = data_at sh (tarray t (n * m)) (concat al) p.
Proof.
  intros.
  change (list (list (reptype t))) with (list (reptype (tarray t m))) in al.
  apply pred_ext.
  - generalize dependent n; generalize dependent p; induction al; intros.
    + entailer!. rewrite Zlength_nil.
      sep_apply data_at_zero_array_inv.
      simpl. replace (0 * m) with 0 by lia.
      rewrite data_at_zero_array_eq; auto.
    + assert_PROP (field_address0 (tarray (tarray t m) n) [ArraySubsc 1] p
          = offset_val (sizeof (tarray t m)) p).
      {
        entailer!.
        unfold field_address0.
        destruct (field_compatible0_dec _ _).
        admit.
        admit.
      }
      rewrite Zlength_cons in H1.
      change (a :: al) with ([a] ++ al).
      rewrite (split2_data_at_Tarray_app 1) by Zlength_solve.

      simpl concat.
      change (reptype (tarray t m)) with (list (reptype t)) in a, al.
      rewrite (split2_data_at_Tarray_app m) by admit.
Admitted.

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