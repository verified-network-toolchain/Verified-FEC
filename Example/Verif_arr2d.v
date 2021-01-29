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

(*duplicated*)
(*Useful utility lemmas from example*)
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


(*
Print Ltac list_solve_preprocess.

Ltac list_solve_preprocess ::=
  fold_Vbyte; autounfold with list_solve_unfold in *; autorewrite with
   list_solve_rewrite in *; repeat match goal with
                                   | |- _ /\ _ => split
                                   end; intros.
*)
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
Proof.
  intros Hn. unfold array_pointers.
  replace (Z.to_nat n) with (S(Z.to_nat (n-1))) by lia. reflexivity.
Qed. 

(*We can consider an instance of t at position p to be a valid array of length 1 at p*)
Lemma data_at_array_len_1: forall sh t a p,
data_at sh t a p |-- !! field_compatible (tarray t 1) [] p.
Proof.
  intros. entailer!. unfold field_compatible in *; simpl in *.
  destruct H as [Hptr [Hleg [Hsz [Hal Ht]]]]. repeat(split; auto).
  unfold size_compatible in *. destruct p; auto. simpl. unfold sizeof in Hsz.
  replace (Ctypes.sizeof t * 1) with (Ctypes.sizeof t) by (rewrite <- Zred_factor0; reflexivity).
  assumption. Print align_compatible_rec. unfold align_compatible in *. destruct p; auto. simpl. 
  apply align_compatible_rec_Tarray. intros.
  replace (i0) with 0 by lia. rewrite Z.mul_0_r. rewrite Z.add_0_r. apply Hal.
Qed.

(* If we have an array, we also have the data for each of the individual elements at the appropriate offsets*)
(*The reverse direction is complicated to prove since we need to show that the array [field_compatible] conditions
  are met*)
Lemma data_at_array_iter_sepcon : forall sh t n (al : list (reptype t)) p,
  isptr p ->
  Zlength al = n ->
  complete_legal_cosu_type t = true ->
  data_at sh (tarray t n) al p
    = iter_sepcon (fun (vp : reptype t * val) => let (v, p) := vp in data_at sh t v p)
          (combine al (array_pointers t p n)).
Proof.
  intros sh t n al p Hptr Hlen Hleg.
  generalize dependent n; generalize dependent p; induction al; intros.
  - simpl. replace n with 0 by list_solve. rewrite data_at_zero_array_eq; auto.
  - rewrite Zlength_cons in Hlen. assert (Hallen: 0 <= Zlength al) by list_solve.  
    rewrite array_pointers_unfold by lia. simpl.
    apply pred_ext.
    + assert_PROP (field_address0 (tarray t n) [ArraySubsc 1] p
          = offset_val (sizeof t) p).
      { entailer!. rewrite arr_field_address0. f_equal. lia. apply H. list_solve. }
      change (a :: al) with ([a] ++ al).
      rewrite (split2_data_at_Tarray_app 1) by Zlength_solve.
      sep_apply data_at_singleton_array_eq. cancel. rewrite IHal. rewrite <- H. cancel. rewrite H; auto. lia.
    + change (a :: al) with ([a] ++ al).
      rewrite (split2_data_at_Tarray_app 1) by Zlength_solve. 
      rewrite <- IHal; auto. 2: lia. 
      rewrite (data_at_singleton_array_eq _ _ a [a] p); auto.
      assert_PROP ((offset_val (sizeof t) p) = (field_address0 (tarray t n) [ArraySubsc 1] p)). {
      sep_apply data_at_array_len_1.
      entailer!. rewrite field_address0_clarify. simpl. f_equal. lia.
      unfold field_address0. simpl. 
      (*Core problem: need to prove field_compatible0 - TODO maybe move to separate lemma*)
      assert ( field_compatible0 (tarray t (Z.succ (Zlength al))) [ArraySubsc 1] p). {
        unfold field_compatible0. unfold field_compatible in H0. unfold field_compatible in H2.
        destruct H0 as [Hptr1 [Hleg1 [Hszc1 [Hal1 Hlegn1]]]].
        destruct H2 as [Hptr2 [Hleg2 [Hszc2 [Hal2 Hlegn2]]]].
        destruct p; inversion Hptr1; simpl in *.
        (*This will be needed for both goals*)
        assert (Hsum: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (sizeof t))) = Ptrofs.unsigned i + sizeof t). {
          unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr_eq (sizeof t)).
          pose proof (Ptrofs.unsigned_range i).
          pose proof (sizeof_pos t). rewrite Zmod_small; try lia.
          rewrite (Ptrofs.unsigned_repr_eq). rewrite Zmod_small. reflexivity. lia. }
        simpl. replace (Ctypes.sizeof t * Z.max 0 (Z.succ (Zlength al))) with
        ((Ctypes.sizeof t) + Ctypes.sizeof t * Zlength al). 2: { 
        replace (Z.max 0 (Z.succ (Zlength al))) with (1 + Zlength al) by lia.
        rewrite Z.mul_add_distr_l. rewrite Z.mul_1_r. reflexivity. }
        repeat(split; auto; try lia). 
        - (*prove [size_compatible] since we have both pieces*)
          unfold size_compatible. 
          rewrite Z.add_assoc. unfold sizeof in *. rewrite <- Hsum.
          replace (Z.max 0 (Z.succ (Zlength al) - 1)) with (Zlength al) in Hszc2 by lia. apply Hszc2.
        - (*prove [align_compatible]*)
          apply align_compatible_rec_Tarray. intros.
          assert (i0 = 0 \/ 0 < i0 <= Zlength al) by lia. destruct H2 as [Hz | Hpos].
          + subst. rewrite Z.mul_0_r. rewrite Z.add_0_r. apply Hal1.
          + inversion Hal2; subst. inversion H2. specialize (H8 (i0 -1)).
            assert (0 <= i0 - 1 < Z.succ (Zlength al) - 1 ) by lia. specialize (H8 H2); clear H2.
            replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (sizeof t))) + Ctypes.sizeof t * (i0 - 1)) with
              (Ptrofs.unsigned i + Ctypes.sizeof t * i0) in H8. apply H8.
            rewrite Hsum. rewrite <- Z.add_assoc. f_equal. rewrite Z.mul_sub_distr_l.
            rewrite Z.mul_1_r. unfold sizeof. rewrite Z.add_sub_assoc. rewrite Z.add_simpl_l. reflexivity. }
      destruct (field_compatible0_dec (tarray t (Z.succ (Zlength al))) [ArraySubsc 1] p); try contradiction.
      apply isptr_is_pointer_or_null. auto. }
    rewrite H. cancel.
Qed.
 

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