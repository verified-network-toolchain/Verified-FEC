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
(*
Lemma data_at_array_len_1: forall sh t a p,
data_at sh t a p = data_at sh (tarray t 1) [a] p.
Proof.
  intros. apply pred_ext.
  - entailer!. unfold field_compatible in *; simpl in *. Search data_at.
  destruct H as [Hptr [Hleg [Hsz [Hal Ht]]]]. repeat(split; auto).
  unfold size_compatible in *. destruct p; auto. simpl. unfold sizeof in Hsz.
  replace (Ctypes.sizeof t * 1) with (Ctypes.sizeof t) by (rewrite <- Zred_factor0; reflexivity).
  assumption. Print align_compatible_rec. unfold align_compatible in *. destruct p; auto. simpl. 
  apply align_compatible_rec_Tarray. intros.
  replace (i0) with 0 by lia. rewrite Z.mul_0_r. rewrite Z.add_0_r. apply Hal.
Qed.

*)

(*We can consider an instance of t at position p to be a valid array of length 1 at p*)
Lemma data_at_array_len_1: forall sh t a p,
data_at sh t a p |-- !! field_compatible (tarray t 1) [] p.
Proof.
  intros. erewrite <- data_at_singleton_array_eq. 2: reflexivity. entailer!.
Qed. 
(*
Lemma data_at_field_address0_len_l: forall t p,
  field_address0 (tarray t 1) (SUB 1) p = field_address0 t [] p.
Proof.
  intros. unfold field_address0. simpl.

field_compatible0_dec t [] p <-> field_compatible0_dec (tarray t 1) [ArraySubsc 1] p


  (field_address0 (tarray (tarray t m) n) [ArraySubsc 1] p*)

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

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  forward. unfold default_val; simpl. unfold Znth; simpl. unfold upd_Znth; simpl.
  unfold sublist; simpl.
  replace (Vundef) with (Vint Int.zero) by admit.
 forward_call (gv _arr, Ews, [0; 0; 0; 0; 0; 0; 5; 0; 0; 0; 0; 0] , 12, 6).
  - entailer!. rewrite data_at_2darray_concat. simpl. unfold Int.zero. cancel. reflexivity. auto. auto.
  - repeat(split). auto. lia. rep_lia. repeat(constructor; auto;try rep_lia). lia.
  - forward.
Admitted.
