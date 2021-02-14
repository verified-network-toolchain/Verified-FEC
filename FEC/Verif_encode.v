Require Import VST.floyd.proofauto.

Require Import fec.
Require Import Common.
Require Import CommonVST.
Require Import VandermondeList.
Require Import Specs.
Require Import Poly.
Require Import FECTactics.

Set Bullet Behavior "Strict Subproofs".

Ltac rewrite_eqs :=
  repeat match goal with
    | [H : ?x = ?y |- context [ ?x ]] => rewrite H
    end.

Ltac solve_in :=
  subst;
  match goal with
  | [ |- In ?x (?x :: ?z)] => left; reflexivity
  | [ |- In ?x (?y :: ?z)] => right; solve_in
  | [ H : _ |- In ?x (?l1 ++ ?l2)] => apply in_or_app; first [left; solve_in | right; solve_in] (*not sure if this works*)
  | [ H : _ |- In ?x ?l] => assumption; auto
  end.

Ltac solve_in_eq :=
  repeat match goal with
   | [ H : In ?x ?y |-In ?x ?y] => apply H 
   | [ H : In ?x (?y :: ?z) |- In ?k ?l] => destruct H
   | [ H : In ?x (?a ++ ?b) |- In ?k ?l] => apply list_in_insert in H; destruct H
   end; solve_in.

Lemma body_fec_blk_encode : semax_body Vprog Gprog f_fec_blk_encode fec_blk_encode_spec.
Proof.
  start_function. forward. forward. (*TODO: make easier with tactic (need sizeof)*)
  assert_PROP (force_val (sem_binary_operation' Oadd (tptr (tptr tuchar)) tint pd (Vint (Int.repr k))) =
    field_address0 (tarray (tptr (tuchar)) (k + h)) [ArraySubsc k] pd) as Hpd. { entailer!. simpl. 
    rewrite arr_field_address0; auto. lia. } rewrite Hpd.
  remember [temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd);
   temp _z (Vint (Int.zero_ext 8 (Int.neg (Int.repr 1)))); temp _k (Vint (Int.repr k));
   temp _h (Vint (Int.repr h)); temp _c (Vint (Int.repr c)); temp _pdata pd; 
   temp _plen pl; temp _pstat ps] as LOCALS.
  remember [INDEX_TABLES gv; data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
       iter_sepcon_arrays packet_ptrs packets; iter_sepcon_arrays parity_ptrs parities;
       data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl;
       data_at Ews (tarray tschar k) (list_repeat (Z.to_nat k) (Vint Int.zero)) ps] as SEPS.
  (*remember the above because the loop invariant is basically trivial and we don't want to repeat twice*)
  forward_loop (EX (i: Z),
    PROP (0 <= i <= k)
    (LOCALx  ( temp _i (Vint (Int.repr i)) :: LOCALS )
    (SEPx (SEPS))))
   break: 
    (PROP ( )  (LOCALx LOCALS (SEPx SEPS))).
  - rewrite_eqs. forward. Exists 0%Z. rewrite_eqs. entailer!.
  - Intros i. rewrite_eqs. forward_if.
    + forward. rewrite Znth_list_repeat_inrange by lia. entailer!.
      forward_if.
      * forward_if True.
        -- contradiction.
        -- forward. entailer!.
        -- rewrite Znth_list_repeat_inrange in H14 by lia. inversion H14.
      * forward. Exists (i+1)%Z. rewrite_eqs. entailer!. solve_repr_int.
    + forward. rewrite_eqs. entailer!.
  - (*another error check that isn't true*) rewrite_eqs. forward_if True. contradiction.
    forward. entailer!.
    (*The real function starts here*)
    (*outer loop - go through all rows selected by weight matrix*)
    clear LOCALS HeqLOCALS.
    (* need to pull out z*)
    remember [temp _pparity (field_address0 (tarray (tptr tuchar) (k + h)) (SUB k) pd);
             temp _k (Vint (Int.repr k));
             temp _h (Vint (Int.repr h)); temp _c (Vint (Int.repr c)); temp _pdata pd; 
             temp _plen pl; temp _pstat ps] as LOCALS.
    rewrite (LOCALx_shuffle' _ _ (temp _z (Vint (Int.zero_ext 8 (Int.neg (Int.repr 1)))) :: LOCALS)).
    2 : { intros Q. rewrite HeqLOCALS. split; intros; solve_in_eq. } clear SEPS HeqSEPS.
    (*Same trick with SEPS to pull out list stored at pd*)
    remember [INDEX_TABLES gv; data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
       iter_sepcon_arrays packet_ptrs packets; 
       data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl;
       data_at Ews (tarray tschar k) (list_repeat (Z.to_nat k) (Vint Int.zero)) ps] as SEPS.
    rewrite (SEPx_Permutation _ (iter_sepcon_arrays parity_ptrs parities :: SEPS)).
    2 : { rewrite HeqSEPS. (*TODO: figure out better way*)
         eapply perm_trans. 2: apply perm_swap. apply perm_skip. eapply perm_trans. 2: apply perm_swap. 
         apply perm_skip. apply perm_swap. }
   (*Loop invariant: each time, up to the ith row of the resulting matrix is correct (ie, each position
     is the dot product of the correct row from the weight mx and column from the packet matrix)*)
    (*z is super annoying bc its unsigned but starts at -1*)
    (*loop invariant will work with int matrices, in the postcondition we will convert this to the equivalent
      matrix in the field. This is because the initial parity matrix (which is overwritten) can be arbitrary*)
   forward_loop (EX (i:Z) (l: list (list Z)),
      PROP (0 <= i <= h; forall x y, 0 <= x < i -> 0 <= y < c -> Znth y (Znth x l) = 
        poly_to_int (proj1_sig (dot_prod (submatrix weight_mx h k) (extend_mx (int_to_poly_mx packets) c) k x y)))
       (LOCALx (temp _i (Vint (Int.repr i)):: temp _z (Vint (Int.repr ((i - 1) mod 256))) :: LOCALS)
          (SEPx (iter_sepcon_arrays parity_ptrs l :: SEPS))))
    break: 
      (PROP ()
      (LOCALx (LOCALS)
        (SEPx ((iter_sepcon_arrays parity_ptrs (norev_mx (encode_list_mx h k c packets))) :: SEPS)))).
    + rewrite_eqs. forward. Exists (0%Z). Exists parities. rewrite_eqs. entailer!.
    + (*loop body*) Intros i. Intros mx. rewrite_eqs. forward_if.
      * (*actual loop body*) admit.
      * forward. rewrite_eqs. entailer!. admit. (*prove matrix equal*)
    + rewrite_eqs; forward_if True. contradiction. forward. entailer!. forward. entailer!.
Admitted.


     (*TODO: see what version of this we need, then make separate lemma*)
(*
     assert (forall l,
      Forall (fun l' : list Z => Forall (fun z : Z => 0 <= z <= Byte.max_unsigned) l') l ->
     (* Forall (fun x => Zlength x = c) l ->*)
      norev_mx (int_to_poly_mx l) = l). { intros l Hlens.
      unfold norev_mx. apply Znth_eq_ext. unfold int_to_poly_mx. list_solve. intros i Hilen.
      unfold int_to_poly_mx in Hilen; rewrite !Zlength_map in Hilen.
      rewrite Znth_map. 2: unfold int_to_poly_mx; list_solve. apply Znth_eq_ext.
      rewrite Zlength_map. apply int_to_poly_mx_length2. intros j HjLen.
      rewrite !Zlength_map in HjLen. rewrite Znth_map by auto.
      rewrite int_to_poly_mx_spec by auto. symmetry. rewrite <- poly_of_int_to_int. reflexivity.
      rewrite Forall_forall in Hlens. specialize (Hlens (Znth i l)). 
      assert (Hin: In (Znth i l) l). apply Znth_In; lia. 
      specialize (Hlens Hin). rewrite Forall_forall in Hlens. specialize (Hlens (Znth j (Znth i l))).
      assert (Hin' : In (Znth j (Znth i l)) (Znth i l)). rewrite int_to_poly_mx_length2 in HjLen.
      apply Znth_In; try lia. specialize (Hlens Hin'). lia. }*)


