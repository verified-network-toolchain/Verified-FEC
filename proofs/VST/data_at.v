Require Import VST.floyd.proofauto.

(*One small test: suppose we have 4 bytes in memory. Can we combine them to make an int?*)

Definition combine_little_endian (b1 b2 b3 b4 : Z) : Z :=
  fold_right Z.land 0 [b1; Z.shiftl b2 8; Z.shiftl b3 16; Z.shiftl b4 24].

Definition change_to_mpred (x: predicates_hered.pred compcert_rmaps.RML.R.rmap) : mpred.
apply x.
Defined.

Ltac destruct_and :=
  repeat match goal with
  | [H : ?P /\ ?Q |- _] => destruct H
  end.

Lemma contra_derives: forall (m: mpred) (P: Prop),
  ~ P ->
  !!P |-- m.
Proof.
  intros. entailer!.
Qed.

(*Make res_predicates.address_mapsto into mpreds for entailer!*)
Ltac all_mpred :=
  repeat match goal with
      | [ |- context [ change_to_mpred (res_predicates.address_mapsto ?a ?p ?sh ?r) ]] =>
        remember (change_to_mpred (res_predicates.address_mapsto a p sh r ))
      | [ |- context [ res_predicates.address_mapsto ?a ?p ?sh ?r ]] => change 
          (res_predicates.address_mapsto a p sh r ) with 
          (change_to_mpred (res_predicates.address_mapsto a p sh r ))
      end; subst.

Lemma sepcon_equiv: forall (m1 m2: predicates_hered.pred compcert_rmaps.RML.R.rmap),
  (m1 * m2)%logic = predicates_sl.sepcon m1 m2.
Proof.
  intros. reflexivity.
Qed.

Lemma exp_equiv: forall {A} (f: A -> predicates_hered.pred compcert_rmaps.RML.R.rmap),
  exp f = predicates_hered.exp f.
Proof.
  intros. reflexivity.
Qed.

(*TODO: will need other direction later*)
Lemma exp_sepcon: forall {A} (P: A -> mpred) (Q: mpred),
  (EX y, P y) * Q |-- EX y, (P y * Q).
Proof.
  intros. entailer!. eapply exp_right. cancel. apply derives_refl.
Qed.

Lemma andp_equiv: forall (p q : mpred),
  p && q = predicates_hered.andp p q.
Proof.
  intros. reflexivity.
Qed.

Lemma prop_equiv: forall {A} {H: ageable.ageable A} P,
  !! P = (@predicates_hered.prop A H P).
Proof.
  intros. reflexivity.
Qed.

Lemma allp_equiv: forall {B} (f: B -> mpred),
  allp f = predicates_hered.allp f.
Proof.
  intros. reflexivity.
Qed. 

Lemma andp_prop: forall (P: Prop) (Q R: mpred),
  ((!!P && Q) * R)%logic = (Q * R)%logic && !! P.
Proof.
  intros. apply pred_ext; entailer!. 
Qed.

Lemma noghost_and: forall p,
  p && res_predicates.noghost |-- res_predicates.noghost.
Proof.
  intros. constructor. rewrite andp_equiv. unfold predicates_hered.derives.
  unfold predicates_hered.app_pred. unfold predicates_hered.andp. simpl.
  intros a [H1 H2]. assumption.
Qed.

Lemma noghost_sepcon: 
  res_predicates.noghost * res_predicates.noghost |-- res_predicates.noghost.
Proof.
  constructor. rewrite sepcon_equiv. unfold predicates_hered.derives.
  unfold predicates_hered.app_pred. unfold predicates_sl.sepcon.
  simpl. intros a [y [z [Hjoin [Hixy Hidz]]]].
  apply compcert_rmaps.RML.ghost_of_join in Hjoin.
  apply sepalg.join_unit1_e in Hjoin; auto. rewrite <- Hjoin. assumption.
Qed.
  

Lemma noghost_and_sepcon_4: forall p q r s,
  (p && res_predicates.noghost) * (q && res_predicates.noghost) *
  (r && res_predicates.noghost) * (s && res_predicates.noghost) |--
  res_predicates.noghost.
Proof.
  intros. eapply derives_trans. apply sepcon_derives.
  2: apply noghost_and.
  eapply derives_trans. apply sepcon_derives. 2: apply noghost_and.
  apply sepcon_derives. apply noghost_and. apply noghost_and.
  2: apply noghost_sepcon. eapply derives_trans.
  apply sepcon_derives. apply noghost_sepcon. 2: apply noghost_sepcon.
  apply derives_refl.
Qed.

Lemma noghost_and': forall p,
  p && res_predicates.noghost |-- p.
Proof.
  intros. constructor. rewrite andp_equiv.
  unfold predicates_hered.derives.
  unfold predicates_hered.app_pred. unfold predicates_hered.andp. simpl.
  unfold predicates_hered.app_pred. intuition.
Qed.

Lemma noghost_and_sepcon_4': forall p q r s,
  (p && res_predicates.noghost) * (q && res_predicates.noghost) *
  (r && res_predicates.noghost) * (s && res_predicates.noghost) |-- p * q * r * s.
Proof.
  intros. eapply derives_trans. apply sepcon_derives.
  2: apply noghost_and'.
  eapply derives_trans. apply sepcon_derives. 2: apply noghost_and'.
  apply sepcon_derives. apply noghost_and'. apply noghost_and'.
  apply derives_refl. apply derives_refl.
Qed.


(*The final result we need*)
Lemma noghost_and_sepcon_complete: forall p q r s x,
  p * q * r * s |-- x ->
  (p && res_predicates.noghost) * (q && res_predicates.noghost) *
  (r && res_predicates.noghost) * (s && res_predicates.noghost) |--
  x && res_predicates.noghost.
Proof.
  intros. apply andp_right.
  eapply derives_trans. apply noghost_and_sepcon_4'.
  assumption.
  apply noghost_and_sepcon_4.
Qed.

Lemma allp_left_4: forall {B} x1 x2 x3 x4 (p q r s: B -> mpred) t,
  p x1 * q x2 * r x3 * s x4 |-- t ->
  (ALL y, p y) * (ALL y, q y) * (ALL y, r y) * (ALL y, s y)  |-- t.
Proof.
  intros. eapply derives_trans. 2: apply H. 
  apply sepcon_derives; [|apply (allp_left s x4); apply derives_refl].
  apply sepcon_derives; [|apply (allp_left r x3); apply derives_refl].
  apply sepcon_derives; [|apply (allp_left q x2); apply derives_refl].
  apply (allp_left p x1); apply derives_refl.
Qed.

Lemma allp_left_noghost_4: forall {B} x1 x2 x3 x4 (p q r s: B -> mpred) t,
  (p x1 && res_predicates.noghost) * 
  (q x2 && res_predicates.noghost) *
  (r x3 && res_predicates.noghost) * 
  (s x4 && res_predicates.noghost) |-- t ->
  ((ALL y, p y) && res_predicates.noghost) * 
  ((ALL y, q y) && res_predicates.noghost) * 
  ((ALL y, r y) && res_predicates.noghost) * 
  ((ALL y, s y) && res_predicates.noghost)  |-- t.
Proof.
  intros. eapply derives_trans. 2: apply H. 
  repeat (apply sepcon_derives; try
    (apply andp_right; 
    [eapply derives_trans; [apply noghost_and' |eapply allp_left; apply derives_refl]| apply noghost_and])).
Qed.


Lemma emp_equiv : predicates_sl.emp = emp.
Proof.
  reflexivity.
Qed.

Lemma allp_noat_emp: (allp res_predicates.noat && res_predicates.noghost)  = emp.
Proof.
  apply pred_ext; constructor; unfold predicates_hered.derives; rewrite andp_equiv;
    unfold predicates_hered.andp; unfold predicates_hered.app_pred; intros; simpl in *.
  + apply compcert_rmaps.RML.all_resource_at_identity.
    destruct H as [H1 H2]. exact H1. apply H.
  + rewrite <- emp_equiv in H. unfold predicates_sl.emp in H. simpl in H.
    split. rewrite allp_equiv. unfold predicates_hered.allp. simpl.
    intros. apply compcert_rmaps.RML.resource_at_identity. assumption.
    apply compcert_rmaps.RML.ghost_of_identity. assumption.
Qed.


Lemma move_preds: forall (P1 P2 P3 P4 : Prop) (A1 A2 A3 A4: mpred),
  ((!!P1 && A1) * (!!P2 && A2) * (!!P3 && A3) * (!!P4 && A4))%logic =
  (A1 * A2 * A3 * A4)%logic && (!!P1 && !!P2 && !!P3 && !!P4).
Proof.
  intros. apply pred_ext; entailer!.
Qed.

(*copied*)
Lemma zbits_small: forall i,
  0 <= i < Byte.modulus ->
  Zbits.Zzero_ext 8 i = i.
Proof.
  intros. rewrite Zbits.Zzero_ext_mod; try rep_lia.
  assert (two_p 8 = 256) by reflexivity. rewrite Zmod_small; rep_lia.
Qed.

Lemma decode_int_single: forall (b: byte),
  decode_int [b] = Byte.unsigned b.
Proof.
  intros b. unfold decode_int. unfold rev_if_be.
  destruct Archi.big_endian; simpl; lia.
Qed.

Lemma not_divide_between: forall a b n,
  0 < n ->
  (n | a) ->
  a < b < a + n ->
  ~ (n | b).
Proof.
  intros a b n H0n H0 H1. intro.
  unfold Z.divide in *. destruct H as [z1 Hdiv1]. destruct H0 as [z2 Hdiv2].
  subst. replace (z2 * n + n) with ((z2 + 1) * n) in H1 by lia.
  destruct H1. apply Zmult_lt_reg_r in H. apply Zmult_lt_reg_r in H0. all: lia.
Qed.

Lemma data_at_4_bytes: forall `{cs: compspecs} sh b1 b2 b3 b4 p,
  field_compatible tuint [] p  ->
  0 <= b1 < Byte.modulus ->
  0 <= b2 < Byte.modulus ->
  0 <= b3 < Byte.modulus ->
  0 <= b4 < Byte.modulus ->
  (data_at sh tuchar (Vubyte (Byte.repr b1)) p *
  data_at sh tuchar (Vubyte (Byte.repr b2)) (offset_val 1 p) *
  data_at sh tuchar (Vubyte (Byte.repr b3)) (offset_val 2 p) *
  data_at sh tuchar (Vubyte (Byte.repr b4)) (offset_val 3 p))%logic =
  data_at sh tuint (Vint (Int.repr (combine_little_endian b1 b2 b3 b4))) p.
Proof.
  intros cs sh b1 b2 b3 b4 p H Hb1 Hb2 Hb3 Hb4. unfold data_at. unfold field_at. normalize. f_equal.
  - admit. (*do later - shouldn't be too hard*)
  - simpl. rewrite !data_at_rec_eq. simpl.
    unfold at_offset. normalize. change (unfold_reptype ?x) with x.
    unfold Vubyte. assert (isptr p) by apply H. destruct p; inversion H0. unfold mapsto. simpl.
    destruct (readable_share_dec sh); simpl; normalize.
    + (* When we can read the data *)
      (*Simplify LHS (all 4 are the same, so we have a single tactic*)
      all_mpred.
      repeat match goal with
      | [ |- context [
          (!! (Byte.unsigned (Byte.repr ?b1) <= Byte.max_unsigned) &&
          change_to_mpred (res_predicates.address_mapsto ?m ?i ?sh ?x1)|| 
          (EX x : val, !! (Vint ?y = Vundef) && 
            res_predicates.address_mapsto ?m1 x ?sh1 ?x2)) ]] =>

          replace (!! (Byte.unsigned (Byte.repr b1) <= Byte.max_unsigned) &&
            change_to_mpred (res_predicates.address_mapsto m i sh x1)|| 
            (EX x : val, !! (Vint y = Vundef) && 
            res_predicates.address_mapsto m1 x sh1 x2)) with
           (change_to_mpred (res_predicates.address_mapsto m i sh x1))
        by ( apply pred_ext; [apply orp_right1; apply andp_right; entailer!|
            apply orp_left; [ apply andp_left2; cancel | apply exp_left; intros;
            apply andp_left1; apply contra_derives; intro C; inversion C]])
          
      end.
      (*simplify the RHS*)
      match goal with
      | [ |- context [
          (change_to_mpred (res_predicates.address_mapsto ?m ?i ?sh ?x1)|| 
          (EX x : val, !! (Vint ?y = Vundef) && 
            res_predicates.address_mapsto ?m1 x ?sh1 ?x2)) ]] =>

          replace (
            change_to_mpred (res_predicates.address_mapsto m i sh x1)|| 
            (EX x : val, !! (Vint y = Vundef) && 
            res_predicates.address_mapsto m1 x sh1 x2)) with
           (change_to_mpred (res_predicates.address_mapsto m i sh x1)) by
           (apply pred_ext; [apply orp_right1; cancel | apply orp_left; 
              [cancel | apply exp_left; intros; apply andp_left1; apply contra_derives;
                intro C; inversion C]])
      end.
      unfold change_to_mpred.
      (*Now everything is in terms of mapsto - the hard part*)
      unfold res_predicates.address_mapsto. rewrite <- !exp_equiv.
      apply pred_ext.
      * (*One side: 4 chars |-- int *)
        (*want to get all lists in context. This is quite annoying*)
        eapply derives_trans. rewrite !sepcon_assoc. apply exp_sepcon.
        apply exp_left. intros l1.
        rewrite sepcon_comm. rewrite !sepcon_assoc.
        eapply derives_trans. apply exp_sepcon. apply exp_left. intros l2.
        rewrite sepcon_comm. rewrite !sepcon_assoc.
        eapply derives_trans. apply exp_sepcon. apply exp_left. intros l3.
        rewrite sepcon_comm. rewrite !sepcon_assoc.
        eapply derives_trans. apply exp_sepcon. apply exp_left. intros l4.
        rewrite sepcon_comm. rewrite !sepcon_assoc.
        apply (exp_right (l1 ++ l2 ++ l3 ++ l4)).
        rewrite <- !andp_equiv. rewrite <- !allp_equiv. rewrite <- !prop_equiv.
        rewrite !(andp_assoc _ _ res_predicates.noghost). normalize.
        assert (Datatypes.length (l1 ++ l2 ++ l3 ++ l4) = size_chunk_nat Mint32 /\
        decode_val Mint32 (l1 ++ l2 ++ l3 ++ l4) = Vint (Int.repr (combine_little_endian b1 b2 b3 b4)) /\
        (align_chunk Mint32 | Ptrofs.unsigned i)). {
          (*Prove the list part*)
          unfold size_chunk_nat in *. unfold size_chunk in *.
          rewrite <- !ZtoNat_Zlength in *.
          repeat match goal with
          | [ H: Z.to_nat (Zlength ?l) = Z.to_nat 1 |- _] =>
            let X := fresh in
            assert (X: Zlength l = 1) by (apply Z2Nat.inj in H; list_solve); clear H
          end.
          (*Prove structure of lists*)
          assert(Hlists: forall l b,
            0 <= b < Byte.modulus ->
            Zlength l = 1 ->
            decode_val Mint8unsigned l = Vint (Int.repr (Byte.unsigned (Byte.repr b))) ->
            l = [Byte (Byte.repr b)]). { intros l' b' Hb' Hl' Hdec. unfold decode_val in Hdec.
              destruct l'; simpl in *. list_solve. destruct m; try inversion Hdec. 
              rewrite Zlength_cons in Hl'. assert (Zlength l' = 0) by lia.
              apply Zlength_nil_inv in H1. clear H14. subst. simpl in Hdec.
              unfold Int.zero_ext in Hdec.
              rewrite decode_int_single in Hdec.
              rewrite Int.unsigned_repr in Hdec by rep_lia.
              rewrite zbits_small  in Hdec by rep_lia.
              rewrite Byte.unsigned_repr in Hdec by rep_lia.
              inversion Hdec; subst. rewrite !Int.Z_mod_modulus_eq in H14.
              rewrite !Zmod_small in H14 by rep_lia. subst. rewrite Byte.repr_unsigned.
              reflexivity. }
            (*TODO: abstract out for other side?*)
          assert (l1 = [Byte (Byte.repr b1)]) by (apply Hlists; auto).
          assert (l2 = [Byte (Byte.repr b2)]) by (apply Hlists; auto).
          assert (l3 = [Byte (Byte.repr b3)]) by (apply Hlists; auto).
          assert (l4 = [Byte (Byte.repr b4)]) by (apply Hlists; auto).
          subst. simpl. split. reflexivity. split. unfold decode_val. simpl.
          f_equal. f_equal. (*TODO: do this later (separate lemma) or just use decode_int*) admit.
          unfold field_compatible in H. unfold align_compatible in H. 
          destruct_and. inversion H23; subst. unfold align_chunk in H26.
          inversion H25; subst. assumption. }
        normalize.
        (*now we ONLY have the separation logic predicates with ALL*)
        apply andp_right. 2: { rewrite <- !sepcon_assoc. apply noghost_and_sepcon_4. }
        (*NOTE: this is the start of where I am pretty lost*) 
        rewrite !allp_equiv, !sepcon_equiv, !andp_equiv. constructor.
        unfold predicates_hered.derives. unfold predicates_sl.sepcon.
        unfold predicates_hered.app_pred. unfold predicates_hered.andp.
        unfold predicates_hered.allp. simpl. intros a H14 adr.
        repeat match goal with
               | [H: exists z, ?Q |- _ ] => destruct H
               | [H: ?P /\ ?Q |- _ ] => destruct H
               end.
        (*the hard part*)
          destruct (adr_range_dec (b, Ptrofs.unsigned i) 4 adr).
          { (*Don't really know what I'm doing here*)
            simpl in a0. destruct adr; simpl in a0. destruct a0; subst.
            (*Now need to determine exactly where z is*)
            specialize (H15 (b0, z)). destruct (adr_range_dec (b0, Ptrofs.unsigned i) 1 (b0, z)).
            simpl in a0. destruct a0; subst. assert (z = Ptrofs.unsigned i) by lia.
            subst. destruct H15 as [sh' Hsh']. normalize. simpl in *.
            replace (Ptrofs.unsigned i - Ptrofs.unsigned i) with 0 in * by lia.
            (*TODO: change where previous lemma is so we have this info and dont need to admit*)
            assert (Hl1: l1 = [Byte (Byte.repr b1) ]) by admit. subst. simpl in *.
            (*TODO: No idea how to move forward here*)
            admit.
          }
          {
            (*we want all of the adr_range_dec's to be false*)
            assert (Hadrs: forall k, 0 <= k <= 3 ->
              ~ adr_range (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr k))) 1 adr). {
              intros k Hk Hc. unfold adr_range in *. destruct adr; simpl in *. 
              apply Classical_Prop.not_and_or in n.
              destruct Hc; subst. destruct n; try contradiction.
              unfold Ptrofs.add in H36. rewrite !Ptrofs.unsigned_repr_eq in H36.
              rewrite !(Zmod_small k) in H36 by rep_lia.
              apply Classical_Prop.not_and_or in H35. (*key fact about pointer wraparound*)
              assert ((Ptrofs.unsigned i + k) mod Ptrofs.modulus = Ptrofs.unsigned i + k). {
                assert (Hlt :(Ptrofs.unsigned i + k) < Ptrofs.modulus \/ (Ptrofs.unsigned i + k) >= Ptrofs.modulus) by rep_lia.
                destruct Hlt. rewrite Zmod_small; rep_lia.
                (*BUT, we know divisible by 4*)
                pose proof (Ptrofs.unsigned_range i). 
                assert (Ptrofs.unsigned i >= Ptrofs.modulus - 3) by lia.
                assert (4 | Ptrofs.modulus - 4). { unfold Z.divide. exists (Ptrofs.modulus / 4 - 1). reflexivity. }
                assert (~(4 | Ptrofs.unsigned i)). { apply (not_divide_between (Ptrofs.modulus - 4)). lia. assumption.
                lia. } contradiction. 
              }
            rep_lia.
            }
            (*Now, we can use this in each of the hypotheses*)
            specialize (H20 adr). destruct (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3))) 1 adr).
            exfalso. apply (Hadrs 3). lia. assumption.
            specialize (H19 adr). destruct (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2))) 1 adr).
            exfalso. apply (Hadrs 2). lia. assumption.
            specialize (H17 adr). destruct (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1))) 1 adr).
            exfalso. apply (Hadrs 1). lia. assumption.
            specialize (H15 adr). destruct (adr_range_dec (b, Ptrofs.unsigned i) 1 adr).
            exfalso. apply (Hadrs 0). lia. rewrite ptrofs_add_repr_0_r. assumption.
            (*Now, we can prove the sepalg.identity*)
            apply (compcert_rmaps.RML.resource_at_join _ _ _ adr) in H14.
            apply sepalg.join_unit2_e in H14. rewrite <- H14. assumption. clear H14.
            apply (compcert_rmaps.RML.resource_at_join _ _ _ adr) in H16.
            apply sepalg.join_unit2_e in H16. rewrite <- H16. assumption. clear H15.
            apply (compcert_rmaps.RML.resource_at_join _ _ _ adr) in H18.
            apply sepalg.join_unit2_e in H18. rewrite <- H18. assumption. assumption.
        }
      * (*other direction: int |-- 4 chars. Will likely be stuck in similar places. Some of the previous
          proof should be reused, it is not well organized right now*)
        admit.
    + (*No readable share case. Not sure how hard this will be*)
      admit.
Admitted.
