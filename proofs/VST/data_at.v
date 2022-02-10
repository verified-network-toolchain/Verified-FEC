Require Import VST.floyd.proofauto.

Lemma exp_equiv: forall {A} (f: A -> predicates_hered.pred compcert_rmaps.RML.R.rmap),
  exp f = predicates_hered.exp f.
Proof.
  intros. reflexivity.
Qed.

Lemma decode_int_single: forall (b: byte),
  decode_int [b] = Byte.unsigned b.
Proof.
  intros b. unfold decode_int. unfold rev_if_be.
  destruct Archi.big_endian; simpl; lia.
Qed.

Lemma zero_ext_8_lemma:
  forall i j, Int.zero_ext 8 (Int.repr (Byte.unsigned i)) = Int.repr (Byte.unsigned j) ->
    i=j.
Proof.
intros.
rewrite zero_ext_inrange in H
  by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
apply repr_inj_unsigned in H; try rep_lia.
rewrite <- (Byte.repr_unsigned i), <- (Byte.repr_unsigned j).
congruence.
Qed.

Lemma decode_val_Vubyte_inj:
  forall i j, decode_val Mint8unsigned [Byte i] = Vubyte j -> i=j.
Proof.
intros.
unfold decode_val, Vubyte in *; simpl in *.
apply Vint_inj in H.
rewrite decode_int_single in *.
apply zero_ext_8_lemma in H.
auto.
Qed.

Lemma andp_pull1:
  forall P (A C: predicates_hered.pred compcert_rmaps.RML.R.rmap), predicates_hered.andp (predicates_hered.andp (predicates_hered.prop P) A) C =
                 predicates_hered.andp (predicates_hered.prop P)  (predicates_hered.andp A C).
Proof.
intros.
apply predicates_hered.andp_assoc.
Qed.

Lemma decode_int_range: forall bl, 0 <= decode_int bl < two_p (Z.of_nat (Datatypes.length bl) * 8).
Proof.
intros.
unfold decode_int.
unfold rev_if_be.
destruct Archi.big_endian.
rewrite <- rev_length.
apply int_of_bytes_range.
apply int_of_bytes_range.
Qed.


Lemma int_of_bytes_inj: forall al bl, length al = length bl -> int_of_bytes al = int_of_bytes bl -> al=bl.
Proof.
intros.
revert bl H H0; induction al; destruct bl; simpl; intros; auto; try discriminate.
pose proof (Byte.unsigned_range a). pose proof (Byte.unsigned_range i).
change Byte.modulus with 256 in *. 
assert (al=bl). {
   apply IHal. congruence.
   forget (int_of_bytes al) as x. forget (int_of_bytes bl) as y.
   lia.
}
subst bl.
f_equal.
clear - H0 H1 H2.
rewrite <- (Byte.repr_unsigned a).
rewrite <- (Byte.repr_unsigned i).
f_equal.
lia.
Qed.

Lemma decode_int_inj: forall al bl, 
   length al = length bl -> 
   decode_int al = decode_int bl -> al=bl.
Proof.
intros.
unfold decode_int in *.
apply int_of_bytes_inj in H0; auto.
Qed.

(** Convert between 4 bytes and int *)

Lemma address_mapsto_4bytes_aux: 
 forall (sh : Share.t)
   (b0 b1 b2 b3 : byte)
   (b : block) (i : ptrofs)
   (SZ : Ptrofs.unsigned i + 4 < Ptrofs.modulus)
   (AL : (4 | Ptrofs.unsigned i))
   (r : readable_share sh),
predicates_sl.sepcon
  (predicates_sl.sepcon
     (predicates_sl.sepcon
        (predicates_hered.andp
           (predicates_hered.allp
              (res_predicates.jam
                 (adr_range_dec (b, Ptrofs.unsigned i) (size_chunk Mint8unsigned))
                 (fun loc : address =>
                  res_predicates.yesat compcert_rmaps.RML.R.NoneP
                    (compcert_rmaps.VAL
                       (nth (Z.to_nat (snd loc - snd (b, Ptrofs.unsigned i)))
                          [Byte b0] Undef)) sh loc) res_predicates.noat))
           res_predicates.noghost)
        (predicates_hered.andp
           (predicates_hered.allp
              (res_predicates.jam
                 (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))
                    (size_chunk Mint8unsigned))
                 (fun loc : address =>
                  res_predicates.yesat compcert_rmaps.RML.R.NoneP
                    (compcert_rmaps.VAL
                       (nth
                          (Z.to_nat
                             (snd loc
                                - snd
                                    (b,
                                    Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))))
                          [Byte b1] Undef)) sh loc) res_predicates.noat))
           res_predicates.noghost))
     (predicates_hered.andp
        (predicates_hered.allp
           (res_predicates.jam
              (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))
                 (size_chunk Mint8unsigned))
              (fun loc : address =>
               res_predicates.yesat compcert_rmaps.RML.R.NoneP
                 (compcert_rmaps.VAL
                    (nth
                       (Z.to_nat
                          (snd loc
                             - snd
                                 (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))))
                       [Byte b2] Undef)) sh loc) res_predicates.noat))
        res_predicates.noghost))
  (predicates_hered.andp
     (predicates_hered.allp
        (res_predicates.jam
           (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))
              (size_chunk Mint8unsigned))
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth
                    (Z.to_nat
                       (snd loc
                          - snd (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))))
                    [Byte b3] Undef)) sh loc) res_predicates.noat))
     res_predicates.noghost) = predicates_hered.andp
                                 (predicates_hered.allp
                                    (res_predicates.jam
                                       (adr_range_dec (b, Ptrofs.unsigned i)
                                          (size_chunk Mint32))
                                       (fun loc : address =>
                                        res_predicates.yesat
                                          compcert_rmaps.RML.R.NoneP
                                          (compcert_rmaps.VAL
                                             (nth
                                                (Z.to_nat
                                                   (snd loc
                                                      - snd (b, Ptrofs.unsigned i)))
                                                [Byte b0; Byte b1; Byte b2; Byte b3]
                                                Undef)) sh loc) res_predicates.noat))
                                 res_predicates.noghost.
Proof.
intros.

     simpl snd.
    simpl size_chunk.
 repeat   match goal with |- context [Ptrofs.add i (Ptrofs.repr ?A)] =>
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr A)))
    with (A + Ptrofs.unsigned i)
    by (unfold Ptrofs.add; rewrite (Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite Ptrofs.unsigned_repr by rep_lia; rep_lia)
   end.
    rewrite  (res_predicates.allp_jam_split2 _ _ _ 
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0; Byte b1; Byte b2; Byte b3] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0; Byte b1; Byte b2] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - (3+Ptrofs.unsigned i)))
                    [Byte b3] Undef)) sh loc)
           (adr_range_dec (b, Ptrofs.unsigned i) 4)
           (adr_range_dec (b, Ptrofs.unsigned i) 3)
           (adr_range_dec (b, 3 + Ptrofs.unsigned i) 1)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0; Byte b1; Byte b2; Byte b3] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0; Byte b1; Byte b2] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - (3+Ptrofs.unsigned i)))
           [Byte b3] Undef)).
    2:{ forget (Ptrofs.unsigned i) as j. clear.
         split; intros [b1 z1]. simpl. intuition rep_lia.
         simpl. intuition rep_lia.
       }
    2:{ intros. destruct l; destruct H; subst. f_equal. f_equal.
          rewrite (app_nth1 [Byte b0; Byte b1; Byte b2] [Byte b3]); auto.
        simpl. rep_lia.
       }
  2:{ intros. f_equal. f_equal. 
       destruct l; destruct H. subst b4. simpl snd.
       assert (z = 3 + Ptrofs.unsigned i) by lia. subst z.
        rewrite Z.sub_diag.
        replace (3 + Ptrofs.unsigned i - Ptrofs.unsigned i) with 3 by lia.
          reflexivity.
      }
   2:{ intros. left. destruct H0. hnf in H0. rewrite H0 in H1 . clear H0.
        destruct l, H. subst. simpl snd in *.
        assert (Z.to_nat (z - Ptrofs.unsigned i) < 4)%nat by rep_lia.
        clear - H1. destruct (Z.to_nat (z - Ptrofs.unsigned i)) as [|[|[|[|]]]]; inv H1; apply I.
       }
   f_equal.
   
    rewrite  (res_predicates.allp_jam_split2 _ _ _ 
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0; Byte b1; Byte b2] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0; Byte b1] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - (2+Ptrofs.unsigned i)))
                    [Byte b2] Undef)) sh loc)
           (adr_range_dec (b, Ptrofs.unsigned i) 3)
           (adr_range_dec (b, Ptrofs.unsigned i) 2)
           (adr_range_dec (b, 2 + Ptrofs.unsigned i) 1)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0; Byte b1; Byte b2] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0; Byte b1] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - (2+Ptrofs.unsigned i)))
           [Byte b2] Undef)).
    2:{ forget (Ptrofs.unsigned i) as j. clear.
         split; intros [b1 z1]. simpl. intuition rep_lia.
         simpl. intuition rep_lia.
       }
    2:{ intros. destruct l; destruct H; subst. f_equal. f_equal.
          rewrite (app_nth1 [Byte b0; Byte b1] [Byte b2]); auto.
        simpl. rep_lia.
       }
  2:{ intros. f_equal. f_equal. 
       destruct l; destruct H. subst b4. simpl snd.
       assert (z = 2 + Ptrofs.unsigned i) by lia. subst z.
        rewrite Z.sub_diag.
        replace (2 + Ptrofs.unsigned i - Ptrofs.unsigned i) with 2 by lia.
          reflexivity.
      }
   2:{ intros. left. destruct H0. hnf in H0. rewrite H0 in H1 . clear H0.
        destruct l, H. subst. simpl snd in *.
        assert (Z.to_nat (z - Ptrofs.unsigned i) < 3)%nat by rep_lia.
        clear - H1. destruct (Z.to_nat (z - Ptrofs.unsigned i)) as [|[|[|]]]; inv H1; apply I.
       }
   f_equal.

    rewrite  (res_predicates.allp_jam_split2 _ _ _ 
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0; Byte b1] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - (1+Ptrofs.unsigned i)))
                    [Byte b1] Undef)) sh loc)
           (adr_range_dec (b, Ptrofs.unsigned i) 2)
           (adr_range_dec (b, Ptrofs.unsigned i) 1)
           (adr_range_dec (b, 1 + Ptrofs.unsigned i) 1)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0; Byte b1] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - (1+Ptrofs.unsigned i)))
           [Byte b1] Undef)).
    2:{ forget (Ptrofs.unsigned i) as j. clear.
         split; intros [b1 z1]. simpl. intuition rep_lia.
         simpl. intuition rep_lia.
       }
    2:{ intros. destruct l; destruct H; subst. f_equal. f_equal.
          rewrite (app_nth1 [Byte b0] [Byte b1]); auto.
        simpl. rep_lia.
       }
  2:{ intros. f_equal. f_equal. 
       destruct l; destruct H. subst b4. simpl snd.
       assert (z = 1 + Ptrofs.unsigned i) by lia. subst z.
        rewrite Z.sub_diag.
        replace (1 + Ptrofs.unsigned i - Ptrofs.unsigned i) with 1 by lia.
          reflexivity.
      }
   2:{ intros. left. destruct H0. hnf in H0. rewrite H0 in H1 . clear H0.
        destruct l, H. subst. simpl snd in *.
        assert (Z.to_nat (z - Ptrofs.unsigned i) < 2)%nat by rep_lia.
        clear - H1. destruct (Z.to_nat (z - Ptrofs.unsigned i)) as [|[|[|]]]; inv H1; apply I.
       }
   f_equal.
Qed.


Lemma address_mapsto_4bytes:
 forall (sh : Share.t)
    (b0 b1 b2 b3 : byte)
    (b : block)
    (i : ptrofs)
    (SZ : Ptrofs.unsigned i + 4 < Ptrofs.modulus)
    (AL : (4 | Ptrofs.unsigned i))
    (r : readable_share sh),
 predicates_sl.sepcon
  (predicates_sl.sepcon
     (predicates_sl.sepcon
        (res_predicates.address_mapsto Mint8unsigned 
           (Vubyte b0) sh (b, Ptrofs.unsigned i))
        (res_predicates.address_mapsto Mint8unsigned 
           (Vubyte b1) sh
           (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))))
     (res_predicates.address_mapsto Mint8unsigned 
        (Vubyte b2) sh (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))))
  (res_predicates.address_mapsto Mint8unsigned (Vubyte b3) sh
     (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))) = 
res_predicates.address_mapsto Mint32
  (Vint (Int.repr (decode_int [b0; b1; b2; b3]))) sh
  (b, Ptrofs.unsigned i).
Proof.
intros.
      unfold res_predicates.address_mapsto. rewrite <- !exp_equiv.
      apply predicates_hered.pred_ext.
  - repeat change (exp ?A) with (predicates_hered.exp A).
      normalize.normalize.
      intros bl3 bl2 bl1 bl0.
      rewrite !andp_pull1.
      rewrite !predicates_sl.sepcon_andp_prop.
      normalize.normalize.
      destruct H as [A3 [ B3 _]].
      destruct H0 as [A2 [ B2 _]].
      destruct H1 as [A1 [ B1 _]].
      destruct H2 as [A0 [ B0 _]].
    destruct bl0 as [ | c0 [|]]; inv A0; inv B0. 
    destruct bl1 as [ | c1 [|]]; inv A1; inv B1.
    destruct bl2 as [ | c2 [|]]; inv A2; inv B2. 
    destruct bl3 as [ | c3 [|]]; inv A3; inv B3.
     destruct c0; try discriminate.
     destruct c1; try discriminate.
     destruct c2; try discriminate.
     destruct c3; try discriminate.
   apply decode_val_Vubyte_inj in H0,H1,H2,H3. subst.
   apply (predicates_hered.exp_right [Byte b0; Byte b1; Byte b2; Byte b3]).
     rewrite predicates_hered.prop_true_andp.
      2:{ split3. reflexivity. reflexivity. apply AL. }
  match goal with |- predicates_hered.derives ?A ?B => 
        assert (EQ: A=B); [ | rewrite EQ; apply predicates_hered.derives_refl]
    end.
  apply address_mapsto_4bytes_aux; auto.

 -
  repeat change (exp ?A) with (predicates_hered.exp A).
      normalize.normalize.
  intros bl.
      rewrite !andp_pull1.
      normalize.normalize.
      destruct H as [? [? ?]]. simpl snd in H1.
      destruct bl as [|c0 [| c1 [| c2 [| c3 [|]]]]]; inv H.
       unfold decode_val, proj_bytes in H0.
       destruct c0; try solve [destruct Archi.ptr64 eqn:AP; discriminate].
       destruct c1; try solve [destruct Archi.ptr64 eqn:AP; discriminate].
       destruct c2; try solve [destruct Archi.ptr64 eqn:AP; discriminate].
       destruct c3; try solve [destruct Archi.ptr64 eqn:AP; discriminate].
       apply Vint_inj in H0.
       pose proof (decode_int_range [b0;b1;b2;b3]).
       pose proof (decode_int_range [i0;i1;i2;i3]).
       change (two_p _) with Int.modulus in H,H2.
       apply repr_inj_unsigned in H0; try rep_lia.
        apply decode_int_inj in H0.
      clear H H2. inv H0.
     apply predicates_hered.exp_right with [Byte b3].
      normalize.normalize.
     apply predicates_hered.exp_right with [Byte b2].
      normalize.normalize.
     apply predicates_hered.exp_right with [Byte b1].
      normalize.normalize.
     apply predicates_hered.exp_right with [Byte b0].
     rewrite !predicates_hered.prop_true_andp by 
     (split3; [ reflexivity |  | apply Z.divide_1_l  ];
     unfold decode_val, Vubyte; simpl; f_equal;
     rewrite decode_int_single;
     apply zero_ext_inrange; change (two_p _ - 1) with 255;
     rewrite Int.unsigned_repr by rep_lia; rep_lia).
  match goal with |- predicates_hered.derives ?A ?B => 
        assert (EQ: B=A); [ | rewrite EQ; apply predicates_hered.derives_refl]
    end.
  apply address_mapsto_4bytes_aux; auto.
  reflexivity.
Qed.

Lemma tc_val_Vubyte: forall b, tc_val tuchar (Vubyte b).
Proof.
intros; red. 
simpl. rewrite Int.unsigned_repr by rep_lia.
rep_lia.
Qed.

Lemma nonlock_permission_4bytes:
 forall (sh : Share.t)
     (b : block) (i : ptrofs) 
     (SZ : Ptrofs.unsigned i + 4 < Ptrofs.modulus),
(res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned i) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3))) 1)%logic = 
res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned i) 4.
Proof.
intros.
 repeat   match goal with |- context [Ptrofs.add i (Ptrofs.repr ?A)] =>
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr A)))
    with (A + Ptrofs.unsigned i)
    by (unfold Ptrofs.add; rewrite (Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite Ptrofs.unsigned_repr by rep_lia; rep_lia)
   end.
 rewrite (res_predicates.nonlock_permission_bytes_split2 3 1 4 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 2 1 3 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 1 1 2 sh) by lia.
 repeat change (predicates_sl.sepcon ?A ?B) with (A * B)%logic.
 rewrite !(Z.add_comm (Ptrofs.unsigned i)).
 f_equal.
Qed.

Lemma data_at_int_bytes: forall `{cs: compspecs} sh 
   (b0 b1 b2 b3 : byte) p,
  field_compatible tuint [] p  ->
  (data_at sh tuchar (Vubyte b0) p *
  data_at sh tuchar (Vubyte b1) (offset_val 1 p) *
  data_at sh tuchar (Vubyte b2) (offset_val 2 p) *
  data_at sh tuchar (Vubyte b3) (offset_val 3 p))%logic =
  data_at sh tuint (Vint (Int.repr (decode_int [b0;b1;b2;b3]))) p.
Proof.
  intros cs sh b0 b1 b2 b3 p. unfold data_at. unfold field_at. normalize. f_equal.
  - f_equal. apply prop_ext.
     split; auto.
     intros _.
     destruct H as   [? [? [? [? ?]]]].
     red in H1.
     repeat split; auto;
     destruct p; inv H0; clear - H1 H2; red; simpl; auto; simpl in H1;
     unfold Ptrofs.add;
     rewrite ?(Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite ?Ptrofs.unsigned_repr by rep_lia; try rep_lia;
     apply align_compatible_rec_by_value with Mint8unsigned; auto;
     apply Z.divide_1_l.
  - simpl. rewrite !data_at_rec_eq. simpl.
    unfold at_offset. normalize. change (unfold_reptype ?x) with x.
   assert (isptr p) by apply H.
   destruct p; inversion H0. clear H0.
    unfold mapsto. simpl.
    destruct H as [_ [_ [SZ [AL _]]]]. red in SZ. simpl sizeof in SZ.
    apply align_compatible_rec_by_value_inv with (ch := Mint32) in AL; auto.
    simpl in AL.
    destruct (readable_share_dec sh); simpl; normalize.
    + 
      rewrite !(prop_true_andp (Byte.unsigned _ <= _)) by rep_lia.
     do 5 (
      replace (EX _:val, _) with (@FF mpred _)
       by (apply pred_ext; [apply FF_left | Intros j; normalize; discriminate]);
       rewrite orp_FF).
   repeat change (?A * ?B)%logic with (predicates_sl.sepcon A B).
   apply address_mapsto_4bytes; auto.
   +
       rewrite !prop_true_andp.
      2:  split; auto; hnf; simpl; auto.
      2: repeat split; auto; try apply Z.divide_1_l; intros _; apply tc_val_Vubyte.
      apply nonlock_permission_4bytes; auto.
Qed.

(** Shorts and Chars *)

Lemma address_mapsto_2bytes_aux: 
 forall (sh : Share.t)
   (b0 b1 b2 b3 : byte)
   (b : block) (i : ptrofs)
   (SZ : Ptrofs.unsigned i + 2 < Ptrofs.modulus)
   (*(AL : (2 | Ptrofs.unsigned i))*)
   (r : readable_share sh),
predicates_sl.sepcon
  (predicates_hered.andp
     (predicates_hered.allp
        (res_predicates.jam (adr_range_dec (b, Ptrofs.unsigned i) (size_chunk Mint8unsigned))
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - snd (b, Ptrofs.unsigned i))) [Byte b0] Undef)) sh loc)
           res_predicates.noat)) res_predicates.noghost)
  (predicates_hered.andp
     (predicates_hered.allp
        (res_predicates.jam
           (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1))) (size_chunk Mint8unsigned))
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - snd (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))))
                    [Byte b1] Undef)) sh loc) res_predicates.noat)) res_predicates.noghost) = 
predicates_hered.andp
  (predicates_hered.allp
     (res_predicates.jam (adr_range_dec (b, Ptrofs.unsigned i) (size_chunk Mint16unsigned))
        (fun loc : address =>
         res_predicates.yesat compcert_rmaps.RML.R.NoneP
           (compcert_rmaps.VAL
              (nth (Z.to_nat (snd loc - snd (b, Ptrofs.unsigned i))) [Byte b0; Byte b1] Undef)) sh loc)
        res_predicates.noat)) res_predicates.noghost.
Proof.
intros. simpl snd. simpl size_chunk.
 repeat   match goal with |- context [Ptrofs.add i (Ptrofs.repr ?A)] =>
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr A)))
    with (A + Ptrofs.unsigned i)
    by (unfold Ptrofs.add; rewrite (Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite Ptrofs.unsigned_repr by rep_lia; rep_lia)
   end.
    rewrite  (res_predicates.allp_jam_split2 _ _ _ 
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0; Byte b1] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - (1+Ptrofs.unsigned i)))
                    [Byte b1] Undef)) sh loc)
           (adr_range_dec (b, Ptrofs.unsigned i) 2)
           (adr_range_dec (b, Ptrofs.unsigned i) 1)
           (adr_range_dec (b, 1 + Ptrofs.unsigned i) 1)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0; Byte b1] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - (1+Ptrofs.unsigned i)))
           [Byte b1] Undef)).
    2:{ forget (Ptrofs.unsigned i) as j. clear.
         split; intros [b1 z1]. simpl. intuition rep_lia.
         simpl. intuition rep_lia.
       }
    2:{ intros. destruct l; destruct H; subst. f_equal. f_equal.
          rewrite (app_nth1 [Byte b0] [Byte b1]); auto.
        simpl. rep_lia.
       }
    2:{ intros. f_equal. f_equal. 
       destruct l; destruct H. subst b4. simpl snd.
       assert (z = 1 + Ptrofs.unsigned i) by lia. subst z.
        rewrite Z.sub_diag.
        replace (1 + Ptrofs.unsigned i - Ptrofs.unsigned i) with 1 by lia.
          reflexivity.
      }
    2:{ intros. left. destruct H0. hnf in H0. rewrite H0 in H1 . clear H0.
        destruct l, H. subst. simpl snd in *.
        assert (Z.to_nat (z - Ptrofs.unsigned i) < 2)%nat by rep_lia.
        clear - H1. destruct (Z.to_nat (z - Ptrofs.unsigned i)) as [|[|[|]]]; inv H1; apply I.
       }
   f_equal.
Qed.

Lemma zero_ext_16: forall z,
  0 <= z < 65536 ->
  Int.zero_ext 16 (Int.repr z) = Int.repr z.
Proof.
  intros. unfold Int.zero_ext. f_equal.
  rewrite Zbits.Zzero_ext_mod by rep_lia.
  replace (two_p 16) with (65536) by reflexivity.
  rewrite Zmod_small; rewrite Int.unsigned_repr; rep_lia.
Qed.

Lemma address_mapsto_2bytes:
 forall (sh : Share.t)
    (b0 b1 : byte)
    (b : block)
    (i : ptrofs)
    (SZ : Ptrofs.unsigned i + 2 < Ptrofs.modulus)
    (AL : (2 | Ptrofs.unsigned i))
    (r : readable_share sh),
predicates_sl.sepcon (res_predicates.address_mapsto Mint8unsigned (Vubyte b0) sh (b, Ptrofs.unsigned i))
  (res_predicates.address_mapsto Mint8unsigned (Vubyte b1) sh
     (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))) = res_predicates.address_mapsto Mint16unsigned
                                                              (Vint (Int.repr (decode_int [b0; b1]))) sh
                                                              (b, Ptrofs.unsigned i).
Proof.
  intros. unfold res_predicates.address_mapsto. rewrite <- !exp_equiv.
  apply predicates_hered.pred_ext.
  - repeat change (exp ?A) with (predicates_hered.exp A).
    normalize.normalize.
    intros bl1 bl0.
    rewrite !andp_pull1.
    rewrite !predicates_sl.sepcon_andp_prop.
    normalize.normalize.
    destruct H as [A1 [ B1 _]].
    destruct H0 as [A0 [ B0 _]].
    destruct bl0 as [ | c0 [|]]; inv A0; inv B0. 
    destruct bl1 as [ | c1 [|]]; inv A1; inv B1.
    destruct c0; try discriminate.
    destruct c1; try discriminate.
    apply decode_val_Vubyte_inj in H0,H1. subst.
    apply (predicates_hered.exp_right [Byte b0; Byte b1]).
    rewrite predicates_hered.prop_true_andp.
    2:{ split3. reflexivity. unfold decode_val. simpl.
        f_equal. apply zero_ext_16. 
        pose proof (decode_int_range [b0; b1]). simpl in H.
        assert (two_power_pos 16 = 65536) by reflexivity. lia. apply AL. 
      }
  match goal with |- predicates_hered.derives ?A ?B => 
        assert (EQ: A=B); [ | rewrite EQ; apply predicates_hered.derives_refl]
    end.
  apply address_mapsto_2bytes_aux; auto.
 - repeat change (exp ?A) with (predicates_hered.exp A).
   normalize.normalize.
   intros bl.
   rewrite !andp_pull1.
   normalize.normalize.
   destruct H as [? [? ?]]. simpl snd in H1.
   destruct bl as [|c0 [| c1 [| c2 [| c3 [|]]]]]; inv H.
   unfold decode_val, proj_bytes in H0.
   destruct c0; try solve [destruct Archi.ptr64 eqn:AP; discriminate].
   destruct c1; try solve [destruct Archi.ptr64 eqn:AP; discriminate].
   apply Vint_inj in H0.
   pose proof (decode_int_range [b0;b1]).
   pose proof (decode_int_range [i0;i1]).
   change (two_p _) with 65536 in H,H2.
   rewrite zero_ext_16 in H0 by lia.
   apply repr_inj_unsigned in H0; try rep_lia.
    apply decode_int_inj in H0.
   clear H H2. inv H0.
  apply predicates_hered.exp_right with [Byte b1].
  normalize.normalize.
  apply predicates_hered.exp_right with [Byte b0].
  rewrite !predicates_hered.prop_true_andp by 
 (split3; [ reflexivity |  | apply Z.divide_1_l  ];
 unfold decode_val, Vubyte; simpl; f_equal;
 rewrite decode_int_single;
 apply zero_ext_inrange; change (two_p _ - 1) with 255;
 rewrite Int.unsigned_repr by rep_lia; rep_lia).
  match goal with |- predicates_hered.derives ?A ?B => 
        assert (EQ: B=A); [ | rewrite EQ; apply predicates_hered.derives_refl]
    end.
  apply address_mapsto_2bytes_aux; auto.
  reflexivity.
Qed.

Lemma nonlock_permission_2bytes:
 forall (sh : Share.t)
     (b : block) (i : ptrofs) 
     (SZ : Ptrofs.unsigned i + 2 < Ptrofs.modulus),
(res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned i) 1
   * res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1))) 1)%logic = 
res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned i) 2.
Proof.
intros.
 repeat   match goal with |- context [Ptrofs.add i (Ptrofs.repr ?A)] =>
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr A)))
    with (A + Ptrofs.unsigned i)
    by (unfold Ptrofs.add; rewrite (Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite Ptrofs.unsigned_repr by rep_lia; rep_lia)
   end.
 rewrite (res_predicates.nonlock_permission_bytes_split2 1 1 2 sh) by lia.
 repeat change (predicates_sl.sepcon ?A ?B) with (A * B)%logic.
 rewrite !(Z.add_comm (Ptrofs.unsigned i)).
 f_equal.
Qed.

Lemma tc_val_short: forall (b0 b1 : byte),
  tc_val tushort (Vint (Int.repr (decode_int [b0; b1]))).
Proof.
  intros. simpl. pose proof (decode_int_range [b0; b1]).
  simpl in H. assert (two_power_pos 16 = 65536) by reflexivity.
  rewrite Int.unsigned_repr; rep_lia.
Qed.

Lemma prop_true_eq: forall  {A : Type} {ND : NatDed A} (P : Prop),
  P ->
  !! P = !! True.
Proof.
  intros. apply ND_prop_ext. split; auto.
Qed.

Lemma data_at_short_bytes: forall `{cs: compspecs} sh
  (b0 b1: byte) p,
  field_compatible tushort [] p ->
  (data_at sh tuchar (Vubyte b0) p *
  data_at sh tuchar (Vubyte b1) (offset_val 1 p))%logic =
  data_at sh tushort (Vint (Int.repr (decode_int [b0; b1]))) p.
Proof.
   intros cs sh b0 b1 p. unfold data_at. unfold field_at. normalize. f_equal.
  - f_equal. apply prop_ext.
     split; auto.
     intros _.
     destruct H as   [? [? [? [? ?]]]].
     red in H1.
     repeat split; auto;
     destruct p; inv H0; clear - H1 H2; red; simpl; auto; simpl in H1;
     unfold Ptrofs.add;
     rewrite ?(Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite ?Ptrofs.unsigned_repr by rep_lia; try rep_lia;
     apply align_compatible_rec_by_value with Mint8unsigned; auto;
     apply Z.divide_1_l.
  - simpl. rewrite !data_at_rec_eq. simpl. 
    unfold at_offset. normalize. change (unfold_reptype ?x) with x.
    assert (isptr p) by apply H.
    destruct p; inversion H0. clear H0.
    unfold mapsto. rewrite (prop_true_eq _ (tc_val_short b0 b1)). simpl.
    destruct H as [_ [_ [SZ [AL _]]]]. red in SZ. simpl sizeof in SZ.
    apply align_compatible_rec_by_value_inv with (ch := Mint16unsigned) in AL; auto.
    simpl in AL.
    destruct (readable_share_dec sh); simpl; normalize.
    + 
      rewrite !(prop_true_andp (Byte.unsigned _ <= _)) by rep_lia.
     do 3 (
      replace (EX _:val, _) with (@FF mpred _)
       by (apply pred_ext; [apply FF_left | Intros j; normalize; discriminate]);
       rewrite orp_FF).
   repeat change (?A * ?B)%logic with (predicates_sl.sepcon A B).
   apply address_mapsto_2bytes; auto.
   
   +
       rewrite !prop_true_andp.
      2 : split; auto; hnf; intros; apply tc_val_short.
      2: repeat split; auto; try apply Z.divide_1_l; intros _; apply tc_val_Vubyte.
      apply nonlock_permission_2bytes; auto.
Qed.

