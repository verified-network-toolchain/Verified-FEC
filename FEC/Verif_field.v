Require Import VST.floyd.proofauto.

Require Import Specs.
Require Import fec.
Require Import ByteField.
Require Import ZSeq.

Set Bullet Behavior "Strict Subproofs".

(** Verification of [fec_find_mod]*)

Lemma body_fec_find_mod : semax_body Vprog Gprog f_fec_find_mod fec_find_mod_spec.
Proof.
start_function. 
forward_if (PROP () LOCAL (temp _modulus (Vint (Int.repr modulus))) SEP ()); try lia.
- forward. forward. entailer!. f_equal. f_equal. rep_lia.
- forward.
Qed.

Lemma zbits_small: forall i,
  0 <= i < Byte.modulus ->
  Zbits.Zzero_ext 8 i = i.
Proof.
  intros i Hi. rewrite Zbits.Zzero_ext_mod; [|rep_lia]. replace (two_p 8) with (256) by reflexivity.
  rewrite Zmod_small; rep_lia.
Qed.

Lemma Int_repr_zero: forall z,
  0 <= z <= Int.max_unsigned ->
  Int.repr z = Int.zero <-> z = 0.
Proof.
  intros z Hz. split; intros Hzero.
  - unfold Int.zero in Hzero. apply repr_inj_unsigned in Hzero; rep_lia.
  - subst. reflexivity.
Qed.

Ltac simpl_map :=
  repeat lazymatch goal with
  | [ |- context [ Znth ?i (map ?f byte_logs) ]] => rewrite Znth_map by (rewrite byte_logs_Zlength; rep_lia)
  | [ |- context [ Znth ?i (map ?f byte_pows) ]] => rewrite Znth_map by (rewrite byte_pows_Zlength; rep_lia)
  end.

(** Verification of [fec_gf_mult] *)
Lemma body_fec_gf_mult : semax_body Vprog Gprog f_fec_gf_mult fec_gf_mult_spec.
Proof.
  start_function.
  forward_if (
    PROP ()
    LOCAL (temp _t'1 (Vubyte (if Byte.eq_dec b1 Byte.zero then Byte.zero else 
                              if Byte.eq_dec b2 Byte.zero then Byte.zero else Byte.one));
     temp _a (Vubyte b1); temp _b (Vubyte b2); gvars gv)
    SEP (INDEX_TABLES gv)).
  - forward. entailer!. if_tac. subst. rewrite Byte.unsigned_zero in H'; contradiction.
    if_tac. subst. rewrite Byte.unsigned_zero. reflexivity.
    destruct (Int.eq (Int.repr (Byte.unsigned b2)) Int.zero) eqn : Hb20. apply Int.same_if_eq in Hb20.
    apply Int_repr_zero in Hb20; [| rep_lia]. apply byte_unsigned_zero in Hb20. contradiction.
    reflexivity.
  - forward. entailer!. rewrite Int_repr_zero in H by rep_lia. apply byte_unsigned_zero in H. subst.
    if_tac; [reflexivity |contradiction].
  - forward_if.
    { destruct (Byte.eq_dec b1 Byte.zero) as [|Hb1]; [contradiction |].
      destruct (Byte.eq_dec b2 Byte.zero) as [|Hb2]; [contradiction |]. clear H H'.
      unfold INDEX_TABLES. Intros. forward; simpl_map; [ entailer! | entailer!; rep_lia |].
      forward; simpl_map; [ entailer! | entailer!; rep_lia |].
      forward_if; simpl_map.
      { forward; simpl_map; [entailer! | entailer! | ].
        forward; simpl_map; [entailer! | entailer! | ].
        forward; simpl_map; [ entailer! | entailer!; rep_lia |]. forward. 
        unfold INDEX_TABLES. entailer!. revert H. rewrite !byte_logs_Znth by rep_lia. 
        rewrite !Byte.repr_unsigned. intros Hlarge. rewrite byte_pows_Znth by rep_lia.
        replace 255 with (fec_n - 1) by rep_lia.
        rewrite mult_large by rep_lia. reflexivity.
      }
      { forward; simpl_map; [entailer! | entailer! | ].
        forward; simpl_map; [entailer! | entailer! | ].
        forward; simpl_map; [ entailer! | entailer!; rep_lia |]. forward. 
        unfold INDEX_TABLES. entailer!. revert H. rewrite !byte_logs_Znth by rep_lia. 
        rewrite !Byte.repr_unsigned. intros Hlarge. rewrite byte_pows_Znth by rep_lia.
        replace 255 with (fec_n - 1) by rep_lia.
        rewrite mult_small by (try assumption; rep_lia). reflexivity.
      }
    }
    { destruct (Byte.eq_dec b1 Byte.zero) as [ Hb1 |Hb1].
      { forward. entailer!. rewrite (@ssralg.GRing.mul0r byte_ring). reflexivity. }
      { destruct (Byte.eq_dec b2 Byte.zero) as [Hb2|].
        { subst. forward. entailer!.  rewrite (@ssralg.GRing.mulr0 byte_ring). reflexivity. }
        { rewrite Int_repr_zero in H by rep_lia. apply byte_unsigned_zero in H. inversion H. }
      }
    }
Qed.

(** Verification of [fec_generate_math_tables]*)

Lemma is_int_Vubyte: forall b: byte, is_int I8 Unsigned (Vubyte b).
Proof.
  intros b. simpl. pose proof (Byte.unsigned_range_2 b) as Hrange.
  rewrite Int.unsigned_repr; rep_lia.
Qed. 

Lemma byte_shiftl1: forall b: byte,
  Int.signed (Int.shl (Int.repr (Byte.unsigned b)) (Int.repr 1)) =
  Z.shiftl (Byte.unsigned b) 1.
Proof.
  intros b. unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia.
  apply Int.signed_repr. rewrite Z.shiftl_mul_pow2; rep_lia.
Qed.

(*TODO: how to generalize this?*)
Lemma byte_shiftl1': forall b: byte,
  Int.unsigned (Int.shl (Int.repr (Byte.unsigned b)) (Int.repr 1)) =
  Z.shiftl (Byte.unsigned b) 1.
Proof.
  intros b. unfold Int.shl. rewrite (Int.unsigned_repr 1) by rep_lia. 
  rewrite (Int.unsigned_repr (Byte.unsigned b)) by rep_lia.
  apply Int.unsigned_repr. rewrite Z.shiftl_mul_pow2; rep_lia.
Qed.

Lemma p256_val_modulus: p256_val = modulus.
Proof.
  unfold p256_val. rep_lia.
Qed.


Lemma body_fec_generate_math_tables : semax_body Vprog Gprog f_fec_generate_math_tables fec_generate_math_tables_spec.
Proof.
start_function.
forward_call.
forward_loop (EX (i: Z),
  PROP (0 <= i <= fec_n)
  LOCAL (temp _i (Vint (Int.repr i)); temp _mod (Vint (Int.repr modulus)); gvars gv)
  SEP (data_at Ews (tarray tuchar fec_n) (map Vubyte (fst (populate_pows_logs i))) (gv _fec_2_index);
       data_at Ews (tarray tuchar fec_n) (map Vubyte (snd (populate_pows_logs i))) (gv _fec_2_power);
       data_at Ews (tarray tuchar fec_n) (zseq fec_n (Vubyte Byte.zero)) (gv _fec_invefec)))
  break: (PROP () LOCAL (temp _mod (Vint (Int.repr modulus)); gvars gv)
          SEP (INDEX_TABLES gv;
               data_at Ews (tarray tuchar fec_n) (zseq fec_n (Vubyte Byte.zero)) (gv _fec_invefec))).
{ forward. Exists 0%Z. entailer!. rewrite populate_pows_logs_0; simpl fst; simpl snd.
  assert (Hz: (zseq fec_n (Vubyte Byte.zero)) =  (map Vubyte (zseq Byte.modulus Byte.zero))). {
    replace fec_n with Byte.modulus by rep_lia. rewrite zseq_map. reflexivity. }
  rewrite Hz. cancel.
}
{ Intros i. forward_if.
  { forward_if (PROP ()
   LOCAL (temp _mod (Vint (Int.repr modulus)); temp _i (Vint (Int.repr i)); gvars gv)
   SEP (data_at Ews (tarray tuchar fec_n) (map Vubyte (fst (populate_pows_logs (i+1)))) (gv _fec_2_index);
       data_at Ews (tarray tuchar fec_n) (map Vubyte (snd (populate_pows_logs i))) (gv _fec_2_power);
       data_at Ews (tarray tuchar fec_n) (zseq fec_n (Vubyte Byte.zero)) (gv _fec_invefec))).
    { forward; entailer!. }
    { forward.
      { entailer!. apply is_int_Vubyte. }
      { forward. rewrite Znth_map by (rewrite populate_pows_logs_length1; rep_lia).
        forward_if; rewrite byte_shiftl1 in H2; forward; entailer!. 
        { unfold Int.xor. rewrite byte_shiftl1'. rewrite !Int.unsigned_repr by rep_lia.
          rewrite populate_pows_logs_plus_1 by lia. destruct (Z.eq_dec i 0); try lia. unfold proj_sumbool.
          unfold byte_mulX. simpl in *.
          destruct (Z_lt_ge_dec (2 * Byte.unsigned (Znth (i - 1) (fst (populate_pows_logs i)))) Byte.modulus); try rep_lia.
          simpl. rewrite <- upd_Znth_map. unfold Vubyte. unfold Int.zero_ext.
          pose proof (xor_modulus_bound H2) as Hbound. rewrite <- p256_val_modulus.
          rewrite !Int.unsigned_repr by rep_lia. rewrite zbits_small by rep_lia.
          rewrite Byte.unsigned_repr; [|rep_lia ]. cancel.
        }
        { unfold Int.zero_ext. rewrite byte_shiftl1'.
          assert (Hnonneg: 0 <= Z.shiftl (Byte.unsigned (Znth (i - 1) (fst (populate_pows_logs i)))) 1). {
            rewrite Z.shiftl_nonneg. rep_lia. } rewrite zbits_small by rep_lia.
          rewrite populate_pows_logs_plus_1 by lia. destruct (Z.eq_dec i 0); try lia; simpl.
          unfold byte_mulX; simpl in *.
          destruct (Z_lt_ge_dec (2 * Byte.unsigned (Znth (i - 1) (fst (populate_pows_logs i)))) Byte.modulus); try rep_lia; simpl.
          rewrite <- upd_Znth_map. unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. cancel.
        }
      }
    }
    { forward; [entailer! | entailer! |].
      { rewrite Znth_map. apply is_int_Vubyte. rewrite populate_pows_logs_length1. rep_lia. }
      { rewrite Znth_map. 2: rewrite populate_pows_logs_length1; rep_lia. forward; [entailer! |].
        forward. Exists (i+1). entailer!. 
        rewrite populate_pows_logs_plus_1 at 2 by lia; simpl. destruct (Z.eq_dec i 0); try lia; simpl.
        { subst. rewrite populate_pows_logs_0. apply derives_refl'. apply data_at_ext_eq; [| auto]. reflexivity. }
        { rewrite <- upd_Znth_map. unfold Int.zero_ext. rewrite Int.unsigned_repr by rep_lia.
          rewrite zbits_small by rep_lia. unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. cancel. }
      }
    }
  }
  { forward. entailer!. unfold INDEX_TABLES.
    replace i with Byte.modulus by rep_lia. rewrite !populate_pows_logs_correct. cancel.
  }
}
{ (*TODO: forward_loop doesn't work here for some reason*)
  forward_for_simple_bound fec_n (EX (i : Z),
    PROP ()
    LOCAL (temp _mod (Vint (Int.repr modulus)); gvars gv)
    SEP (INDEX_TABLES gv;
         data_at Ews (tarray tuchar fec_n) (map Vubyte (populate_invs i)) (gv _fec_invefec))).
  { f_equal. rep_lia. }
  { entailer!. rewrite populate_invs_0. rewrite zseq_map. replace fec_n with Byte.modulus by rep_lia. cancel. }
  { unfold INDEX_TABLES. Intros. forward.
    { rewrite Znth_map by (rewrite byte_logs_Zlength; rep_lia).
      entailer!. rep_lia. }
    { rewrite Znth_map by (rewrite byte_logs_Zlength; rep_lia).
      forward; simpl_map; [ entailer! | entailer!; rep_lia |].
      forward; entailer!. unfold INDEX_TABLES. cancel. rewrite populate_invs_plus_1 by lia.
      rewrite byte_logs_Znth by rep_lia. rewrite byte_pows_Znth by rep_lia.
      rewrite <- upd_Znth_map. replace (fec_n -1) with 255%Z by rep_lia.
      apply derives_refl'. apply data_at_ext_eq; [| reflexivity]. f_equal.
      unfold Int.zero_ext. rewrite Int.unsigned_repr by rep_lia. rewrite zbits_small by rep_lia.
      unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
    }
  }
  { entailer!. unfold FIELD_TABLES. cancel. replace fec_n with Byte.modulus by rep_lia.
    rewrite populate_invs_correct. cancel.
  }
}
Qed.

(*TODO: tactic for unsigned_repr, zbits, unfold Vubyte, etc*)
 