Require Import VST.floyd.proofauto.

(*Require Import Common.
Require Import CommonVST.*)
Require Import Specs.
Require Import fec.
Require Import ByteField.
Require Import ZSeq.
(*Require Import Poly.
Require Import FECTactics.*)

Set Bullet Behavior "Strict Subproofs".

(** Verification of [fec_find_mod]*)

Lemma body_fec_find_mod : semax_body Vprog Gprog f_fec_find_mod fec_find_mod_spec.
Proof.
start_function. 
forward_if (PROP () LOCAL (temp _modulus (Vint (Int.repr modulus))) SEP ()); try lia.
- forward. forward. entailer!. f_equal. f_equal. rep_lia.
- forward.
Qed.


(** Verification of [fec_gf_mult] *)
(*
(*Verification of multiply function *)
Lemma body_fec_gf_mult : semax_body Vprog Gprog f_fec_gf_mult fec_gf_mult_spec.
Proof.
  start_function.
  forward_if (
    PROP ()
    LOCAL (temp _t'1 (Vint (Int.repr (if Z.eq_dec f 0%Z then 0%Z else if Z.eq_dec g 0%Z then 0%Z else 1%Z)));
     temp _a (Vint (Int.repr f)); temp _b (Vint (Int.repr g)); gvars gv)
    SEP (INDEX_TABLES gv)).
  - forward. entailer!. f_equal. repeat(if_tac; subst; try contradiction; try reflexivity).
    rewrite (ssrbool.introF (Int_eq_reflect (Int.repr g) Int.zero)); auto. 
    intro Hg. apply repr_inj_unsigned in Hg; rep_lia.
  - forward. entailer!. if_tac. reflexivity. 
    apply repr_inj_unsigned in H1; rep_lia.
  - forward_if.
    + destruct H as [Hf Hg]. destruct (Z.eq_dec f 0) as [? | Hf0]. contradiction.
      destruct (Z.eq_dec g 0) as [? | Hg0]. contradiction. clear H1 H1'. deadvars!.
      unfold INDEX_TABLES. Intros.
      forward.
      * entailer!. rewrite index_to_power_contents_Znth by lia. simpl_repr.
      * forward.
        -- entailer!. rewrite index_to_power_contents_Znth by lia. simpl_repr. 
        -- pose_power (poly_of_int f) Hfp Hfp_bound. pose_power (poly_of_int g) Hgp Hgp_bound.
          (*for i + j > fec_n - 1, get conditional in usable form*)
           rewrite? index_to_power_contents_Znth by lia. 
           forward_if.
          ++ forward. (*overflow case*)
             ** entailer!. rewrite index_to_power_contents_Znth by lia. simpl_repr.
             ** forward. 
                --- entailer!. rewrite index_to_power_contents_Znth by lia. simpl_repr.
                --- rewrite !index_to_power_contents_Znth by lia. forward.
                  +++ entailer!.
                  +++ entailer!. rewrite power_to_index_contents_Znth by rep_lia. simpl_repr.
                  +++ forward. unfold INDEX_TABLES. entailer!. (*now, we prove that this actually computes the product for this case*)
                      rewrite power_to_index_contents_Znth by rep_lia. f_equal. f_equal. f_equal.
                      rewrite Hfp at 2. rewrite Hgp at 2. rewrite <- pmod_mult_distr; [| apply mod_poly_PosPoly].
                      rewrite (monomial_exp_law). rewrite (@monomial_add_field_size mod_poly _ mod_poly_PrimPoly).
                      f_equal. f_equal. pose proof field_size_fec_n. rep_lia.
          ++ (*other side of the if statement*) forward.
            ** entailer!. rewrite index_to_power_contents_Znth by lia. simpl_repr. 
            ** forward. 
                --- entailer!. rewrite index_to_power_contents_Znth by lia. simpl_repr. 
                --- rewrite !index_to_power_contents_Znth by lia. forward.
                  +++ entailer!.
                  +++ entailer!. rewrite power_to_index_contents_Znth by rep_lia. simpl_repr. 
                  +++ forward. entailer!. (*now the easier, but similar case*) 
                      rewrite power_to_index_contents_Znth by rep_lia. f_equal. f_equal. f_equal. 
                      rewrite Z2Nat.inj_add by rep_lia.
                      rewrite <- monomial_exp_law. rewrite pmod_mult_distr; [| apply mod_poly_PosPoly].
                      rewrite <- Hfp. rewrite <- Hgp. reflexivity.
    + if_tac; subst.
      * forward. entailer!. rewrite_zero. rewrite poly_mult_0_l. rewrite pmod_zero; auto. apply mod_poly_PosPoly.
      * if_tac; subst.
        -- forward. entailer!. rewrite_zero. rewrite poly_mult_0_r. rewrite pmod_zero; auto. apply mod_poly_PosPoly.
        -- inversion H1.
Qed. *)

Lemma zbits_small: forall i,
  0 <= i < Byte.modulus ->
  Zbits.Zzero_ext 8 i = i.
Proof.
  intros i Hi. rewrite Zbits.Zzero_ext_mod; [|rep_lia]. replace (two_p 8) with (256) by reflexivity.
  rewrite Zmod_small; rep_lia.
Qed.

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

(** Verification of [fec_generate_math_tables]*)

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
    { forward.
      { entailer!. }
      { entailer!. }
    }
    { forward.
      { entailer!. apply is_int_Vubyte. }
      { forward. rewrite Znth_map. 2: { rewrite populate_pows_logs_length1. rep_lia. }
        forward_if.
        { rewrite byte_shiftl1 in H2. forward. 
          { entailer!. }
          { entailer!. unfold Int.xor. rewrite byte_shiftl1'. rewrite !Int.unsigned_repr by rep_lia.
            rewrite populate_pows_logs_plus_1 by lia. destruct (Z.eq_dec i 0); try lia. unfold proj_sumbool.
            unfold byte_mulX. simpl in *.
            destruct (Z_lt_ge_dec (2 * Byte.unsigned (Znth (i - 1) (fst (populate_pows_logs i)))) Byte.modulus); try rep_lia.
            simpl. rewrite <- upd_Znth_map. unfold Vubyte. unfold Int.zero_ext.
            pose proof (xor_modulus_bound H2) as Hbound. rewrite <- p256_val_modulus.
            rewrite !Int.unsigned_repr by rep_lia. rewrite zbits_small by rep_lia.
            rewrite Byte.unsigned_repr; [|rep_lia ]. cancel.
          }
        }
        { rewrite byte_shiftl1 in H2. forward.
          { entailer!. }
          { entailer!. unfold Int.zero_ext. rewrite byte_shiftl1'.
            assert (Hnonneg: 0 <= Z.shiftl (Byte.unsigned (Znth (i - 1) (fst (populate_pows_logs i)))) 1). {
              rewrite Z.shiftl_nonneg. rep_lia. } rewrite zbits_small by rep_lia.
            rewrite populate_pows_logs_plus_1 by lia. destruct (Z.eq_dec i 0); try lia; simpl.
            unfold byte_mulX; simpl in *.
            destruct (Z_lt_ge_dec (2 * Byte.unsigned (Znth (i - 1) (fst (populate_pows_logs i)))) Byte.modulus); try rep_lia; simpl.
            rewrite <- upd_Znth_map. unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. cancel.
          }
        }
      }
    }
    { forward.
      { entailer!. }
      { entailer!. rewrite Znth_map. apply is_int_Vubyte. rewrite populate_pows_logs_length1. rep_lia. }
      { rewrite Znth_map. 2: rewrite populate_pows_logs_length1; rep_lia. forward.
        { entailer!. }
        { forward. Exists (i+1). entailer!. 
          rewrite populate_pows_logs_plus_1 at 2 by lia; simpl. destruct (Z.eq_dec i 0); try lia; simpl.
          { subst. rewrite populate_pows_logs_0. apply derives_refl'. apply data_at_ext_eq; [| auto]. reflexivity. }
          { rewrite <- upd_Znth_map. unfold Int.zero_ext. rewrite Int.unsigned_repr by rep_lia.
            rewrite zbits_small by rep_lia. unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. cancel. }
        }
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
  { unfold INDEX_TABLES. Intros. forward. (*why is this slow?*)
    { rewrite Znth_map by (rewrite byte_logs_Zlength; rep_lia).
      entailer!. rep_lia. }
    { rewrite Znth_map by (rewrite byte_logs_Zlength; rep_lia).
      forward. (*also slow*)
      { entailer!. }
      { rewrite Znth_map by (rewrite byte_pows_Zlength; rep_lia). entailer!. rep_lia. }
      { rewrite Znth_map by (rewrite byte_pows_Zlength; rep_lia). 
        forward.
        { entailer!. }
        { entailer!. unfold INDEX_TABLES. cancel. rewrite populate_invs_plus_1 by lia.
          rewrite byte_logs_Znth by rep_lia. rewrite byte_pows_Znth by rep_lia.
          rewrite <- upd_Znth_map. replace (fec_n -1) with 255%Z by rep_lia.
          apply derives_refl'. apply data_at_ext_eq; [| reflexivity]. f_equal.
          unfold Int.zero_ext. rewrite Int.unsigned_repr by rep_lia. rewrite zbits_small by rep_lia.
          unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
        }
      }
    }
  }
  { entailer!. unfold FIELD_TABLES. cancel. replace fec_n with Byte.modulus by rep_lia.
    rewrite populate_invs_correct. cancel.
  }
}
Qed.

(*TODO: tactic for unsigned_repr, zbits, unfold Vubyte, etc*)
 