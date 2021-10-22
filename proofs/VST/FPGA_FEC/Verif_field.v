(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

Require Import VST.floyd.proofauto.

Require Import FPGA_FEC.Specs.
Require Import fpga.
Require Import ByteField.
Require Import ZSeq.
Require Import ByteFacts.
Require Import FECTactics.

Ltac simpl_map :=
  repeat lazymatch goal with
  | [ |- context [ Znth ?i (map ?f byte_logs) ]] => rewrite Znth_map by (rewrite byte_logs_Zlength; rep_lia)
  | [ |- context [ Znth ?i (map ?f byte_pows) ]] => rewrite Znth_map by (rewrite byte_pows_Zlength; rep_lia)
  end.

(** Verification of [mult] *)
Lemma body_mult : semax_body Vprog Gprog f_mult mult_spec.
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

(** Verification of [generate_field_tables]*)

Lemma body_generate_field_tables : semax_body Vprog Gprog f_generate_field_tables generate_field_tables_spec.
Proof.
start_function. replace 285 with modulus by rep_lia. forward.
forward_loop (EX (i: Z),
  PROP (0 <= i <= fec_n)
  LOCAL (temp _i (Vint (Int.repr i)); temp _mod (Vint (Int.repr modulus)); gvars gv)
  SEP (data_at Ews (tarray tuchar fec_n) (map Vubyte (fst (populate_pows_logs i))) (gv _fec_2_index);
       data_at Ews (tarray tuchar fec_n) (map Vubyte (snd (populate_pows_logs i))) (gv _fec_2_power)))
  break: (PROP () LOCAL (temp _mod (Vint (Int.repr modulus)); gvars gv)
          SEP (INDEX_TABLES gv)).
{ forward. Exists 0%Z. entailer!. rewrite populate_pows_logs_0; simpl fst; simpl snd.
  assert (Hz: (zseq fec_n (Vubyte Byte.zero)) =  (map Vubyte (zseq Byte.modulus Byte.zero))). {
    replace fec_n with Byte.modulus by rep_lia. rewrite zseq_map. reflexivity. }
  rewrite Hz. cancel.
}
{ Intros i. forward_if.
  { forward_if (PROP ()
   LOCAL (temp _mod (Vint (Int.repr modulus)); temp _i (Vint (Int.repr i)); gvars gv)
   SEP (data_at Ews (tarray tuchar fec_n) (map Vubyte (fst (populate_pows_logs (i+1)))) (gv _fec_2_index);
       data_at Ews (tarray tuchar fec_n) (map Vubyte (snd (populate_pows_logs i))) (gv _fec_2_power))).
    { forward; entailer!. }
    { forward.
      { entailer!. apply is_int_Vubyte. }
      { forward. rewrite Znth_map by (rewrite populate_pows_logs_length1; rep_lia).
        (*forward_if. *)
        forward_if; rewrite byte_shiftl1' in H2; forward; entailer!. 
        { unfold Int.xor. rewrite byte_shiftl1'. rewrite Int.unsigned_repr by rep_lia.
          rewrite populate_pows_logs_plus_1 by lia. destruct (Z.eq_dec i 0); try lia. unfold proj_sumbool.
          unfold byte_mulX. simpl in *.
          destruct (Z_lt_ge_dec (2 * Byte.unsigned (Znth (i - 1) (fst (populate_pows_logs i)))) Byte.modulus); try rep_lia.
          simpl. rewrite <- upd_Znth_map. unfold Vubyte.
          pose proof (xor_modulus_bound H2) as Hbound. simpl_repr_byte.
        }
        { unfold Int.zero_ext. rewrite byte_shiftl1'.
          assert (Hnonneg: 0 <= Z.shiftl (Byte.unsigned (Znth (i - 1) (fst (populate_pows_logs i)))) 1). {
            rewrite Z.shiftl_nonneg. rep_lia. } simpl_repr_byte.
          rewrite populate_pows_logs_plus_1 by lia. destruct (Z.eq_dec i 0); try lia; simpl.
          unfold byte_mulX; simpl in *.
          destruct (Z_lt_ge_dec (2 * Byte.unsigned (Znth (i - 1) (fst (populate_pows_logs i)))) Byte.modulus); try rep_lia; simpl.
          rewrite <- upd_Znth_map. unfold Vubyte. simpl_repr_byte.
        }
      }
    }
    { forward; [entailer! | entailer! |].
      { rewrite Znth_map. apply is_int_Vubyte. rewrite populate_pows_logs_length1. rep_lia. }
      { rewrite Znth_map. 2: rewrite populate_pows_logs_length1; rep_lia. forward; [entailer! |].
        forward. Exists (i+1). entailer!. 
        rewrite populate_pows_logs_plus_1 at 2 by lia; simpl. destruct (Z.eq_dec i 0); try lia; simpl.
        { subst. rewrite populate_pows_logs_0. apply derives_refl'. apply data_at_ext_eq; [| auto]. reflexivity. }
        { rewrite <- upd_Znth_map. unfold Vubyte. simpl_repr_byte. }
      }
    }
  }
  { forward. entailer!. unfold INDEX_TABLES.
    replace i with Byte.modulus by rep_lia. rewrite !populate_pows_logs_correct. cancel.
  }
}
entailer!.
Qed.