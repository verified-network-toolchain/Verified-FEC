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
(*
Lemma body_fec_find_mod : semax_body Vprog Gprog f_fec_find_mod fec_find_mod_spec.
Proof.
start_function. 
(*TODO: why doesn't this work, and how to prove a switch statement in which only 1 branch can be taken?*)
forward_if (PROP () LOCAL (temp _modulus (Vint (Int.repr modulus))) SEP ()).
*)


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

(*TODO: figure out common*)
Lemma unsigned_repr: forall z,
  0 <= z < Int.modulus -> Int.unsigned (Int.repr z) = z.
Proof.
  intros.
  pose proof (Int.eqm_unsigned_repr z).
  apply Int.eqm_sym in H0.
  unfold Int.eqm in H0. eapply Zbits.eqmod_small_eq. apply H0. all: rep_lia. 
Qed.

Lemma zbits_small: forall i,
  0 <= i < Byte.modulus ->
  Zbits.Zzero_ext 8 i = i.
Proof.
  intros i Hi. rewrite Zbits.Zzero_ext_mod; [|rep_lia]. replace (two_p 8) with (256) by reflexivity.
  rewrite Zmod_small; rep_lia.
Qed.

Lemma byte_unsigned_repr: forall z,
  0 <= z < Byte.modulus -> Byte.unsigned (Byte.repr z) = z.
Proof.
  intros z Hz. rewrite Byte.unsigned_repr_eq.  apply Z.mod_small. apply Hz.
Qed.

Lemma is_int_Vubyte: forall b: byte, is_int I8 Unsigned (Vubyte b).
Proof.
  intros b. simpl. pose proof (Byte.unsigned_range_2 b) as Hrange.
  rewrite unsigned_repr; rep_lia.
Qed. 

Lemma byte_shiftl1: forall b: byte,
  Int.signed (Int.shl (Int.repr (Byte.unsigned b)) (Int.repr 1)) =
  Z.shiftl (Byte.unsigned b) 1.
Proof.
  intros b. unfold Int.shl. rewrite !unsigned_repr by rep_lia.
  apply Int.signed_repr. rewrite Z.shiftl_mul_pow2; rep_lia.
Qed.

(*TODO: how to generalize this?*)
Lemma byte_shiftl1': forall b: byte,
  Int.unsigned (Int.shl (Int.repr (Byte.unsigned b)) (Int.repr 1)) =
  Z.shiftl (Byte.unsigned b) 1.
Proof.
  intros b. unfold Int.shl. rewrite (unsigned_repr 1) by rep_lia. 
  rewrite (unsigned_repr (Byte.unsigned b)) by rep_lia.
  apply unsigned_repr. rewrite Z.shiftl_mul_pow2; rep_lia.
Qed.

(*Let's see*)
Lemma testbit_lt: forall m z1 z2,
  0 <= m ->
  (*0 <= z1 ->*)
  2 <= z2 ->
  (forall n, m <= n -> Z.testbit z1 n = false) ->
  Z.testbit z2 m = true ->
  Z.log2 z1 < Z.log2 z2.
Proof.
  intros m z1 z2 Hm Hz2 Hafter Htestm.
  assert (Hz1: z1 <= 0 \/ 0 < z1) by lia. destruct Hz1 as [Hz1 | Hz1].
  - rewrite Z.log2_nonpos; [| apply Hz1]. apply Z.log2_le_mono in Hz2. simpl in Hz2. lia.
  - assert (Hmlog: m <= Z.log2 z2). { assert (m <= Z.log2 z2 \/ Z.log2 z2 < m) as Hlogcase by lia.
     destruct Hlogcase as [H|Hlogm]; [lia|]. apply Z.bits_above_log2 in Hlogm; [| lia].
      rewrite Hlogm in Htestm. inversion Htestm. } 
    assert ( Hz12comp: Z.log2 z1 < Z.log2 z2 \/ Z.log2 z2 <= Z.log2 z1) by lia.
    destruct Hz12comp as [Hz12 | Hz12]; [assumption |].
    assert (Htestf: Z.testbit z1 (Z.log2 z1) = false). apply Hafter; lia.
    rewrite Z.bit_log2 in Htestf. inversion Htestf. apply Hz1.
Qed.

(*This is actually not too easy to prove*)
Lemma Z_lxor_smaller: forall z1 z2,
  2 <= z1 ->
  Z.log2 z1 = Z.log2 z2 ->
  Z.log2 (Z.lxor z1 z2) < Z.log2 z1.
Proof.
  intros z1 z2 Hz1 Hlog. assert (Hz2: 2 <= z2). { assert ( Hz2: 1 <= Z.log2 z2).
    rewrite <- Hlog. apply  Z.log2_le_mono in Hz1. simpl in Hz1. apply Hz1.
    assert (Hcase: z2 <= 1 \/ 2 <= z2) by lia. destruct Hcase as [Hz21 | Hz22]; [| assumption].
    rewrite <- Z.log2_null in Hz21. lia. }
  apply (testbit_lt (Z.log2 z1)).
  - apply Z.log2_nonneg.
  - assumption.
  - intros n Hn. rewrite Z.lxor_spec. 
    assert (Hzn: Z.log2 z1 = n \/ Z.log2 z1 < n) by lia. destruct Hzn as [Hzn | Hzn].
    + subst. rewrite Hlog at 2. rewrite !Z.bit_log2 by lia. reflexivity.
    + rewrite !Z.bits_above_log2 by lia. reflexivity.
  - apply Z.bit_log2. lia.
Qed.

(*Now, we can prove the result we want*)
Lemma xor_modulus_bound: forall (b: byte),
  2 * Byte.unsigned b >= Byte.modulus ->
  0 <= Z.lxor (2 * Byte.unsigned b) modulus < Byte.modulus.
Proof.
  intros b Hlarge. split.
  - rewrite Z.lxor_nonneg. rep_lia.
  - assert (Hb: Byte.unsigned b <= 255) by rep_lia.
    apply Z.log2_le_mono in Hb. simpl in Hb. 
    assert (H2b: Z.log2 (2 * (Byte.unsigned b)) = 1 + Z.log2 (Byte.unsigned b)).
      rewrite Z.log2_double. lia. rep_lia. 
    assert (H2b': Z.log2 256 <= Z.log2 (2 * Byte.unsigned b)). apply Z.log2_le_mono. rep_lia.
    simpl in H2b'. assert (Hlog: Z.log2 (2 * Byte.unsigned b) = 8) by lia.
    assert (Hmod: Z.log2 modulus = 8). replace modulus with 285 by rep_lia. reflexivity.
    assert (Hxor: Z.log2 (Z.lxor (2 * Byte.unsigned b) modulus) < 8). rewrite <- Hlog. apply Z_lxor_smaller.
    rep_lia. lia. apply Z.log2_lt_cancel. simpl. apply Hxor.
Qed.


(*What we need to know:
  We have a byte b such that 2 * b >= Byte.modulus.
  Want to know that Z.lxor b p256_val < Byte.modulus

what about?
if Z.log2 z1 = Z.log2 z2, then Z.log2 (Z.lxor z1 z2) < Z.log2 z1.
So we have that Z.log2 b + 1 = 9, so Z.lodg2 (Z.lxor z1 z2) < 8,so Z.lxor z1 z2 < 256
- lets try this (though we need to prove the other thing anyway)*) 

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
        (*TODO: change the definition to use Znth of the previous instead of rewriting it out*)
        forward_if.
        { rewrite byte_shiftl1 in H2. forward. 
          { entailer!. }
          { entailer!. unfold Int.xor. rewrite byte_shiftl1'. rewrite !unsigned_repr by rep_lia.
            rewrite populate_pows_logs_plus_1 by lia. destruct (Z.eq_dec i 0); try lia. unfold proj_sumbool.
            unfold byte_mulX. simpl in *.
            destruct (Z_lt_ge_dec (2 * Byte.unsigned (Znth (i - 1) (fst (populate_pows_logs i)))) Byte.modulus); try rep_lia.
            simpl. rewrite <- upd_Znth_map. unfold Vubyte. unfold Int.zero_ext.
            pose proof (xor_modulus_bound _ H2) as Hbound.
            rewrite !unsigned_repr by rep_lia. rewrite zbits_small by rep_lia.
            rewrite p256_val_modulus. rewrite byte_unsigned_repr; [|apply Hbound]. cancel.
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
            rewrite <- upd_Znth_map. unfold Vubyte. rewrite byte_unsigned_repr by rep_lia. cancel.
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
            rewrite zbits_small by rep_lia. unfold Vubyte. rewrite byte_unsigned_repr by rep_lia. cancel. }
        }
      }
    }
  }
  { forward. (*Now, need to prove correctness*)
        {
          {


 cancel.


 cancel. rewrite populate_pows_logs_plus_1.



            rewrite upd_Znth_same. reflexivity. simpl.


 Search data_at.


 by rep_lia.



 simpl.


 rewrite Znth_map. entailer!.   
        {


 unfold proj_sumbool.


Z.shiftl_nonneg
            Search Z.shiftl (_ <= ?x).


 entailer
          {


 Search Z.lxor (_ <= _).
            
 Search Z.lxor.



  So Z.lxor z1 z2 <  

Why?
As polynomials, shift puts a 0 in front. So size (shift f) = 1 + size f. Since size f < 9 and 1 + size f >= 9,
  size f = 8. So p256 and 



 simpl.






 rewrite <- Int.signed_eq_unsigned. Search Int.shl.


 Search Int.signed Int.unsigned.


 rewrite byte_shiftl1. rewrite Znth_map.
            - simpl. unfold Int.shl. rewrite !unsigned_repr by rep_lia. unfold Int.xor.
              rewrite !unsigned_repr; try rep_lia. 2: { rewrite Z.shiftl_mul_pow2 by lia.
              rep_lia. } a.

 Search Z.shiftl.


  unfold sem_shift_ii. Print Vubyte. simpl.



 Search is_int.


 simpl.

 admit. admit.


pose proof mod_poly_PrimPoly as Hprimpoly.
pose proof mod_poly_PosPoly as Hpospoly.
(*loop invariants
  1. fec_2_index: filled out up to ith position, this is relatively straightforward to specity
  2. fec_2_power: is a list l such that for all z, 0 < z < fec_n ->
      find_power (poly_of_int z) <= i ->
      Znth l z = index_of_poly (poly_of_int z)
  this way, when we finish, all elements are present
  0 is an annoying special case. - 0th index is not used, so find_power[0] = 0*) 
  forward_loop (EX (i : Z) (l: list Z),
    PROP (0 <= i <= fec_n; forall z, 0 < z < fec_n -> 0 < find_power mod_poly (poly_of_int z) < i ->
          Znth z l = find_power mod_poly (poly_of_int z); Znth 0 l = 0%Z)
    LOCAL (temp _i (Vint (Int.repr i)); temp _mod (Vint (Int.repr modulus)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents i ++ map Vint (map Int.repr (list_repeat
      (Z.to_nat (fec_n - i)) 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
         data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z)))
     (gv _fec_invefec)))
    break: (PROP () LOCAL (temp _mod (Vint (Int.repr modulus)); gvars gv)
            SEP (INDEX_TABLES gv;
          data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z)))
     (gv _fec_invefec))).
  - forward. Exists 0%Z. Exists ((list_repeat (Z.to_nat fec_n) 0%Z)). entailer!.
    rewrite Znth_list_repeat_inrange; rep_lia. simpl. rewrite !map_list_repeat. cancel.
  - Intros i. Intros l.
    forward_if.
    + (*Loop body*)  forward_if 
      (PROP (0 <= i <= fec_n; forall z, 0 < z < fec_n -> 0 < find_power mod_poly (poly_of_int z) < i -> 
          Znth z l = find_power mod_poly (poly_of_int z); Znth 0 l = 0%Z)
      LOCAL (temp _mod (Vint (Int.repr modulus)); temp _i (Vint (Int.repr i)); gvars gv)
      SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents (i + 1) ++ 
              map Vint (map Int.repr (list_repeat ((Z.to_nat fec_n) - Z.to_nat (i + 1))%nat 0%Z))) (gv _fec_2_index);
           data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
           data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z)))
              (gv _fec_invefec))).
      * (*i=0 case (base case)*) forward. entailer!. entailer!.
        simpl. replace (Z.to_nat fec_n) with (1%nat + (Z.to_nat fec_n - 1))%nat at 1 by rep_lia.
        rewrite <- list_repeat_app. simpl. rewrite upd_Znth0. 
        rewrite monomial_0. rewrite pmod_refl; auto. rewrite poly_to_int_one. entailer!.
        apply one_lt_deg; auto.
      * forward. 
        -- (*array access valid*)
           entailer!. rewrite Znth_app1;[| list_solve]. rewrite power_to_index_contents_Znth. simpl_repr. lia. 
        -- (*body continue with shift, rewrite shift into polynomial mult*)
           forward. 
           (*TODO: The resulting if condition is very strange and needs a lot of work to get into a usable form*)
           assert (Hshl : (Int.shl (Int.repr (poly_to_int (monomial (Z.to_nat (i - 1)) %~ mod_poly))) (Int.repr 1)) =
                     (Int.repr (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))))). {
           unfold Int.shl. rewrite !unsigned_repr; try rep_lia. 2: solve_poly_bounds. 
           rewrite Z.shiftl_mul_pow2 by lia. replace (2 ^ 1) with 2 by reflexivity. f_equal.
           rewrite <- poly_of_int_to_int. 2: pose_poly_bounds (poly_to_int (monomial (Z.to_nat (i - 1)) %~ mod_poly)); rep_lia.
           rewrite Z.mul_comm. rewrite poly_shiftl.
           rewrite poly_of_int_inv. reflexivity. apply modulus_poly_monomial. } rewrite Znth_app1 by solve_prop_length.
           assert (Hxbound: 0 <= 
              poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) <= 1023). {
            (*Need to prove bounds differently bc it is not smaller than mod_poly*)
             pose proof (poly_to_int_bounded (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))).
             split; try rep_lia. rewrite poly_mult_deg in H4. 2: solve_poly_zero.
             rewrite deg_x in H4. 
             assert (2 ^ (1 + deg (monomial (Z.to_nat (i - 1)) %~ mod_poly) + 1) - 1 <=
              2 ^ (1 + 8 + 1) - 1). { rewrite <- Z.sub_le_mono_r.
              apply Z.pow_le_mono_r. lia. apply Zplus_le_compat_r. apply Zplus_le_compat_l.
              pose proof (pmod_lt_deg mod_poly (monomial (Z.to_nat (i - 1)))). pose proof mod_poly_deg_eq; lia. }
            rep_lia. solve_poly_zero. }
          forward_if.
          ++  (*need to simplify condition in H4, not sure why it is not automated*)
             rewrite power_to_index_contents_Znth in H4 by lia. unfold sem_cast_i2i in H4. unfold force_val in H4. 
             unfold both_int in H4. simpl sem_shift_ii in H4. unfold sem_cast_pointer in H4. rewrite Hshl in H4.
             unfold Int.lt in H4. unfold cast_int_int in H4.
             destruct (zlt
                 (Int.signed (Int.repr (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)))))
                 (Int.signed (Int.repr 256))) as [Hif | Hif]. inversion H4. clear H4.
             rewrite !Int.signed_repr in Hif; try rep_lia.
             forward.
             ** entailer!.
             ** rewrite !power_to_index_contents_Znth by lia. entailer!. simpl. 
                 (*Core of proof: this actually finds x^i % f in this case (complicated because x * (x^(i-1) %f) overflows)*)
                assert (Hdeg: deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) = deg mod_poly). {
                  assert (Hupper: deg mod_poly <= deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))). {
                  rewrite mod_poly_deg_log. 
                  rewrite <- (poly_of_int_inv (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly) )).
                  rewrite poly_of_int_deg. apply Z.log2_le_mono. rep_lia.  apply poly_to_int_pos. solve_poly_zero. }
                  assert (Hlower: deg (monomial (Z.to_nat (i - 1)) %~ mod_poly) < deg mod_poly). {
                  apply pmod_lt_deg. auto. }
                  assert (Hnonz: monomial (Z.to_nat (i - 1)) %~ mod_poly <> zero) by solve_poly_zero.
                  assert (Hx: x <> zero) by solve_poly_zero. 
                  rewrite poly_mult_deg; auto. rewrite poly_mult_deg in Hupper; auto. 
                  rewrite deg_x. rewrite deg_x in Hupper. lia. }
                assert (Hxor : Z.lxor (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))) modulus =
                  poly_to_int (monomial (Z.to_nat i) %~ mod_poly)). {
                  rewrite <- poly_of_int_to_int. rewrite xor_addition; try rep_lia.
                  rewrite poly_of_int_inv.
                  assert (Hdeglt: deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly) +~ poly_of_int modulus) < deg mod_poly). {
                   rewrite poly_add_comm. rewrite <- mod_poly_eq. apply poly_add_deg_same; auto. solve_poly_zero.  }
                  rewrite <- (pmod_refl mod_poly _ Hdeglt). rewrite <- mod_poly_eq. rewrite pmod_add_distr; auto.
                  rewrite pmod_same by auto. rewrite poly_add_0_r. rewrite <- (pmod_refl mod_poly x).
                  rewrite <- pmod_mult_distr by auto. rewrite <- monomial_expand. rewrite pmod_twice; auto.
                  f_equal. f_equal. lia. rewrite deg_x. rewrite mod_poly_deg_eq; lia.
                  rewrite Z.lxor_nonneg. split; intros; rep_lia.  }
                unfold Int.xor. rewrite Hshl. rewrite !unsigned_repr by rep_lia. rewrite Hxor. simpl_repr.
                rewrite upd_Znth_app2 by list_solve. 
                replace ((i - Zlength (power_to_index_contents i))) with 0%Z by list_solve.
                assert (Hlr: (list_repeat (Z.to_nat (fec_n - i)) 0%Z) = 0%Z :: 
                    (list_repeat (Z.to_nat fec_n - Z.to_nat (i + 1)) 0%Z)). { 
                 replace (Z.to_nat (fec_n - i)) with 
                 (1%nat + (Z.to_nat fec_n - Z.to_nat (i + 1)))%nat by rep_lia. rewrite <- list_repeat_app. auto. }
                rewrite Hlr. simpl. rewrite upd_Znth0. rewrite power_to_index_contents_plus_1 by lia.
                rewrite <- app_assoc; simpl. cancel.
          ++ (*Now on other case of if statement, again need a lot of work to simplify if condition*)
             rewrite power_to_index_contents_Znth in H4 by lia. unfold sem_cast_i2i in H4. unfold force_val in H4. 
             unfold both_int in H4. simpl sem_shift_ii in H4. unfold sem_cast_pointer in H4. rewrite Hshl in H4.
             unfold Int.lt in H4. unfold cast_int_int in H4.  destruct (zlt
             (Int.signed (Int.repr (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)))))
             (Int.signed (Int.repr 256))) as [Hlt | ]. 2: inversion H4. clear H4.
             rewrite !Int.signed_repr in Hlt by rep_lia. forward.
             --- entailer!.
             --- entailer!. rewrite !power_to_index_contents_Znth by lia. simpl. rewrite Hshl. simpl_repr.
                 assert (Hdeg: deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) < deg mod_poly). {
                   rewrite mod_poly_deg_log. rewrite <- (poly_of_int_inv (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))).
                   replace (Z.log2 fec_n) with 8 by (rewrite fec_n_eq; reflexivity).
                   rewrite poly_of_int_deg. 
                   assert (Hle: poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) <= 255) by lia.
                   apply Z.log2_le_mono in Hle. replace (Z.log2 255) with 7 in Hle by reflexivity. lia.
                   apply poly_to_int_pos. solve_poly_zero. }
                 assert (Hmon: (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) = monomial (Z.to_nat i) %~ mod_poly). {
                   rewrite <- (pmod_refl mod_poly _ Hdeg).
                   rewrite pmod_mult_distr; auto. rewrite pmod_twice by auto. rewrite <- pmod_mult_distr by auto.
                   rewrite <- monomial_expand. f_equal. f_equal. lia. } rewrite Hmon.
                 rewrite upd_Znth_app2 by list_solve.
                 replace ((i - Zlength (power_to_index_contents i))) with 0%Z by list_solve.
                 assert (Hlr: (list_repeat (Z.to_nat (fec_n - i)) 0%Z) = 0%Z :: 
                  (list_repeat (Z.to_nat fec_n - Z.to_nat (i + 1)) 0%Z)). { 
                  assert (i < fec_n) by (rewrite fec_n_eq; lia).
                  replace (Z.to_nat (fec_n - i)) with 
                  (1%nat + (Z.to_nat fec_n - Z.to_nat (i + 1)))%nat by lia. rewrite <- list_repeat_app.
                  auto. } rewrite Hlr. simpl. rewrite upd_Znth0. rewrite power_to_index_contents_plus_1; try lia.
                 rewrite <- app_assoc; simpl. cancel.
      * (*Now need to prove [fec_2_power] part*) 
        assert (Hbound: 0 <= poly_to_int (monomial (Z.to_nat i) %~ mod_poly) < fec_n) by solve_poly_bounds. 
        forward.
        -- entailer!. 
        -- entailer!. rewrite Znth_app1 by solve_prop_length. rewrite power_to_index_contents_Znth by lia. simpl_repr. 
        -- rewrite Znth_app1 by solve_prop_length. rewrite power_to_index_contents_Znth by lia.
           forward. forward. 
          (*now continue and show loop invariant preserved - this is a bit tricky because
          we are not filling up the array in an orderly way - need to show that we dont fill in the same
          spot twice (other than 0, special case). We rely on the uniqueness of [find_power] *)
          Exists (i+1). Exists ((upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)) l i)).
          (*Now, let's prove the invariant is preserved*) 
          pose proof field_size_fec_n as S1. entailer!.  
            ** split; intros.
              --- assert (Hfp: 0 < find_power mod_poly (poly_of_int z) < i \/ 
                  find_power mod_poly (poly_of_int z) = i) by lia. destruct Hfp as [Hfp | Hfp].
                +++ (*if smaller than i - MUST be different than the current one - uniqueness*)
                    rewrite upd_Znth_diff. apply H0. all: try lia. list_solve. list_solve.
                    intro Hz. assert (find_power mod_poly (poly_of_int z) = i).
                    symmetry. rewrite <- find_power_iff.
                    split. rewrite Hz. rewrite poly_of_int_inv. reflexivity. rep_lia. apply mod_poly_PrimPoly. solve_poly_zero.
                    solve_poly_bounds. lia.
                +++ assert (Hz: z = (poly_to_int (monomial (Z.to_nat i) %~ mod_poly))). { symmetry in Hfp.
                    rewrite <- find_power_iff in Hfp. destruct Hfp as [Hfp  Hi]. rewrite <- poly_of_int_to_int.
                    symmetry. assumption. lia. apply mod_poly_PrimPoly. solve_poly_zero. solve_poly_bounds.  } 
                    rewrite Hz. rewrite upd_Znth_same. rewrite <- Hz. rewrite <- Hfp. reflexivity.
                    list_solve.
              --- rewrite upd_Znth_diff. assumption. list_solve. list_solve. 
                  pose proof (modulus_poly_monomial (Z.to_nat i)). lia.
            ** rewrite upd_Znth_map.  assert (Hl: (map Vint
                (upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)) 
                (map Int.repr l) (Int.zero_ext 8 (Int.repr i)))) =  (map Vint
                (map Int.repr (upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)) l i)))). {
                f_equal. rewrite <- upd_Znth_map. f_equal. solve_repr_int. } rewrite Hl. cancel.
                replace ((Z.to_nat fec_n - Z.to_nat (i + 1))%nat) with (Z.to_nat (fec_n - (i + 1))) by lia. cancel.
    + (*end of first loop - need to prove postcondition*) forward. entailer!.
      assert (i = fec_n) by rep_lia. subst. replace (Z.to_nat (fec_n - fec_n)) with 0%nat by lia.
      simpl. rewrite app_nil_r. unfold INDEX_TABLES. cancel. 
      (*The only nontrivial part: l is the correct index_to_power_contents list*)
      assert (Hl: (map Vint (map Int.repr l)) =
      (map Vint (map Int.repr (prop_list (fun z : Z => find_power mod_poly (poly_of_int z)) fec_n)))). {
        f_equal. f_equal. apply Znth_eq_ext. rewrite prop_list_length. list_solve. lia. intros i Hi.
        rewrite? Zlength_map in H7. rewrite H7 in Hi.
        destruct (Z.eq_dec 0 i).
        - subst. rewrite H1. rewrite prop_list_Znth. rewrite_zero. rewrite (@find_power_zero _ mod_poly_PosPoly). reflexivity.
          apply mod_poly_PrimPoly. auto. 
        - pose_power (poly_of_int i) Hfp Hfpbound. rewrite H0; try lia. rewrite prop_list_Znth by rep_lia.
          reflexivity. }
        rewrite Hl. unfold index_to_power_contents. cancel.
  - (*Second loop: calculate inverses*) 
    pose proof field_size_fec_n as Hfieldsize. 
    assert (Hmodpos: deg mod_poly > 0) by (rewrite mod_poly_deg_eq; rep_lia).
    assert (Hirred: irreducible mod_poly) by (apply (@f_irred _ _ mod_poly_PrimPoly)).
    assert (Hmodnotx : mod_poly <> x) by (apply (@Hnotx _ _ mod_poly_PrimPoly)).
    clear Hpospoly.
    forward_for_simple_bound 256%Z (EX (i : Z) (l: list Z),
    PROP (0 <= i <= fec_n; Znth 0 l = 0%Z; forall z, 0 < z < fec_n -> 
          0 <= poly_to_int (poly_inv mod_poly (poly_of_int z)) < i ->
          Znth z l = poly_to_int (poly_inv mod_poly (poly_of_int z)))
    LOCAL (temp _mod (Vint (Int.repr modulus));  gvars gv)
    SEP (INDEX_TABLES gv;
         data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_invefec ))).
    + Exists (list_repeat (Z.to_nat fec_n ) 0%Z). entailer!. rewrite Znth_list_repeat_inrange; rep_lia.
    + assert (Hfpbound: 0 <= find_power mod_poly (poly_of_int i) <= fec_n - 1). {
       destruct (Z.eq_dec i 0).
       - subst. rewrite_zero.  rewrite (@find_power_zero _ _ mod_poly_PrimPoly). lia.
       - solve_poly_bounds. } unfold INDEX_TABLES; Intros. 
      forward.
      * entailer!.
      * entailer!. rewrite index_to_power_contents_Znth by rep_lia. simpl_repr. 
      * rewrite index_to_power_contents_Znth by rep_lia. 
        assert (Hinvbound: 0 <=
            poly_to_int (monomial (Z.to_nat (255 - find_power mod_poly (poly_of_int i))) %~ mod_poly) <
            256) by solve_poly_bounds. 
        forward.
        -- entailer!.
        -- entailer!. rewrite power_to_index_contents_Znth; simpl_repr.  
        -- rewrite power_to_index_contents_Znth by solve_poly_bounds.
           forward.
          ++ entailer!.
          ++ (*loop invariant preservation*)
              Exists (upd_Znth (poly_to_int (monomial (Z.to_nat 
                (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly)) l i).
            entailer!.
            ** assert (Hlen: Zlength l = fec_n) by list_solve. split.
              --- (*handle 0 case separately*)
                  destruct (Z.eq_dec 0%Z (poly_to_int (monomial (Z.to_nat 
                    (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly))).
                +++ rewrite <- poly_of_int_to_int in e. rewrite_zero. exfalso. 
                    apply (irred_doesnt_divide_monomial mod_poly (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i)))).
                    apply Hpos. apply (@f_irred _ _ mod_poly_PrimPoly). apply (@Hnotx _ _ mod_poly_PrimPoly).
                    rewrite divides_pmod_iff. unfold divides_pmod. apply e. left. solve_poly_zero. lia. 
                +++ rewrite upd_Znth_diff. assumption. list_solve. rewrite Hlen. solve_poly_bounds. apply n. 
        --- intros z Hzf Hpi1. 
            (*Will come in handy for both branches*)
            assert (Hpowmod: monomial (Z.to_nat (find_power mod_poly (poly_of_int i)) +
              Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly = one). {
              replace ((Z.to_nat (find_power mod_poly (poly_of_int i)) +
               Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i)))%nat) with (Z.to_nat (fec_n - 1)) by lia.
              rewrite (@monomial_powers_eq_mod _ _ mod_poly_PrimPoly _ 0). rewrite monomial_0. apply pmod_refl; auto.
              apply mod_poly_PosPoly. apply (@deg_gt_one _ _ mod_poly_PrimPoly). apply Nat2Z.inj. rewrite mod_Zmod by rep_lia.
              rewrite mod_Zmod by rep_lia. rewrite Hfieldsize. rewrite Z2Nat.id by lia. rewrite Z_mod_same_full.
              rewrite Z.mod_0_l; lia. }
              assert (0 <=  poly_to_int (poly_inv mod_poly (poly_of_int z)) < i \/
                poly_to_int (poly_inv mod_poly (poly_of_int z)) = i) by lia. 
              destruct H14 as [Hilt | Hi].
            +++ rewrite upd_Znth_diff. apply H2; try assumption; try lia. list_solve. rewrite Hlen. solve_poly_bounds. 
                (*contradiction: i and z are inverses*)
                intro Hz. assert (poly_to_int (poly_inv mod_poly (poly_of_int z)) = i). {
                symmetry. rewrite <- poly_of_int_to_int by lia. 
                destruct (Z.eq_dec z 0%Z).
                - subst. symmetry in e. rewrite <- poly_of_int_to_int in e; try lia. rewrite_zero.
                  exfalso. apply (irred_doesnt_divide_monomial mod_poly 
                    (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i)))); try assumption.
                  rewrite divides_pmod_iff. unfold divides_pmod. assumption. left. solve_poly_zero.
                - symmetry. rewrite <- poly_inv_iff; [| assumption | ]. rewrite Hz.
                  rewrite poly_of_int_inv. pose_power (poly_of_int i) Hi Hfp_bound. rewrite Hi at 2. split. 
                  2: solve_poly_bounds. pose proof mod_poly_PosPoly as HmodPos.
                  rewrite pmod_mult_reduce by auto. rewrite poly_mult_comm. rewrite pmod_mult_reduce by auto. 
                  rewrite monomial_exp_law. assumption. rewrite pmod_refl; auto. solve_poly_zero. apply mod_poly_PosPoly.
                  solve_poly_bounds. } lia. 
            +++ (*proving the actual update, since i and z are correctly inverses this time*)
                symmetry in Hi. rewrite <- poly_of_int_to_int in Hi by lia.
                assert (Hzi : poly_of_int z = poly_inv mod_poly (poly_of_int i)). {
                  rewrite poly_inv_sym; auto; solve_poly_bounds.  }
                assert (Hz: z = (poly_to_int (monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly))). {
                  rewrite <- poly_of_int_to_int. rewrite Hzi by lia.
                  destruct (destruct_poly (poly_of_int i)).
                  - rewrite e in Hi. rewrite <- poly_inv_zero in Hi by auto. rewrite pmod_refl in Hi; try auto. 
                    rewrite poly_of_int_zero in Hi. lia. apply mod_poly_PosPoly. solve_poly_bounds. 
                  - rewrite <- poly_inv_iff; auto. split. pose_power (poly_of_int i) Hpi Hfp_bound.
                    rewrite Hpi at 1. rewrite pmod_mult_reduce by apply mod_poly_PosPoly.
                    rewrite poly_mult_comm. rewrite pmod_mult_reduce by apply mod_poly_PosPoly. rewrite monomial_exp_law.
                    rewrite Nat.add_comm. apply Hpowmod. apply pmod_lt_deg; auto. apply mod_poly_PosPoly. rewrite pmod_refl; auto.
                    apply mod_poly_PosPoly. 
                    solve_poly_bounds.
                  - lia. }
                rewrite <- Hz. rewrite upd_Znth_same. rewrite <- poly_of_int_to_int. assumption.
                lia. list_solve.
            ** assert (Hl: (upd_Znth
                (poly_to_int (monomial (Z.to_nat (255 - find_power mod_poly (poly_of_int i))) %~ mod_poly))
                (map Vint (map Int.repr l)) (Vint (Int.zero_ext 8 (Int.repr i)))) = 
                (map Vint (map Int.repr (upd_Znth (poly_to_int
                  (monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly)) l
                  i)))). { rewrite upd_Znth_map. f_equal. rewrite <- upd_Znth_map. repeat(f_equal). rep_lia.
                solve_repr_int.  } 
               rewrite Hl. unfold INDEX_TABLES; cancel.
    + (*postcondition of 2nd loop*)
      Intros l. unfold FIELD_TABLES; unfold INDEX_TABLES. entailer!.
      assert (Hl: (map Vint (map Int.repr l)) = (inverse_contents fec_n)). {
        unfold inverse_contents. f_equal. f_equal. apply Znth_eq_ext. rewrite prop_list_length. list_solve. lia.
        intros i Hi.
        rewrite prop_list_Znth by list_solve. assert (i = 0%Z \/ 0 < i) by lia. destruct H11 as [Hiz | Hipos].
        - subst. rewrite H0. rewrite_zero. rewrite poly_inv_of_zero. symmetry. rewrite poly_to_int_zero_iff.
          reflexivity. auto.
        - rewrite H1. reflexivity. list_solve. replace (Zlength l) with fec_n in Hi by list_solve. 
          pose_inv (poly_of_int i) A B. solve_poly_bounds. }
        rewrite Hl. cancel.
Qed.


Lemma body_fec_generate_math_tables : semax_body Vprog Gprog f_fec_generate_math_tables fec_generate_math_tables_spec.
Proof.
start_function.
forward_call.
pose proof mod_poly_PrimPoly as Hprimpoly.
pose proof mod_poly_PosPoly as Hpospoly.
(*loop invariants
  1. fec_2_index: filled out up to ith position, this is relatively straightforward to specity
  2. fec_2_power: is a list l such that for all z, 0 < z < fec_n ->
      find_power (poly_of_int z) <= i ->
      Znth l z = index_of_poly (poly_of_int z)
  this way, when we finish, all elements are present
  0 is an annoying special case. - 0th index is not used, so find_power[0] = 0*) 
  forward_loop (EX (i : Z) (l: list Z),
    PROP (0 <= i <= fec_n; forall z, 0 < z < fec_n -> 0 < find_power mod_poly (poly_of_int z) < i ->
          Znth z l = find_power mod_poly (poly_of_int z); Znth 0 l = 0%Z)
    LOCAL (temp _i (Vint (Int.repr i)); temp _mod (Vint (Int.repr modulus)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents i ++ map Vint (map Int.repr (list_repeat
      (Z.to_nat (fec_n - i)) 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
         data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z)))
     (gv _fec_invefec)))
    break: (PROP () LOCAL (temp _mod (Vint (Int.repr modulus)); gvars gv)
            SEP (INDEX_TABLES gv;
          data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z)))
     (gv _fec_invefec))).
  - forward. Exists 0%Z. Exists ((list_repeat (Z.to_nat fec_n) 0%Z)). entailer!.
    rewrite Znth_list_repeat_inrange; rep_lia. simpl. rewrite !map_list_repeat. cancel.
  - Intros i. Intros l.
    forward_if.
    + (*Loop body*)  forward_if 
      (PROP (0 <= i <= fec_n; forall z, 0 < z < fec_n -> 0 < find_power mod_poly (poly_of_int z) < i -> 
          Znth z l = find_power mod_poly (poly_of_int z); Znth 0 l = 0%Z)
      LOCAL (temp _mod (Vint (Int.repr modulus)); temp _i (Vint (Int.repr i)); gvars gv)
      SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents (i + 1) ++ 
              map Vint (map Int.repr (list_repeat ((Z.to_nat fec_n) - Z.to_nat (i + 1))%nat 0%Z))) (gv _fec_2_index);
           data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
           data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z)))
              (gv _fec_invefec))).
      * (*i=0 case (base case)*) forward. entailer!. entailer!.
        simpl. replace (Z.to_nat fec_n) with (1%nat + (Z.to_nat fec_n - 1))%nat at 1 by rep_lia.
        rewrite <- list_repeat_app. simpl. rewrite upd_Znth0. 
        rewrite monomial_0. rewrite pmod_refl; auto. rewrite poly_to_int_one. entailer!.
        apply one_lt_deg; auto.
      * forward. 
        -- (*array access valid*)
           entailer!. rewrite Znth_app1;[| list_solve]. rewrite power_to_index_contents_Znth. simpl_repr. lia. 
        -- (*body continue with shift, rewrite shift into polynomial mult*)
           forward. 
           (*TODO: The resulting if condition is very strange and needs a lot of work to get into a usable form*)
           assert (Hshl : (Int.shl (Int.repr (poly_to_int (monomial (Z.to_nat (i - 1)) %~ mod_poly))) (Int.repr 1)) =
                     (Int.repr (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))))). {
           unfold Int.shl. rewrite !unsigned_repr; try rep_lia. 2: solve_poly_bounds. 
           rewrite Z.shiftl_mul_pow2 by lia. replace (2 ^ 1) with 2 by reflexivity. f_equal.
           rewrite <- poly_of_int_to_int. 2: pose_poly_bounds (poly_to_int (monomial (Z.to_nat (i - 1)) %~ mod_poly)); rep_lia.
           rewrite Z.mul_comm. rewrite poly_shiftl.
           rewrite poly_of_int_inv. reflexivity. apply modulus_poly_monomial. } rewrite Znth_app1 by solve_prop_length.
           assert (Hxbound: 0 <= 
              poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) <= 1023). {
            (*Need to prove bounds differently bc it is not smaller than mod_poly*)
             pose proof (poly_to_int_bounded (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))).
             split; try rep_lia. rewrite poly_mult_deg in H4. 2: solve_poly_zero.
             rewrite deg_x in H4. 
             assert (2 ^ (1 + deg (monomial (Z.to_nat (i - 1)) %~ mod_poly) + 1) - 1 <=
              2 ^ (1 + 8 + 1) - 1). { rewrite <- Z.sub_le_mono_r.
              apply Z.pow_le_mono_r. lia. apply Zplus_le_compat_r. apply Zplus_le_compat_l.
              pose proof (pmod_lt_deg mod_poly (monomial (Z.to_nat (i - 1)))). pose proof mod_poly_deg_eq; lia. }
            rep_lia. solve_poly_zero. }
          forward_if.
          ++  (*need to simplify condition in H4, not sure why it is not automated*)
             rewrite power_to_index_contents_Znth in H4 by lia. unfold sem_cast_i2i in H4. unfold force_val in H4. 
             unfold both_int in H4. simpl sem_shift_ii in H4. unfold sem_cast_pointer in H4. rewrite Hshl in H4.
             unfold Int.lt in H4. unfold cast_int_int in H4.
             destruct (zlt
                 (Int.signed (Int.repr (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)))))
                 (Int.signed (Int.repr 256))) as [Hif | Hif]. inversion H4. clear H4.
             rewrite !Int.signed_repr in Hif; try rep_lia.
             forward.
             ** entailer!.
             ** rewrite !power_to_index_contents_Znth by lia. entailer!. simpl. 
                 (*Core of proof: this actually finds x^i % f in this case (complicated because x * (x^(i-1) %f) overflows)*)
                assert (Hdeg: deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) = deg mod_poly). {
                  assert (Hupper: deg mod_poly <= deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))). {
                  rewrite mod_poly_deg_log. 
                  rewrite <- (poly_of_int_inv (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly) )).
                  rewrite poly_of_int_deg. apply Z.log2_le_mono. rep_lia.  apply poly_to_int_pos. solve_poly_zero. }
                  assert (Hlower: deg (monomial (Z.to_nat (i - 1)) %~ mod_poly) < deg mod_poly). {
                  apply pmod_lt_deg. auto. }
                  assert (Hnonz: monomial (Z.to_nat (i - 1)) %~ mod_poly <> zero) by solve_poly_zero.
                  assert (Hx: x <> zero) by solve_poly_zero. 
                  rewrite poly_mult_deg; auto. rewrite poly_mult_deg in Hupper; auto. 
                  rewrite deg_x. rewrite deg_x in Hupper. lia. }
                assert (Hxor : Z.lxor (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))) modulus =
                  poly_to_int (monomial (Z.to_nat i) %~ mod_poly)). {
                  rewrite <- poly_of_int_to_int. rewrite xor_addition; try rep_lia.
                  rewrite poly_of_int_inv.
                  assert (Hdeglt: deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly) +~ poly_of_int modulus) < deg mod_poly). {
                   rewrite poly_add_comm. rewrite <- mod_poly_eq. apply poly_add_deg_same; auto. solve_poly_zero.  }
                  rewrite <- (pmod_refl mod_poly _ Hdeglt). rewrite <- mod_poly_eq. rewrite pmod_add_distr; auto.
                  rewrite pmod_same by auto. rewrite poly_add_0_r. rewrite <- (pmod_refl mod_poly x).
                  rewrite <- pmod_mult_distr by auto. rewrite <- monomial_expand. rewrite pmod_twice; auto.
                  f_equal. f_equal. lia. rewrite deg_x. rewrite mod_poly_deg_eq; lia.
                  rewrite Z.lxor_nonneg. split; intros; rep_lia.  }
                unfold Int.xor. rewrite Hshl. rewrite !unsigned_repr by rep_lia. rewrite Hxor. simpl_repr.
                rewrite upd_Znth_app2 by list_solve. 
                replace ((i - Zlength (power_to_index_contents i))) with 0%Z by list_solve.
                assert (Hlr: (list_repeat (Z.to_nat (fec_n - i)) 0%Z) = 0%Z :: 
                    (list_repeat (Z.to_nat fec_n - Z.to_nat (i + 1)) 0%Z)). { 
                 replace (Z.to_nat (fec_n - i)) with 
                 (1%nat + (Z.to_nat fec_n - Z.to_nat (i + 1)))%nat by rep_lia. rewrite <- list_repeat_app. auto. }
                rewrite Hlr. simpl. rewrite upd_Znth0. rewrite power_to_index_contents_plus_1 by lia.
                rewrite <- app_assoc; simpl. cancel.
          ++ (*Now on other case of if statement, again need a lot of work to simplify if condition*)
             rewrite power_to_index_contents_Znth in H4 by lia. unfold sem_cast_i2i in H4. unfold force_val in H4. 
             unfold both_int in H4. simpl sem_shift_ii in H4. unfold sem_cast_pointer in H4. rewrite Hshl in H4.
             unfold Int.lt in H4. unfold cast_int_int in H4.  destruct (zlt
             (Int.signed (Int.repr (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)))))
             (Int.signed (Int.repr 256))) as [Hlt | ]. 2: inversion H4. clear H4.
             rewrite !Int.signed_repr in Hlt by rep_lia. forward.
             --- entailer!.
             --- entailer!. rewrite !power_to_index_contents_Znth by lia. simpl. rewrite Hshl. simpl_repr.
                 assert (Hdeg: deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) < deg mod_poly). {
                   rewrite mod_poly_deg_log. rewrite <- (poly_of_int_inv (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))).
                   replace (Z.log2 fec_n) with 8 by (rewrite fec_n_eq; reflexivity).
                   rewrite poly_of_int_deg. 
                   assert (Hle: poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) <= 255) by lia.
                   apply Z.log2_le_mono in Hle. replace (Z.log2 255) with 7 in Hle by reflexivity. lia.
                   apply poly_to_int_pos. solve_poly_zero. }
                 assert (Hmon: (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) = monomial (Z.to_nat i) %~ mod_poly). {
                   rewrite <- (pmod_refl mod_poly _ Hdeg).
                   rewrite pmod_mult_distr; auto. rewrite pmod_twice by auto. rewrite <- pmod_mult_distr by auto.
                   rewrite <- monomial_expand. f_equal. f_equal. lia. } rewrite Hmon.
                 rewrite upd_Znth_app2 by list_solve.
                 replace ((i - Zlength (power_to_index_contents i))) with 0%Z by list_solve.
                 assert (Hlr: (list_repeat (Z.to_nat (fec_n - i)) 0%Z) = 0%Z :: 
                  (list_repeat (Z.to_nat fec_n - Z.to_nat (i + 1)) 0%Z)). { 
                  assert (i < fec_n) by (rewrite fec_n_eq; lia).
                  replace (Z.to_nat (fec_n - i)) with 
                  (1%nat + (Z.to_nat fec_n - Z.to_nat (i + 1)))%nat by lia. rewrite <- list_repeat_app.
                  auto. } rewrite Hlr. simpl. rewrite upd_Znth0. rewrite power_to_index_contents_plus_1; try lia.
                 rewrite <- app_assoc; simpl. cancel.
      * (*Now need to prove [fec_2_power] part*) 
        assert (Hbound: 0 <= poly_to_int (monomial (Z.to_nat i) %~ mod_poly) < fec_n) by solve_poly_bounds. 
        forward.
        -- entailer!. 
        -- entailer!. rewrite Znth_app1 by solve_prop_length. rewrite power_to_index_contents_Znth by lia. simpl_repr. 
        -- rewrite Znth_app1 by solve_prop_length. rewrite power_to_index_contents_Znth by lia.
           forward. forward. 
          (*now continue and show loop invariant preserved - this is a bit tricky because
          we are not filling up the array in an orderly way - need to show that we dont fill in the same
          spot twice (other than 0, special case). We rely on the uniqueness of [find_power] *)
          Exists (i+1). Exists ((upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)) l i)).
          (*Now, let's prove the invariant is preserved*) 
          pose proof field_size_fec_n as S1. entailer!.  
            ** split; intros.
              --- assert (Hfp: 0 < find_power mod_poly (poly_of_int z) < i \/ 
                  find_power mod_poly (poly_of_int z) = i) by lia. destruct Hfp as [Hfp | Hfp].
                +++ (*if smaller than i - MUST be different than the current one - uniqueness*)
                    rewrite upd_Znth_diff. apply H0. all: try lia. list_solve. list_solve.
                    intro Hz. assert (find_power mod_poly (poly_of_int z) = i).
                    symmetry. rewrite <- find_power_iff.
                    split. rewrite Hz. rewrite poly_of_int_inv. reflexivity. rep_lia. apply mod_poly_PrimPoly. solve_poly_zero.
                    solve_poly_bounds. lia.
                +++ assert (Hz: z = (poly_to_int (monomial (Z.to_nat i) %~ mod_poly))). { symmetry in Hfp.
                    rewrite <- find_power_iff in Hfp. destruct Hfp as [Hfp  Hi]. rewrite <- poly_of_int_to_int.
                    symmetry. assumption. lia. apply mod_poly_PrimPoly. solve_poly_zero. solve_poly_bounds.  } 
                    rewrite Hz. rewrite upd_Znth_same. rewrite <- Hz. rewrite <- Hfp. reflexivity.
                    list_solve.
              --- rewrite upd_Znth_diff. assumption. list_solve. list_solve. 
                  pose proof (modulus_poly_monomial (Z.to_nat i)). lia.
            ** rewrite upd_Znth_map.  assert (Hl: (map Vint
                (upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)) 
                (map Int.repr l) (Int.zero_ext 8 (Int.repr i)))) =  (map Vint
                (map Int.repr (upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)) l i)))). {
                f_equal. rewrite <- upd_Znth_map. f_equal. solve_repr_int. } rewrite Hl. cancel.
                replace ((Z.to_nat fec_n - Z.to_nat (i + 1))%nat) with (Z.to_nat (fec_n - (i + 1))) by lia. cancel.
    + (*end of first loop - need to prove postcondition*) forward. entailer!.
      assert (i = fec_n) by rep_lia. subst. replace (Z.to_nat (fec_n - fec_n)) with 0%nat by lia.
      simpl. rewrite app_nil_r. unfold INDEX_TABLES. cancel. 
      (*The only nontrivial part: l is the correct index_to_power_contents list*)
      assert (Hl: (map Vint (map Int.repr l)) =
      (map Vint (map Int.repr (prop_list (fun z : Z => find_power mod_poly (poly_of_int z)) fec_n)))). {
        f_equal. f_equal. apply Znth_eq_ext. rewrite prop_list_length. list_solve. lia. intros i Hi.
        rewrite? Zlength_map in H7. rewrite H7 in Hi.
        destruct (Z.eq_dec 0 i).
        - subst. rewrite H1. rewrite prop_list_Znth. rewrite_zero. rewrite (@find_power_zero _ mod_poly_PosPoly). reflexivity.
          apply mod_poly_PrimPoly. auto. 
        - pose_power (poly_of_int i) Hfp Hfpbound. rewrite H0; try lia. rewrite prop_list_Znth by rep_lia.
          reflexivity. }
        rewrite Hl. unfold index_to_power_contents. cancel.
  - (*Second loop: calculate inverses*) 
    pose proof field_size_fec_n as Hfieldsize. 
    assert (Hmodpos: deg mod_poly > 0) by (rewrite mod_poly_deg_eq; rep_lia).
    assert (Hirred: irreducible mod_poly) by (apply (@f_irred _ _ mod_poly_PrimPoly)).
    assert (Hmodnotx : mod_poly <> x) by (apply (@Hnotx _ _ mod_poly_PrimPoly)).
    clear Hpospoly.
    forward_for_simple_bound 256%Z (EX (i : Z) (l: list Z),
    PROP (0 <= i <= fec_n; Znth 0 l = 0%Z; forall z, 0 < z < fec_n -> 
          0 <= poly_to_int (poly_inv mod_poly (poly_of_int z)) < i ->
          Znth z l = poly_to_int (poly_inv mod_poly (poly_of_int z)))
    LOCAL (temp _mod (Vint (Int.repr modulus));  gvars gv)
    SEP (INDEX_TABLES gv;
         data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_invefec ))).
    + Exists (list_repeat (Z.to_nat fec_n ) 0%Z). entailer!. rewrite Znth_list_repeat_inrange; rep_lia.
    + assert (Hfpbound: 0 <= find_power mod_poly (poly_of_int i) <= fec_n - 1). {
       destruct (Z.eq_dec i 0).
       - subst. rewrite_zero.  rewrite (@find_power_zero _ _ mod_poly_PrimPoly). lia.
       - solve_poly_bounds. } unfold INDEX_TABLES; Intros. 
      forward.
      * entailer!.
      * entailer!. rewrite index_to_power_contents_Znth by rep_lia. simpl_repr. 
      * rewrite index_to_power_contents_Znth by rep_lia. 
        assert (Hinvbound: 0 <=
            poly_to_int (monomial (Z.to_nat (255 - find_power mod_poly (poly_of_int i))) %~ mod_poly) <
            256) by solve_poly_bounds. 
        forward.
        -- entailer!.
        -- entailer!. rewrite power_to_index_contents_Znth; simpl_repr.  
        -- rewrite power_to_index_contents_Znth by solve_poly_bounds.
           forward.
          ++ entailer!.
          ++ (*loop invariant preservation*)
              Exists (upd_Znth (poly_to_int (monomial (Z.to_nat 
                (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly)) l i).
            entailer!.
            ** assert (Hlen: Zlength l = fec_n) by list_solve. split.
              --- (*handle 0 case separately*)
                  destruct (Z.eq_dec 0%Z (poly_to_int (monomial (Z.to_nat 
                    (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly))).
                +++ rewrite <- poly_of_int_to_int in e. rewrite_zero. exfalso. 
                    apply (irred_doesnt_divide_monomial mod_poly (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i)))).
                    apply Hpos. apply (@f_irred _ _ mod_poly_PrimPoly). apply (@Hnotx _ _ mod_poly_PrimPoly).
                    rewrite divides_pmod_iff. unfold divides_pmod. apply e. left. solve_poly_zero. lia. 
                +++ rewrite upd_Znth_diff. assumption. list_solve. rewrite Hlen. solve_poly_bounds. apply n. 
        --- intros z Hzf Hpi1. 
            (*Will come in handy for both branches*)
            assert (Hpowmod: monomial (Z.to_nat (find_power mod_poly (poly_of_int i)) +
              Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly = one). {
              replace ((Z.to_nat (find_power mod_poly (poly_of_int i)) +
               Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i)))%nat) with (Z.to_nat (fec_n - 1)) by lia.
              rewrite (@monomial_powers_eq_mod _ _ mod_poly_PrimPoly _ 0). rewrite monomial_0. apply pmod_refl; auto.
              apply mod_poly_PosPoly. apply (@deg_gt_one _ _ mod_poly_PrimPoly). apply Nat2Z.inj. rewrite mod_Zmod by rep_lia.
              rewrite mod_Zmod by rep_lia. rewrite Hfieldsize. rewrite Z2Nat.id by lia. rewrite Z_mod_same_full.
              rewrite Z.mod_0_l; lia. }
              assert (0 <=  poly_to_int (poly_inv mod_poly (poly_of_int z)) < i \/
                poly_to_int (poly_inv mod_poly (poly_of_int z)) = i) by lia. 
              destruct H14 as [Hilt | Hi].
            +++ rewrite upd_Znth_diff. apply H2; try assumption; try lia. list_solve. rewrite Hlen. solve_poly_bounds. 
                (*contradiction: i and z are inverses*)
                intro Hz. assert (poly_to_int (poly_inv mod_poly (poly_of_int z)) = i). {
                symmetry. rewrite <- poly_of_int_to_int by lia. 
                destruct (Z.eq_dec z 0%Z).
                - subst. symmetry in e. rewrite <- poly_of_int_to_int in e; try lia. rewrite_zero.
                  exfalso. apply (irred_doesnt_divide_monomial mod_poly 
                    (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i)))); try assumption.
                  rewrite divides_pmod_iff. unfold divides_pmod. assumption. left. solve_poly_zero.
                - symmetry. rewrite <- poly_inv_iff; [| assumption | ]. rewrite Hz.
                  rewrite poly_of_int_inv. pose_power (poly_of_int i) Hi Hfp_bound. rewrite Hi at 2. split. 
                  2: solve_poly_bounds. pose proof mod_poly_PosPoly as HmodPos.
                  rewrite pmod_mult_reduce by auto. rewrite poly_mult_comm. rewrite pmod_mult_reduce by auto. 
                  rewrite monomial_exp_law. assumption. rewrite pmod_refl; auto. solve_poly_zero. apply mod_poly_PosPoly.
                  solve_poly_bounds. } lia. 
            +++ (*proving the actual update, since i and z are correctly inverses this time*)
                symmetry in Hi. rewrite <- poly_of_int_to_int in Hi by lia.
                assert (Hzi : poly_of_int z = poly_inv mod_poly (poly_of_int i)). {
                  rewrite poly_inv_sym; auto; solve_poly_bounds.  }
                assert (Hz: z = (poly_to_int (monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly))). {
                  rewrite <- poly_of_int_to_int. rewrite Hzi by lia.
                  destruct (destruct_poly (poly_of_int i)).
                  - rewrite e in Hi. rewrite <- poly_inv_zero in Hi by auto. rewrite pmod_refl in Hi; try auto. 
                    rewrite poly_of_int_zero in Hi. lia. apply mod_poly_PosPoly. solve_poly_bounds. 
                  - rewrite <- poly_inv_iff; auto. split. pose_power (poly_of_int i) Hpi Hfp_bound.
                    rewrite Hpi at 1. rewrite pmod_mult_reduce by apply mod_poly_PosPoly.
                    rewrite poly_mult_comm. rewrite pmod_mult_reduce by apply mod_poly_PosPoly. rewrite monomial_exp_law.
                    rewrite Nat.add_comm. apply Hpowmod. apply pmod_lt_deg; auto. apply mod_poly_PosPoly. rewrite pmod_refl; auto.
                    apply mod_poly_PosPoly. 
                    solve_poly_bounds.
                  - lia. }
                rewrite <- Hz. rewrite upd_Znth_same. rewrite <- poly_of_int_to_int. assumption.
                lia. list_solve.
            ** assert (Hl: (upd_Znth
                (poly_to_int (monomial (Z.to_nat (255 - find_power mod_poly (poly_of_int i))) %~ mod_poly))
                (map Vint (map Int.repr l)) (Vint (Int.zero_ext 8 (Int.repr i)))) = 
                (map Vint (map Int.repr (upd_Znth (poly_to_int
                  (monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly)) l
                  i)))). { rewrite upd_Znth_map. f_equal. rewrite <- upd_Znth_map. repeat(f_equal). rep_lia.
                solve_repr_int.  } 
               rewrite Hl. unfold INDEX_TABLES; cancel.
    + (*postcondition of 2nd loop*)
      Intros l. unfold FIELD_TABLES; unfold INDEX_TABLES. entailer!.
      assert (Hl: (map Vint (map Int.repr l)) = (inverse_contents fec_n)). {
        unfold inverse_contents. f_equal. f_equal. apply Znth_eq_ext. rewrite prop_list_length. list_solve. lia.
        intros i Hi.
        rewrite prop_list_Znth by list_solve. assert (i = 0%Z \/ 0 < i) by lia. destruct H11 as [Hiz | Hipos].
        - subst. rewrite H0. rewrite_zero. rewrite poly_inv_of_zero. symmetry. rewrite poly_to_int_zero_iff.
          reflexivity. auto.
        - rewrite H1. reflexivity. list_solve. replace (Zlength l) with fec_n in Hi by list_solve. 
          pose_inv (poly_of_int i) A B. solve_poly_bounds. }
        rewrite Hl. cancel.
Qed.

