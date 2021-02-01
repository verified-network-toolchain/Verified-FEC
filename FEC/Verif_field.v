Require Import VST.floyd.proofauto.

Require Import Common.
Require Import CommonVST.
Require Import Specs.
Require Import fec.
Require Import Poly.

Set Bullet Behavior "Strict Subproofs".

Import WPoly.

(** Verification of [fec_find_mod]*)
(*
Lemma body_fec_find_mod : semax_body Vprog Gprog f_fec_find_mod fec_find_mod_spec.
Proof.
start_function. 
(*TODO: why doesn't this work, and how to prove a switch statement in which only 1 branch can be taken?*)
forward_if (PROP () LOCAL (temp _modulus (Vint (Int.repr modulus))) SEP ()).
*)

(*reflect_iff*)

(*TODO: move to COmmon*)
Lemma Int_eq_reflect: forall (a b : int),
  reflect (a = b) (Int.eq a b).
Proof.
  intros. destruct (Int.eq a b) eqn : Heq. apply ReflectT. apply Int.same_if_eq; auto.
  apply ReflectF. apply int_eq_false_e; auto.
Qed.

(** Verification of [fec_gf_mult] *)

(*Verification of multiply function *)
Lemma body_fec_gf_mult : semax_body Vprog Gprog f_fec_gf_mult fec_gf_mult_spec.
Proof.
  start_function.
  pose proof fec_n_bound as Fbound.
  forward_if (
    PROP ()
    LOCAL (temp _t'1 (Vint (Int.repr (if Z.eq_dec f 0%Z then 0%Z else if Z.eq_dec g 0%Z then 0%Z else 1%Z)));
     temp _a (Vint (Int.repr f)); temp _b (Vint (Int.repr g)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
   data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power))).
  - forward. entailer!. f_equal.  
    if_tac. subst. contradiction. if_tac. subst.
    assert (Htriv: Int.eq (Int.repr 0) Int.zero = true).
    apply (reflect_iff _ _ (Int_eq_reflect (Int.repr 0) Int.zero)). reflexivity.
    rewrite Htriv. reflexivity.
    assert (Hnon: Int.eq (Int.repr g) Int.zero = false).
    apply (ssrbool.introF (Int_eq_reflect (Int.repr g) Int.zero)). intro Hz.
    apply repr_inj_unsigned in Hz; rep_lia. rewrite Hnon. reflexivity.
  - forward. entailer!. if_tac. reflexivity. 
    apply repr_inj_unsigned in H0; rep_lia.
  - pose proof modulus_poly_deg_pos as Hpos.
    pose proof modulus_poly_not_x as Hnotx.
    pose proof modulus_poly_primitive as Hprim.
    pose proof modulus_poly_irred as Hirred.
    pose proof modulus_poly_not_zero as Hnonzero.
    pose proof modulus_poly_deg_bounds as Hbounds.
    pose proof modulus_poly_deg as Hdeglog. destruct H.
    pose proof (polys_deg_bounded _ H) as Hfbound.
    pose proof (polys_deg_bounded _ H0) as Hgbound.
    pose proof field_size_fec_n as Hfield_size.
    forward_if.
    + destruct H. destruct (Z.eq_dec f 0) as [? | Hf0]. contradiction.
      destruct (Z.eq_dec g 0) as [? | Hg0]. contradiction.
      clear H1'. deadvars!.
      assert (Hfnonzero: poly_of_int f <> zero). { intro Hz. rewrite poly_of_int_zero in Hz. lia. }
      assert (Hgnonzero: poly_of_int g <> zero). { intro Hz. rewrite poly_of_int_zero in Hz. lia. }
      forward.
      * entailer!. rewrite index_to_power_contents_Znth; try lia. simpl.
        pose proof (find_power_spec mod_poly Hpos Hprim Hnotx (poly_of_int f) Hfnonzero Hfbound) as Hfp.
        destruct Hfp.
        pose proof field_size_fec_n. rewrite unsigned_repr; rep_lia.
      * forward.
        -- entailer!. rewrite index_to_power_contents_Znth; try lia. simpl.
           pose proof (find_power_spec mod_poly Hpos Hprim Hnotx (poly_of_int g) Hgnonzero Hgbound) as Hfp.
           destruct Hfp.
           pose proof field_size_fec_n. rewrite unsigned_repr; rep_lia.
        -- pose proof (find_power_spec mod_poly Hpos Hprim Hnotx (poly_of_int f) Hfnonzero Hfbound) as [Hfp Hfp_bound].
           pose proof (find_power_spec mod_poly Hpos Hprim Hnotx (poly_of_int g) Hgnonzero Hgbound) as [Hgp Hgp_bound].
           (*for i + j > fec_n - 1, get conditional in usable form*)
           rewrite? index_to_power_contents_Znth; try lia. 
           forward_if.
          ++ forward. (*overflow case*)
             ** entailer!. rewrite index_to_power_contents_Znth; try lia. simpl.
                rewrite unsigned_repr; rep_lia.
             ** forward. 
                --- entailer!. rewrite index_to_power_contents_Znth; try lia. simpl.
                    rewrite unsigned_repr; rep_lia.
                --- rewrite !index_to_power_contents_Znth; try lia.
                    forward.
                  +++ entailer!. rewrite power_to_index_contents_Znth; try lia. simpl.
                      remember (monomial (Z.to_nat
                      ((find_power mod_poly (poly_of_int f) + find_power mod_poly (poly_of_int g)) -
                      (255))) %~ mod_poly) as prod.
                      pose proof modulus_poly_bound prod as Hprodb. 
                      assert (Hdeg: deg prod < deg mod_poly) by (rewrite Heqprod; apply pmod_lt_deg; assumption).
                      specialize (Hprodb Hdeg). rewrite unsigned_repr; rep_lia.
                  +++ forward. entailer!. (*now, we prove that this actually computes the product for this case*)
                      rewrite power_to_index_contents_Znth; try lia. f_equal. f_equal. f_equal.
                      rewrite monomial_add_field_size; try assumption.
                      replace (Z.to_nat (find_power mod_poly (poly_of_int f) + find_power mod_poly (poly_of_int g) - 
                      (256 - 1)))
                      with ((Z.to_nat (find_power mod_poly (poly_of_int f)) +
                           Z.to_nat (find_power mod_poly (poly_of_int g)) -
                           Z.to_nat (fec_n - 1))%nat) by (rewrite fec_n_eq; lia).
                      rewrite <- Hfield_size. replace (Z.to_nat (Z.of_nat (field_size mod_poly))) with
                      (field_size mod_poly) by lia. 
                      replace (Z.to_nat (find_power mod_poly (poly_of_int f)) + 
                        Z.to_nat (find_power mod_poly (poly_of_int g)) - field_size mod_poly + 
                        field_size mod_poly)%nat with
                        ((Z.to_nat (find_power mod_poly (poly_of_int f)) + 
                          Z.to_nat (find_power mod_poly (poly_of_int g)))%nat) by lia.
                      rewrite <- monomial_exp_law. rewrite pmod_mult_distr; try assumption.
                      rewrite <- Hfp. rewrite <- Hgp. reflexivity.
          ++ (*other side of the if statement*) forward.
            ** entailer!. rewrite index_to_power_contents_Znth; try lia. simpl.
               rewrite unsigned_repr; rep_lia.
            ** forward. 
                --- entailer!. rewrite index_to_power_contents_Znth; try lia. simpl.
                    rewrite unsigned_repr; rep_lia.
                --- rewrite !index_to_power_contents_Znth; try lia.
                    assert (Hsumbd: 0 <= find_power mod_poly (poly_of_int f) +
                       find_power mod_poly (poly_of_int g) < fec_n) by (rewrite fec_n_eq; lia).
                    forward.
                  +++ entailer!. rewrite power_to_index_contents_Znth; try lia. remember (monomial (Z.to_nat
                      ((find_power mod_poly (poly_of_int f) + find_power mod_poly (poly_of_int g)))) %~ mod_poly) 
                      as prod.
                      pose proof modulus_poly_bound prod as Hprodb. 
                      assert (Hdeg: deg prod < deg mod_poly) by (rewrite Heqprod; apply pmod_lt_deg; assumption).
                      specialize (Hprodb Hdeg). simpl.
                      rewrite unsigned_repr; rep_lia.
                  +++ forward. entailer!. (*now the easier, but similar case*) 
                      rewrite power_to_index_contents_Znth; try lia. f_equal. f_equal. f_equal. 
                      replace
                      (Z.to_nat (find_power mod_poly (poly_of_int f) + find_power mod_poly (poly_of_int g))) with
                      (Z.to_nat (find_power mod_poly (poly_of_int f)) + 
                        Z.to_nat (find_power mod_poly (poly_of_int g)))%nat by lia.
                      rewrite <- monomial_exp_law. rewrite pmod_mult_distr; try assumption.
                      rewrite <- Hfp. rewrite <- Hgp. reflexivity.
    + assert (Hzero: poly_of_int 0%Z = zero). rewrite poly_of_int_zero. lia. if_tac; subst.
      * forward. entailer!.  rewrite Hzero. rewrite poly_mult_0_l. rewrite pmod_zero; auto.
      * if_tac; subst.
        -- forward. entailer!. rewrite Hzero. rewrite poly_mult_0_r. rewrite pmod_zero; auto.
        -- inversion H1.
Qed. 

(** Verification of [fec_generate_math_tables]*)

(*TODO: Qed takes a long time (about 70 sec), and I don't know why. It might be unfolding constants or something*)
Lemma body_fec_generate_math_tables : semax_body Vprog Gprog f_fec_generate_math_tables fec_generate_math_tables_spec.
Proof.
start_function.
forward_call.
pose proof fec_n_bound as Fbound.
pose proof modulus_poly_deg_pos as Hpos.
pose proof modulus_poly_not_x as Hnotx.
pose proof modulus_poly_primitive as Hprim.
pose proof modulus_poly_irred as Hirred.
pose proof modulus_poly_not_zero as Hnonzero.
pose proof modulus_poly_deg_bounds as Hbounds.
pose proof modulus_poly_deg as Hdeglog.
pose proof modulus_pos as Hmodulus.
(*loop invariants
  1. fec_2_index: filled out up to ith position, this is relatively straightforward to specity
  2. fec_2_power: is a list l such that for all z, 0 < z < fec_n ->
      find_power (poly_of_int z) <= i ->
      Znth l z = index_of_poly (poly_of_int z)
  this way, when we finish, all elements are present
  0 is an annoying special case. - 0th index is not used, so find_power[0] = 0*) 
  forward_loop (EX (i : Z) (l: list Z),
    PROP (0 <= i <= fec_n /\ (forall z, 0 < z < fec_n -> 0 < find_power mod_poly (poly_of_int z) < i ->
          Znth z l = find_power mod_poly (poly_of_int z)) /\
      Znth 0 l = 0%Z)
    LOCAL (temp _i (Vint (Int.repr i)); temp _mod (Vint (Int.repr modulus)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents i ++ map Vint (map Int.repr (list_repeat
      (Z.to_nat (fec_n - i)) 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
         data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z)))
     (gv _fec_invefec)))
    break: (PROP () LOCAL (temp _mod (Vint (Int.repr modulus)); gvars gv)
            SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
          data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z)))
     (gv _fec_invefec))).
  - forward. Exists 0%Z. Exists ((list_repeat (Z.to_nat fec_n) 0%Z)). entailer!.
    rewrite Znth_list_repeat_inrange; lia. simpl. cancel.
  - Intros i. Intros l.
    forward_if.
    + (*Loop body*)  forward_if (PROP (0 <= i <= fec_n /\ 
      (forall z, 0 < z < fec_n -> 0 < find_power mod_poly (poly_of_int z) < i -> 
          Znth z l = find_power mod_poly (poly_of_int z)) /\
      Znth 0 l = 0%Z)
      LOCAL (temp _mod (Vint (Int.repr modulus)); temp _i (Vint (Int.repr i)); gvars gv)
      SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents (i + 1) ++ map Vint (map Int.repr (list_repeat
      ((Z.to_nat fec_n) - Z.to_nat (i + 1))%nat 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z)))
        (gv _fec_invefec))).
      * (*i=0 case (base case)*) forward. entailer!.
        simpl. replace (Z.to_nat fec_n) with (1%nat + (Z.to_nat fec_n - 1))%nat at 1 by lia.
        rewrite <- list_repeat_app. simpl. rewrite upd_Znth0. 
        rewrite monomial_0. rewrite pmod_refl; auto. rewrite poly_to_int_one. entailer!.
        replace (deg one) with (0%Z) by (rewrite deg_one; reflexivity). lia.
      * (*i <> 0*) assert (Hi1bound: 0 <= poly_to_int (monomial (Z.to_nat (i - 1)) %~ mod_poly) < fec_n). {
          apply modulus_poly_bound. apply pmod_lt_deg; auto. } 
        forward. 
        -- (*array access valid*)
           entailer!. rewrite Znth_app1. 2: list_solve. rewrite power_to_index_contents_Znth. simpl.
           rewrite unsigned_repr; try rep_lia. lia.
        -- (*body continue with shift, rewrite shift into polynomial mult*)
           forward. 
           (*TODO: What is going on here. forward_if takes forever, rewriting doesnt work, the resulting
              if condition is terrible, even simpl hangs. Is it just because of a constant?*)
           assert (Hshl : (Int.shl (Int.repr (poly_to_int (monomial (Z.to_nat (i - 1)) %~ mod_poly))) (Int.repr 1)) =
                     (Int.repr (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))))). {
           unfold Int.shl. rewrite !unsigned_repr; try rep_lia. rewrite Z.shiftl_mul_pow2; try lia.
           replace (2 ^ 1) with 2 by lia.
           assert ((poly_to_int (monomial (Z.to_nat (i - 1)) %~ mod_poly) * 2) = 
            poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))). {
            rewrite <- poly_of_int_to_int; try lia. rewrite Z.mul_comm. rewrite poly_shiftl.
            rewrite poly_of_int_inv. reflexivity. apply modulus_poly_monomial. } f_equal; f_equal; auto. }
            
           assert (Hxpoly : (force_val (sem_binary_operation' Oshl tuchar tint (Znth (i - 1)
                    (power_to_index_contents i ++ map Vint (map Int.repr (list_repeat (Z.to_nat (fec_n - i)) 0%Z))))
                  (Vint (Int.repr 1)))) = 
                  (Vint (Int.repr (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)))))). { 
           rewrite Znth_app1. 2: rewrite power_to_index_contents_length; lia.
           rewrite power_to_index_contents_Znth; try lia. simpl. f_equal. apply Hshl. }
           assert (Hxbound: Int.min_signed <= 
              poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) <= Int.max_signed). {
            (*very annoying proof to prove bounds*)
             pose proof (poly_to_int_bounded (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))).
             split; try rep_lia. rewrite poly_mult_deg in H4. 2: intro Hz; inversion Hz.
             rewrite deg_x in H4. 
             assert (2 ^ (1 + deg (monomial (Z.to_nat (i - 1)) %~ mod_poly) + 1) - 1 <=
              2 ^ (1 + 8 + 1) - 1). { rewrite <- Z.sub_le_mono_r.
              apply Z.pow_le_mono_r. lia. apply Zplus_le_compat_r. apply Zplus_le_compat_l.
              pose proof (pmod_lt_deg mod_poly Hpos (monomial (Z.to_nat (i - 1)))). lia. } rep_lia.
             intro Hmon. pose proof (modulus_poly_monomial (Z.to_nat (i - 1))).
             rewrite <- poly_to_int_zero_iff in Hmon. lia. }
           forward_if;
           replace (force_val (sem_binary_operation' Oshl tuchar tint (Znth (i - 1)
                     (power_to_index_contents i ++  map Vint (map Int.repr (list_repeat (Z.to_nat (fec_n - i)) 0%Z))))
                  (Vint (Int.repr 1)))) with 
           (Vint (Int.repr (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))))) by apply Hxpoly.
          ++  (*ugh this is awful, but cant rewrite the Znth beforehand for some reason*)
             rewrite Znth_app1 in H4. 2: rewrite power_to_index_contents_length; lia.
             rewrite power_to_index_contents_Znth in H4; try lia. unfold sem_cast_pointer in H4. unfold force_val in H4. 
             unfold both_int in H4. simpl sem_shift_ii in H4. unfold sem_cast_pointer in H4. rewrite Hshl in H4.
             unfold Int.lt in H4.
             destruct (zlt
                 (Int.signed (Int.repr (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)))))
                 (Int.signed (Int.repr 256))) as [Hif | Hif]. inversion H4. clear H4.
             rewrite !Int.signed_repr in Hif; try rep_lia.
             forward.
             ** entailer!. rewrite fec_n_eq; lia.
             ** entailer!. unfold Int.xor. rewrite !unsigned_repr; try rep_lia.
                 (*Core of proof: this actually finds x^i % f in this case (complicated because x * (x^(i-1) %f) overflows)*)
                 assert (Hpi : Vint (Int.zero_ext 8 (Int.repr (Z.lxor 
                  (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))) modulus))) = 
                  Vint (Int.repr (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)))). { f_equal.
                 assert (Hxor : Z.lxor (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))) modulus =
                    poly_to_int (monomial (Z.to_nat i) %~ mod_poly)). {
                  rewrite <- poly_of_int_to_int. rewrite xor_addition; try rep_lia.
                  assert (Hdeg: deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) = deg mod_poly). {
                  assert (Hupper: deg mod_poly <= deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))). {
                  rewrite Hdeglog. rewrite <- (poly_of_int_inv (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly) )).
                  rewrite poly_of_int_deg. apply Z.log2_le_mono. rewrite fec_n_eq; lia. apply poly_to_int_pos.
                  intro Hzero. rewrite poly_mult_zero_iff in Hzero. destruct Hzero. inversion H14.
                  rewrite <- poly_to_int_zero_iff in H14. 
                  pose proof (modulus_poly_monomial (Z.to_nat (i-1))). lia. }
                  assert (Hlower: deg (monomial (Z.to_nat (i - 1)) %~ mod_poly) < deg mod_poly). {
                  apply pmod_lt_deg. auto. }
                  assert (Hnonz: monomial (Z.to_nat (i - 1)) %~ mod_poly <> zero). intro Hz.
                  pose proof (modulus_poly_monomial (Z.to_nat (i-1))). rewrite <- poly_to_int_zero_iff in Hz. lia.
                  rewrite poly_mult_deg; auto. rewrite poly_mult_deg in Hupper; auto. 
                  rewrite deg_x. rewrite deg_x in Hupper. lia. all: intro Z; inversion Z. }
                  rewrite poly_of_int_inv.
                  assert (Hdeglt: deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly) +~ poly_of_int modulus) < deg mod_poly). {
                   rewrite poly_add_comm. rewrite <- mod_poly_eq. apply poly_add_deg_same; auto. }
                  rewrite <- (pmod_refl _ Hpos _ Hdeglt). rewrite <- mod_poly_eq. rewrite pmod_add_distr; auto.
                  rewrite pmod_same; auto. rewrite poly_add_0_r. rewrite <- (pmod_refl _ Hpos x).
                  rewrite <- pmod_mult_distr; auto. rewrite <- monomial_expand. rewrite pmod_twice; auto.
                  f_equal. f_equal. lia. rewrite deg_x. lia. 
                  rewrite Z.lxor_nonneg. pose proof modulus_pos. rep_lia. }
                 unfold Int.zero_ext. f_equal. rewrite Zbits.Zzero_ext_mod; try lia.
                 assert (Hpbound: 0 <= Z.lxor (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))) modulus < fec_n). {
                  rewrite Hxor. apply modulus_poly_bound. apply pmod_lt_deg. auto. }
                 rewrite Zmod_small. 2: { replace (two_p 8) with 256 by reflexivity.
                 rewrite unsigned_repr; try rep_lia. }
                 rewrite unsigned_repr; rewrite Hxor. reflexivity. rep_lia. } rewrite Hpi.
                 rewrite upd_Znth_app2. 2: list_solve.
                 replace ((i - Zlength (power_to_index_contents i))) with 0%Z by list_solve.
                 assert (Hlr: (list_repeat (Z.to_nat (fec_n - i)) 0%Z) = 0%Z :: 
                    (list_repeat (Z.to_nat fec_n - Z.to_nat (i + 1)) 0%Z)). { 
                  assert (i < fec_n) by (rewrite fec_n_eq; lia).
                  replace (Z.to_nat (fec_n - i)) with 
                    (1%nat + (Z.to_nat fec_n - Z.to_nat (i + 1)))%nat by lia. rewrite <- list_repeat_app.
                  auto. } rewrite Hlr. simpl. rewrite upd_Znth0. rewrite power_to_index_contents_plus_1; try lia.
                  rewrite <- app_assoc; simpl. cancel.
          ++ (*Now on other case of if statement, again need a lot of work to simplify if condition*)
             rewrite Znth_app1 in H4. 2: rewrite power_to_index_contents_length; lia.
             rewrite power_to_index_contents_Znth in H4; try lia. unfold sem_cast_pointer in H4. unfold force_val in H4. 
             unfold both_int in H4. simpl sem_shift_ii in H4. unfold sem_cast_pointer in H4. rewrite Hshl in H4.
             unfold Int.lt in H4.  destruct (zlt
             (Int.signed (Int.repr (poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)))))
             (Int.signed (Int.repr 256))) as [Hlt | ]. inversion H4. clear H4.
             rewrite !Int.signed_repr in Hlt; try rep_lia.
             ** forward.
                --- entailer!. rewrite fec_n_eq; lia.
                --- entailer!. assert (Hmon : (Vint (Int.zero_ext 8 (Int.repr (poly_to_int
                     (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)))))) = 
                      Vint (Int.repr (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)))). {
                     f_equal. unfold Int.zero_ext. f_equal. rewrite Zbits.Zzero_ext_mod; try lia.
                     pose proof (poly_to_int_bounded (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))) as Hlb.
                     replace (two_p 8) with (256) by reflexivity.
                     rewrite Zmod_small; try rep_lia. all: rewrite unsigned_repr; try rep_lia. f_equal.
                     assert (Hdeg: deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) < deg mod_poly). {
                     rewrite Hdeglog. rewrite <- (poly_of_int_inv (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly))).
                     replace (Z.log2 fec_n) with 8 by (rewrite fec_n_eq; reflexivity).
                     rewrite poly_of_int_deg. 
                     assert (Hle: poly_to_int (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly)) <= 255) by lia.
                     apply Z.log2_le_mono in Hle. replace (Z.log2 255) with 7 in Hle by reflexivity. lia.
                     apply poly_to_int_pos. intro Hz. rewrite poly_mult_zero_iff in Hz. destruct Hz.
                     inversion H14. rewrite <- poly_to_int_zero_iff in H14. 
                     pose proof (modulus_poly_monomial (Z.to_nat (i-1))). lia. }
                     rewrite <- (pmod_refl _ Hpos _ Hdeg). rewrite <- (pmod_refl _ Hpos x).
                     rewrite <- pmod_mult_distr; auto. rewrite <- monomial_expand. f_equal. f_equal. lia.
                     rewrite deg_x. lia. }
                     rewrite Hmon.  rewrite upd_Znth_app2. 2: list_solve.
                     replace ((i - Zlength (power_to_index_contents i))) with 0%Z by list_solve.
                     assert (Hlr: (list_repeat (Z.to_nat (fec_n - i)) 0%Z) = 0%Z :: 
                      (list_repeat (Z.to_nat fec_n - Z.to_nat (i + 1)) 0%Z)). { 
                      assert (i < fec_n) by (rewrite fec_n_eq; lia).
                      replace (Z.to_nat (fec_n - i)) with 
                      (1%nat + (Z.to_nat fec_n - Z.to_nat (i + 1)))%nat by lia. rewrite <- list_repeat_app.
                      auto. } rewrite Hlr. simpl. rewrite upd_Znth0. rewrite power_to_index_contents_plus_1; try lia.
                     rewrite <- app_assoc; simpl. cancel.
             ** inversion H4.
      * (*Now need to prove [fec_2_power] part*)
        assert (Hbound: 0 <= poly_to_int (monomial (Z.to_nat i) %~ mod_poly) < fec_n). { apply modulus_poly_bound.
        apply pmod_lt_deg; auto. } rewrite fec_n_eq in Hbound.
        forward.
        -- entailer!. rewrite fec_n_eq; lia.
        -- entailer!. rewrite Znth_app1. 2: solve_prop_length. rewrite power_to_index_contents_Znth; try lia. simpl.
           rewrite unsigned_repr; rep_lia.
        -- rewrite Znth_app1. 2: solve_prop_length. rewrite power_to_index_contents_Znth; try lia.
           forward.
           ++ entailer!. rewrite fec_n_eq; lia.
           ++ forward. entailer!.
              (*now continue and show loop invariant preserved - this is a bit tricky because
              we are not filling up the array in an orderly way - need to show that we dont fill in the same
              spot twice (other than 0, special case). We rely on the uniqueness of [find_power] *)
              Exists (i+1). Exists ((upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)) l i)).
              (*Now, let's prove the invariant is preserved*) 
              pose proof field_size_fec_n as S1. rewrite fec_n_eq in H8. entailer!.  
              (*rewrite Zlength_upd_Znth in H9. rewrite? Zlength_map in H9. split.*)
                ** split; intros.
                  --- assert (Hfp: 0 < find_power mod_poly (poly_of_int z) < i \/ 
                      find_power mod_poly (poly_of_int z) = i) by lia. destruct Hfp as [Hfp | Hfp].
                    +++ (*if smaller than i - MUST be different than the current one - uniqueness*)
                        rewrite upd_Znth_diff. apply H0. all: try lia. list_solve. list_solve.
                        intro Hz. assert (find_power mod_poly (poly_of_int z) = i).
                        symmetry. rewrite <- find_power_iff.
                        split. rewrite Hz. rewrite poly_of_int_inv. reflexivity. rewrite S1.
                        rewrite fec_n_eq; lia. all: auto.
                        intro Hzero. apply poly_of_int_zero in Hzero. lia.
                        apply polys_deg_bounded. lia. lia.
                    +++ assert (Hz: z = (poly_to_int (monomial (Z.to_nat i) %~ mod_poly))). { symmetry in Hfp.
                        rewrite <- find_power_iff in Hfp. destruct Hfp as [Hfp  Hi]. rewrite <- poly_of_int_to_int.
                        symmetry. assumption. lia. all: auto. intro Hzero. rewrite poly_of_int_zero in Hzero. lia.
                        apply polys_deg_bounded. lia. } 
                        rewrite Hz. rewrite upd_Znth_same. rewrite <- Hz. rewrite <- Hfp. reflexivity.
                        list_solve.
                  --- rewrite upd_Znth_diff. assumption. list_solve. list_solve. 
                      pose proof (modulus_poly_monomial (Z.to_nat i)). lia.
                ** rewrite upd_Znth_map.  assert (Hl: (map Vint
                    (upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)) 
                    (map Int.repr l) (Int.zero_ext 8 (Int.repr i)))) =  (map Vint
                    (map Int.repr (upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)) l i)))). {
                    f_equal. rewrite <- upd_Znth_map. f_equal. unfold Int.zero_ext.
                    f_equal. rewrite Zbits.Zzero_ext_mod; try lia. replace (two_p 8) with (256) by reflexivity.
                    rewrite Zmod_small; try rewrite unsigned_repr; try rep_lia. } rewrite Hl. cancel.
                    replace ((Z.to_nat fec_n - Z.to_nat (i + 1))%nat) with (Z.to_nat (fec_n - (i + 1))) by lia. cancel.
    + (*end of first loop - need to prove postcondition*) forward. entailer!.
      assert (i = fec_n). rewrite fec_n_eq; lia. subst. replace (Z.to_nat (fec_n - fec_n)) with 0%nat by lia.
      simpl. rewrite app_nil_r. cancel. 
      (*The only nontrivial part: l is the correct index_to_power_contents list*)
      assert (Hl: (map Vint (map Int.repr l)) =
      (map Vint (map Int.repr (prop_list (fun z : Z => find_power mod_poly (poly_of_int z)) fec_n)))). {
        f_equal. f_equal. apply Znth_eq_ext. rewrite prop_list_length. list_solve. lia. intros i Hi.
        rewrite? Zlength_map in H7. rewrite H7 in Hi.
        destruct (Z.eq_dec 0 i).
        - subst. rewrite H1. rewrite prop_list_Znth. assert (Hzero: poly_of_int 0 = zero) by 
          (rewrite poly_of_int_zero; lia). rewrite Hzero. rewrite find_power_zero. reflexivity. all: assumption. 
        - rewrite H0; try lia. rewrite prop_list_Znth. reflexivity. assumption. 
          pose proof (find_power_spec mod_poly Hpos Hprim Hnotx (poly_of_int i)) as Hfp.
          assert (Hnz: poly_of_int i <> zero). intro Hz. rewrite poly_of_int_zero in Hz. lia.
          specialize (Hfp Hnz (polys_deg_bounded _ Hi)). destruct Hfp as [ ? Hfpbound].
          rewrite field_size_fec_n in Hfpbound. lia. } rewrite Hl. unfold index_to_power_contents. cancel.
  - (*Second loop: calculate inverses*) 
    pose proof field_size_fec_n as Hfieldsize.
    forward_for_simple_bound 256%Z (EX (i : Z) (l: list Z),
    PROP (0 <= i <= fec_n  /\ Znth 0 l = 0%Z /\ (forall z, 0 < z < fec_n -> 0 <= poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int z)) < i ->
          Znth z l = poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int z))
      ))
    LOCAL (temp _mod (Vint (Int.repr modulus));  gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_invefec ))).
    + Exists (list_repeat (Z.to_nat fec_n ) 0%Z). entailer!. rewrite Znth_list_repeat_inrange.
      reflexivity. lia.
    + assert (Hfpbound: 0 <= find_power mod_poly (poly_of_int i) <= fec_n - 1). {
       destruct (Z.eq_dec i 0).
       - subst. assert (Hz: (poly_of_int 0 = zero)) by (rewrite poly_of_int_zero; lia). rewrite Hz.
         rewrite find_power_zero. lia. all: assumption.
       - pose proof (find_power_spec _ Hpos Hprim Hnotx (poly_of_int i)) as Hfp.
         assert (poly_of_int i <> zero). intro Hz. rewrite poly_of_int_zero in Hz. lia.
         assert (deg (poly_of_int i) < deg mod_poly). apply polys_deg_bounded. rewrite fec_n_eq; lia. 
         specialize (Hfp H0 H1). rewrite fec_n_eq; destruct Hfp; rep_lia. }
      forward.
      * entailer!. rewrite fec_n_eq; lia.
      * entailer!. rewrite index_to_power_contents_Znth. 2: rewrite fec_n_eq; lia. simpl.
        rewrite unsigned_repr; rep_lia.
      * rewrite index_to_power_contents_Znth. 2: rewrite fec_n_eq; lia.
        assert (Hinvbound: 0 <=
            poly_to_int (monomial (Z.to_nat (255 - find_power mod_poly (poly_of_int i))) %~ mod_poly) <
            256). { rewrite <- fec_n_eq. apply modulus_poly_bound. apply pmod_lt_deg. auto. }
        forward.
        -- entailer!. rewrite fec_n_eq; lia.
        -- entailer!. rewrite power_to_index_contents_Znth. simpl.
           rewrite unsigned_repr; rep_lia. rewrite fec_n_eq; lia.
        -- rewrite power_to_index_contents_Znth. 2: { simpl. rewrite fec_n_eq; lia. }
           forward.
          ++ entailer!. rewrite fec_n_eq; lia.
          ++ (*loop invariant preservation*)
              Exists (upd_Znth (poly_to_int (monomial (Z.to_nat 
                (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly)) l i).
            entailer!.
            ** assert (Hlen: Zlength l = fec_n) by list_solve. split. rewrite fec_n_eq; lia. split.
              --- (*handle 0 case separately*)
                  destruct (Z.eq_dec 0%Z (poly_to_int (monomial (Z.to_nat 
                    (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly))).
                +++ rewrite <- poly_of_int_to_int in e. assert (Hz: poly_of_int 0 = zero) by (rewrite poly_of_int_zero; lia).
                    rewrite Hz in e. exfalso. 
                    apply (irred_doesnt_divide_monomial mod_poly (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i)))).
                    all: try assumption. rewrite divides_pmod_iff. unfold divides_pmod. apply e. left. 
                    assumption. lia.
                +++ rewrite upd_Znth_diff. assumption. list_solve. rewrite Hlen; rewrite fec_n_eq; auto. 
                    assumption.
              --- intros z Hzf Hpi1. 
                  assert (0 <=  poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int z)) < i \/
                    poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int z)) = i) by lia. 
                  destruct H14 as [Hilt | Hi].
                +++ rewrite upd_Znth_diff. apply H2; try assumption; try lia. list_solve.
                    rewrite Hlen; rewrite fec_n_eq; auto. (*contradiction: i and z are inverses*)
                    intro Hz. assert (poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int z)) = i). {
                    symmetry. rewrite <- poly_of_int_to_int. 2 : lia. 
                    destruct (Z.eq_dec z 0%Z).
                    - subst. symmetry in e. rewrite <- poly_of_int_to_int in e; try lia.
                      assert (Hzero: poly_of_int 0 = zero) by (rewrite poly_of_int_zero; lia). rewrite Hzero in e.
                      exfalso. apply (irred_doesnt_divide_monomial mod_poly 
                        (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i)))); try assumption.
                      rewrite divides_pmod_iff. unfold divides_pmod. assumption. left. assumption.
                    - symmetry. rewrite <- poly_inv_iff. rewrite Hz. rewrite poly_of_int_inv.
                      pose proof (find_power_spec _ Hpos Hprim Hnotx (poly_of_int i)) as Hfp.
                      assert (Hinz: poly_of_int i <> zero). { intro Hzero. rewrite poly_of_int_zero in Hzero. lia. }
                      assert (Hdegi: deg (poly_of_int i) < deg mod_poly). apply polys_deg_bounded; rewrite fec_n_eq; lia.
                      specialize (Hfp Hinz Hdegi). destruct Hfp as [Hi Hfp_bound]. rewrite Hi at 2. split. 2: assumption.
                      rewrite pmod_mult_reduce. rewrite poly_mult_comm. rewrite pmod_mult_reduce. rewrite monomial_exp_law.
                      replace ((Z.to_nat (find_power mod_poly (poly_of_int i)) +
                      Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i)))%nat) with (Z.to_nat (fec_n - 1)) by lia.
                      replace (Z.to_nat (fec_n - 1)) with (0%nat + Z.to_nat (fec_n -1))%nat by lia.
                      rewrite <- Hfieldsize. replace (Z.to_nat (Z.of_nat (field_size mod_poly))) with
                      (field_size mod_poly) by lia.
                      rewrite <- monomial_add_field_size. rewrite monomial_0. apply pmod_refl.
                      all: try assumption. assert (0%Z = deg one) by (rewrite deg_one; reflexivity). lia.
                      intro Hzero. rewrite pmod_refl in Hzero. rewrite poly_of_int_zero in Hzero. lia.
                      assumption. apply polys_deg_bounded. lia. } lia.
                +++ (*proving the actual update, since i and z are correctly inverses this time*)
                    symmetry in Hi. rewrite <- poly_of_int_to_int in Hi. 2: lia.
                    assert (Hzi : poly_of_int z = poly_inv mod_poly modulus_poly_deg_pos (poly_of_int i)). {
                      rewrite poly_inv_sym. rewrite Hi. reflexivity. all: try assumption. apply polys_deg_bounded.
                      rewrite fec_n_eq; lia. apply polys_deg_bounded. lia. }
                    assert (Hz: z = (poly_to_int (monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly))). {
                      rewrite <- poly_of_int_to_int. rewrite Hzi. 2: lia.
                      destruct (destruct_poly (poly_of_int i)).
                      - rewrite e in Hi. rewrite <- poly_inv_zero in Hi. rewrite pmod_refl in Hi. 
                        rewrite poly_of_int_zero in Hi. lia. all: try assumption. apply polys_deg_bounded.
                        lia.
                      - rewrite <- poly_inv_iff. split. pose proof (find_power_spec _ Hpos Hprim Hnotx (poly_of_int i) n) as Hfp.
                        assert (Hideg: deg (poly_of_int i) < deg mod_poly). { apply polys_deg_bounded; rewrite fec_n_eq; lia. }
                        specialize (Hfp Hideg). destruct Hfp as [Hpi Hfp_bound]. rewrite Hpi at 1. rewrite pmod_mult_reduce.
                        rewrite poly_mult_comm. rewrite pmod_mult_reduce. rewrite monomial_exp_law.
                        replace ((Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i)) +
                          Z.to_nat (find_power mod_poly (poly_of_int i))))%nat with (0 + Z.to_nat (fec_n - 1))%nat by lia.
                        rewrite <- Hfieldsize. replace ( Z.to_nat (Z.of_nat (field_size mod_poly))) with (field_size mod_poly)
                        by lia. rewrite <- monomial_add_field_size. rewrite monomial_0. apply pmod_refl.
                        all: try assumption. assert (0%Z = deg one) by (rewrite deg_one; reflexivity). lia.
                        apply pmod_lt_deg; assumption. rewrite pmod_refl; try assumption. 
                        apply polys_deg_bounded; rewrite fec_n_eq; lia. }
                    rewrite <- Hz. rewrite upd_Znth_same. rewrite <- poly_of_int_to_int. assumption.
                    lia. list_solve.
            ** assert (Hl: (upd_Znth
                (poly_to_int (monomial (Z.to_nat (255 - find_power mod_poly (poly_of_int i))) %~ mod_poly))
                (map Vint (map Int.repr l)) (Vint (Int.zero_ext 8 (Int.repr i)))) = 
                (map Vint (map Int.repr (upd_Znth (poly_to_int
                  (monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly)) l
                  i)))). { rewrite upd_Znth_map. f_equal. rewrite <- upd_Znth_map. f_equal. unfold Int.zero_ext.
                rewrite fec_n_eq; simpl. reflexivity. unfold Int.zero_ext. f_equal. rewrite Zbits.Zzero_ext_mod.
                replace (two_p 8) with (256) by reflexivity.
                 rewrite Zmod_small. all: try(rewrite unsigned_repr; rep_lia). lia. } 
               rewrite Hl. cancel.
    + (*postcondition of 2nd loop*)
      Intros l. entailer!.
      assert (Hl: (map Vint (map Int.repr l)) = (inverse_contents fec_n)). {
        unfold inverse_contents. f_equal. f_equal. apply Znth_eq_ext. rewrite prop_list_length. list_solve. lia.
        intros i Hi.
        rewrite prop_list_Znth. 2: list_solve. assert (i = 0%Z \/ 0 < i) by lia. destruct H11 as [Hiz | Hipos].
        - subst. rewrite H0. assert (Hz: poly_of_int 0 = zero) by (rewrite poly_of_int_zero; lia). rewrite Hz.
          rewrite poly_inv_of_zero. symmetry. rewrite poly_to_int_zero_iff. reflexivity. all: try assumption.
        - rewrite H1. reflexivity. list_solve. 
          rewrite <- fec_n_eq. apply modulus_poly_bound.
          pose proof (poly_inv_spec _ modulus_poly_deg_pos Hirred (poly_of_int i)) as Hinv. apply Hinv.
          rewrite pmod_refl; auto. intro Hzero. rewrite poly_of_int_zero in Hzero. lia.
          apply polys_deg_bounded; try rep_lia. list_solve. } rewrite Hl. cancel.
Qed.
