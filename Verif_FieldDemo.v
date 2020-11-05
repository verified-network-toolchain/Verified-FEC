Require Import VST.floyd.proofauto.
Require Import FieldDemo.
Require Import Helper.
Require Import Poly.
Require Import ConcretePolys.
Require Import PolyMod.
Require Import PrimitiveFacts.
Require Import PropList.
Require Import IntPoly.

Import WPoly.

Instance CompSpecs : compspecs.
make_compspecs prog. Defined.

Definition Vprog : varspecs.
mk_varspecs prog. Defined.

(*Probably helpful more generally*)
Lemma unsigned_repr: forall z,
  0 <= z < Int.modulus -> Int.unsigned (Int.repr z) = z.
Proof.
  intros.
  pose proof (Int.eqm_unsigned_repr z).
  apply Int.eqm_sym in H0.
  unfold Int.eqm in H0. eapply Zbits.eqmod_small_eq. apply H0. rep_lia. rep_lia.
Qed.

(** Facts about [FEC_N and modulus] (hardcoded for now) *)

(*We keep fec_n, modulus, and (poly_of_int modulus) opaque, since for some reason when that is not the case,
  Qed takes forever. This also gives the benefit that the proofs work for any valid value of fec_n and modulus; we
  just have to prove these small and easy lemmas*)

(*Other than [modulus_poly], [fec_n_eq], and [modulus_eq], these lemmas are generic and true no matter the
  choice of (valid) FEC_N and modulus (the proofs will be different). The above 3 lemmas are not used in 
  any of the VST proofs, which are generic *)

Definition fec_n : Z := proj1_sig (opaque_constant 128).
Definition fec_n_eq : fec_n = 128%Z := proj2_sig (opaque_constant _).

Definition modulus : Z := proj1_sig (opaque_constant 137).
Definition modulus_eq : modulus = 137%Z := proj2_sig (opaque_constant _).

Lemma fec_n_bound: 8 <= fec_n <= 256.
Proof.
rewrite fec_n_eq. lia.
Qed.

Definition mod_poly : poly := proj1_sig (opaque_constant (poly_of_int modulus)).
Definition mod_poly_eq : mod_poly = poly_of_int modulus := proj2_sig (opaque_constant _).

(*not used in main proof - proof is generic*)
Lemma modulus_poly: mod_poly = p128.
Proof.
  rewrite mod_poly_eq. rewrite modulus_eq. reflexivity.
Qed. 

Lemma modulus_poly_deg: deg mod_poly = Z.log2 (fec_n).
Proof.
  rewrite modulus_poly. replace (deg p128) with 7 by reflexivity. rewrite fec_n_eq.
  reflexivity. 
Qed.

Lemma modulus_poly_deg_bounds: 3 <= deg mod_poly <= 8.
Proof.
  rewrite modulus_poly_deg. pose proof fec_n_bound.
  destruct H. apply Z.log2_le_mono in H. apply Z.log2_le_mono in H0.
  replace (Z.log2 8) with 3 in H by reflexivity. replace (Z.log2 256) with 8 in H0 by reflexivity. lia.
Qed.

Lemma fec_n_log2: Z.log2 (fec_n - 1) < Z.log2 (fec_n).
Proof.
  rewrite fec_n_eq.
  replace (Z.log2 (128 - 1)) with 6 by reflexivity.
  replace (Z.log2 128) with 7 by reflexivity. lia.
Qed.

Lemma modulus_poly_deg_pos: deg mod_poly > 0.
Proof.
  rewrite modulus_poly_deg. rewrite fec_n_eq. replace (Z.log2 128) with 7 by reflexivity.
  lia.
Qed.

Lemma modulus_poly_not_zero: mod_poly <> zero.
Proof.
  intro. pose proof modulus_poly_deg_pos. assert (deg zero < 0) by (rewrite deg_zero; reflexivity). rewrite H in H0.
  lia.
Qed.

Lemma polys_deg_bounded: forall z,
  0 <= z < fec_n ->
  deg (poly_of_int z) < deg mod_poly.
Proof.
  intros. destruct (Z.eq_dec 0 z).
  - subst. assert (poly_of_int 0 = zero) by (rewrite poly_of_int_zero; lia). rewrite H0.
    assert (deg zero < 0) by (rewrite deg_zero; reflexivity).
    pose proof (modulus_poly_deg_pos). lia.
  - rewrite poly_of_int_deg. rewrite modulus_poly_deg.
    assert (z <= fec_n - 1) by lia.
    apply Z.log2_le_mono in H0. pose proof fec_n_log2. lia. lia.
Qed.

Lemma fec_n_pow_2: 2 ^ (Z.log2 (fec_n)) = fec_n.
Proof.
  rewrite fec_n_eq. replace (Z.log2 128) with 7 by reflexivity. reflexivity.
Qed.

(*should be possible to prove from previous lemma, but not easy to relate Z.pow and Nat.pow*)
Lemma fec_n_pow_2_nat: (2%nat ^ (Z.to_nat (Z.log2 fec_n)))%nat = Z.to_nat (fec_n).
Proof.
  rewrite fec_n_eq.  
  replace (Z.log2 128) with 7 by reflexivity. reflexivity.
Qed.

Lemma modulus_poly_bound: forall p,
  deg p < deg mod_poly ->
  0 <= poly_to_int p < fec_n.
Proof.
  intros. pose proof (poly_to_int_bounded p).
  rewrite modulus_poly_deg in H.
  assert (poly_to_int p + 1 <= 2 ^ (deg p + 1)) by lia.
  assert (2 ^ (deg p + 1) <= 2 ^ (Z.log2 fec_n)). apply Z.pow_le_mono_r.
  lia. lia. rewrite fec_n_pow_2 in H2. lia.
Qed. 

Lemma modulus_poly_not_x: mod_poly <> x.
Proof.
  intros. rewrite modulus_poly. solve_neq.
Qed.

Lemma modulus_poly_primitive: primitive mod_poly.
Proof.
  rewrite modulus_poly. apply p128_primitive.
Qed.

Lemma modulus_poly_irred: irreducible mod_poly.
Proof.
  apply modulus_poly_primitive.
Qed.

Lemma field_size_fec_n: Z.of_nat (field_size mod_poly) = fec_n - 1.
Proof.
  unfold field_size. rewrite modulus_poly_deg.
  rewrite fec_n_pow_2_nat. pose proof fec_n_bound.  lia.
Qed.

Lemma modulus_poly_monomial: forall n,
  0 < poly_to_int ((monomial n) %~ mod_poly).
Proof.
  intros. apply poly_to_int_monomial_irred.
  apply modulus_poly_irred. apply modulus_poly_not_x.
  apply modulus_poly_deg_pos.
Qed.

Lemma modulus_pos: 0 <= modulus < Int.modulus.
Proof.
  rewrite modulus_eq. rep_lia.
Qed.

(** Definition of lookup tables *)

(* i -> x^i % f in fec_2_index*)
Definition power_to_index_contents (bound : Z) :=
  (map Vint (map Int.repr (prop_list (fun z => 
      poly_to_int ( (monomial (Z.to_nat z)) %~ mod_poly)) bound))).

(*p -> i such that x^i % f = p in fec_2_power. This is the coq function [find_power]*)
Definition index_to_power_contents :=
  (map Vint (map Int.repr (prop_list
  (fun z => find_power mod_poly (poly_of_int z)) fec_n))).

Definition inverse_contents bound :=
    (map Vint (map Int.repr (prop_list (fun z => 
      poly_to_int (poly_inv mod_poly modulus_poly_deg_pos  (poly_of_int z))) bound))).


Ltac solve_prop_length := try (unfold power_to_index_contents); try(unfold inverse_contents); rewrite? Zlength_map; rewrite prop_list_length; lia.


Lemma power_to_index_contents_plus_1: forall bound,
  0 <= bound ->
  power_to_index_contents (bound + 1) = power_to_index_contents bound ++ 
  (Vint (Int.repr (poly_to_int (monomial (Z.to_nat bound) %~ mod_poly)))) :: nil.
Proof.
  unfold power_to_index_contents. intros. rewrite prop_list_plus_1. rewrite? map_app.
  reflexivity. assumption.
Qed.

Lemma power_to_index_contents_length: forall bound,
  0 <= bound ->
  Zlength (power_to_index_contents bound) = bound.
Proof.
  intros. solve_prop_length.
Qed.

Lemma power_to_index_contents_Znth: forall bound i,
  0 <= i < bound ->
  Znth i (power_to_index_contents bound) = Vint (Int.repr (poly_to_int ((monomial (Z.to_nat i)) %~ mod_poly))).
Proof.
  intros. unfold power_to_index_contents. rewrite? Znth_map; try solve_prop_length.
  rewrite prop_list_Znth. reflexivity. lia.
Qed. 

Hint Rewrite Zlength_map : list_solve_rewrite. 

Lemma index_to_power_contents_length: Zlength (index_to_power_contents) = fec_n.
Proof.
  pose proof fec_n_bound.
  unfold index_to_power_contents. solve_prop_length.
Qed.

Lemma index_to_power_contents_Znth: forall i,
  0 <= i < fec_n ->
  Znth i index_to_power_contents = Vint (Int.repr (find_power mod_poly (poly_of_int i))).
Proof.
  intros. unfold index_to_power_contents. rewrite? Znth_map; try solve_prop_length.
  rewrite prop_list_Znth. reflexivity. lia.
Qed.



Lemma inverse_contents_length: forall bound,
  0 <= bound ->
  Zlength (inverse_contents bound) = bound.
Proof.
  intros. solve_prop_length.
Qed.

Lemma inverse_contents_Znth: forall bound i,
  0 <= i < bound ->
  Znth i (inverse_contents bound) = Vint (Int.repr (poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int i)))).
Proof.
  intros. unfold inverse_contents. rewrite? Znth_map; try solve_prop_length.
  rewrite prop_list_Znth. reflexivity. lia.
Qed.

Definition generate_index_power_tables_spec :=
  DECLARE _generate_index_power_tables
  WITH  gv: globals
  PRE [ ]
    PROP ()
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z))) (gv _fec_2_power);
        data_at Ews tint (Vint (Int.repr modulus)) (gv _modulus);
        data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N))
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
      data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
      data_at Ews tint (Vint (Int.repr modulus)) (gv _modulus);
       data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N)).

Definition multiply_spec :=
  DECLARE _multiply
  WITH gv: globals, f : Z, g : Z
  PRE [ tuchar, tuchar ]
    PROP (0 <= f < fec_n /\ 0 <= g < fec_n)
    PARAMS (Vint (Int.repr f); Vint (Int.repr g))
    GLOBALS (gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
      data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
       data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N))
  POST [ tuchar ]
    PROP ()
    RETURN (Vint (Int.repr (poly_to_int (((poly_of_int f) *~ (poly_of_int g)) %~ mod_poly ))))
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
      data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
       data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N)).

Definition generate_inverse_table_spec :=
  DECLARE _generate_inverse_table
  WITH gv: globals
  PRE [ ]
    PROP ()
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
         data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N);
         data_at Ews (tarray tuchar fec_n)  
            (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z))) (gv _fec_invefec))
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
         data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N);
         data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec)).
    
(*TODO: add*)
Definition Gprog := [generate_index_power_tables_spec; multiply_spec; generate_inverse_table_spec].

(*TODO: move*)
Lemma body_generate_inverse_table: semax_body Vprog Gprog f_generate_inverse_table generate_inverse_table_spec.
Proof.
  start_function. forward.
  pose proof fec_n_bound as Hfec.
  forward_loop (EX (i : Z) (l: list Z),
    PROP (0 <= i <= fec_n  /\ (forall z, 0 <= z < fec_n -> 0 <= poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int z)) < i ->
          Znth z l = poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int z))
      ))
    LOCAL (temp _i (Vint (Int.repr i)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
        data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_invefec ))).
    - Exists 0%Z. Exists (list_repeat (Z.to_nat fec_n ) 0%Z). entailer!.
    - Intros i. Intros l. forward.
      pose proof modulus_poly_deg_pos as Hpos.
      pose proof modulus_poly_not_x as Hnotx.
      pose proof modulus_poly_primitive as Hprim.
      pose proof modulus_poly_irred as Hirred.
      pose proof modulus_poly_not_zero as Hnonzero.
      pose proof modulus_poly_deg_bounds as Hbounds.
      pose proof modulus_poly_deg as Hdeglog.
      pose proof modulus_pos as Hmodulus. 
      pose proof field_size_fec_n as Hfieldsize.
      forward_if.
      + (*body of the loop*)
        forward.
        assert (E: 0 <= find_power mod_poly (poly_of_int i) <= fec_n - 1). {
        destruct (Z.eq_dec i 0).
        - subst. assert ((poly_of_int 0 = zero)) by (rewrite poly_of_int_zero; lia). rewrite H2.
          rewrite find_power_zero. lia.  all: assumption.
        -  pose proof (find_power_spec _ Hpos Hprim Hnotx (poly_of_int i)).
           assert (poly_of_int i <> zero). intro. rewrite poly_of_int_zero in H3. lia.
           assert (deg (poly_of_int i) < deg mod_poly). apply polys_deg_bounded; lia. 
           specialize (H2 H3 H4). destruct H2. rep_lia. }
        forward.
        * entailer!. rewrite index_to_power_contents_Znth; try lia. simpl. rewrite unsigned_repr; rep_lia.
        * rewrite index_to_power_contents_Znth; try lia.
          assert (0 <=
            poly_to_int (monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly) <
            fec_n). {  pose proof (modulus_poly_bound
              ((monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly))).
              assert (deg (monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly) <
              deg mod_poly). apply pmod_lt_deg. assumption. specialize (H2 H3). lia. }
          forward.
          -- entailer!. rewrite power_to_index_contents_Znth. simpl. rewrite unsigned_repr; try rep_lia.
              rep_lia.
          -- rewrite power_to_index_contents_Znth. forward. 2: rep_lia.
             forward. entailer!. Exists (i+1). Exists (upd_Znth
          (poly_to_int (monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly)) l i).
            entailer!.
          ++ intros. assert (0 <=  poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int z)) < i \/
             poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int z)) = i) by lia. destruct H18.
             ** rewrite upd_Znth_diff. apply H0; try assumption; try lia. list_solve. list_solve. 
                intro. assert (poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int z)) = i). { symmetry.
                rewrite <- poly_of_int_to_int. 2 : lia. 
                destruct (Z.eq_dec z 0%Z).
                --- subst. symmetry in e. rewrite <- poly_of_int_to_int in e; try lia.
                    assert (poly_of_int 0 = zero) by (rewrite poly_of_int_zero; lia). rewrite H19 in e.
                    exfalso. apply (irred_doesnt_divide_monomial mod_poly 
                      (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i)))); try assumption.
                    rewrite divides_pmod_iff. unfold divides_pmod. assumption. left. assumption.
                --- symmetry. rewrite <- poly_inv_iff. rewrite H19. rewrite poly_of_int_inv.
                    pose proof (find_power_spec _ Hpos Hprim Hnotx (poly_of_int i)).
                    assert (poly_of_int i <> zero). { intro. rewrite poly_of_int_zero in H21. lia. }
                    assert (deg (poly_of_int i) < deg mod_poly). apply polys_deg_bounded; lia.
                    specialize (H20 H21 H22). destruct H20. rewrite H20 at 2. split. 2: assumption.
                    rewrite pmod_mult_reduce. rewrite poly_mult_comm.
                    rewrite pmod_mult_reduce. rewrite monomial_exp_law.
                    replace ((Z.to_nat (find_power mod_poly (poly_of_int i)) +
                    Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i)))%nat) with (Z.to_nat (fec_n - 1)) by lia.
                    replace (Z.to_nat (fec_n - 1)) with (0%nat + Z.to_nat (fec_n -1))%nat by lia.
                    rewrite <- Hfieldsize. replace (Z.to_nat (Z.of_nat (field_size mod_poly))) with
                    (field_size mod_poly) by lia.
                    rewrite <- monomial_add_field_size. rewrite monomial_0. apply pmod_refl.
                    all: try assumption. assert (0%Z = deg one) by (rewrite deg_one; reflexivity). lia.
                    intro. rewrite pmod_refl in H20. rewrite poly_of_int_zero in H20. lia.
                    assumption. apply polys_deg_bounded. lia. }
                 lia.
             ** (*may need to do i=0 case separately*) symmetry in H18. rewrite <- poly_of_int_to_int in H18. 2: lia.
                assert (poly_of_int z = poly_inv mod_poly modulus_poly_deg_pos (poly_of_int i)).
                rewrite poly_inv_refl. rewrite H18. reflexivity. all: try assumption. apply polys_deg_bounded.
                lia. apply polys_deg_bounded. lia. intro. rewrite poly_of_int_zero in H19. lia.
                apply polys_bound.



 assert ((poly_to_int (monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly)) = z). {
                symmetry in H18. rewrite <- poly_of_int_to_int in H18. 2: lia.
                pose proof (poly_inv_iff).
                pose proof (find_power_spec _ Hpos Hprim Hnotx (poly_of_int i)).


 rewrite <- H18.
                


 rewrite upd_Znth_same.
                a
                    
                    rewrite pmod_mult_distr.
                    . }
                  
(*shit my loop invariant is wrong
 assert ((Int.min_signed <=
              poly_to_int (monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly) <=
              Int.max_signed))



 rewrite power_to_index_contents_Znth. forward.
             Search poly_to_int.
             
      assert (0 < find_power mod_poly (poly_of_int i) <= Z.of_nat (field_size mod_poly)). {
      destruct (Z.eq_dec i 0). 
      - subst. assert ((poly_of_int 0 = zero)) by (rewrite poly_of_int_zero; lia). rewrite H1.
        rewrite find_power_zero. rep_lia.
        simpl.
 forward_if.
      + (*body of the loop*) 
        forward. 


 forward. 
        * entailer!. rewrite index_to_power_contents_Znth. simpl. pose proof (find_power_iff).  rep_lia.
      + (*end of the loop*) 
        forward. assert ( i = fec_n) by lia. entailer!. replace (fec_n - fec_n) with (0%Z) by lia.
        simpl. rewrite app_nil_r. cancel. Exists 0%Z. entailer!. lia.

(find_power mod_poly (poly_of_int i))

Lemma body_generate_index_power_tables : semax_body Vprog Gprog f_generate_index_power_tables generate_index_power_tables_spec.
Proof.
  start_function. forward.
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
    LOCAL (temp _i (Vint (Int.repr i)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents i ++ map Vint (map Int.repr (list_repeat
      ((Z.to_nat fec_n) - Z.to_nat i)%nat 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
        data_at Ews tint (Vint (Int.repr modulus)) (gv _modulus);
       data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N))).
- Exists 0%Z. Exists (list_repeat (Z.to_nat fec_n) 0%Z). entailer!.
  pose proof fec_n_bound. split. lia. apply Znth_list_repeat_inrange. rep_lia.
  unfold power_to_index_contents. rewrite prop_list_0. simpl.
  replace ((Z.to_nat fec_n - 0)%nat) with (Z.to_nat fec_n) by rep_lia. entailer!.
- Intros i. Intros l.
  pose proof modulus_poly_deg_pos as Hpos.
  pose proof modulus_poly_not_x as Hnotx.
  pose proof modulus_poly_primitive as Hprim.
  pose proof modulus_poly_irred as Hirred.
  pose proof modulus_poly_not_zero as Hnonzero.
  pose proof modulus_poly_deg_bounds as Hbounds.
  pose proof modulus_poly_deg as Hdeglog.
  pose proof fec_n_bound as Fbound.
  pose proof modulus_pos as Hmodulus. 
  forward. forward_if. 2 : { assert (i = fec_n) by lia.
  forward. entailer!.
  replace ((Z.to_nat fec_n - Z.to_nat fec_n)%nat) with 0%nat by lia.
  simpl. rewrite app_nil_r. entailer!. unfold index_to_power_contents.
  (*prove that our invariant actually leads to correct list at the end*) 
  assert ((map Vint (map Int.repr l)) =
  (map Vint (map Int.repr (prop_list (fun z : Z => find_power mod_poly (poly_of_int z)) fec_n)))). {
  f_equal. f_equal. apply Znth_eq_ext. rewrite prop_list_length. list_solve. lia. intros.
  rewrite? Zlength_map in H8. rewrite H8 in H15.
  destruct (Z.eq_dec 0 i).
  - subst. rewrite H1. rewrite prop_list_Znth. assert (poly_of_int 0 = zero) by (rewrite poly_of_int_zero; lia).
    rewrite H16. rewrite find_power_zero. reflexivity. all: assumption. 
  - rewrite H0. rewrite prop_list_Znth. reflexivity. assumption. lia. pose proof (find_power_spec
    mod_poly Hpos Hprim Hnotx (poly_of_int i)).
    assert (poly_of_int i <> zero). intro. rewrite poly_of_int_zero in H17. lia.
    specialize (H16 H17); clear H17. specialize (H16 (polys_deg_bounded _ H15)).
    destruct H16.
    rewrite field_size_fec_n in H17. lia. } rewrite H15. cancel. }
  (*loop body - first, i=0 case*)
  forward_if (PROP (0 <= i <= fec_n /\ 
      (forall z, 0 < z < fec_n -> 0 < find_power mod_poly (poly_of_int z) < i -> 
          Znth z l = find_power mod_poly (poly_of_int z)) /\
      Znth 0 l = 0%Z)
    LOCAL (temp _i (Vint (Int.repr i)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents (i + 1) ++ map Vint (map Int.repr (list_repeat
      ((Z.to_nat fec_n) - Z.to_nat (i + 1))%nat 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
        data_at Ews tint (Vint (Int.repr modulus)) (gv _modulus);
       data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N))).
  + forward. entailer!. rewrite Zlength_upd_Znth in H5. 
    unfold power_to_index_contents.
    replace ((Z.to_nat fec_n) - Z.to_nat 0%Z)%nat with (Z.to_nat fec_n)%nat by lia. 
    rewrite prop_list_0. simpl.  
    replace (Z.to_nat (fec_n)) with (1%nat + (Z.to_nat fec_n - Z.to_nat 1)%nat)%nat by rep_lia.
    rewrite <- list_repeat_app. rewrite map_app. rewrite map_app.
    rewrite upd_Znth_app1. 
    assert ((upd_Znth 0 (map Vint (map Int.repr (list_repeat 1 0%Z))) (Vint (Int.zero_ext 8 (Int.repr 1)))) =
    Vint (Int.zero_ext 8 (Int.repr 1)) :: nil). simpl.
    rewrite upd_Znth0. reflexivity. rewrite H3. clear H3. simpl.
    assert ((Vint (Int.zero_ext 8 (Int.repr 1))) = (Vint (Int.repr (poly_to_int (monomial 0 %~ mod_poly))))). {
    rewrite monomial_0. rewrite pmod_refl. rewrite poly_to_int_one. reflexivity. all: try assumption.
    assert (0%Z = deg one) by (apply deg_one; reflexivity). lia. }
    rewrite H3. replace (Z.to_nat fec_n - 1 - 0)%nat with (Z.to_nat fec_n - 1)%nat
    by lia. cancel. 
    rewrite? Zlength_map. simpl. list_solve.
  + (* i <> 0*) forward. 
    * (*array access is valid*) entailer!. rewrite Znth_app1.
      unfold power_to_index_contents. rewrite? Znth_map.
      rewrite prop_list_Znth. pose proof (modulus_poly_bound (monomial (Z.to_nat (i - 1)) %~ mod_poly)).
      specialize (H14 (pmod_lt_deg _ Hpos _)). simpl. rewrite unsigned_repr. all: try rep_lia.
      all: solve_prop_length.
    * (*continue function body - set fec_2_index*)
      forward. rewrite Znth_app1. unfold power_to_index_contents at 1. 
      unfold power_to_index_contents at 1. 
      rewrite Znth_map. rewrite Znth_map. rewrite prop_list_Znth. simpl. 
      unfold Int.shl. remember (poly_to_int (monomial (Z.to_nat (i - 1)) %~ mod_poly)) as prior.
      pose proof (modulus_poly_bound (monomial (Z.to_nat (i-1)) %~ mod_poly) (pmod_lt_deg _ Hpos _))
      as Hpriorbound. 
      rewrite (unsigned_repr prior); try rep_lia.
      rewrite (unsigned_repr 1); try rep_lia. simpl. all: try rep_lia.
      all: try solve_prop_length. forward.
      (*if statement - first, if overflow*)
      forward_if (PROP (0 <= i <= fec_n /\ 
      (forall z, 0 < z < fec_n -> 0 < find_power mod_poly (poly_of_int z) < i -> 
          Znth z l = find_power mod_poly (poly_of_int z)) /\
      Znth 0 l = 0%Z)
    LOCAL (temp _i (Vint (Int.repr i)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents (i + 1) ++ map Vint (map Int.repr (list_repeat
      ((Z.to_nat fec_n) - Z.to_nat (i + 1))%nat 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
        data_at Ews tint (Vint (Int.repr modulus)) (gv _modulus);
       data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N))).
      -- forward. forward. entailer!. 
         remember (poly_to_int (monomial (Z.to_nat (i - 1)) %~ mod_poly)) as prior.
         unfold Int.xor. rewrite (unsigned_repr (2 * prior)); try rep_lia.
         rewrite (unsigned_repr modulus); try(rep_lia).
         rewrite power_to_index_contents_plus_1.
         assert (Zlength (power_to_index_contents i) = i) by (unfold power_to_index_contents; solve_prop_length ).
         rewrite upd_Znth_app2. replace (i - Zlength (power_to_index_contents i)) with 0%Z by lia.
         assert (list_repeat (Z.to_nat fec_n - Z.to_nat i) 0%Z = 
         0%Z :: (list_repeat (Z.to_nat fec_n - Z.to_nat (i + 1)) 0%Z)).
         replace (Z.to_nat fec_n - Z.to_nat i)%nat with (1%nat + (Z.to_nat fec_n - Z.to_nat (i + 1))%nat)%nat by lia. 
         rewrite <- list_repeat_app. reflexivity. rewrite H17. clear H17.
         simpl.
         rewrite upd_Znth0. (*finally, prove that this finds x^i % f - this is where we use properties of pmod and deg*) 
         2: list_solve. 2 : lia.
         assert (Vint (Int.zero_ext 8 (Int.repr (Z.lxor (2 * prior) modulus))) = 
          Vint (Int.repr (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)))). f_equal.
         assert ((Z.lxor (2 * prior) modulus) = (poly_to_int (monomial (Z.to_nat i) %~ mod_poly))). {
         rewrite <- poly_of_int_to_int. rewrite xor_addition; try rep_lia. 
         assert (Hdeg: deg (poly_of_int (2 * prior)) = deg (mod_poly)). { rewrite poly_shiftl.
         rewrite poly_mult_deg. rewrite deg_x. rewrite poly_of_int_deg. all: try lia.
         rewrite modulus_poly_deg.
         assert ((Z.log2 prior) <= Z.log2 (fec_n - 1)). apply Z.log2_le_mono. rep_lia.
         pose proof fec_n_log2. pose proof (Z.log2_double prior). assert (0 < prior) by rep_lia. specialize (H19 H20); clear H20.
         replace (Z.succ (Z.log2 prior)) with (1 + Z.log2 prior) in H19 by lia.
         assert (Z.log2 (fec_n) <= Z.log2 (2 * prior)). apply Z.log2_le_mono. lia. lia.
         intro. pose proof deg_x. rewrite <- deg_zero in H17. lia.
         intro. rewrite poly_of_int_zero in H17. lia. }
         rewrite Heqprior. rewrite Heqprior in Hdeg. 
         rewrite poly_shiftl. rewrite poly_shiftl in Hdeg. rewrite poly_of_int_inv.
         rewrite poly_of_int_inv in Hdeg.
         all: try (apply modulus_poly_monomial).
         assert (deg (x *~ (monomial (Z.to_nat (i - 1)) %~ mod_poly) +~ mod_poly)
          < deg (mod_poly)). {
         rewrite poly_add_comm.
         apply poly_add_deg_same. rewrite Hdeg. reflexivity. assumption. }
         rewrite <- mod_poly_eq.
         rewrite <- (pmod_refl _ Hpos _ H17).
         rewrite pmod_add_distr. rewrite pmod_same. rewrite poly_add_0_r.
         rewrite? pmod_twice. rewrite <- (pmod_refl _ Hpos x). rewrite <- pmod_mult_distr.
         rewrite <- monomial_expand. replace (S (Z.to_nat (i - 1))) with (Z.to_nat i) by lia.
         reflexivity. all: try assumption. pose proof deg_x. lia. 
         rewrite Z.lxor_nonneg. pose proof modulus_pos. rep_lia.  }
         rewrite H17. unfold Int.zero_ext.  f_equal.
         pose proof (modulus_poly_bound (monomial (Z.to_nat i) %~ mod_poly)
         (pmod_lt_deg _ Hpos _)). 
         rewrite Zbits.Zzero_ext_mod. replace (two_p 8) with (256) by reflexivity.
         rewrite Zmod_small. apply unsigned_repr; try rep_lia. 
         rewrite unsigned_repr; try rep_lia. lia. rewrite H17. rewrite <- app_assoc. simpl.
         cancel.
      -- forward. entailer!.  (*similar case, a bit easier because no overflow*)
         remember (poly_to_int (monomial (Z.to_nat (i - 1)) %~ mod_poly)) as prior.
         rewrite power_to_index_contents_plus_1.
         assert (Zlength (power_to_index_contents i) = i) by ( unfold power_to_index_contents; solve_prop_length).
         2: lia. rewrite upd_Znth_app2. 2 : list_solve.
         replace (i - Zlength (power_to_index_contents i)) with 0%Z by lia.
         assert (list_repeat (Z.to_nat fec_n - Z.to_nat i) 0%Z = 
         0%Z :: (list_repeat (Z.to_nat fec_n - Z.to_nat (i + 1)) 0%Z)).
         replace (Z.to_nat fec_n - Z.to_nat i)%nat with (1%nat + (Z.to_nat fec_n - Z.to_nat (i + 1))%nat)%nat by lia. 
         rewrite <- list_repeat_app. simpl. reflexivity. rewrite H17. clear H17.
         simpl.
         rewrite upd_Znth0. (*finally, prove that this find x^i % f*) 
         assert (Vint (Int.zero_ext 8 (Int.repr (2 * prior))) = 
          Vint (Int.repr (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)))). f_equal.
         assert (2 * prior = (poly_to_int (monomial (Z.to_nat i) %~ mod_poly))). {
         rewrite <- poly_of_int_to_int. 2 : lia. 
         assert (Hdeg: deg (poly_of_int (2 * prior)) < deg mod_poly). { 
         assert (0%Z = 2 * prior \/ 0 < 2 * prior) by lia. destruct H17. rewrite <- H17.
         assert (poly_of_int 0 = zero). rewrite poly_of_int_zero. lia. rewrite H18. 
         assert (deg zero < 0) by (rewrite deg_zero; reflexivity). lia.
         rewrite poly_of_int_deg. 
         assert (2 * prior <= fec_n - 1) by lia. apply Z.log2_le_mono in H18.
         pose proof fec_n_log2. lia. assumption. }
         pose proof (modulus_poly_monomial (Z.to_nat (i-1))) as Hpriorpos.
         rewrite Heqprior. rewrite Heqprior in Hdeg. 
         rewrite poly_shiftl. rewrite poly_shiftl in Hdeg. rewrite poly_of_int_inv.
         rewrite poly_of_int_inv in Hdeg. all: try lia. 
         (*now the goal is simple*)
         rewrite <- (pmod_refl _ Hpos _ Hdeg). rewrite pmod_mult_distr.
         rewrite pmod_twice. rewrite <- pmod_mult_distr. rewrite <- monomial_expand.
         replace (S (Z.to_nat (i - 1))) with (Z.to_nat i) by lia. reflexivity. all: assumption. }
         rewrite H17. unfold Int.zero_ext. f_equal.
         pose proof (modulus_poly_bound (monomial (Z.to_nat i) %~ mod_poly)
         (pmod_lt_deg _ Hpos _)). 
         rewrite Zbits.Zzero_ext_mod. replace (two_p 8) with (256) by reflexivity.
         rewrite Zmod_small. apply unsigned_repr; try rep_lia. 
         rewrite unsigned_repr; try rep_lia. lia. rewrite H17. rewrite <- app_assoc. simpl.
         cancel.
    + (*now, need to prove the other invariant (for the index -> power array*) 
      pose proof (modulus_poly_bound (monomial (Z.to_nat i) %~ mod_poly)
         (pmod_lt_deg _ Hpos _)). 
      forward.
      (*prove index is valid*)
      entailer!. rewrite Znth_app1. unfold power_to_index_contents. rewrite? Znth_map.
      rewrite prop_list_Znth. simpl. rewrite unsigned_repr. all: try rep_lia. 
      all: try solve_prop_length.
      (*now continue and show loop invariant preserved - this is a bit tricky because
      we are not filling up the array in an orderly way - need to show that we dont fill in the same
      spot twice (other than 0, special case). We rely on the uniqueness of [find_power] *)
      rewrite Znth_app1. all: try solve_prop_length.
      all: unfold power_to_index_contents at 1. rewrite? Znth_map. rewrite prop_list_Znth.  2 :lia.
      all: try solve_prop_length. 
      forward. forward. Exists (i+1).
      Exists ((upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)) l i)).
      (*Now, let's prove the invariant is preserved*) entailer!. 
      pose proof field_size_fec_n as S1.
      rewrite Zlength_upd_Znth in H9. rewrite? Zlength_map in H9. split.
        -- intros. 
            assert (0 < find_power mod_poly (poly_of_int z) < i \/ 
            find_power mod_poly (poly_of_int z) = i) by lia.
            destruct H17.
            ++ (*if smaller than i - MUST be different than the current one - uniqueness*)
               rewrite upd_Znth_diff. apply H0. all: try lia. 
               intro. assert (find_power mod_poly (poly_of_int z) = i).
               symmetry. rewrite <- find_power_iff.
               split. rewrite H18. rewrite poly_of_int_inv. reflexivity. lia. all: try assumption.
               intro. apply poly_of_int_zero in H19. lia.
               apply polys_deg_bounded. lia. lia.
            ++ assert (z = (poly_to_int (monomial (Z.to_nat i) %~ mod_poly))). { symmetry in H17.
               rewrite <- find_power_iff in H17. destruct H17. rewrite <- poly_of_int_to_int.
               symmetry. assumption. lia. all: try assumption. intro. rewrite poly_of_int_zero in H18. lia.
               apply polys_deg_bounded. lia. }
               rewrite H18. rewrite upd_Znth_same. rewrite <- H18. rewrite <- H17. reflexivity.
               lia.
          -- rewrite upd_Znth_diff. assumption. lia. lia. pose proof (modulus_poly_monomial (Z.to_nat i)). lia. 
          -- rewrite upd_Znth_map.  assert ((map Vint
     (upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)) 
        (map Int.repr l) (Int.zero_ext 8 (Int.repr i)))) =  
              (map Vint
         (map Int.repr (upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ mod_poly)) l i)))).
              f_equal. rewrite <- upd_Znth_map. f_equal. unfold Int.zero_ext.
              f_equal. rewrite Zbits.Zzero_ext_mod; try lia. replace (two_p 8) with (256) by reflexivity.
              rewrite Zmod_small. rewrite unsigned_repr. reflexivity. rep_lia.
              rewrite unsigned_repr. rep_lia. rep_lia. rewrite H15. cancel.
Qed.

(*Verification of multiply function *)
Lemma body_multiply : semax_body Vprog Gprog f_multiply multiply_spec.
Proof.
  start_function.
  pose proof fec_n_bound as Fbound.
  forward_if (
    PROP ()
    LOCAL (temp _t'1 (Vint (Int.repr (if Z.eq_dec f 0%Z then 0%Z else if Z.eq_dec g 0%Z then 0%Z else 1%Z)));
     temp _a (Vint (Int.repr f)); temp _b (Vint (Int.repr g)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
   data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
   data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N))).
  - forward. entailer!.
    if_tac. subst. contradiction. if_tac. subst. 
    assert (Int.eq (Int.repr 0) Int.zero = true) by (unfold Int.zero; apply Int.eq_true).
    rewrite H12.  unfold Int.zero; reflexivity.
    assert (Int.eq (Int.repr g) (Int.zero) = false). {
      destruct (Int.eq (Int.repr g) Int.zero ) eqn : B.
      unfold Int.zero in B. symmetry in B. apply binop_lemmas2.int_eq_true in B.
      apply repr_inj_unsigned in B. contradiction. rep_lia. rep_lia. reflexivity. }
    rewrite H13. reflexivity.
  - forward. entailer!. if_tac. reflexivity. 
    unfold Int.zero in H0. apply repr_inj_unsigned in H0; rep_lia.
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
    + destruct H. destruct (Z.eq_dec f 0). contradiction. destruct (Z.eq_dec g 0). contradiction.
      clear H1'. deadvars!.
      assert (Hfnonzero: poly_of_int f <> zero). { intro. rewrite poly_of_int_zero in H3. lia. }
      assert (Hgnonzero: poly_of_int g <> zero). { intro. rewrite poly_of_int_zero in H3. lia. }
      forward.
      * entailer!. rewrite index_to_power_contents_Znth; try lia. simpl.
        pose proof (find_power_spec mod_poly Hpos Hprim Hnotx (poly_of_int f) Hfnonzero Hfbound).
        destruct H13.
        pose proof field_size_fec_n. rewrite unsigned_repr; rep_lia.
      * forward.
        -- entailer!. rewrite index_to_power_contents_Znth; try lia. simpl.
           pose proof (find_power_spec mod_poly Hpos Hprim Hnotx (poly_of_int g) Hgnonzero Hgbound).
           destruct H14.
           pose proof field_size_fec_n. rewrite unsigned_repr; rep_lia.
        -- forward. forward.
           pose proof (find_power_spec mod_poly Hpos Hprim Hnotx (poly_of_int f) Hfnonzero Hfbound).
           pose proof (find_power_spec mod_poly Hpos Hprim Hnotx (poly_of_int g) Hgnonzero Hgbound).
           destruct H3. destruct H4. 
           (*for i + j > fec_n - 1, get conditional in usable form*)
           rewrite? index_to_power_contents_Znth; try lia. simpl.
           unfold Int.add. rewrite? unsigned_repr; try rep_lia. 
           forward_if.
           ++  assert (Hbound: 0 <= (find_power mod_poly (poly_of_int f) + find_power mod_poly (poly_of_int g))
                - (fec_n - 1) < fec_n) by rep_lia.
              remember (monomial
                  (Z.to_nat
                  ((find_power mod_poly (poly_of_int f) + find_power mod_poly (poly_of_int g)) -
                  (fec_n - 1))) %~ mod_poly) as prod.
                 pose proof modulus_poly_bound prod. assert (deg prod < deg mod_poly) by (rewrite Heqprod;
                 apply pmod_lt_deg; assumption). specialize (H8 H9). 
              forward. forward.
              ** entailer!. rewrite power_to_index_contents_Znth; try lia. simpl.
                 rewrite unsigned_repr. rep_lia. rep_lia.
              ** forward. entailer!. (*now, we prove that this actually computes the product for this case*)
                 rewrite power_to_index_contents_Znth; try lia. f_equal. f_equal. f_equal. (*TODO from here*)
                 rewrite monomial_add_field_size; try assumption.
                 replace (Z.to_nat (find_power mod_poly (poly_of_int f) + find_power mod_poly (poly_of_int g) - (fec_n - 1)))
                 with ((Z.to_nat (find_power mod_poly (poly_of_int f)) +
                      Z.to_nat (find_power mod_poly (poly_of_int g)) -
                      Z.to_nat (fec_n - 1))%nat) by lia.
                 rewrite <- Hfield_size. replace (Z.to_nat (Z.of_nat (field_size mod_poly))) with
                 (field_size mod_poly) by lia. replace 
                  (Z.to_nat (find_power mod_poly (poly_of_int f)) + Z.to_nat (find_power mod_poly (poly_of_int g)) -
                  field_size mod_poly + field_size mod_poly)%nat with
                  ((Z.to_nat (find_power mod_poly (poly_of_int f)) + Z.to_nat (find_power mod_poly (poly_of_int g)))%nat) by lia.
                  rewrite <- monomial_exp_law. rewrite pmod_mult_distr; try assumption.
                  rewrite <- H3. rewrite <- H4. reflexivity.
            ++ (*other side of the if statement*) 
                assert (Hbound: 0 <= (find_power mod_poly (poly_of_int f) + find_power mod_poly (poly_of_int g)) < fec_n) by rep_lia.
               remember (monomial
                  (Z.to_nat
                  ((find_power mod_poly (poly_of_int f) + find_power mod_poly (poly_of_int g)))) %~ mod_poly) as prod.
                 pose proof modulus_poly_bound prod. assert (deg prod < deg mod_poly) by (rewrite Heqprod;
                 apply pmod_lt_deg; assumption). specialize (H8 H9).
                 forward.
                ** entailer!.  rewrite power_to_index_contents_Znth. simpl. rewrite unsigned_repr;  rep_lia. rep_lia.
                ** forward. entailer!. (*now the easier, but similar case*) rewrite power_to_index_contents_Znth; try lia.
                   f_equal. f_equal. f_equal. replace
                   (Z.to_nat (find_power mod_poly (poly_of_int f) + find_power mod_poly (poly_of_int g))) with
                   (Z.to_nat (find_power mod_poly (poly_of_int f)) + Z.to_nat (find_power mod_poly (poly_of_int g)))%nat by lia.
                   rewrite <- monomial_exp_law. rewrite pmod_mult_distr; try assumption.
                   rewrite <- H3. rewrite <- H4. reflexivity.
    + if_tac; subst.
      * forward. entailer!. assert (poly_of_int 0%Z = zero). rewrite poly_of_int_zero. lia.
        rewrite H12. rewrite poly_mult_0_l. rewrite pmod_zero; try assumption. 
        assert (poly_to_int zero = 0%Z). rewrite poly_to_int_zero_iff. reflexivity. rewrite H13. reflexivity.
      * if_tac; subst.
        -- forward. entailer!.  assert (poly_of_int 0%Z = zero). rewrite poly_of_int_zero. lia.
           rewrite H13. rewrite poly_mult_0_r. rewrite pmod_zero; try assumption. 
           assert (poly_to_int zero = 0%Z). rewrite poly_to_int_zero_iff. reflexivity. rewrite H14. reflexivity.
        -- inversion H1.
Qed.

(*Verification of generate inverse function*)


