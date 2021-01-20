Require Import VST.floyd.proofauto.

Require Import fec.
Require Import Helper.
Require Import Poly.
Require Import ConcretePolys.
Require Import PolyMod.
Require Import PrimitiveFacts.
Require Import PropList.
Require Import IntPoly.
Require Import ListMatrix.
Require Import PolyField.

Import WPoly.

Set Bullet Behavior "Strict Subproofs".

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
  unfold Int.eqm in H0. eapply Zbits.eqmod_small_eq. apply H0. all: rep_lia. 
Qed.

(** Facts about [FEC_N and modulus] (hardcoded for now) *)

(*We keep fec_n, modulus, and (poly_of_int modulus) opaque, since for some reason when that is not the case,
  Qed takes forever. This also gives the benefit that the proofs work for any valid value of fec_n and modulus; we
  just have to prove these small and easy lemmas*)

(*Other than [modulus_poly], [fec_n_eq], and [modulus_eq], these lemmas are generic and true no matter the
  choice of (valid) FEC_N and modulus (the proofs will be different). The above 3 lemmas are not used in 
  any of the VST proofs, which are generic *)

Definition fec_n : Z := proj1_sig (opaque_constant 256).
Definition fec_n_eq : fec_n = 256%Z := proj2_sig (opaque_constant _).

Definition modulus : Z := proj1_sig (opaque_constant 285).
Definition modulus_eq : modulus = 285%Z := proj2_sig (opaque_constant _).

Lemma fec_n_bound: 8 <= fec_n <= 256.
Proof.
rewrite fec_n_eq. lia.
Qed.

Definition mod_poly : poly := proj1_sig (opaque_constant (poly_of_int modulus)).
Definition mod_poly_eq : mod_poly = poly_of_int modulus := proj2_sig (opaque_constant _).

(*not used in main proof - proof is generic*)
Lemma modulus_poly: mod_poly = p256.
Proof.
  rewrite mod_poly_eq. rewrite modulus_eq. reflexivity.
Qed. 

Lemma modulus_poly_deg: deg mod_poly = Z.log2 (fec_n).
Proof.
  rewrite modulus_poly. replace (deg p256) with 8 by reflexivity. rewrite fec_n_eq.
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
  replace (Z.log2 (256 - 1)) with 7 by reflexivity.
  replace (Z.log2 256) with 8 by reflexivity. lia.
Qed.

Lemma modulus_poly_deg_pos: deg mod_poly > 0.
Proof.
  rewrite modulus_poly_deg. rewrite fec_n_eq. replace (Z.log2 256) with 8 by reflexivity.
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
  rewrite fec_n_eq. replace (Z.log2 256) with 8 by reflexivity. reflexivity.
Qed.

(*should be possible to prove from previous lemma, but not easy to relate Z.pow and Nat.pow*)
Lemma fec_n_pow_2_nat: (2%nat ^ (Z.to_nat (Z.log2 fec_n)))%nat = Z.to_nat (fec_n).
Proof.
  rewrite fec_n_eq.  
  replace (Z.log2 256) with 8 by reflexivity. reflexivity.
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
  rewrite modulus_poly. apply p256_primitive. 
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

Definition F := qpoly_fieldType modulus_poly_deg_pos modulus_poly_irred.

Instance F_inhab : Inhabitant (ssralg.GRing.Field.sort F) := inhabitant_F F.

(*Matrices are represented in the C code by a single pointer, pointing to a location in memory of
  size m * n, such that the reversed rows appear one after another. We need to flatten a matrix
  into a single list to represent this in Coq*)

Definition flatten_mx_aux (mx: matrix F) (base: list Z) : list Z :=
  fold_right (fun l acc => rev (map (fun q => poly_to_int (proj1_sig q)) l) ++ acc) base  mx.

Definition flatten_mx (mx: matrix F) : list Z :=
  flatten_mx_aux mx nil.

(*Since matrices are not necessarily well formed*)
Definition whole_Zlength (l: matrix F) :=
  fold_right (fun x acc => Zlength x + acc) 0%Z l.

Lemma whole_Zlength_nonneg: forall l,
  0 <= whole_Zlength l.
Proof.
  intros. induction l; simpl.
  - lia.
  - pose proof (Zlength_nonneg a). (*Why doesn't lia work?*)
    apply Z.add_nonneg_nonneg; assumption.
Qed. 

Lemma flatten_mx_aux_Znth: forall (mx: matrix F) b i,
  whole_Zlength mx <= i ->
  Znth i (flatten_mx_aux mx b) = Znth (i - whole_Zlength mx) b.
Proof.
  intros mx b i Hi. unfold flatten_mx_aux. generalize dependent i. induction mx; intros i Hi; simpl.
  - f_equal. lia.
  - simpl in Hi.
    assert (Hlen: Zlength (rev (map (fun q : {p : poly | deg p < deg mod_poly} => poly_to_int (proj1_sig q)) a)) =
      Zlength a). rewrite initial_world.Zlength_rev. list_solve. rewrite app_Znth2.
    rewrite Hlen. rewrite IHmx. f_equal. rewrite Z.sub_add_distr. reflexivity. rewrite <- Z.le_add_le_sub_l.
    assumption. rewrite Hlen. pose proof (whole_Zlength_nonneg mx). 
    assert (forall z1 z2 z3, 0 <= z2 -> z1 + z2 <= z3 -> z1 <= z3). intros. lia.
    assert (Zlength a <= i). eapply H0. apply H. assumption. lia.
Qed.

Lemma whole_Zlength_wf_matrix: forall (mx: matrix F) m n,
  wf_matrix mx m n ->
  whole_Zlength mx = m * n.
Proof.
  intros mx m n Hwf. destruct Hwf as [Hlen [Hn Hin]]. generalize dependent m.
  induction mx; intros m Hlen.
  - list_solve.
  - simpl. rewrite Zlength_cons in Hlen. assert ((Zlength mx) = m -1) by lia.
    assert (whole_Zlength mx = (m-1) * n). apply IHmx. intros. apply Hin. right; assumption.
    assumption. rewrite H0. rewrite Hin. lia. left; reflexivity.
Qed.

Lemma whole_Zlength_sublist: forall (mx: matrix F) m n lo hi,
  wf_matrix mx m n ->
  0 <= lo <= hi ->
  hi <= Zlength mx -> 
  whole_Zlength (sublist lo hi mx) = (hi - lo) * n.
Proof.
  intros mx m n lo hi Hwf Hlo Hi. apply whole_Zlength_wf_matrix.
  destruct Hwf as [Hlen [Hn Hin]].
  unfold wf_matrix. split. list_solve. split. assumption.
  intros. apply Hin. eapply sublist_In. apply H.
Qed.

Lemma flatten_mx_aux_app: forall mx mx' base,
  flatten_mx_aux (mx ++ mx') base = flatten_mx_aux mx (flatten_mx_aux mx' base).
Proof.
  intros. unfold flatten_mx_aux. rewrite fold_right_app. reflexivity.
Qed.

(*The real result that we want: allows us to convert from the indexing used in the C code to
  our matrix functions*)
Lemma flatten_mx_Znth: forall {m n} (mx: matrix F) i j,
  wf_matrix mx m n ->
  0 <= i < m ->
  0 <= j < n ->
  Znth (i * n + n - 1 - j) (flatten_mx mx) = poly_to_int (proj1_sig (get mx i j)).
Proof.
  intros m n mx i j Hwf Him Hjn. unfold get. unfold flatten_mx.
  assert (Hwf' := Hwf).
  destruct Hwf as [Hlen [Hn Hin]]. 
  assert (Hsplit : mx = sublist 0 i mx ++ sublist i (Zlength mx) mx). rewrite <- sublist_split; try lia.
  rewrite sublist_same; reflexivity. rewrite Hsplit at 1.
  rewrite flatten_mx_aux_app.
  rewrite flatten_mx_aux_Znth. rewrite (whole_Zlength_sublist _ m n); try lia; try auto.
  replace (i * n + n - 1 - j - (i - 0) * n)  with (n - 1 - j) by lia.
  rewrite (sublist_split _ (i+1) _); try lia. rewrite sublist_len_1; try lia. simpl.
  assert (Hlen1: (Zlength (map (fun q : {p : poly | deg p < deg mod_poly} => poly_to_int (proj1_sig q)) (Znth i mx)) = n)).
  rewrite Zlength_map. apply Hin. apply Znth_In; lia.
  assert (Hlen2 : Zlength (rev (map (fun q : {p : poly | deg p < deg mod_poly} => poly_to_int (proj1_sig q)) (Znth i mx))) = n).
  rewrite initial_world.Zlength_rev. lia.
  rewrite app_Znth1. 2: list_solve. 
  rewrite Znth_rev. 2: list_solve. list_simplify. rewrite Hin. rewrite Znth_map. f_equal. f_equal.
  replace ((n - (n - 1 - j) - 1)) with j by lia. reflexivity. rewrite Hin. lia. all: try(apply Znth_In; lia).
  rewrite (whole_Zlength_sublist _ m n); try lia. assumption.
Qed.

(*TODO: go back and update field proofs with real code (or see if we need qpoly)*)
(*TODO: make sure this makes sense/is workable*)

(*Note: removed dependent types from matrix definition since it causes issues in VST and lia*)
Definition fec_matrix_transform_spec :=
  DECLARE _fec_matrix_transform
  WITH gv: globals, m : Z, n : Z, mx : matrix F, s : val
  PRE [ tptr tuchar, tuchar, tuchar]
    PROP ((0 <= m <= n) /\ n <= Byte.max_unsigned /\ (wf_matrix mx m n) /\ (strong_inv_list m n mx 0))
    PARAMS ( s; Vint (Int.repr m); Vint (Int.repr n))
    GLOBALS (gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
         data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
         data_at Ews (tarray tuchar (m * n))(map Vint (map Int.repr( (flatten_mx mx)))) s)
  POST [tint]
    PROP()
    RETURN (Vint (Int.repr 0))
    SEP(data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
         data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
         data_at Ews (tarray tuchar (m * n)) 
          (map Vint (map Int.repr (flatten_mx (gauss_restrict_rows mx m)))) s).

Definition fec_gf_mult_spec :=
  DECLARE _fec_gf_mult
  WITH gv: globals, f : Z, g : Z
  PRE [ tuchar, tuchar ]
    PROP (0 <= f < fec_n /\ 0 <= g < fec_n)
    PARAMS (Vint (Int.repr f); Vint (Int.repr g))
    GLOBALS (gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
      data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power))
  POST [ tuchar ]
    PROP ()
    RETURN (Vint (Int.repr (poly_to_int (((poly_of_int f) *~ (poly_of_int g)) %~ mod_poly ))))
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
      data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power)).

(*TODO: make sure it is OK to assume initialized to 0, should be good for global variables*)
Definition fec_generate_math_tables_spec :=
  DECLARE _fec_generate_math_tables
  WITH gv : globals
  PRE [ ]
    PROP ()
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z))) 
          (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z))) 
          (gv _fec_2_power);
         data_at Ews (tarray tuchar fec_n)  
            (map Vint (map Int.repr (list_repeat (Z.to_nat fec_n) 0%Z))) (gv _fec_invefec))
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
         data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec)).

(*TODO: how to do without the WITH?*)
Definition fec_find_mod_spec :=
  DECLARE _fec_find_mod 
  WITH x : unit
  PRE [ ]
    PROP ()
    PARAMS ()
    SEP ()
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr modulus))
    SEP ().

Definition Gprog := [fec_find_mod_spec; fec_generate_math_tables_spec; fec_matrix_transform_spec; fec_gf_mult_spec].

(** Verification of [fec_find_mod]*)
(*
Lemma body_fec_find_mod : semax_body Vprog Gprog f_fec_find_mod fec_find_mod_spec.
Proof.
start_function.
(*TODO: why doesn't this work, and how to prove a switch statement in which only 1 branch can be taken?*)
forward_if (PROP () LOCAL (temp _modulus (Vint (Int.repr 285))) SEP ()).
*)

(** Verification of [fec_generate_math_tables]*)

(*TODO: Qed takes a long time, and I don't know why. It might be unfolding constants or something*)
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
           rewrite unsigned_repr. all: rep_lia.
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
             split; try rep_lia. rewrite poly_mult_deg in H4. 2: solve_neq.
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
                  rewrite deg_x. rewrite deg_x in Hupper. lia. all: solve_neq. }
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


 specialize (H17 H18).
        destruct H17. specialize (H16 H19). lia. } rewrite H14. cancel.
      



            **


 rewrite H17; cancel.
                +++
                     lia.

 apply n. 
           simpl.

 split; try lia. assert (forall x y z, x < z -> y >= 0 -> x - y < z).
            intros. lia. apply H13.


  pose proof (modulus_poly_bound
              ((monomial (Z.to_nat (255 - find_power mod_poly (poly_of_int i))) %~ mod_poly))).
              assert (deg (monomial (Z.to_nat (fec_n - 1 - find_power mod_poly (poly_of_int i))) %~ mod_poly) <
              deg mod_poly). apply pmod_lt_deg. assumption. specialize (H3 H4). lia. }
          forward.


 entailer!.
    forward_loop (EX (i : Z) (l: list Z),
    PROP (0 <= i <= fec_n  /\ Znth 0 l = 0%Z /\ (forall z, 0 < z < fec_n -> 0 <= poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int z)) < i ->
          Znth z l = poly_to_int (poly_inv mod_poly modulus_poly_deg_pos (poly_of_int z))
      ))
    LOCAL (temp _mod (Vint (Int.repr modulus)); temp _i (Vint (Int.repr i)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_invefec ))).
    (*need the Znth 0 l because of annoying corner case - technically, when i=0 and i=1, we fill in the
      same spot in the inverse array, overwriting the previous one correctly*)


Lemma sem_sub_pi_offset: forall ty s off n,
  isptr s ->
  complete_type cenv_cs ty = true ->
  Int.min_signed <= n <= Int.max_signed ->
  force_val (sem_sub_pi ty Signed (offset_val off s) (Vint (Int.repr n))) =
  offset_val (off - (sizeof ty) * n) s.
Proof.
  intros ty s off n Hptr Hty Hn.
  replace (off - (sizeof ty) * n) with (off + (- (sizeof ty) * n)) by lia. rewrite <- offset_offset_val.
  assert (Hptr' : isptr (offset_val off s)). rewrite isptr_offset_val; auto.
  destruct (offset_val off s) eqn : Hoff; inversion Hptr'. simpl.
  unfold sem_sub_pi. rewrite Hty. simpl. f_equal. unfold sizeof.
  assert ((Ptrofs.of_ints (Int.repr n)) = Ptrofs.repr n). unfold Ptrofs.of_ints.
  f_equal. apply Int.signed_repr; auto. rewrite H. rewrite ptrofs_mul_repr.
  rewrite Ptrofs.sub_add_opp. f_equal. replace (- Ctypes.sizeof ty * n) with (-(Ctypes.sizeof ty * n)) by lia.
  rewrite <- (Ptrofs.neg_repr). reflexivity.
Qed.

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

Lemma arr_field_compatible : forall t size p i, 
  field_compatible (tarray t size) [] p ->
  0 <= i < size ->
  field_compatible (tarray t size) (SUB i) p.
Proof.
  intros t size p i Hcomp Hsz.
  unfold field_compatible in *. unfold field_compatible0. destruct Hcomp as [Hptr [Hleg [Hsz_comp [Hal Hnest]]]].
  repeat(split; auto).
Qed.

Lemma arr_field_address: forall t size p i, 
  field_compatible (tarray t size) [] p ->
  0 <= i < size ->
  field_address (tarray t size) (SUB i) p = offset_val (sizeof t * i) p.
Proof.
  intros t size p i Hcomp Hi.
  unfold field_address. destruct (field_compatible_dec (tarray t size) [ArraySubsc i] p).
  simpl. auto. exfalso. apply n. apply arr_field_compatible; auto.
Qed.

(*Matrix accesses are within bounds - this is a bit annoying due to the multiplication, can't just use lia*)
Lemma matrix_bounds_within: forall m n i j,
  0 <= i < m ->
  0 <= j < n ->
  0 <= (i * n) + n - 1 - j < m * n.
Proof.
  intros m n i j Him Hjn. split.
  - assert (1 + j <= i * n + n). { replace (i * n + n) with ((i+1) * n) by lia.
    assert (1 + j <= n) by lia. eapply Z.le_trans. apply H. replace n with (1 * n) at 1 by lia.
    apply Z.mul_le_mono_nonneg_r; lia. } lia.
  - assert (i * n + n - 1 < m * n). { 
    assert (i * n + n <= m * n). { replace (i * n + n) with ((i+1)*n) by lia.
    apply Z.mul_le_mono_nonneg_r; lia. } lia. } lia.
Qed.

Lemma qpoly_int_bound: forall (q: qpoly mod_poly),
  0 <= poly_to_int (proj1_sig q) <= Byte.max_unsigned.
Proof.
  intros q. destruct q. simpl.
  apply modulus_poly_bound in l.
  pose proof fec_n_bound. rep_lia.
Qed. 

(*TODO: move*)
Lemma poly_to_qpoly_unfold: forall (f: poly) (Hnonneg: deg f > 0) (a: qpoly f),
  poly_to_qpoly f Hnonneg (proj1_sig a) = a.
Proof.
  intros. unfold poly_to_qpoly.
  destruct a. simpl. exist_eq. apply pmod_refl; auto.
Qed.

Lemma Z_expand_bounds: forall a b c d n,
  a <= b ->
  c <= d ->
  b <= n <= c ->
  a <= n <= d.
Proof.
  intros. lia.
Qed.

(*copied from previous - TODO: see what we need*)
Lemma isptr_denote_tc_test_order: forall p1 p2,
  isptr p1 ->
  isptr p2 ->
  denote_tc_test_order p1 p2 = test_order_ptrs p1 p2.
Proof.
  intros p1 p2 Hptr1 Hptr2. destruct p1; destruct Hptr1. destruct p2; destruct Hptr2. reflexivity.
Qed.

Lemma isptr_offset_val_sameblock : forall p i,
  isptr p ->
  sameblock p (offset_val i p) = true.
Proof.
  intros. destruct p; destruct H.
  simpl. unfold proj_sumbool. apply peq_true.
Qed.

Lemma sameblock_refl : forall p,
  isptr p ->
  sameblock p p = true.
Proof.
  intros.
  destruct p; destruct H. apply peq_true.
Qed.

Lemma sameblock_symm : forall p1 p2,
  sameblock p1 p2 = true ->
  sameblock p2 p1 = true.
Proof.
  intros.
  destruct p1; destruct p2; try discriminate.
  simpl in *. destruct (peq b b0); try discriminate.
  subst.
  apply peq_true.
Qed.

Lemma sameblock_trans : forall p1 p2 p3,
  sameblock p1 p2 = true ->
  sameblock p2 p3 = true->
  sameblock p1 p3 = true.
Proof.
  intros.
  destruct p1; try discriminate.
  destruct p2; try discriminate.
  destruct p3; try discriminate.
  simpl in *.
  destruct (peq b b0); try discriminate.
  destruct (peq b0 b1); try discriminate.
  subst.
  apply peq_true.
Qed.

(*Verification of [fec_matrix_transform]*)
Lemma body_fec_matrix_transform : semax_body Vprog Gprog f_fec_matrix_transform fec_matrix_transform_spec.
Proof.
  start_function. destruct H as [Hmn [Hnbound [Hwf Hstr]]].
  forward_loop (EX (row : Z),
    PROP (0 <= row <= m)
    LOCAL (temp _k (Vint (Int.repr (row))); temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n));
      gvars gv)
    SEP(data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
   data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
   data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
   data_at Ews (tarray tuchar (m * n))
     (map Vint (map Int.repr (flatten_mx 
        (gauss_all_steps_rows_partial mx m row )))) s))
    break: (PROP ()
           LOCAL (temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n));
      gvars gv)
            SEP(data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
   data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
   data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
   data_at Ews (tarray tuchar (m * n))
     (map Vint (map Int.repr (flatten_mx 
        (gauss_all_steps_rows_partial mx m m )))) s)). 
{ forward. Exists 0%Z. entailer!. }
{ Intros gauss_step_row. forward_if.
  { (*body of outer loop *) 
    (*now there are 2 inner loops; the first is [all_cols_one_partial]*)
    forward_loop 
    (EX (row : Z),
      PROP (0 <= row <= m)
      LOCAL (temp _i (Vint (Int.repr (row))); temp _k (Vint (Int.repr gauss_step_row)); temp _p s; 
      temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); gvars gv)
      SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
        data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
        data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr 
          (flatten_mx (all_cols_one_partial 
            (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row row )))) s))
      break: (PROP ()
        LOCAL (temp _k (Vint (Int.repr gauss_step_row)); temp _p s; 
      temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); gvars gv)
      SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
        data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
        data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr 
          (flatten_mx (all_cols_one_partial 
            (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row m )))) s)).
    { forward. Exists 0%Z. entailer!. }
    { Intros cols_one_row. forward_if.
      { forward. (*Want to simplify pointer in q*)
        assert_PROP ((force_val (sem_binary_operation' Osub (tptr tuchar) tint
          (eval_binop Oadd (tptr tuchar) tuchar (eval_binop Oadd (tptr tuchar) tint s
           (eval_binop Omul tuchar tuchar (Vint (Int.repr cols_one_row))
           (Vint (Int.repr n)))) (Vint (Int.repr n))) (Vint (Int.repr 1)))) =
           (offset_val (((cols_one_row * n) + n) - 1) s)). { entailer!.
        rewrite sem_sub_pi_offset; auto. rep_lia. }
        rewrite H3. clear H3.
        forward.
        { entailer!. rewrite sem_sub_pi_offset; auto; try rep_lia. }
        { (*Now, we will simplify pointer in m*)
          assert_PROP ((force_val
               (sem_binary_operation' Oadd (tptr tuchar) tint
                  (eval_binop Osub (tptr tuchar) tuchar (offset_val (cols_one_row * n + n - 1) s)
                     (Vint (Int.repr n))) (Vint (Int.repr 1)))) =
            offset_val (cols_one_row * n) s). { entailer!.
          rewrite sem_sub_pi_offset; auto; try rep_lia. f_equal. simpl. rewrite sem_add_pi_ptr_special; auto;
          try rep_lia. simpl. rewrite offset_offset_val. f_equal. lia. }
          rewrite H3; clear H3.
          assert_PROP ((offset_val (cols_one_row * n) s) = field_address (tarray tuchar (m * n)) 
            (SUB ((cols_one_row * n) + n - 1 - (n-1))) s). { entailer!. rewrite arr_field_address; auto.
            simpl. f_equal. lia. apply (matrix_bounds_within); lia. } rewrite H3; rename H3 into Hm_offset. 
          forward.
          assert (Hwf' : wf_matrix (F:=F) (all_cols_one_partial (F:=F) 
            (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row cols_one_row) m n). {
          apply all_cols_one_partial_wf. lia. apply gauss_all_steps_rows_partial_wf. lia. assumption. }
        (*Now we are at the while loop - because of the [strong_inv] condition of the matrix,
          the loop guard is false (the loop finds the element to swap if one exists, but returns
          with an error whether or not one exists*)
        (*Because of this, we give a trivial loop invariant*)
        remember ((PROP ( )
           LOCAL (temp _w (Vint (Int.zero_ext 8 (Int.repr cols_one_row)));
           temp _m (field_address (tarray tuchar (m * n)) [ArraySubsc (cols_one_row * n + n - 1 - (n - 1))] s);
           temp _q (offset_val (cols_one_row * n + n - 1) s);
           temp _i (Vint (Int.repr cols_one_row)); temp _k (Vint (Int.repr gauss_step_row)); 
           temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); 
           gvars gv)
           SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
           data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
           data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
           data_at Ews (tarray tuchar (m * n))
             (map Vint
                (map Int.repr
                   (flatten_mx
                      (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row)
                         gauss_step_row cols_one_row)))) s))) as x.
         forward_loop x break: x; subst. (*so I don't have to write it twice*)
        { entailer!. }
        { assert_PROP (force_val (sem_sub_pi tuchar Signed 
            (offset_val (cols_one_row * n + n - 1) s) (Vint (Int.repr gauss_step_row))) =
            offset_val (cols_one_row * n + n - 1 - gauss_step_row) s). { entailer!.
           rewrite sem_sub_pi_offset;auto. simpl. f_equal. lia. rep_lia. }
           (*TODO: will need more general stuff probably*)
           assert (0 <= cols_one_row * n + n - 1 - gauss_step_row < m * n). {
            apply matrix_bounds_within; lia. }
           assert_PROP (force_val (sem_sub_pi tuchar Signed 
            (offset_val (cols_one_row * n + n - 1) s) (Vint (Int.repr gauss_step_row))) =
            field_address (tarray tuchar (m * n)) (SUB  (cols_one_row * n + n - 1 - gauss_step_row)) s). {
            entailer!. rewrite H3. rewrite arr_field_address; auto. simpl. f_equal. lia. }
            clear H3.
           assert_PROP ((0 <= cols_one_row * n + n - 1 - gauss_step_row <
              Zlength (map Int.repr (flatten_mx
              (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row)
              gauss_step_row cols_one_row))))). {
           entailer!. list_solve. } simpl_reptype. rewrite Zlength_map in H3.
           forward.
          { entailer!. rewrite (@flatten_mx_Znth m n); try lia. 
            pose proof (qpoly_int_bound (get (F:=F) (all_cols_one_partial (F:=F) 
                (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row cols_one_row) 
                cols_one_row gauss_step_row)). rewrite Int.unsigned_repr; rep_lia. assumption. }
          { entailer!. rewrite sem_sub_pi_offset; auto. rep_lia. }
          { forward_if.
            { (*contradiction due to [strong_inv]*)
              assert (Znth (cols_one_row * n + n - 1 - gauss_step_row)
                (flatten_mx (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row)
                gauss_step_row cols_one_row)) <> 0%Z). {
              rewrite (@flatten_mx_Znth m n); try lia. 2: assumption. intro Hzero.
              rewrite poly_to_int_zero_iff in Hzero. 
              assert (Hrm : 0 <= gauss_step_row < m) by lia.
              assert (Hcm : 0 <= cols_one_row < m) by lia.
              apply (gauss_all_steps_columns_partial_zeroes_list Hrm H1 (proj2 Hmn) Hwf Hstr Hcm). 
              replace (ssralg.GRing.zero (ssralg.GRing.Field.zmodType F)) with (q0 modulus_poly_deg_pos) by reflexivity.
              destruct ((get (F:=F)
              (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row)
                gauss_step_row cols_one_row) cols_one_row gauss_step_row)) eqn : G. unfold q0. unfold r0. exist_eq.
              simpl in Hzero. assumption. } 
              apply mapsto_memory_block.repr_inj_unsigned in H6. contradiction. 2: rep_lia.
              rewrite (@flatten_mx_Znth m n); try lia. eapply Z_expand_bounds.
              3 : { apply qpoly_int_bound. } lia. rep_lia. assumption. }
            { forward. entailer!. }
          }
        }
      { (*after the while loop*)
         assert_PROP (force_val (sem_sub_pi tuchar Signed 
            (offset_val (cols_one_row * n + n - 1) s) (Vint (Int.repr gauss_step_row))) =
            field_address (tarray tuchar (m * n)) (SUB  (cols_one_row * n + n - 1 - gauss_step_row)) s). {
            entailer!. rewrite sem_sub_pi_offset;auto. simpl. rewrite arr_field_address; auto. simpl. f_equal. lia.
            apply matrix_bounds_within; lia. rep_lia. } 
         assert (0 <= cols_one_row * n + n - 1 - gauss_step_row < m * n). {
            apply matrix_bounds_within; lia. }
         assert_PROP ((0 <= cols_one_row * n + n - 1 - gauss_step_row <
          Zlength (map Int.repr (flatten_mx
         (all_cols_one_partial (F:=F) (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row)
            gauss_step_row cols_one_row))))). entailer!. list_solve. rewrite Zlength_map in H5.
         (*Doing some stuff to simplify here so we don't need to repeat this in each branch*)
         pose proof (Hpolybound:= (qpoly_int_bound (get (F:=F) (all_cols_one_partial (F:=F) 
                (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row cols_one_row) 
                cols_one_row gauss_step_row))).
          forward; try rewrite (@flatten_mx_Znth m n); try lia; try assumption.
        { entailer!. lia. }
        { entailer!. rewrite sem_sub_pi_offset; auto. rep_lia. }
        { forward.
          { entailer!. apply modulus_poly_bound. apply (@ssrfun.svalP _ (fun x => deg x < deg mod_poly)). }
          { entailer!. rewrite inverse_contents_Znth. rewrite poly_of_int_inv.
            simpl. rewrite unsigned_repr. unfold poly_inv. apply (proj2 (qpoly_int_bound _)).
            unfold poly_inv. split. apply (proj1 (qpoly_int_bound _)). eapply Z.le_lt_trans.
            apply (proj2 (qpoly_int_bound _)). rep_lia. apply modulus_poly_bound.
            apply (@ssrfun.svalP _ (fun x => deg x < deg mod_poly)). }
          { forward. (*simplify before for loop*)
            rewrite inverse_contents_Znth. 2 : { apply modulus_poly_bound.
            apply (@ssrfun.svalP _ (fun x => deg x < deg mod_poly)). } rewrite poly_of_int_inv. simpl.
            remember (get (F:=F) (all_cols_one_partial (F:=F)
                      (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row
                       cols_one_row) cols_one_row gauss_step_row) as qij eqn : Hqij. 
            remember (proj1_sig qij) as pij eqn : Hpij.
            (*assert_PROP ((offset_val (cols_one_row * n + n - 1) s) = 
              field_address (tarray tuchar (m * n)) (SUB (cols_one_row * n + n - 1)) s). {
            entailer!. rewrite arr_field_address. simpl. f_equal. lia. auto. 
            pose proof (matrix_bounds_within m n cols_one_row 0). lia. } rewrite H6. clear H6.*)
            remember (find_inv mod_poly modulus_poly_deg_pos qij) as qij_inv eqn : Hqinv.
            replace (poly_inv mod_poly modulus_poly_deg_pos pij) with (proj1_sig qij_inv). 2 : {
            unfold poly_inv. rewrite Hpij. rewrite poly_to_qpoly_unfold. rewrite Hqinv. reflexivity. }
            (*Scalar multiplication loop*)
            (*Unfortunately, lots of duplication here: can we save locals in a variable?*)
            forward_loop (EX (j : Z),
            PROP (0 <= j <= n)
            LOCAL (temp _inv (Vint (Int.zero_ext 8 (Int.repr (poly_to_int (proj1_sig qij_inv)))));
              temp _t'11 (Vint (Int.repr (poly_to_int (proj1_sig qij_inv))));
              temp _t'10 (Vint (Int.repr (poly_to_int pij)));
              temp _w (Vint (Int.zero_ext 8 (Int.repr cols_one_row)));
              temp _m (field_address (tarray tuchar (m * n)) [ArraySubsc (cols_one_row * n + n - 1 - (n - 1))] s);
              (*temp _q (field_address (tarray tuchar (m * n)) [ArraySubsc (cols_one_row * n + n - 1)] s);*)
              temp _q (offset_val (cols_one_row * n + n - 1) s);
              temp _i (Vint (Int.repr cols_one_row)); temp _k (Vint (Int.repr gauss_step_row)); 
              temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); 
              gvars gv;
              (*temp _n (field_address0 (tarray tuchar (m * n)) (SUB (cols_one_row * n + n - 1 - j)) s))*)
              temp _n (offset_val (cols_one_row * n + n - 1 - j) s))
            SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
                 data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
                 data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
                 data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr
                  (flatten_mx (scalar_mul_row_partial (all_cols_one_partial (F:=F) 
                    (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row cols_one_row) 
                    cols_one_row qij_inv j)))) s))
            break: (PROP ()
              LOCAL (temp _inv (Vint (Int.zero_ext 8 (Int.repr (poly_to_int (proj1_sig qij_inv)))));
              temp _t'11 (Vint (Int.repr (poly_to_int (proj1_sig qij_inv))));
              temp _t'10 (Vint (Int.repr (poly_to_int pij)));
              temp _w (Vint (Int.zero_ext 8 (Int.repr cols_one_row)));
              temp _m (field_address (tarray tuchar (m * n)) [ArraySubsc (cols_one_row * n + n - 1 - (n - 1))] s); 
              temp _q (field_address (tarray tuchar (m * n)) [ArraySubsc (cols_one_row * n + n - 1)] s);
              temp _i (Vint (Int.repr cols_one_row)); temp _k (Vint (Int.repr gauss_step_row)); 
              temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n)); 
              gvars gv)
              SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
                 data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
                 data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
                 data_at Ews (tarray tuchar (m * n)) (map Vint (map Int.repr
                  (flatten_mx (scalar_mul_row (all_cols_one_partial (F:=F) 
                    (gauss_all_steps_rows_partial (F:=F) mx m gauss_step_row) gauss_step_row cols_one_row) 
                    cols_one_row qij_inv)))) s)).
            { forward. Exists 0%Z. entailer!. rewrite scalar_mul_row_partial_0. cancel. }
            { Intros j. (*TODO: this still doesn't quite work because when the loop exits, n is too small and so the
                          if conditions doesn't typecheck*)


 assert (Hcj: 0 <= cols_one_row * n + n - 1 - j <= m * n).


 forward_if.
              { rewrite <- Hm_offset. rewrite isptr_denote_tc_test_order; auto. unfold test_order_ptrs.
                assert (Hsame: sameblock (offset_val (cols_one_row * n + n - 1 - j) s) 
                  (offset_val (cols_one_row * n) s) = true). eapply sameblock_trans.
                apply sameblock_symm. all: try apply isptr_offset_val_sameblock; auto. rewrite Hsame; clear Hsame.
                apply andp_right.
                - eapply derives_trans. 2: {  sep_apply 
                    (memory_block_weak_valid_pointer Ews (m * n) s (cols_one_row * n + n - 1 - j)); auto; try rep_lia.
                  assert (0 <= cols_one_row * n + n - 1 - j < m * n). apply matrix_bounds_within. lia. lia.
                  pose proof (matrix_bounds_within m n cols_one_row j).
                   4: apply derives_refl. entailer!.
                sep_apply (data_at_memory_block Ews (tarray tuchar fec_n) _ s).
    apply andp_right.
                Search weak_valid_pointer.
                Search weak_valid_pointer.



              { assert (0 <= cols_one_row * n + n - 1 < m * n).
                assert (0 <= cols_one_row * n + n - 1 - 0 < m * n). apply matrix_bounds_within; lia. lia.
                destruct (field_compatible_dec (tarray tuchar (m * n)) [ArraySubsc (cols_one_row * n + n - 1)] s).
                rewrite <- field_address_offset; auto.
                rewrite arr_field_address0; auto; try lia. rewrite arr_field_address; auto; try lia.
                exfalso. apply n0. apply arr_field_compatible; try lia; auto. }
              { rewrite scalar_mul_row_partial_0. cancel. }
            }
            { Intros j. forward_if.
              { Search isptr. Print field_compatible0. Check isptr_denote_tc_test_order. assert (Hibound: 0 <= cols_one_row * n + n - 1 - i <= m * n). 
                



 entailer!. rewrite !arr_field_address0; auto. simpl. 
              { entailer!. Print scalar_mul_row_partial.
 reflexivity. all: auto.
                apply matrix_bounds_within; lia.
                 (*Loop to scalar multiply a row*)
                 forward_loop
                 forward.
                 
  assert (forall v, sem_cast tuchar tuchar (Vint v) = Some (Vint v)). { intros. simpl. unfold sem_cast_i2i. destruct t; try reflexivity. unfold sem_cast. simpl.

 

(*





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
*)

