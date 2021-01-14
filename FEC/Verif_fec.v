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

Definition F := qpoly_fieldType modulus_poly_deg_pos modulus_poly_irred.
(*Not sure if we need this but good that it's provable*)
Lemma field_sort : (ssralg.GRing.Field.sort F) = qpoly (mod_poly).
Proof.
  reflexivity.
Qed.

Instance F_inhab : Inhabitant (ssralg.GRing.Field.sort F) := inhabitant_F F.

Definition flatten_mx (mx: matrix F) : list Z :=
  fold_right (fun l acc => rev (map (fun q => poly_to_int (proj1_sig q)) l) ++ acc) nil  mx.

(*TODO: resume once i see proof obligations - also see about fold_right or fold_left
Lemma flatten_Znth_aux: forall {m n} (mx: matrix F m n) i j,
  i < m ->
  0 <= j < n ->
  Znth (i * n + j) (flatten_mx mx) = poly_to_int (proj1_sig (Znth j (Znth i (proj1_sig mx)))).
Proof.
  intros m n mx i j Him Hjn. unfold flatten_mx.
  assert Hsplit : (proj1_sig mx) = sublist 0 i (proj1_sig mx) + 

sublist_same
  Search sublist.


Definition flatten_Znth: forall {m n} (mx: matrix F m n) i j,
  Znth (i * n + n - j - 1) (flatten_mx mx) = poly_to_int (proj1_sig (get mx i j)).
Proof.
  intros m n mx i j. unfold flatten_mx.
*)

(*TODO: go back and update field proofs with real code (or see if we need qpoly)*)
(*TODO: make sure this makes sense/is workable*)
(*Note: we use nats rather than Z because we need m and n to be nonnegative - if not, we cannot
  construct a default matrix (for matrix_of_list), and need to use Z.abs, which causes all sorts
  of complications due to the dependent types (eg: lia doesnt work)*)

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

Definition Gprog := [fec_matrix_transform_spec].

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
- forward. Exists 0%Z. entailer!.
- Intros gauss_step_row. forward_if.
  + (*body of outer loop *) 
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
    * forward. Exists 0%Z. entailer!.
    * Intros cols_one_row. forward_if.
      -- forward. simpl. forward. entailer!. simpl. (*TODO: start with isptr stuff and see how best to deal
          with arrays/ pointers*)

Print data_at.
         Print sem_sub_pi.

 rewrite mul_repr. rewrite sem_add_pi_ptr_special. 2 : { reflexivity. }
          2 : { apply isptr_force_sem_add_ptr_int. reflexivity.   reflexivity. auto.
          Search isptr force_val.
           by []. Search sem_add_ptr_int. Print complete_type. rewrite complete_type.



 simpl. Search sem_add_ptr_int.


Print sem_binary_operation'. forward. entailer!. Search s. Search is_pointer_or_null.

.


  + forward. entailer!. assert (row = m) by rep_lia. subst. cancel.
- (*after the first loop*)
  +
    rewrite Int.signed_repr in H1; try rep_lia. simpl in H2. assert (row = m). rep_lia.

 Search Int.repr. rewrite Int.unsigned_repr in H2; try lia. Search (Int.unsigned (Int.repr ?x)).

 entailer!.


 forward.


 destruct H. destruct H15.
  



  (*It turns out that using the hacky [matrix_of_list] gives problems with lia (error: hypothesis H
    depends on the body of z15). So instead we use the preconditions to construct and work with the
    matrix directly*)
  destruct H as [Hmn [Hwf Hstr']].
  remember (exist (fun x => wf_matrix x m n) _ Hwf) as mx' eqn : Hmx'. fold (matrix F m n) in mx'.
  assert (Hm: m = Z.abs m). { symmetry. rewrite Z.abs_eq_iff. apply Hmn. }
  assert (Hn: n = Z.abs n). { symmetry. rewrite Z.abs_eq_iff. destruct Hmn as [H0m Hmn]. (*Can't use lia in here which is annoying*)
    apply (Z.le_trans _ _ _ H0m Hmn). }
  assert (Hmxequiv : proj1_sig (matrix_of_list (F:=F) mx m n) = proj1_sig mx'). {
    unfold matrix_of_list. destruct (bool_dec (wf_matrix_bool (F:=F) mx (Z.abs m) (Z.abs n)) true).
    rewrite Hmx'. reflexivity.
    assert (Hwf_abs : wf_matrix (F := F) mx (Z.abs m) (Z.abs n)). apply wf_matrix_abs. assumption.
    rewrite <- wf_bool_wf in Hwf_abs. contradiction. }
  assert (Hstr : strong_inv_list (F:=F) mx' 0). unfold strong_inv_list in *.
  (*Need lots of destructing, or else I get errors about abstracting over terms*)
  destruct (range_le_lt_dec 0 0 (Z.abs m)). 2: destruct Hstr'.
  destruct (range_le_lt_dec 0 0 m). 2 : { rewrite Hm in n0. contradiction. }
  destruct (Z_le_lt_dec (Z.abs m) (Z.abs n)). 2: destruct Hstr'.
  destruct (Z_le_lt_dec m n). 2 : { rewrite Hm in l0. rewrite Hn in l0. apply Zlt_not_le in l0. contradiction. }
  
  clear a.
  2: { destruct Hstr'.  auto.

 rewrite <- Hm in Hstr'. clear Hstr.
  assert (Htest2 : (flatten_mx (matrix_of_list (F:=F) mx m n)) = (flatten_mx mx')) by admit. rewrite Htest2.
  unfold POSTCONDITION. unfold abbreviate.
  assert (Htest3 : (flatten_mx (gauss_restrict_rows (F:=F)(matrix_of_list (F:=F) mx m n)) =
  flatten_mx (gauss_restrict_rows (F:=F) mx'))) by admit. rewrite Htest3. clear Htest2. clear Htest3. 

  (*Outer loop corresponds to one [gaussian_step]. We need this duplication because we need the postcondition
    TODO: may need to add things about [gaussian_invar] and [strong_invar]*)
  forward_loop (EX (row : Z),
    PROP (0 <= row <= m)
    LOCAL (temp _k (Vint (Int.repr (row))); temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n));
      gvars gv)
    SEP(data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
   data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
   data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
   data_at Ews (tarray tuchar (m * n))
     (map Vint (map Int.repr (flatten_mx 
        (gauss_all_steps_rows_partial mx' row )))) s))
    break: (PROP ()
           LOCAL (temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n));
      gvars gv)
            SEP(data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
   data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
   data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
   data_at Ews (tarray tuchar (m * n))
     (map Vint (map Int.repr (flatten_mx 
        (gauss_all_steps_rows_partial mx' m )))) s)).
- forward. Exists 0%Z. entailer!. destruct H. destruct H15.
(* 
 
  assert (mx' = (matrix_of_list (F:=F) mx m n)).

*)
  (*Outer loop corresponds to one [gaussian_step]. We need this duplication because we need the postcondition
    TODO: may need to add things about [gaussian_invar] and [strong_invar]*)
  forward_loop (EX (row : Z),
    PROP (0 <= row <= m)
    LOCAL (temp _k (Vint (Int.repr (row))); temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n));
      gvars gv)
    SEP(data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
   data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
   data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
   data_at Ews (tarray tuchar (m * n))
     (map Vint (map Int.repr (flatten_mx 
        (gauss_all_steps_rows_partial (matrix_of_list (F:=F) mx m n) row )))) s))
    break: (PROP ()
           LOCAL (temp _p s; temp _i_max (Vint (Int.repr m)); temp _j_max (Vint (Int.repr n));
      gvars gv)
            SEP(data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
   data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
   data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
   data_at Ews (tarray tuchar (m * n))
     (map Vint (map Int.repr (flatten_mx 
        (gauss_all_steps_rows_partial (matrix_of_list (F:=F) mx m n) m )))) s)).
- forward. Exists 0%Z. entailer!. destruct H. destruct H15.


 clear H16. lia. split. rep_lia. lia. apply H. lia. Check ( (matrix_of_list (F:=F) mx m n)). destruct H. assert ( 0 <= m <= n). lia. Check z16. lia. Print All. lia.


 forward.

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

