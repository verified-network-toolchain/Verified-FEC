Require Import VST.floyd.proofauto.

Require Export Poly.
Require Export IntPoly.
Require Import ConcretePolys.
Require Export PropList.
Require Export PolyMod.
Require Export PrimitiveFacts.
Require Export PolyField.
Require Export ListMatrix.

Set Bullet Behavior "Strict Subproofs".

Import WPoly.

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
  intros. rewrite modulus_poly. intro C; inversion C. 
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
      Zlength a). rewrite Zlength_rev. list_solve. rewrite app_Znth2.
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
  rewrite Zlength_rev. lia.
  rewrite app_Znth1. 2: list_solve. 
  rewrite Znth_rev. 2: list_solve. list_simplify. rewrite Hin. rewrite Znth_map. f_equal. f_equal.
  replace ((n - (n - 1 - j) - 1)) with j by lia. reflexivity. rewrite Hin. lia. all: try(apply Znth_In; lia).
  rewrite (whole_Zlength_sublist _ m n); try lia. assumption.
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