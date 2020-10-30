Require Import VST.floyd.proofauto.
Require Import FieldDemo.
Require Import Helper.
Require Import GF2.
Require Import PolyDefs.
Require Import Poly.
Require Import ConcretePolys.
Require Import PolyMod.
Require Import PrimitiveFacts.


Instance CompSpecs : compspecs.
make_compspecs prog. Defined.

Definition Vprog : varspecs.
mk_varspecs prog. Defined.


(*This gives us a way to specify arrays by saying that "forall i, a[i] = f(i)"*)
Definition prop_list {A: Type} (f: Z -> A) (bound: Z) :=
  map f (map (Z.of_nat) (seq 0 (Z.to_nat bound))).

Lemma prop_list_length: forall {A} (f: Z -> A) bound,
  0 <= bound ->
  Zlength (prop_list f bound) = bound.
Proof.
  intros. unfold prop_list. rewrite? Zlength_map. 
  rewrite Zlength_seq. lia.
Qed.

Lemma prop_list_Znth: forall {A} `{Inhabitant A} (f: Z -> A) bound i,
  0 <= i < bound ->
  Znth i (prop_list f bound) = f i.
Proof.
  intros. unfold prop_list. rewrite Znth_map.
  rewrite Znth_map. rewrite Znth_seq. simpl. f_equal. lia. lia.
  rewrite Zlength_seq. lia. rewrite Zlength_map. rewrite Zlength_seq. lia.
Qed.

Lemma prop_list_0: forall {A: Type} (f: Z -> A),
  prop_list f 0 = nil.
Proof.
  intros. unfold prop_list. simpl. reflexivity.
Qed.

Lemma prop_list_plus_1: forall {A : Type} (f: Z -> A) (z: Z),
  0 <= z ->
  prop_list f (z+1) = prop_list f z ++ (f z) :: nil.
Proof.
  intros. unfold prop_list. replace (Z.to_nat (z+1)) with (Z.to_nat z + 1)%nat by lia.
  rewrite seq_app. simpl. rewrite map_app. simpl. rewrite map_app. simpl. 
  f_equal. f_equal. f_equal. lia.
Qed.

(*Znth_eq_ext*)

(*

Function bits_of_int (z: Z) {measure Z.to_nat} : list bit :=
  if (Z_lt_ge_dec z 0) then nil else
  if (Z.eq_dec z 0) then nil else 
  if (Z.eq_dec z 1) then (One :: nil) else
  if (Z.odd z) then (One :: bits_of_int (Z.div2 z)) else (Zero :: bits_of_int (Z.div2 z)).
Proof.
- intros. destruct (Zeven_odd_dec z).
  + apply Zeven_div2 in z0. lia.
  + apply Zodd_div2 in z0. lia.
- intros. destruct (Zeven_odd_dec z).
  + apply Zeven_div2 in z0. lia.
  + apply Zodd_div2 in z0. lia.
Qed.

(*Todo move - have this but for polys*)
Lemma wf_nil: P.wf_poly nil.
Proof.
  unfold P.wf_poly. intros. contradiction.
Qed.

Lemma bits_of_int_nil: forall z,
  (bits_of_int z) = [] -> z <= 0.
Proof.
  intros. rewrite bits_of_int_equation in H.
  destruct (Z_lt_ge_dec z 0). lia.
  destruct (Z.eq_dec z 0). lia.
  destruct (Z.eq_dec z 1). inversion H.
  destruct (Z.odd z). inversion H. inversion H.
Qed.

Lemma div2_0_iff: forall z,
  Z.div2 z = 0%Z <-> z = 0%Z \/ z = 1%Z.
Proof.
  intros. split; intros.
  - assert (z < 0 \/ z = 0%Z \/ z = 1 %Z \/ z > 1%Z) by lia. destruct H0.
    rewrite <- Z.div2_neg in H0. lia.
    destruct H0. left. assumption.
    destruct H0. right. assumption.
    destruct (Zeven_odd_dec z).
    + apply Zeven_div2 in z0. lia.
    + apply Zodd_div2 in z0. lia.
  - destruct H. subst. reflexivity. subst. reflexivity.
Qed.

Lemma bits_of_int_wf: forall z, P.wf_poly (bits_of_int z).
Proof.
  intros. apply bits_of_int_rec; intros; try (apply wf_nil).
  - unfold P.wf_poly. reflexivity.
  - destruct (bits_of_int (Z.div2 z0)) eqn : P.
    + unfold P.wf_poly; reflexivity.
    + apply P.wf_poly_cons. solve_neq. assumption. 
  - destruct (bits_of_int (Z.div2 z0)) eqn : P.
    + apply bits_of_int_nil in P.
      assert (Z.div2 z0 < 0 \/ Z.div2 z0 = 0%Z) by lia. destruct H0.
      
      Search Z.div2.
      lia.


 apply P.wf_poly_cons. solve_neq. rewrite e3 in H. assumption.
Qed.



 (*ensure we get well formed poly*)
    match (bits_of_int (Z.div2 z)) with
    | nil => nil
    | x :: t => Zero :: x :: t
    end. 
Proof.
- intros. destruct (Zeven_odd_dec z).
  + apply Zeven_div2 in z0. lia.
  + apply Zodd_div2 in z0. lia.
- intros. destruct (Zeven_odd_dec z).
  + apply Zeven_div2 in z0. lia.
  + apply Zodd_div2 in z0. lia.
Defined.
*)



Function bits_of_int (z: Z) {measure Z.to_nat} : list bit :=
  if (Z_lt_ge_dec z 0) then nil else
  if (Z.eq_dec z 0) then nil else 
  if (Z.eq_dec z 1) then (One :: nil) else
  if (Z.odd z) then (One :: bits_of_int (Z.div2 z)) else (*ensure we get well formed poly*)
    match (bits_of_int (Z.div2 z)) with
    | nil => nil
    | x :: t => Zero :: x :: t
    end. 
Proof.
- intros. destruct (Zeven_odd_dec z).
  + apply Zeven_div2 in z0. lia.
  + apply Zodd_div2 in z0. lia.
- intros. destruct (Zeven_odd_dec z).
  + apply Zeven_div2 in z0. lia.
  + apply Zodd_div2 in z0. lia.
Defined.

(*Todo move - have this but for polys*)
Lemma wf_nil: P.wf_poly nil.
Proof.
  unfold P.wf_poly. intros. contradiction.
Qed.


Lemma bits_of_int_wf: forall z, P.wf_poly (bits_of_int z).
Proof.
  intros. apply bits_of_int_rec; intros; try (apply wf_nil).
  - unfold P.wf_poly. reflexivity.
  - destruct (bits_of_int (Z.div2 z0)) eqn : P.
    + unfold P.wf_poly; reflexivity.
    + apply P.wf_poly_cons. solve_neq. assumption. 
  - apply P.wf_poly_cons. solve_neq. rewrite e3 in H. assumption.
Qed.

Lemma div2_0_iff: forall z,
  Z.div2 z = 0%Z <-> z = 0%Z \/ z = 1%Z.
Proof.
  intros. split; intros.
  - assert (z < 0 \/ z = 0%Z \/ z = 1 %Z \/ z > 1%Z) by lia. destruct H0.
    rewrite <- Z.div2_neg in H0. lia.
    destruct H0. left. assumption.
    destruct H0. right. assumption.
    destruct (Zeven_odd_dec z).
    + apply Zeven_div2 in z0. lia.
    + apply Zodd_div2 in z0. lia.
  - destruct H. subst. reflexivity. subst. reflexivity.
Qed.


Lemma bits_of_int_nil: forall z,
  (bits_of_int z) = [] -> z <= 0.
Proof.
  intros z.
  apply bits_of_int_rect; intros; try lia.
  - inversion H.
  - inversion H0.
  - apply H in e3. assert (Z.div2 z0 < 0 \/ Z.div2 z0 = 0%Z) by lia.
    destruct H1. rewrite Z.div2_neg in H1. lia.
    rewrite div2_0_iff in H1. destruct H1; lia.
  - inversion H0.
Qed.

Import WPoly.
Definition poly_of_int z := from_list (bits_of_int z).

(*why we want to have [bits_of_int] return a well formed poly rather than just letting from_list do the work*)
Lemma poly_of_int_bits: forall z,
  poly_of_int z = exist _ (bits_of_int z) (bits_of_int_wf z).
Proof.
  intros. unfold poly_of_int.
  unfold from_list. exist_eq. apply P.wf_no_trailing_zeroes. apply bits_of_int_wf.
Qed.

Lemma poly_of_int_zero: forall z,
  poly_of_int z = zero <-> z <= 0%Z.
Proof.
  intros. split; intros.
  - rewrite poly_of_int_bits in H. unfold zero in H. inversion H.
    apply bits_of_int_nil. assumption.
  - rewrite poly_of_int_bits. unfold zero. exist_eq. rewrite bits_of_int_equation.
    if_tac. reflexivity. if_tac. reflexivity. if_tac. lia. destruct (Z.odd z). lia.
    destruct (bits_of_int (Z.div2 z)). reflexivity. lia.
Qed.

Lemma log2_div2: forall z,
  1 < z ->
  1 + Z.log2 (Z.div2 z) = Z.log2 z.
Proof.
  intros. rewrite Z.div2_spec. rewrite Z.log2_shiftr.
  assert (Z.log2 z >= 1). pose proof (Z.log2_nonneg z).
  assert (Z.log2 z = 0%Z \/ Z.log2 z > 0) by lia. destruct H1.
  rewrite Z.log2_null in H1. lia. lia. lia. lia.
Qed. 

Lemma poly_of_int_deg: forall z,
  0 < z ->
  deg(poly_of_int z) = Z.log2 z.
Proof.
  intros.
  rewrite poly_of_int_bits. unfold deg. simpl. generalize dependent z. intros z.
  apply bits_of_int_rec; intros; try lia.
  - subst. reflexivity.
  - assert (Z.div2 z0 <0 \/ Z.div2 z0 = 0%Z \/ 0 < Z.div2 z0) by lia. destruct H1.
    rewrite Z.div2_neg in H1. lia. destruct H1. apply div2_0_iff in H1. destruct H1; lia.
    apply H in H1; clear H. rewrite P.deg_cons. rewrite H1. apply log2_div2. lia.
  - apply bits_of_int_nil in e3. assert (Z.div2 z0 < 0 \/ Z.div2 z0 = 0%Z) by  lia.
    destruct H1. rewrite Z.div2_neg in H1. lia. rewrite div2_0_iff in H1.
    destruct H1; lia.
  - assert (Z.div2 z0 <0 \/ Z.div2 z0 = 0%Z \/ 0 < Z.div2 z0) by lia. destruct H1.
    rewrite Z.div2_neg in H1. lia. destruct H1. apply div2_0_iff in H1. destruct H1; lia.
    apply H in H1; clear H. rewrite P.deg_cons. rewrite <- e3. rewrite H1. apply log2_div2. lia.
Qed.

Fixpoint bits_to_int (l: list bit) : Z :=
  match l with
  | nil => 0%Z
  | 1 :: l' => 2 * (bits_to_int l') + 1
  | 0 :: l' => 2 * (bits_to_int l')
  end.

Definition poly_to_int (p: poly) :=
  bits_to_int (to_list p).

Lemma poly_to_int_one: poly_to_int one = 1%Z.
Proof.
  reflexivity.
Qed.

Lemma poly_to_int_bounded: forall (p: poly),
  0 <= poly_to_int p <= 2 ^ (deg p + 1) - 1.
Proof.
  intros. unfold poly_to_int. unfold to_list. unfold deg. 
  induction (proj1_sig p).
  - simpl. lia.
  - simpl. destruct a. rewrite Zlength_cons. unfold P.deg in IHp0. destruct p0.
    simpl. lia.
    replace (Zlength (b :: p0) - 1 + 1)  with (Zlength (b :: p0)) in IHp0 by lia.
    replace (Z.succ (Zlength (b :: p0)) - 1 + 1)%Z with (Z.succ (Zlength (b :: p0))) by lia.
    rewrite Z.pow_succ_r. 2 : list_solve. lia. 
    unfold P.deg in IHp0. destruct p0. simpl. lia.
    rewrite Zlength_cons.
    replace (Zlength (b :: p0) - 1 + 1)  with (Zlength (b :: p0)) in IHp0 by lia.
    replace (Z.succ (Zlength (b :: p0)) - 1 + 1)%Z with (Z.succ (Zlength (b :: p0))) by lia.
    rewrite Z.pow_succ_r. 2 : list_solve.  lia.
Qed.

Definition modulus : Z := 137.

Lemma modulus_poly: poly_of_int modulus = p128. 
Proof.
  reflexivity.
Qed.

(*special for this case*)
Lemma polys_deg_bounded: forall z,
  0 < z < 128 ->
  deg (poly_of_int z) < deg (p128).
Proof.
  intros. assert (deg p128 = 7) by reflexivity. rewrite H0.
  rewrite poly_of_int_deg.
  assert (Z.log2 z <= Z.log2 127). apply Z.log2_le_mono. lia. 
  assert (Z.log2 127 = 6) by reflexivity. lia. lia.
Qed.

Lemma p128_deg: deg p128 = 7.
Proof.
  reflexivity.
Qed.

Lemma p128_deg_pos: deg p128 > 0.
Proof.
  pose proof p128_deg. lia.
Qed.

Lemma qpoly_128_bound: forall p,
  deg p < deg p128 ->
  0 <= poly_to_int p < 128.
Proof.
  intros. pose proof poly_to_int_bounded p. 
  pose proof p128_deg. rewrite H1 in H. split. lia.
  destruct H0.
  assert ((poly_to_int p) + 1 <= 2 ^ (deg p + 1)) by lia.
  assert (2 ^ (deg p + 1) <= 2 ^7). apply Z.pow_le_mono_r.
  lia. lia. lia.
Qed.

Lemma p128_not_x: p128 <> x.
Proof.
solve_neq.
Qed.

Lemma bits_of_int_double: forall q,
  0 < q ->
  bits_of_int (2 * q) = 0 :: bits_of_int q.
Proof.
  intros. rewrite bits_of_int_equation at 1. if_tac. lia. if_tac. lia.
  if_tac. lia.
  assert (Z.even (2 * q) = true). rewrite Z.even_mul. rewrite orb_true_iff. left.
  apply Z.even_2. 
 destruct (Z.odd (2 * q)) eqn : P.
  - rewrite Zodd_even_bool in P. rewrite H3 in P. inversion P.
  - assert (Z.div2 (2 * q) = q). rewrite Zeven_bool_iff in H3.
    apply Zeven_div2 in H3. lia. rewrite H4.
    destruct (bits_of_int q) eqn : L.
    + apply bits_of_int_nil in L. lia.
    + reflexivity.
Qed.

Lemma poly_shiftl: forall q,
  0 < q ->
  poly_of_int (2 * q) = x *~ poly_of_int q.
Proof.
  intros. rewrite poly_of_int_bits.
  rewrite poly_of_int_bits. unfold x. unfold poly_mult. exist_eq.
  rewrite bits_of_int_double.
  unfold monomial. simpl. rewrite <- P.shift_monomial.
  unfold P.shift. simpl. reflexivity. intro.
  apply bits_of_int_nil in H0. lia. assumption.
Qed.

(*xor is polynomial addition*)
Definition bool_to_bit (b: bool) : bit :=
  if b then 1 else 0.

(*TODO: move*)
Lemma ith_cons: forall (f: P.poly) (n : Z) (x: bit),
  n > 0 ->
  P.ith (x :: f) n = P.ith f (n-1).
Proof.
  intros. unfold P.ith. list_solve.
Qed.

Lemma poly_of_int_spec: forall z n,
  0 <= z ->
  bool_to_bit (Z.testbit z n) =  (ith (poly_of_int z) n).
Proof.
  intros. rewrite poly_of_int_bits. unfold ith. simpl.
  generalize dependent n. revert H. apply bits_of_int_rect; intros.
  - lia.
  - subst. rewrite P.ith_zero. rewrite Z.bits_0. reflexivity.
  - subst. assert (n < 0 \/ n = 0%Z \/ n > 0) by lia. destruct H0.
    + rewrite P.ith_unbounded. 2 : left; assumption. rewrite Z.testbit_neg_r. reflexivity. assumption.
    + destruct H0.
      * subst. simpl. reflexivity.
      * rewrite P.ith_unbounded. 2 : { right. simpl. assumption. }
        rewrite Z.bits_above_log2. reflexivity. lia. simpl. lia.
  - assert (0 <= Z.div2 z0). 
    assert (Z.div2 z0 < 0 \/ Z.div2 z0 = 0%Z \/ 0 <= Z.div2 z0) by lia.
    destruct H1. rewrite Z.div2_neg in H1. lia. destruct H1.
    rewrite div2_0_iff in H1. destruct H1; lia. assumption.
    specialize (H H1); clear H1.
    assert (n < 0 \/ n = 0%Z \/ n > 0) by lia. destruct H1.
    + rewrite P.ith_unbounded. rewrite Z.testbit_neg_r. reflexivity. assumption.
      left. assumption.
    + destruct H1.
      * subst. simpl. rewrite e2. simpl. reflexivity.
      * replace n with (Z.succ (n-1)) at 1 by lia. rewrite Zbits.Ztestbit_succ.
        2 : lia. rewrite H. rewrite ith_cons. reflexivity. assumption.
  - apply bits_of_int_nil in e3. 
    assert (Z.div2 z0 < 0 \/ Z.div2 z0 = 0%Z) by lia. destruct H1.
    rewrite Z.div2_neg in H1. lia. rewrite div2_0_iff in H1. destruct H1; lia.
  - rewrite <- e3.  assert (0 <= Z.div2 z0). 
    assert (Z.div2 z0 < 0 \/ Z.div2 z0 = 0%Z \/ 0 <= Z.div2 z0) by lia.
    destruct H1. rewrite Z.div2_neg in H1. lia. destruct H1.
    rewrite div2_0_iff in H1. destruct H1; lia. assumption.
    specialize (H H1); clear H1.
    assert (n < 0 \/ n = 0%Z \/ n > 0) by lia. destruct H1.
    + rewrite P.ith_unbounded. rewrite Z.testbit_neg_r. reflexivity. assumption.
      left. assumption.
    + destruct H1.
      * subst. simpl. rewrite e2. reflexivity. 
      * replace n with (Z.succ (n-1)) at 1 by lia. rewrite Zbits.Ztestbit_succ.
        2 : lia. rewrite H. rewrite ith_cons. reflexivity. assumption.
Qed.

Lemma xor_addition: forall q1 q2,
  0 <= q1 ->
  0 <= q2 ->
  poly_of_int (Z.lxor q1 q2) = (poly_of_int q1) +~ (poly_of_int q2).
Proof.
  intros. rewrite ith_eq. intros.
  rewrite <- poly_of_int_spec. rewrite ith_poly_add.
  repeat(rewrite <- poly_of_int_spec; try lia).
  2 : { apply Z.lxor_nonneg. split; intros; assumption. }
  rewrite Z.lxor_spec. 
  destruct ((Z.testbit q1 i)); simpl; simple_if_tac; reflexivity.
Qed.

Definition bit_to_bool (b: bit) :=
  match b with
  | 0 => false
  | 1 => true
  end.

Lemma evens_even: forall z,
  Z.even (2 * z) = true.
Proof.
  intros. rewrite Z.even_mul. rewrite orb_true_iff. left.
  apply Z.even_2. 
Qed.

Lemma odds_odd: forall z,
  Z.odd (1 + 2 * z) = true.
Proof.
  intros. replace (1 + 2 * z) with (Z.succ (2 * z)) by lia. 
  rewrite Z.odd_succ. apply evens_even.
Qed.

Lemma div2_even: forall z,
  Z.div2 (2 * z) = z.
Proof.
  intros. 
  pose proof (evens_even z). rewrite Zeven_bool_iff in H.
  apply Zeven_div2 in H. lia.
Qed.

Lemma div2_odd: forall z,
  Z.div2 (1 + 2 * z) = z.
Proof.
  intros. rewrite Z.div2_spec. apply Z.bits_inj. unfold Z.eqf. intros.
  assert (n< 0 \/ 0 <= n) by lia. destruct H.
  rewrite Z.testbit_neg_r. rewrite Z.testbit_neg_r. reflexivity. all: try assumption.
  rewrite Z.shiftr_spec; try assumption.
  replace (n +1) with (Z.succ n) by lia. rewrite Z.add_comm.
  rewrite Z.testbit_odd_succ. reflexivity. assumption.
Qed.

Lemma poly_to_int_spec: forall p n,
    Z.testbit (poly_to_int p) n = bit_to_bool (ith p n).
Proof.
  intros. unfold poly_to_int. unfold to_list. unfold ith. revert n. 
  induction (proj1_sig p); intros.
  - simpl. rewrite P.ith_zero. rewrite Z.bits_0. reflexivity.
  - simpl. assert (n < 0 \/ n = 0%Z \/ n > 0) by lia.
    destruct H.
    + rewrite P.ith_unbounded. rewrite Z.testbit_neg_r. reflexivity. assumption.
      left. assumption.
    + destruct H.
      * subst. unfold P.ith. rewrite Znth_0_cons.
        destruct a.
        -- rewrite Z.testbit_even_0. reflexivity.
        -- rewrite Z.bit0_odd. rewrite Z.add_comm. rewrite odds_odd. reflexivity.
      * rewrite ith_cons; try assumption. destruct a.
        -- replace n with (Z.succ (n-1)) at 1 by lia. rewrite Z.double_bits_succ. apply IHp0.
        -- pose proof (Zbits.Ztestbit_succ (n-1) (2 * bits_to_int p0 + 1) ).
           replace (Z.succ (n-1)) with n in H0 by lia. rewrite H0. 2 : lia.
           clear H0. pose proof odds_odd. setoid_rewrite Z.add_comm in H0.
           specialize (H0 (bits_to_int p0)). rewrite Zodd_bool_iff in H0. apply Zodd_div2 in H0.
           rewrite Z.add_comm.
           rewrite div2_odd. apply IHp0.
Qed.

Lemma bit_bool_id: forall b,
  bit_to_bool (bool_to_bit b) = b.
Proof.
  intros; destruct b; reflexivity.
Qed.

Lemma bool_bit_id: forall b,
  bool_to_bit (bit_to_bool b) = b.
Proof.
  intros; destruct b; reflexivity.
Qed.

Lemma poly_of_int_to_int: forall z p,
  0 <= z ->
  p = poly_of_int z <-> z = poly_to_int p.
Proof.
  intros. split; intros.
  - apply Z.bits_inj. unfold Z.eqf. intros.
    rewrite poly_to_int_spec. rewrite H0.
    rewrite <- poly_of_int_spec; try lia. rewrite bit_bool_id. reflexivity.
  - apply ith_eq. intros. rewrite <- poly_of_int_spec. rewrite H0.
    rewrite poly_to_int_spec. rewrite bool_bit_id. reflexivity. assumption.
Qed. 

Lemma poly_of_int_inv: forall p,
  poly_of_int (poly_to_int p) = p.
Proof.
  intros. symmetry. rewrite poly_of_int_to_int. reflexivity. pose proof (poly_to_int_bounded p). lia.
Qed.

Lemma unsigned_repr: forall z,
  0 <= z < Int.modulus -> Int.unsigned (Int.repr z) = z.
Proof.
  intros.
  pose proof (Int.eqm_unsigned_repr z).
  apply Int.eqm_sym in H0.
  unfold Int.eqm in H0. eapply Zbits.eqmod_small_eq. apply H0. rep_lia. rep_lia.
Qed.

(*TODO: move*)
Lemma pmod_same: forall f,
  deg f > 0 ->
  f %~ f = zero.
Proof.
  intros. unfold pmod. destruct (poly_div f f) as [q r] eqn : P.
  rewrite poly_div_correct in P.
  - destruct P. rewrite <- poly_add_cancel_1 in H0.
    rewrite <- (poly_mult_1_l f) in H0 at 1. rewrite <- poly_mult_distr_r in H0.
    simpl. assert (deg r = deg r) by reflexivity. rewrite <- H0 in H2 at 1.
    destruct (destruct_poly (one +~ q)). rewrite e in H0.
    rewrite poly_mult_0_l in H0. subst. reflexivity.
    rewrite poly_mult_deg in H2. rewrite <- deg_nonzero in n. lia.
    assumption. apply f_nonzero; assumption.
  - apply f_nonzero; assumption.
Qed.

Lemma poly_to_int_zero_iff: forall p,
  poly_to_int p = 0%Z <-> p = zero.
Proof.
  intros. split; intros.
  - unfold poly_to_int in H. unfold to_list in H. unfold zero. destruct p. exist_eq.
    simpl in H. generalize dependent w. induction x.
    + reflexivity.
    + intros. simpl in H. destruct a. assert (bits_to_int x = 0%Z) by lia.
      destruct x. unfold P.wf_poly in w. assert (0=1). apply w. solve_neq. inversion H1.
      apply IHx in H0. inversion H0. rewrite P.wf_poly_cons in w. assumption. solve_neq.
      lia.
  - subst. reflexivity.
Qed.

Lemma poly_to_int_pos: forall p,
  p <> zero ->
  0 < poly_to_int p.
Proof.
  intros. pose proof (poly_to_int_bounded p).
  assert (poly_to_int p = 0%Z \/ poly_to_int p > 0) by lia. destruct H1.
  rewrite poly_to_int_zero_iff in H1. contradiction. lia.
Qed.


(** Verification of [generate_index_power_tables] *)

Definition fec_n : Z := proj1_sig (opaque_constant 128).
Definition fec_n_eq : fec_n = 128%Z := proj2_sig (opaque_constant _).
Hint Rewrite fec_n_eq : rep_lia.

(* i -> x^i % f in fec_2_index*)
Definition power_to_index_contents (bound : Z) :=
  (map Vint (map Int.repr (prop_list (fun z => 
      poly_to_int ( (monomial (Z.to_nat z)) %~ p128)) bound))).

Lemma power_to_index_contents_plus_1: forall bound,
  0 <= bound ->
  power_to_index_contents (bound + 1) = power_to_index_contents bound ++ 
  (Vint (Int.repr (poly_to_int (monomial (Z.to_nat bound) %~ p128)))) :: nil.
Proof.
  unfold power_to_index_contents. intros. rewrite prop_list_plus_1. rewrite? map_app.
  reflexivity. assumption.
Qed.
  

(*p -> i such that x^i % f = p in fec_2_power. This is the coq function [find_power]*)
Definition index_to_power_contents :=
  (map Vint (map Int.repr (prop_list
  (fun z => find_power p128 (poly_of_int z)) fec_n))).

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

(*TODO: add*)
Definition Gprog := [generate_index_power_tables_spec].

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
    PROP (0 <= i <= fec_n /\ (forall z, 0 < z < fec_n -> 0 < find_power p128 (poly_of_int z) < i ->
          Znth z l = find_power p128 (poly_of_int z)) /\
      Znth 0 l = 0%Z)
    LOCAL (temp _i (Vint (Int.repr i)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents i ++ map Vint (map Int.repr (list_repeat
      ((Z.to_nat fec_n) - Z.to_nat i)%nat 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
        data_at Ews tint (Vint (Int.repr modulus)) (gv _modulus);
       data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N))).
- Exists 0%Z. Exists (list_repeat (Z.to_nat fec_n) 0%Z). entailer!.
  apply Znth_list_repeat_inrange. rep_lia.
  unfold power_to_index_contents. rewrite prop_list_0. simpl.
  replace ((Z.to_nat fec_n - 0)%nat) with (Z.to_nat fec_n) by rep_lia. entailer!.
- Intros i. Intros l. forward. forward_if. 2 : {
  forward. entailer!. assert (i = fec_n) by lia. subst. 
  replace ((Z.to_nat fec_n - Z.to_nat fec_n)%nat) with 0%nat by lia.
  simpl. rewrite app_nil_r. entailer!. unfold index_to_power_contents.
  (*prove that our invariant actually leads to correct list at the end*) 
  assert ((map Vint (map Int.repr l)) = (map Vint (map Int.repr (prop_list (fun z : Z => find_power p128 (poly_of_int z)) fec_n)))). {
  f_equal. f_equal. apply Znth_eq_ext.
  rewrite? Zlength_map in H7. rewrite H7. rewrite prop_list_length. reflexivity. lia. intros.
  rewrite? Zlength_map in H7. rewrite H7 in H15.
  destruct (Z.eq_dec 0 i).
  - subst. rewrite H1. rewrite prop_list_Znth. assert (poly_of_int 0 = zero). rewrite poly_of_int_zero. lia.
    rewrite H16. rewrite find_power_zero. reflexivity. apply p128_deg_pos. apply p128_primitive.
    apply p128_not_x. assumption.
  - rewrite H0. rewrite prop_list_Znth. reflexivity. assumption. lia. pose proof (find_power_spec
    p128 p128_deg_pos p128_primitive p128_not_x (poly_of_int i)).
    assert (poly_of_int i <> zero). intro. rewrite poly_of_int_zero in H17. lia.
    specialize (H16 H17); clear H17. 
    assert (deg (poly_of_int i) < deg p128). rewrite poly_of_int_deg.
    rewrite p128_deg. assert (i <= fec_n -1) by lia. apply Z.log2_le_mono in H17.
    replace (fec_n - 1) with 127 in H17 by rep_lia. 
    replace (Z.log2 127) with 6 in H17 by reflexivity.
    lia. lia. specialize (H16 H17); clear H17. destruct H16.
    unfold field_size in H17. rewrite p128_deg in H17.
    replace ( Z.of_nat (2 ^ Z.to_nat 7 - 1)) with (127) in H17 by reflexivity.
    rep_lia. } rewrite H15. cancel. }
  forward_if (PROP (0 <= i <= fec_n /\ 
      (forall z, 0 < z < fec_n -> 0 < find_power p128 (poly_of_int z) < i -> 
          Znth z l = find_power p128 (poly_of_int z)) /\
      Znth 0 l = 0%Z)
    LOCAL (temp _i (Vint (Int.repr i)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents (i + 1) ++ map Vint (map Int.repr (list_repeat
      ((Z.to_nat fec_n) - Z.to_nat (i + 1))%nat 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
        data_at Ews tint (Vint (Int.repr modulus)) (gv _modulus);
       data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N))).
  + forward. entailer!.
    replace ((Z.to_nat fec_n) - Z.to_nat 0%Z)%nat with (Z.to_nat fec_n)%nat by lia. 
    unfold power_to_index_contents.
    rewrite prop_list_0. assert ((map Vint (map Int.repr []) = nil)). reflexivity.
    rewrite H3. rewrite app_nil_l. 
    replace (Z.to_nat (fec_n)) with (1%nat + (Z.to_nat fec_n - Z.to_nat 1)%nat)%nat by rep_lia.
    rewrite <- list_repeat_app. rewrite map_app. rewrite map_app.
    rewrite upd_Znth_app1. 
    assert ((upd_Znth 0 (map Vint (map Int.repr (list_repeat 1 0%Z))) (Vint (Int.zero_ext 8 (Int.repr (1))))) =
    Vint (Int.zero_ext 8 (Int.repr 1)) :: nil). simpl.
    rewrite upd_Znth0. reflexivity. rewrite H14. clear H14.
    assert ((map Vint (map Int.repr (prop_list (fun z : Z => poly_to_int (monomial (Z.to_nat z) %~ p128)) 1))) =
    Vint (Int.zero_ext 8 (Int.repr 1)) :: nil). simpl.
    rewrite monomial_0. rewrite pmod_refl. rewrite poly_to_int_one. reflexivity. apply p128_deg_pos.
    pose proof p128_deg. assert (0%Z = deg one) by (apply deg_one; reflexivity). lia.
    rewrite H14. replace (1 + (Z.to_nat fec_n - Z.to_nat 1) - Z.to_nat 1)%nat with (Z.to_nat fec_n - Z.to_nat 1)%nat
    by rep_lia. entailer!.
    rewrite? Zlength_map. simpl. list_solve.
  + forward. 
    * entailer!. rewrite Znth_app1.
      unfold power_to_index_contents. rewrite Znth_map. rewrite Znth_map.
      rewrite prop_list_Znth. pose proof (qpoly_128_bound (monomial (Z.to_nat (i - 1)) %~ p128)).
      assert (deg (monomial (Z.to_nat (i - 1)) %~ p128) < deg p128). 
      apply pmod_lt_deg. apply p128_deg_pos. apply H14 in H15.
      remember (poly_to_int (monomial (Z.to_nat (i - 1)) %~ p128)) as n.
      simpl. rewrite unsigned_repr. all: try rep_lia. rewrite prop_list_length. lia. lia.
      rewrite Zlength_map. rewrite prop_list_length. lia. lia.
      unfold power_to_index_contents. rewrite? Zlength_map.
      rewrite prop_list_length. lia. lia.
    * forward. forward. rewrite Znth_app1. unfold power_to_index_contents at 1.
      unfold power_to_index_contents at 1.
      rewrite Znth_map. rewrite Znth_map. rewrite prop_list_Znth. simpl.
      unfold Int.shl. remember (poly_to_int (monomial (Z.to_nat (i - 1)) %~ p128)) as prior.
      pose proof (qpoly_128_bound (monomial (Z.to_nat (i - 1)) %~ p128)) as Hpriorbound.
      assert (Hpriordeg: deg (monomial (Z.to_nat (i - 1)) %~ p128) < deg p128). apply pmod_lt_deg.
      apply p128_deg_pos. specialize (Hpriorbound Hpriordeg). rewrite <- Heqprior in Hpriorbound.
      rewrite (unsigned_repr prior); try rep_lia. simpl. all: try rep_lia.
      2 : { rewrite prop_list_length; lia. }
      2 : { rewrite Zlength_map. rewrite prop_list_length; lia. }
      2 : { unfold power_to_index_contents. rewrite? Zlength_map. rewrite prop_list_length; lia. } 
 forward_if (PROP (0 <= i <= fec_n /\ 
      (forall z, 0 < z < fec_n -> 0 < find_power p128 (poly_of_int z) < i -> 
          Znth z l = find_power p128 (poly_of_int z)) /\
      Znth 0 l = 0%Z)
    LOCAL (temp _i (Vint (Int.repr i)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents (i + 1) ++ map Vint (map Int.repr (list_repeat
      ((Z.to_nat fec_n) - Z.to_nat (i + 1))%nat 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
        data_at Ews tint (Vint (Int.repr modulus)) (gv _modulus);
       data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N))).
      -- forward. forward. entailer!. 
         remember (poly_to_int (monomial (Z.to_nat (i - 1)) %~ p128)) as prior.
         unfold Int.xor.
         rewrite (unsigned_repr (2 * prior)); try rep_lia.
         rewrite (unsigned_repr modulus); try(unfold modulus; rep_lia).
         rewrite power_to_index_contents_plus_1.
         assert (Zlength (power_to_index_contents i) = i). unfold power_to_index_contents.
         rewrite Zlength_map. rewrite Zlength_map. apply prop_list_length. lia.
         rewrite upd_Znth_app2. replace (i - Zlength (power_to_index_contents i)) with 0%Z by lia.
         assert (list_repeat (Z.to_nat fec_n - Z.to_nat i) 0%Z = 
         0%Z :: (list_repeat (Z.to_nat fec_n - Z.to_nat (i + 1)) 0%Z)).
         replace (Z.to_nat fec_n - Z.to_nat i)%nat with (1%nat + (Z.to_nat fec_n - Z.to_nat (i + 1))%nat)%nat by lia. 
         rewrite <- list_repeat_app. simpl. reflexivity. rewrite H17. clear H17.
         simpl.
         rewrite upd_Znth0. (*finally, prove that this find x^i % f*) 
         assert (Vint (Int.zero_ext 8 (Int.repr (Z.lxor (2 * prior) modulus))) = 
          Vint (Int.repr (poly_to_int (monomial (Z.to_nat i) %~ p128)))). f_equal.
         assert ((Z.lxor (2 * prior) modulus) = (poly_to_int (monomial (Z.to_nat i) %~ p128))). {
         rewrite <- poly_of_int_to_int. rewrite xor_addition.
         rewrite modulus_poly.
         assert (Hdeg: deg (poly_of_int (2 * prior)) = deg p128). { rewrite poly_shiftl.
         rewrite poly_mult_deg. rewrite deg_x. rewrite poly_of_int_deg.
         rewrite p128_deg. assert ((Z.log2 prior) <= Z.log2 (fec_n - 1)). apply Z.log2_le_mono. rep_lia.
         replace (fec_n - 1) with (127) in H17 by rep_lia. replace (Z.log2 127) with (6) in H17 by reflexivity.
         assert (1 + Z.log2 prior <= 7) by lia.
         assert (Z.log2 (fec_n) <= Z.log2 (2 * prior)). apply Z.log2_le_mono. lia.
         rewrite Z.log2_double in H19. replace (fec_n) with 128 in H19 by rep_lia.
         replace (Z.log2 (128)) with (7) in H19 by reflexivity. all: try lia.
         intro. pose proof deg_x. rewrite <- deg_zero in H17. lia.
         intro. rewrite poly_of_int_zero in H17. lia. }
         rewrite Heqprior. rewrite Heqprior in Hdeg. 
         rewrite poly_shiftl. rewrite poly_shiftl in Hdeg. rewrite poly_of_int_inv.
         rewrite poly_of_int_inv in Hdeg.
         all: try ((try unfold modulus); rep_lia).
         assert (deg (x *~ (monomial (Z.to_nat (i - 1)) %~ p128) +~ p128) < deg p128). {
         rewrite poly_add_comm.
         apply poly_add_deg_same. rewrite Hdeg. reflexivity. intro. inversion H17. }
         rewrite <- (pmod_refl _ p128_deg_pos _ H17).
         rewrite pmod_add_distr; try apply p128_deg_pos.
         rewrite pmod_same; try apply p128_deg_pos. rewrite poly_add_0_r.
         rewrite? pmod_twice; try apply p128_deg_pos.
         rewrite <- (pmod_refl _ p128_deg_pos x). rewrite <- pmod_mult_distr.
         rewrite <- monomial_expand. replace (S (Z.to_nat (i - 1))) with (Z.to_nat i) by lia.
         reflexivity. apply p128_deg_pos. pose proof deg_x. pose proof p128_deg. lia.
         rewrite Z.lxor_nonneg. split; intros. unfold modulus; lia. lia. }
         rewrite H17. unfold Int.zero_ext. f_equal. 
         assert (0 <= poly_to_int (monomial (Z.to_nat i) %~ p128) <= 128). {
         pose proof (poly_to_int_bounded (monomial (Z.to_nat i) %~ p128)). 
         pose proof (pmod_lt_deg p128 p128_deg_pos (monomial (Z.to_nat i))).
         rewrite p128_deg in H19.
         assert (deg (monomial (Z.to_nat i) %~ p128) + 1 <= 7) by lia. clear H19.
         apply (Z.pow_le_mono_r 2) in H20. replace (2^7) with (128) in H20 by reflexivity.
         all: try rep_lia. }
         rewrite Zbits.Zzero_ext_mod. replace (two_p 8) with (256) by reflexivity.
         rewrite Zmod_small. apply unsigned_repr; try rep_lia. 
         rewrite unsigned_repr; try rep_lia. lia. rewrite H17. rewrite <- app_assoc. simpl.
         cancel. rewrite H16. list_solve. lia.
      -- forward. entailer!.  (*similar case, a bit easier because no overflow*)
         remember (poly_to_int (monomial (Z.to_nat (i - 1)) %~ p128)) as prior.
         rewrite power_to_index_contents_plus_1.
         assert (Zlength (power_to_index_contents i) = i). unfold power_to_index_contents.
         rewrite Zlength_map. rewrite Zlength_map. apply prop_list_length. lia. 2: lia.
         rewrite upd_Znth_app2. replace (i - Zlength (power_to_index_contents i)) with 0%Z by lia.
         assert (list_repeat (Z.to_nat fec_n - Z.to_nat i) 0%Z = 
         0%Z :: (list_repeat (Z.to_nat fec_n - Z.to_nat (i + 1)) 0%Z)).
         replace (Z.to_nat fec_n - Z.to_nat i)%nat with (1%nat + (Z.to_nat fec_n - Z.to_nat (i + 1))%nat)%nat by lia. 
         rewrite <- list_repeat_app. simpl. reflexivity. rewrite H17. clear H17.
         simpl.
         rewrite upd_Znth0. (*finally, prove that this find x^i % f*) 
         assert (Vint (Int.zero_ext 8 (Int.repr (2 * prior))) = 
          Vint (Int.repr (poly_to_int (monomial (Z.to_nat i) %~ p128)))). f_equal.
         assert (2 * prior = (poly_to_int (monomial (Z.to_nat i) %~ p128))). {
         rewrite <- poly_of_int_to_int. 2 : lia. 
         assert (Hdeg: deg (poly_of_int (2 * prior)) < deg p128). { 
         assert (0%Z = 2 * prior \/ 0 < 2 * prior) by lia. destruct H17. rewrite <- H17.
         assert (poly_of_int 0 = zero). rewrite poly_of_int_zero. lia. rewrite H18.
         assert (deg zero < 0) by (rewrite deg_zero; reflexivity). pose proof p128_deg_pos. lia. 
         rewrite poly_of_int_deg. 
         assert (2 * prior <= fec_n - 1) by lia. apply Z.log2_le_mono in H18.
         replace (fec_n) with 128 in H18 by rep_lia. replace (Z.log2 (128-1)) with (6) in H18 by reflexivity.
         rewrite p128_deg. lia. assumption. } (*this time, we need to make sure that the previous poly is not zero -
         this follows because p128 is irreducible*) 
         assert (Hpriorpos : poly_to_int (monomial (Z.to_nat (i - 1)) %~ p128) > 0). {
         assert ( poly_to_int (monomial (Z.to_nat (i - 1)) %~ p128) = 0%Z \/  poly_to_int (monomial (Z.to_nat (i - 1)) %~ p128) > 0) by lia.
         destruct H17. 2 : lia. rewrite poly_to_int_zero_iff in H17.
         pose proof (irred_doesnt_divide_monomial p128 (Z.to_nat (i-1)) p128_deg_pos p128_irred).
         assert (p128 <> x) by solve_neq. specialize (H18 H19). clear H19.
         exfalso. apply H18. apply divides_pmod_iff. left. intro. inversion H19.
         unfold divides_pmod. assumption. }
         rewrite Heqprior. rewrite Heqprior in Hdeg. 
         rewrite poly_shiftl. rewrite poly_shiftl in Hdeg. rewrite poly_of_int_inv.
         rewrite poly_of_int_inv in Hdeg. all: try lia. 
         (*now the goal is simple*)
         rewrite <- (pmod_refl p128 p128_deg_pos _ Hdeg). rewrite pmod_mult_distr.
         rewrite pmod_twice. rewrite <- pmod_mult_distr. rewrite <- monomial_expand.
         replace (S (Z.to_nat (i - 1))) with (Z.to_nat i) by lia. reflexivity. all: apply p128_deg_pos. }
         rewrite H17. unfold Int.zero_ext. f_equal.
         assert (0 <= poly_to_int (monomial (Z.to_nat i) %~ p128) <= 128). {
         pose proof (poly_to_int_bounded (monomial (Z.to_nat i) %~ p128)). 
         pose proof (pmod_lt_deg p128 p128_deg_pos (monomial (Z.to_nat i))).
         rewrite p128_deg in H19.
         assert (deg (monomial (Z.to_nat i) %~ p128) + 1 <= 7) by lia. clear H19.
         apply (Z.pow_le_mono_r 2) in H20. replace (2^7) with (128) in H20 by reflexivity.
         all: try rep_lia. }
         rewrite Zbits.Zzero_ext_mod. replace (two_p 8) with (256) by reflexivity.
         rewrite Zmod_small. apply unsigned_repr; try rep_lia. 
         rewrite unsigned_repr; try rep_lia. lia. rewrite H17. rewrite <- app_assoc. simpl.
         cancel. rewrite H16. list_solve.
    + (*now, need to prove the other invariant (for the index -> power array*) forward.
      entailer!. rewrite Znth_app1. unfold power_to_index_contents. rewrite? Znth_map.
      rewrite prop_list_Znth. simpl.
      pose proof (qpoly_128_bound (monomial (Z.to_nat i) %~ p128)). 
      assert (deg (monomial (Z.to_nat i) %~ p128) < deg p128). apply pmod_lt_deg.
      apply p128_deg_pos. rewrite unsigned_repr. rep_lia. rep_lia. lia.
      rewrite prop_list_length; lia. rewrite Zlength_map.
      rewrite prop_list_length; lia. unfold power_to_index_contents.
      rewrite? Zlength_map. rewrite prop_list_length; lia.
      rewrite Znth_app1. all: unfold power_to_index_contents at 1. rewrite Znth_map.
      rewrite Znth_map. rewrite prop_list_Znth. 
      pose proof (qpoly_128_bound (monomial (Z.to_nat i) %~ p128)).
      assert (deg (monomial (Z.to_nat i) %~ p128) < deg p128 ). apply pmod_lt_deg.
      apply p128_deg_pos. specialize (H3 H4); clear H4. forward.
      * entailer!.
      * forward. Exists (i+1). Exists ((upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ p128)) l i)).
        (*Now, let's prove the invariant is preserved*) entailer!.
         assert (S1: Z.of_nat (field_size p128) = fec_n -1). {
            unfold field_size. rewrite p128_deg. replace (fec_n) with (128) by rep_lia. reflexivity. }
            rewrite Zlength_upd_Znth in H9. rewrite? Zlength_map in H9. split.
        -- intros. 
            assert (0 < find_power p128 (poly_of_int z) < i \/ find_power p128 (poly_of_int z) = i) by lia.
            destruct H17.
            ++ rewrite upd_Znth_diff. apply H0. lia. lia. lia. rewrite H9. rep_lia.
               intro. assert (find_power p128 (poly_of_int z) = i). symmetry. rewrite <- find_power_iff.
               split. rewrite H18. rewrite poly_of_int_inv. reflexivity. lia. apply p128_deg_pos. apply p128_primitive.
               apply p128_not_x. intro. subst. rewrite poly_of_int_inv in H19.
               apply (irred_doesnt_divide_monomial p128 (Z.to_nat i)). apply p128_deg_pos.
               apply p128_irred. apply p128_not_x. rewrite divides_pmod_iff. unfold divides_pmod.
               assumption. left. solve_neq. subst. rewrite poly_of_int_inv. apply pmod_lt_deg.
               apply p128_deg_pos. lia.
            ++ assert (z = (poly_to_int (monomial (Z.to_nat i) %~ p128))). { symmetry in H17.
               rewrite <- find_power_iff in H17. destruct H17. rewrite <- poly_of_int_to_int.
               symmetry. assumption. lia. apply p128_deg_pos. apply p128_primitive.
               apply p128_not_x. intro. rewrite poly_of_int_zero in H18. lia.
               rewrite poly_of_int_deg; try lia. assert (z <= fec_n - 1) by lia.
               apply Z.log2_le_mono in H18. replace (fec_n - 1) with 127 in H18 by rep_lia.
              replace (Z.log2 127) with 6 in H18 by reflexivity. rewrite p128_deg. lia. }
                rewrite H18. rewrite upd_Znth_same. rewrite <- H18. rewrite <- H17. reflexivity.
               lia.
          -- rewrite upd_Znth_diff. assumption. rep_lia. rep_lia. intro. symmetry in H15.
             rewrite poly_to_int_zero_iff in H15. apply (irred_doesnt_divide_monomial p128 (Z.to_nat i)).
             apply p128_deg_pos. apply p128_irred. apply p128_not_x. rewrite divides_pmod_iff. unfold divides_pmod.
               assumption. left. solve_neq.
          -- rewrite upd_Znth_map. assert ( (map Vint
              (upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ p128)) (map Int.repr l)
              (Int.zero_ext 8 (Int.repr i)))) =  
              (map Vint (map Int.repr (upd_Znth (poly_to_int (monomial (Z.to_nat i) %~ p128)) l i)))).
              f_equal. rewrite <- upd_Znth_map. f_equal. unfold Int.zero_ext.
              f_equal. rewrite Zbits.Zzero_ext_mod; try lia. replace (two_p 8) with (256) by reflexivity.
              rewrite Zmod_small. rewrite unsigned_repr. reflexivity. rep_lia.
              rewrite unsigned_repr. rep_lia. rep_lia. rewrite H15. cancel.
      * lia.
      * rewrite prop_list_length; lia.
      * rewrite Zlength_map. rewrite prop_list_length; lia.
      * rewrite? Zlength_map. rewrite prop_list_length; lia.
Qed.

(*next step - want to redo with generic poly, get lemmas instead of constantly unfolding, make proof cleaner,
  separate out stuff into separate files*)





