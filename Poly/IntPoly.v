Require Import VST.floyd.functional_base.
Require Import GF2.
Require Import PolyDefs.
Require Import Poly.
Require Import PolyMod.
Require Import IntFacts.
Require Import Helper.
Import WPoly.
(** * Polynomials Represented By Integers*)

(*There is a natural encoding of polynomials over GF(2) as integers - the ith coefficient is the ith bit*)

(** Convert from int -> poly *)

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

Definition poly_of_int z := from_list (bits_of_int z).

Lemma bits_of_int_wf: forall z, P.wf_poly (bits_of_int z).
Proof.
  intros. apply bits_of_int_rec; intros; try (apply wf_zero).
  - unfold P.wf_poly. reflexivity.
  - destruct (bits_of_int (Z.div2 z0)) eqn : P.
    + unfold P.wf_poly; reflexivity.
    + apply P.wf_poly_cons. solve_neq. assumption. 
  - apply P.wf_poly_cons. solve_neq. rewrite e3 in H. assumption.
Qed.

(*why we want to have [bits_of_int] return a well formed poly rather than just letting from_list do the work. We
  can directly work with bits_of_int, so we can use induction*)
Lemma poly_of_int_bits: forall z,
  poly_of_int z = exist _ (bits_of_int z) (bits_of_int_wf z).
Proof.
  intros. unfold poly_of_int.
  unfold from_list. exist_eq. apply P.wf_no_trailing_zeroes. apply bits_of_int_wf.
Qed.

Lemma bits_of_int_nil: forall z,
  (bits_of_int z) = nil -> z <= 0.
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

(*To fully specify [poly_of_int], we need to convert between bits and booleans, which are isomorphic*)
Definition bool_to_bit (b: bool) : bit :=
  if b then 1 else 0.

(*Specification for [poly_of_int]. This, along with [ith_eq] allows us to prove equality of integer
  representations by comparing ints bitwise, which is very helpful*)
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
        2 : lia. rewrite H. rewrite P.ith_cons. reflexivity. assumption.
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
        2 : lia. rewrite H. rewrite P.ith_cons. reflexivity. assumption.
Qed.

(*xor is polynomial addition*)

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

(* Some special cases*)

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



(** Convert from poly -> int *)

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
  - unfold bits_to_int; fold bits_to_int. 
    destruct a. rewrite P.deg_cons.
    replace (1 + P.deg p0 + 1) with (Z.succ (P.deg p0 + 1)) by lia.
    rewrite Z.pow_succ_r. lia. destruct p0; simpl. lia. list_solve. 
    rewrite P.deg_cons. 
    replace (1 + P.deg p0 + 1) with (Z.succ (P.deg p0 + 1)) by lia.
    rewrite Z.pow_succ_r. lia. destruct p0; simpl. lia. list_solve.
Qed. 

Lemma poly_to_int_zero_iff: forall p,
  poly_to_int p = 0%Z <-> p = zero.
Proof.
  intros. split; intros.
  - unfold poly_to_int in H. unfold to_list in H. unfold zero. destruct p. exist_eq.
    simpl in H. generalize dependent w. induction x0.
    + reflexivity.
    + intros. unfold bits_to_int in H; fold bits_to_int in H.  destruct a. assert (bits_to_int x0 = 0%Z) by lia.
      destruct x0. unfold P.wf_poly in w. assert (0=1). apply w. solve_neq. inversion H1.
      apply IHx0 in H0. inversion H0. rewrite P.wf_poly_cons in w. assumption. solve_neq.
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

Lemma poly_to_int_monomial_irred: forall f n,
  irreducible f ->
  f <> x ->
  deg f > 0 ->
  0 < poly_to_int ((monomial n) %~ f).
Proof.
  intros. apply poly_to_int_pos. intro.
  apply (irred_doesnt_divide_monomial f n); try assumption. rewrite divides_pmod_iff.
  unfold divides_pmod. assumption. left. intro. subst.
  assert (deg zero < 0) by (rewrite deg_zero; reflexivity). lia.
Qed.


(* Likewise, to specify, we convert between bits and bools, then give a similar specifiation*)
Definition bit_to_bool (b: bit) :=
  match b with
  | 0 => false
  | 1 => true
  end.

(*Specification of [poly_to_int]*)
Lemma poly_to_int_spec: forall p n,
    Z.testbit (poly_to_int p) n = bit_to_bool (ith p n).
Proof.
  intros. unfold poly_to_int. unfold to_list. unfold ith. revert n. 
  induction (proj1_sig p); intros.
  - simpl. rewrite P.ith_zero. rewrite Z.bits_0. reflexivity.
  - unfold bits_to_int; fold bits_to_int.  assert (n < 0 \/ n = 0%Z \/ n > 0) by lia.
    destruct H.
    + rewrite P.ith_unbounded. rewrite Z.testbit_neg_r. reflexivity. assumption.
      left. assumption.
    + destruct H.
      * subst. unfold P.ith. rewrite Znth_0_cons.
        destruct a.
        -- rewrite Z.testbit_even_0. reflexivity.
        -- rewrite Z.bit0_odd. rewrite Z.add_comm. rewrite odds_odd. reflexivity.
      * rewrite P.ith_cons; try assumption. destruct a.
        -- replace n with (Z.succ (n-1)) at 1 by lia. rewrite Z.double_bits_succ. apply IHp0.
        -- pose proof (Zbits.Ztestbit_succ (n-1) (2 * bits_to_int p0 + 1) ).
           replace (Z.succ (n-1)) with n in H0 by lia. rewrite H0. 2 : lia.
           clear H0. pose proof odds_odd. setoid_rewrite Z.add_comm in H0.
           specialize (H0 (bits_to_int p0)). rewrite Zodd_bool_iff in H0. apply Zodd_div2 in H0.
           rewrite Z.add_comm.
           rewrite div2_odd. apply IHp0.
Qed.

(** Converting back and forth *)
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





