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
(*
Lemma xor_list_of_bits: forall q1 q2,
  bits_of_int (Z.lxor q1 q2) = P.poly_add_inter (bits_of_int q1) (bits_of_int q2).
Proof.
  intros. Print Z.lxor.
*)

Definition bitwise_xor (q1 q2 : Z) :=
  if (Z.eq_dec q1 0) then 
    if (Z.eq_dec q2 0) then 0%Z
    else 1%Z
  else 
    if (Z.eq_dec q2 0) then 1%Z else 0%Z.

Lemma mod2_cases: forall z,
  (z mod 2 = 0%Z) \/ (z mod 2 = 1%Z).
Proof.
  intros. rewrite Zmod_even. simple_if_tac. left. reflexivity. right. reflexivity.
Qed.

Lemma xor_expand: forall q1 q2,
  Z.lxor q1 q2 = (bitwise_xor (q1 mod 2) (q2 mod 2)) + 2 * Z.lxor (Z.div2 q1) (Z.div2 q2).
Proof.
  intros. apply Z.bits_inj. unfold Z.eqf. intros.
  assert (n < 0 \/ n >= 0) by lia. destruct H.
  - rewrite Z.testbit_neg_r. rewrite Z.testbit_neg_r. reflexivity. all: assumption.
  - rewrite Zbits.Z_add_is_or; try lia. 2 : {
    intros. rewrite andb_false_iff. assert (j = 0%Z \/ j > 0 ) by lia.
    destruct H1. subst. right.
    assert ((2 * Z.lxor (Z.div2 q1) (Z.div2 q2)) = (Z.shiftl (Z.lxor (Z.div2 q1) (Z.div2 q2)) 1)).
    simpl. reflexivity. rewrite H1.
    rewrite Z.shiftl_spec_low. reflexivity. lia.
    left.  
    assert ((bitwise_xor (q1 mod 2) (q2 mod 2) = 0%Z \/ 
      (bitwise_xor (q1 mod 2) (q2 mod 2)) = 1%Z)). 
    pose proof (mod2_cases q1).
    pose proof (mod2_cases q2).
    destruct H2; destruct H3; rewrite H2; rewrite H3; subst; simpl.
    - left. reflexivity.
    - right. reflexivity.
    - right. reflexivity.
    - left. reflexivity.
    - destruct H2. rewrite H2. apply Z.bits_0.
      rewrite H2. apply Z.bits_above_log2. lia. simpl. lia. }
    rewrite Z.lxor_spec. 
    assert (n = 0%Z \/ n > 0%Z) by lia.
    destruct H0.
    + subst. 
      assert (Z.testbit (2 * Z.lxor (Z.div2 q1) (Z.div2 q2)) 0 = false). {
      assert ((2 * Z.lxor (Z.div2 q1) (Z.div2 q2)) = (Z.shiftl (Z.lxor (Z.div2 q1) (Z.div2 q2)) 1)).
      reflexivity. rewrite H0. rewrite Z.shiftl_spec_low. reflexivity. lia. }
      rewrite H0. rewrite orb_false_r.
      rewrite Z.bit0_eqb. rewrite Z.bit0_eqb.
      pose proof (mod2_cases q1). pose proof (mod2_cases q2).
      destruct H1; destruct H2; rewrite H1; rewrite H2; simpl; reflexivity.
    + assert (Z.testbit (bitwise_xor (q1 mod 2) (q2 mod 2)) n = false). {
      assert ((bitwise_xor (q1 mod 2) (q2 mod 2) = 0%Z \/ 
      (bitwise_xor (q1 mod 2) (q2 mod 2)) = 1%Z)). 
       pose proof (mod2_cases q1).
    pose proof (mod2_cases q2).
    destruct H1; destruct H2; rewrite H1; rewrite H2; subst; simpl.
      - left. reflexivity.
      - right. reflexivity.
      - right. reflexivity.
      - left. reflexivity.
      - destruct H1. rewrite H1. apply Z.bits_0. rewrite H1.
        apply Z.bits_above_log2. lia. simpl. lia. }
    rewrite H1. simpl.
    assert ((2 * Z.lxor (Z.div2 q1) (Z.div2 q2)) = (Z.shiftl (Z.lxor (Z.div2 q1) (Z.div2 q2)) 1)).
    reflexivity. rewrite H2. clear H2. rewrite Z.shiftl_spec. 2: lia.
    rewrite Z.lxor_spec. rewrite <- Zbits.Ztestbit_succ. rewrite <- Zbits.Ztestbit_succ.
    replace (Z.succ (n - 1)) with n by lia. reflexivity. all: lia.
Qed.

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
 (*do this tomorrow i am too tired*)
Lemma xor_addition: forall q1 q2,
  0 <= q1 ->
  0 <= q2 ->
  poly_of_int (Z.lxor q1 q2) = (poly_of_int q1) +~ (poly_of_int q2).
Proof.
  intros. rewrite? poly_of_int_bits. unfold poly_add. exist_eq.
  simpl. symmetry. generalize dependent q2. revert H. apply bits_of_int_rect; intros; try lia.
  - unfold P.poly_add. rewrite P.poly_add_inter_nil_l. subst. simpl.
    rewrite P.wf_no_trailing_zeroes. reflexivity. apply bits_of_int_wf.
  - subst. rewrite xor_expand. simpl. symmetry. assert (1 mod 2 = 1%Z) by reflexivity. rewrite H1.
    assert (q2 = 0%Z \/ q2 = 1%Z \/ q2 > 1) by lia.
    destruct H2. subst. simpl. reflexivity. destruct H2. subst. reflexivity.
    pose proof (mod2_cases q2). destruct H3; rewrite H3.
    + unfold bitwise_xor; simpl.
      assert (Z.div2 q2 > 0). {
      assert (Z.div2 q2 = 0%Z \/ Z.div2 q2 < 0 \/ Z.div2 q2 > 0) by lia.
      destruct H4. apply div2_0_iff in H4. destruct H4; lia. destruct H4.
      rewrite Z.div2_neg in H4. lia. lia. }
    rewrite bits_of_int_equation. if_tac. lia. if_tac. lia. if_tac. lia.
    pose proof (odds_odd (Z.div2 q2)). rewrite H8.
    


    assert (Z.odd (1 + 2 * Z.div2 q2) = true). replace (1 + 2 * Z.div2 q2)  with
     (Z.succ (2 * Z.div2 q2)) by lia. rewrite Z.odd_succ.


 symmetry. generalize dependent H0. apply (bits_of_int_rect); intros; try lia.
    + subst. reflexivity.
    + subst. reflexivity.
    + 


 rewrite (bits_of_int_equation q2). if_tac. lia. if_tac. subst. simpl. reflexivity.
    if_tac. subst. reflexivity.
    destruct (Z.odd q2) eqn : E.
    +  simpl.



 simpl. simpl.
    lia.
    Search Z

 Search Z.lxor.  unfold P.poly_add.

  assert (forall z, 0 < z -> 

 unfold poly_of_int. 
  
  
  simpl.

(*need to show that poly_of_int (2 * poly) = x * poly_of_int poly

(Int.repr (Z.lxor (2 * prior) modulus))))) 


(** Verification of [generate_index_power_tables] *)

Definition fec_n : Z := proj1_sig (opaque_constant 128).
Definition fec_n_eq : fec_n = 128%Z := proj2_sig (opaque_constant _).
Hint Rewrite fec_n_eq : rep_lia.

(* i -> x^i % f in fec_2_index*)
Definition power_to_index_contents (bound : Z) :=
  (map Vint (map Int.repr (prop_list (fun z => 
      poly_to_int ( (monomial (Z.to_nat z)) %~ p128)) bound))).

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
    PROP (0 <= i < fec_n /\ 
      (forall z, 0 < z < fec_n -> find_power p128 (poly_of_int z) < i -> 
          Znth z l = find_power p128 (poly_of_int z)) /\
      Znth 0 l = 0%Z)
    LOCAL (temp _i (Vint (Int.repr i)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents i ++ map Vint (map Int.repr (list_repeat
      ((Z.to_nat fec_n) - Z.to_nat i)%nat 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
        data_at Ews tint (Vint (Int.repr modulus)) (gv _modulus);
       data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N))).
- Exists 0%Z. Exists (list_repeat (Z.to_nat fec_n) 0%Z). entailer!. split. 
  intros. pose proof (find_power_spec p128  p128_deg_pos p128_primitive (poly_of_int z)).
  assert (poly_of_int z <> zero). intro. rewrite poly_of_int_zero in H10. lia.
  specialize (H9 H10); clear H10.
  assert (deg (poly_of_int z) < deg p128). apply polys_deg_bounded. rep_lia.
  specialize (H9 H10); clear H10. destruct H9. lia.
  apply Znth_list_repeat_inrange. rep_lia.
  unfold power_to_index_contents. rewrite prop_list_0. simpl.
  replace ((Z.to_nat fec_n - 0)%nat) with (Z.to_nat fec_n) by rep_lia. entailer!.
- Intros i. Intros l. forward. forward_if. 2 : {
  forward. entailer!. lia.  }
  forward_if (PROP (0 <= i < fec_n /\ 
      (forall z, 0 < z < fec_n -> find_power p128 (poly_of_int z) < i -> 
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
      simpl. pose proof (Int.eqm_unsigned_repr n). unfold Int.eqm in H16.
      assert (n = Int.unsigned (Int.repr n)). eapply Zbits.eqmod_small_eq. apply H16.
      rep_lia. rep_lia. rep_lia. lia. rewrite prop_list_length. lia. lia.
      rewrite Zlength_map. rewrite prop_list_length. lia. lia.
      unfold power_to_index_contents. rewrite? Zlength_map.
      rewrite prop_list_length. lia. lia.
    * forward. forward. forward_if (PROP (0 <= i < fec_n /\ 
      (forall z, 0 < z < fec_n -> find_power p128 (poly_of_int z) < i -> 
          Znth z l = find_power p128 (poly_of_int z)) /\
      Znth 0 l = 0%Z)
    LOCAL (temp _i (Vint (Int.repr i)); gvars gv)
    SEP (data_at Ews (tarray tuchar fec_n) (power_to_index_contents (i + 1) ++ map Vint (map Int.repr (list_repeat
      ((Z.to_nat fec_n) - Z.to_nat (i + 1))%nat 0%Z))) (gv _fec_2_index);
        data_at Ews (tarray tuchar fec_n) (map Vint (map Int.repr l)) (gv _fec_2_power);
        data_at Ews tint (Vint (Int.repr modulus)) (gv _modulus);
       data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N))).
      -- forward. forward. entailer!. rewrite Znth_app1. 2 : {
         unfold power_to_index_contents. rewrite? Zlength_map.
         rewrite prop_list_length. lia. lia. }
         unfold power_to_index_contents at 2. rewrite Znth_map.
         rewrite Znth_map.
         rewrite prop_list_Znth. 2 : {
          lia. }
         simpl. unfold Int.shl. remember (poly_to_int (monomial (Z.to_nat (i - 1)) %~ p128)) as prior.
         pose proof (qpoly_128_bound (monomial (Z.to_nat (i - 1)) %~ p128)).
         assert (deg (monomial (Z.to_nat (i - 1)) %~ p128) < deg p128). apply pmod_lt_deg.
         apply p128_deg_pos. apply H17 in H18. clear H17. rewrite <- Heqprior in H18. 
         assert (Int.unsigned (Int.repr prior) = prior). {
         pose proof (Int.eqm_unsigned_repr prior).
         apply Int.eqm_sym in H17.
         unfold Int.eqm in H17. eapply Zbits.eqmod_small_eq. apply H17. rep_lia.
          rep_lia. }
         rewrite H17. 
         simpl. unfold Int.xor.
         assert (2 * prior = Int.unsigned (Int.repr (2 * prior))). {
         pose proof (Int.eqm_unsigned_repr (2 * prior)). unfold Int.eqm in H19.
         eapply Zbits.eqmod_small_eq. apply H19. rep_lia. rep_lia. }
         rewrite <- H19. 
         assert ((Int.unsigned (Int.repr modulus)) = modulus). { unfold modulus.
         pose proof (Int.eqm_unsigned_repr). unfold Int.eqm in H19.
         eapply Zbits.eqmod_small_eq. apply H20. rep_lia. rep_lia. }
         rewrite H20.
         rep_lia.
         
         Search p128.
         apply deg_p128_pos.
         
         rep_lia. Search  apply H17. apply Int.eqm_unsigned_repr.



Search (Int.shl (Int.repr _)). Search Z.shiftl. Search Int.shl.
         rewrite Int.shl_mul_two_p. simpl. Print two_power_pos.
         entailer!.
          



.
      -- forward. forward. entailer!.
      


 rewrite Z 
      rep_lia.
      list_simplify.
      list_solve.
      rep_lia.


 unfold Byte.max_unsigned. unfold Byte.modulus. simpl. Search (Int.unsigned (Int.repr _)). rep_lia. lia.
      rep_lia.

 simpl. 


 rep_lia. lia. rep_lia.
      apply pmod_deg.


 simpl.


 rep_lia.
      rep_lia. simpl.
      


 assert ( i <> 0%Z). apply repr_neq_e in H3.


 forward. 
    * entailer!. apply repr_neq_e in H3. unfold fec_n in *; rep_lia.
    * remember (128)%nat as n. entailer!.




    * rewrite Zlength_map. rewrite Zlength_map. list
     simpl.


 Print upd_Znth. Search Int.zero_ext.


 entailer!. rewrite nil_app_l.
    repeat(replace 128 with (fec_n) by reflexivity). simpl.



rep_lia.
    
  j


 entailer!. 
  + 
    
      


  forward_loop (EX i : Z,
    PROP(0 <= i < fec_n)
    LOCAL (temp _i (Vint (Int.repr i)); gvars gv)
    SEP (data_at Ews (tarray tuchar 128)
          ((map Vint (map Int.repr (prop_list (fun z => 
      poly_to_int ( (monomial (Z.to_nat z)) %~ (poly_of_int modulus))) i))) ++
          sublist (i) (fec_n) (map Vint (map Int.repr index_contents_init))) 
          (gv _fec_2_index);
   data_at Ews (tarray tuchar 128)
     (map Vint (map Int.repr power_contents_init)) 
     (gv _fec_2_power);
   data_at Ews tint (Vint (Int.repr modulus)) (gv _modulus);
   data_at Ews tint (Vint (Int.repr fec_n)) (gv _FEC_N))).
  - entailer!. Exists 0%Z. entailer!. simpl. rewrite sublist_same. entailer!. reflexivity.
    unfold fec_n. rewrite <- H0. reflexivity.
  - Intros i. forward. forward_if. 2 : {
    forward. rewrite Int.signed_repr in H0. rewrite Int.signed_repr in H0. lia.
    unfold fec_n. rep_lia. unfold fec_n in H. rep_lia. }
    forward_if True.
    + forward. entailer!. unfold fec_n in H. rewrite Int.signed_repr. rewrite Int.signed_repr. rep_lia.
      rep_lia. rep_lia. entailer!.


(*go back, write function poly -> index (for nonzero poly)
  then make definition for 2 specs so its cleaner
  spec for 2nd is similar (with prop_list)
  for loop invariant - we will just say, exists l,
  (forall z, 0 <= z < fec_c, index_of_poly (poly_of_int z) <= i -> Znth l z = index_of_poly (poly_of_int z))
  and l is stored in the global table

  so at the end of the loop, we get that: forall z, 0 <= z < fec, Znth l z = index_of_poly (poly_of_int z)
  want to show that this is equivalent (need iff) to prop_list*)
    j
    rep_lia.
    + 

 hint. help. Exists 0. Intros a. Exists 0. 
    
      











