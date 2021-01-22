Require Import VST.floyd.proofauto.

Require Import Common.
Require Import fec.

Import WPoly.

Instance CompSpecs : compspecs.
make_compspecs prog. Defined.

Definition Vprog : varspecs.
mk_varspecs prog. Defined.

(*We require that m * n is nonzero (or else we do not have weak_valid_pointers in the loop guards). *)
Definition fec_matrix_transform_spec :=
  DECLARE _fec_matrix_transform
  WITH gv: globals, m : Z, n : Z, mx : matrix F, s : val
  PRE [ tptr tuchar, tuchar, tuchar]
    PROP (0 < m * n /\ (0 <= m <= n) /\ n <= Byte.max_unsigned /\ (wf_matrix mx m n) /\ (strong_inv_list m n mx 0))
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

(*Functions for working with memory - we need the Compspecs for these, so they are here, not in Common*)

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