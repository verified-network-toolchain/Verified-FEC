Require Import VST.floyd.proofauto.

Require Import Common.
Require Import VandermondeList.
Require Import fec.

Import WPoly.

Instance CompSpecs : compspecs.
make_compspecs prog. Defined.

Definition Vprog : varspecs.
mk_varspecs prog. Defined.

Definition fec_generate_weights_spec :=
  DECLARE _fec_generate_weights
  WITH gv : globals
  PRE [ ]
    PROP ()
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at Ews (tint) (Vint (Int.zero)) (gv _trace);
         data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
         data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
         data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) 
            (list_repeat (Z.to_nat fec_max_h) (list_repeat (Z.to_nat (fec_n -1)) (Vint Int.zero))) (gv _fec_weights))
  POST [tvoid]
    PROP ()
    RETURN ()
    SEP (data_at Ews (tint) (Vint (Int.zero)) (gv _trace);
         data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power);
         data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec);
         data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) 
            (rev_mx_val (gauss_restrict_rows 
            (weight_mx_list fec_max_h  (fec_n - 1)) fec_max_h)) (gv _fec_weights)).

(*We require that m * n is nonzero (or else we do not have weak_valid_pointers in the loop guards).
  We require that m > 0 since the last loop goes from 0 to m - 1 *)
Definition fec_matrix_transform_spec :=
  DECLARE _fec_matrix_transform
  WITH gv: globals, m : Z, n : Z, mx : matrix F, s : val
  PRE [ tptr tuchar, tuchar, tuchar]
    PROP (0 < m /\ 0 < m * n /\ (0 <= m <= n) /\ n <= Byte.max_unsigned /\ (wf_matrix mx m n) /\ (strong_inv_list m n mx 0))
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

Definition Gprog := [fec_find_mod_spec; fec_generate_math_tables_spec; fec_matrix_transform_spec; fec_gf_mult_spec; 
  fec_generate_weights_spec].

