Require Import VST.floyd.proofauto.

Require Import fec.
Require Import ByteField.
Require Import ZSeq.
(*
Require Import Common.
Require Import CommonVST.
Require Import VandermondeList.
Require Import fec.
Require Import Poly.
Require Import List2D.
*)
Instance CompSpecs : compspecs.
make_compspecs prog. Defined.

Definition Vprog : varspecs.
mk_varspecs prog. Defined.

(** Constants*)

Definition modulus : Z := proj1_sig (opaque_constant 285).
Definition modulus_eq : modulus = 285%Z := proj2_sig (opaque_constant _).

Definition fec_max_h : Z := proj1_sig (opaque_constant 128).
Definition fec_max_h_eq : fec_max_h = 128%Z := proj2_sig (opaque_constant _).

Definition fec_max_cols : Z := proj1_sig (opaque_constant 16000).
Definition fec_max_cols_eq: fec_max_cols = 16000%Z := proj2_sig(opaque_constant _).

Hint Rewrite fec_n_eq : rep_lia.
Hint Rewrite fec_max_h_eq : rep_lia.
Hint Rewrite modulus_eq : rep_lia.
Hint Rewrite fec_max_cols_eq : rep_lia.

(** Field tables*)

Definition INDEX_TABLES gv :=
  (data_at Ews (tarray tuchar fec_n) (map Vubyte byte_pows) (gv _fec_2_index) *
   data_at Ews (tarray tuchar fec_n) (map Vubyte byte_logs) (gv _fec_2_power))%logic.

Definition FIELD_TABLES gv :=
  (INDEX_TABLES gv *
   data_at Ews (tarray tuchar fec_n) (map Vubyte byte_invs) (gv _fec_invefec))%logic.

(*
(*For multiplication, we do not need the inverse table*)
Definition INDEX_TABLES gv :=
   (data_at Ews (tarray tuchar fec_n) (power_to_index_contents fec_n) (gv _fec_2_index) *
      data_at Ews (tarray tuchar fec_n) index_to_power_contents (gv _fec_2_power))%logic.


(*In most of the functions, we need the three field tables to be populated*)
Definition FIELD_TABLES gv :=
  (INDEX_TABLES gv * 
      data_at Ews (tarray tuchar fec_n) (inverse_contents fec_n) (gv _fec_invefec))%logic.

Definition fec_generate_weights_spec :=
  DECLARE _fec_generate_weights
  WITH gv : globals
  PRE [ ]
    PROP ()
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at Ews (tint) (Vint (Int.zero)) (gv _trace); FIELD_TABLES gv;
         data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) 
            (list_repeat (Z.to_nat fec_max_h) (list_repeat (Z.to_nat (fec_n -1)) (Vint Int.zero))) (gv _fec_weights))
  POST [tvoid]
    PROP ()
    RETURN ()
    SEP (data_at Ews (tint) (Vint (Int.zero)) (gv _trace); FIELD_TABLES gv;
         data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h)  (rev_mx_val weight_mx) (gv _fec_weights)).

(*We require that m * n is nonzero (or else we do not have weak_valid_pointers in the loop guards).
  We require that m > 0 since the last loop goes from 0 to m - 1 *)
Definition fec_matrix_transform_spec :=
  DECLARE _fec_matrix_transform
  WITH gv: globals, m : Z, n : Z, mx : matrix F, s : val
  PRE [ tptr tuchar, tuchar, tuchar]
    PROP (0 < m <= n; n <= Byte.max_unsigned; wf_matrix mx m n; strong_inv_list m n mx 0)
    PARAMS (s; Vint (Int.repr m); Vint (Int.repr n))
    GLOBALS (gv)
    SEP (FIELD_TABLES gv;
         data_at Ews (tarray tuchar (m * n))(map Vint (map Int.repr (flatten_mx mx))) s)
  POST [tint]
    PROP()
    RETURN (Vint Int.zero)
    SEP(FIELD_TABLES gv;
        data_at Ews (tarray tuchar (m * n)) 
          (map Vint (map Int.repr (flatten_mx (gauss_restrict_rows m n mx)))) s).

Definition fec_gf_mult_spec :=
  DECLARE _fec_gf_mult
  WITH gv: globals, f : Z, g : Z
  PRE [ tuchar, tuchar ]
    PROP (0 <= f < fec_n; 0 <= g < fec_n)
    PARAMS (Vint (Int.repr f); Vint (Int.repr g))
    GLOBALS (gv)
    SEP (INDEX_TABLES gv)
  POST [ tuchar ]
    PROP ()
    RETURN (Vint (Int.repr (poly_to_int (((poly_of_int f) *~ (poly_of_int g)) %~ mod_poly ))))
    SEP (INDEX_TABLES gv).*)

Definition fec_generate_math_tables_spec :=
  DECLARE _fec_generate_math_tables
  WITH gv : globals
  PRE [ ]
    PROP ()
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at Ews (tarray tuchar fec_n) (zseq fec_n (Vubyte Byte.zero)) (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) (zseq fec_n (Vubyte Byte.zero)) (gv _fec_2_power);
         data_at Ews (tarray tuchar fec_n) (zseq fec_n (Vubyte Byte.zero)) (gv _fec_invefec))
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (FIELD_TABLES gv).

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
(*
Definition rse_init_spec :=
  DECLARE _rse_init
  WITH gv: globals
  PRE []
    PROP ()
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at Ews (tarray tuchar fec_n) (list_repeat (Z.to_nat fec_n) (Vint Int.zero)) (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) (list_repeat (Z.to_nat fec_n) (Vint Int.zero)) (gv _fec_2_power);
         data_at Ews (tarray tuchar fec_n) (list_repeat (Z.to_nat fec_n) (Vint Int.zero)) (gv _fec_invefec);
         data_at Ews tint (Vint (Int.zero)) (gv _trace);
         data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) 
            (list_repeat (Z.to_nat fec_max_h) (list_repeat (Z.to_nat (fec_n -1)) (Vint Int.zero))) (gv _fec_weights))
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (FIELD_TABLES gv; data_at Ews tint (Vint (Int.zero)) (gv _trace);
         data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h)  (rev_mx_val weight_mx) (gv _fec_weights)).

(*Since the packets are an unsigned char **, this is represented in memory as an array of pointers to
  arrays of unsigned chars. For our purposes, we would like to represent the contents in Coq as a list (list Z),
  so we need to iterate through each of these pointers with a [data_at]. So we additionally take in the list of pointers,
  and we use [iter_sepcon] to relate this list to the contents*)
(*Additionally, this specification is quite involved. The parity packets can be described as follows:
  - take the [packets] list of lists, interpret as a list of lists of qpolys ([int_to_poly_mx])
  - extend to a k x c matrix by adding necessary zeroes ([extend_mx])
  - take the first h rows and k columns of the weight matrix ([submatrix])
  - multiply these two matrices together ([list_matrix_multiply]
  - convert the result back to a list list Z, which will be stored in memory ([norev_mx]*)
Definition fec_blk_encode_spec :=
  DECLARE _fec_blk_encode
  WITH gv: globals, k : Z, h : Z, c : Z, pd: val, pl : val, ps: val, packets: list (list Z), parities : list (list Z),
        lengths : list Z, packet_ptrs: list val, parity_ptrs: list val
  PRE [ tint, tint, tint, tptr (tptr tuchar), tptr (tint), tptr (tschar) ]
    PROP (0 < k < fec_n - fec_max_h; 0 <= h <= fec_max_h; 0 < c <= fec_max_cols; (*bounds for int inputs*)
          Zlength packets = k; Zlength packet_ptrs = k; Zlength parity_ptrs = h; 
          Zlength parities = h; (*lengths for arrays*)
          Forall (fun x => Zlength x <= c) packets; Forall (fun x => Zlength x = c) parities;
          Forall2D (fun z => 0 <= z <= Byte.max_unsigned) parities;
          Forall2D (fun z => 0 <= z <= Byte.max_unsigned) packets; 
          forall (i: Z), 0 <= i < k -> Znth i lengths = Zlength (Znth i packets))
    PARAMS (Vint (Int.repr k); Vint (Int.repr h); Vint (Int.repr c); pd; pl; ps)
    GLOBALS (gv)
    SEP (iter_sepcon_arrays parity_ptrs parities; (*since this is changing, it is helpful to have it first*)
         data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
         iter_sepcon_arrays packet_ptrs packets;
         data_at Ews (tarray tint k) (map Vint (map Int.repr (lengths))) pl;
         data_at Ews (tarray tschar k) (list_repeat (Z.to_nat k) (Vint (Int.zero))) ps;
         INDEX_TABLES gv; 
         data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h)  (rev_mx_val weight_mx) (gv _fec_weights))
  POST [ tint ]
    PROP ()
    RETURN (Vint Int.zero)
    SEP (iter_sepcon_arrays parity_ptrs (norev_mx (encode_list_mx h k c packets));
         data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
         iter_sepcon_arrays packet_ptrs packets;
         data_at Ews (tarray tint k) (map Vint (map Int.repr (lengths))) pl;
         data_at Ews (tarray tschar k) (list_repeat (Z.to_nat k) (Vint (Int.zero))) ps;
         INDEX_TABLES gv;
         data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h)  (rev_mx_val weight_mx) (gv _fec_weights)).
          
Definition Gprog := [fec_find_mod_spec; fec_generate_math_tables_spec; fec_matrix_transform_spec; fec_gf_mult_spec; 
  fec_generate_weights_spec; rse_init_spec; fec_blk_encode_spec].*)
Definition Gprog := [fec_generate_math_tables_spec; fec_find_mod_spec].

