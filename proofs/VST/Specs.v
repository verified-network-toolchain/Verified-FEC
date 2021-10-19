(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

Require Import VST.floyd.proofauto.

Require Import fec.
Require Import ByteField.
Require Import ZSeq.
Require Import ListMatrix.

Require Import MatrixTransform.
Require Import ByteFacts.
Require Import VandermondeByte.
Require Import CommonVST.
Require Import ReedSolomonList.

Instance CompSpecs : compspecs.
make_compspecs prog. Defined.

Definition Vprog : varspecs.
mk_varspecs prog. Defined.

(** Field tables*)

Definition INDEX_TABLES gv :=
  (data_at Ews (tarray tuchar fec_n) (map Vubyte byte_pows) (gv _fec_2_index) *
   data_at Ews (tarray tuchar fec_n) (map Vubyte byte_logs) (gv _fec_2_power))%logic.

Definition FIELD_TABLES gv :=
  (INDEX_TABLES gv *
   data_at Ews (tarray tuchar fec_n) (map Vubyte byte_invs) (gv _fec_invefec))%logic.

Definition FEC_TABLES gv :=
  (FIELD_TABLES gv * data_at Ews tint (Vint (Int.zero)) (gv _trace) *
  data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h) (rev_mx_val weight_mx) (gv _fec_weights))%logic.

Notation data_at_zeroes l v :=
  (data_at Ews (tarray tuchar l) (zseq l (Vubyte Byte.zero)) v).
Notation data_at_zeroes_2d m n v :=
  (data_at Ews (tarray (tarray tuchar m) n) (zseq n (zseq m (Vubyte Byte.zero))) v).

Definition fec_generate_weights_spec :=
  DECLARE _fec_generate_weights
  WITH gv : globals
  PRE [ ]
    PROP ()
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at Ews tint (Vint (Int.zero)) (gv _trace); FIELD_TABLES gv;
         data_at_zeroes_2d (fec_n - 1) fec_max_h (gv _fec_weights))
  POST [tvoid]
    PROP ()
    RETURN ()
    SEP (FEC_TABLES gv). 

(*We require that m * n is nonzero (or else we do not have weak_valid_pointers in the loop guards).
  We require that m > 0 since the last loop goes from 0 to m - 1 *)
Definition fec_matrix_transform_spec :=
  DECLARE _fec_matrix_transform
  WITH gv: globals, m : Z, n : Z, mx : list (list byte), s : val, sh: share
  PRE [ tptr tuchar, tuchar, tuchar]
    PROP (0 < m <= n; n <= Byte.max_unsigned; wf_lmatrix mx m n; strong_inv_list m n mx; writable_share sh)
    PARAMS (s; Vubyte (Byte.repr m); Vubyte (Byte.repr n))
    GLOBALS (gv)
    SEP (FIELD_TABLES gv;
         data_at sh (tarray tuchar (m * n)) (map Vubyte (flatten_mx mx)) s)
  POST [tint]
    PROP()
    RETURN (Vint Int.zero)
    SEP(FIELD_TABLES gv;
        data_at sh (tarray tuchar (m * n))(map Vubyte (flatten_mx (gauss_restrict_list m n mx))) s).

Definition fec_gf_mult_spec :=
  DECLARE _fec_gf_mult
  WITH gv: globals, b1 : byte, b2 : byte
  PRE [ tuchar, tuchar ]
    PROP ()
    PARAMS (Vubyte b1; Vubyte b2)
    GLOBALS (gv)
    SEP (INDEX_TABLES gv)
  POST [ tuchar ]
    PROP ()
    RETURN (Vubyte (byte_mul b1 b2))
    SEP (INDEX_TABLES gv).

Definition fec_generate_math_tables_spec :=
  DECLARE _fec_generate_math_tables
  WITH gv : globals
  PRE [ ]
    PROP ()
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at_zeroes fec_n (gv _fec_2_index); 
         data_at_zeroes fec_n (gv _fec_2_power);
         data_at_zeroes fec_n (gv _fec_invefec))
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

Definition rse_init_spec :=
  DECLARE _rse_init
  WITH gv: globals
  PRE []
    PROP ()
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at_zeroes fec_n (gv _fec_2_index);
         data_at_zeroes fec_n (gv _fec_2_power);
         data_at_zeroes fec_n (gv _fec_invefec);
         data_at_zeroes_2d (fec_n - 1) fec_max_h (gv _fec_weights);
         data_at Ews tint (Vint (Int.zero)) (gv _trace))
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (FEC_TABLES gv).

(*TODO: decide whether to use FEC_TABLES, which includes inverse*)
(*Since the packets are an unsigned char **, this is represented in memory as an array of pointers to
  arrays of unsigned chars. For our purposes, we would like to represent the contents in Coq as a list (list Z),
  so we need to iterate through each of these pointers with a [data_at]. So we additionally take in the list of pointers,
  and we use [iter_sepcon] to relate this list to the contents*)
(*Additionally, this specification is a bit involved. The parity packets can be described as follows:
  - take the [packets] list of lists, extend to a k x c matrix by adding necessary zeroes ([extend_mx])
  - take the first h rows and k columns of the weight matrix ([submatrix])
  - multiply these two matrices together ([list_matrix_multiply])*)
Definition fec_blk_encode_spec :=
  DECLARE _fec_blk_encode
  WITH gv: globals, k : Z, h : Z, c : Z, pd: val, pl : val, ps: val, packets: list (list byte), 
       lengths : list Z, packet_ptrs: list val, parity_ptrs: list val
  PRE [ tint, tint, tint, tptr (tptr tuchar), tptr (tint), tptr (tschar) ]
    PROP (0 < k < fec_n - fec_max_h; 0 <= h <= fec_max_h; 0 < c <= fec_max_cols; (*bounds for int inputs*)
          Zlength packet_ptrs = k;  (*lengths for arrays*)
          Forall (fun x => Zlength x <= c) packets;
          lengths = map (@Zlength byte) packets)
    PARAMS (Vint (Int.repr k); Vint (Int.repr h); Vint (Int.repr c); pd; pl; ps)
    GLOBALS (gv)
    SEP (iter_sepcon_arrays parity_ptrs (zseq h (zseq c Byte.zero));
         data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
         iter_sepcon_arrays packet_ptrs packets;
         data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl;
         data_at Ews (tarray tschar k) (zseq k (Vbyte Byte.zero)) ps;
         INDEX_TABLES gv; 
         data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h)  (rev_mx_val weight_mx) (gv _fec_weights))
  POST [ tint ]
    PROP ()
    RETURN (Vint Int.zero)
    SEP (iter_sepcon_arrays parity_ptrs (encoder_list h k c packets);
         data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
         iter_sepcon_arrays packet_ptrs packets;
         data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl;
         data_at Ews (tarray tschar k) (zseq k (Vbyte Byte.zero)) ps;
         INDEX_TABLES gv;
         data_at Ews (tarray (tarray tuchar (fec_n - 1)) fec_max_h)  (rev_mx_val weight_mx) (gv _fec_weights)).

(*We still include h to make the spec nicer; it is not an input to the function, but we can always pass in
  Zlength parities when using the spec*)
Definition fec_blk_decode_spec :=
  DECLARE _fec_blk_decode
  WITH gv: globals, k : Z, h : Z, c : Z, parbound: Z, pd: val, pl : val, ps: val, packets: list (list byte), 
       parities: list (option (list byte)), lengths : list Z, stats: list byte, packet_ptrs: list val, 
       parity_ptrs: list val
  PRE [ tint, tint, tptr (tptr tuchar), tptr (tint), tptr (tschar) ]
    PROP (0 < k < fec_n - fec_max_h; 0 <= h <= fec_max_h; 0 < c <= fec_max_cols; 0 <= parbound <= h; (*bounds for int inputs*)
          Zlength packet_ptrs = k; Zlength parities = h; (*lengths for arrays*)
          Forall (fun x => Zlength x <= c) packets;
          lengths = map (@Zlength byte) packets;
          Zlength (filter (fun x => Z.eq_dec (Byte.signed x) 1) stats) = 
          Zlength (filter ssrbool.isSome (sublist 0 parbound parities));
          forall (i: Z), 0 <= i < h -> Znth i parities = None <-> Znth i parity_ptrs = nullval;
          forall (i: Z) (l: list byte), 0 <= i < h -> Znth i parities = Some l -> Zlength l = c;
          Forall (fun x => x = Byte.zero \/ x = Byte.one) stats)
    PARAMS (Vint (Int.repr k); Vint (Int.repr c); pd; pl; ps)
    GLOBALS (gv)
    SEP (iter_sepcon_arrays packet_ptrs packets;
         iter_sepcon_options parity_ptrs parities;
         data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
         data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl;
         data_at Ews (tarray tschar k) (map Vbyte stats) ps;
         FEC_TABLES gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (Zlength (filter (fun x => Z.eq_dec (Byte.signed x) 1) stats)))) (*this is xh*)
    SEP (iter_sepcon_arrays packet_ptrs (decoder_list k c packets parities stats lengths parbound) ;
         iter_sepcon_options parity_ptrs parities;
         data_at Ews (tarray (tptr tuchar) (k + h)) (packet_ptrs ++ parity_ptrs) pd;
         data_at Ews (tarray tint k) (map Vint (map Int.repr lengths)) pl;
         data_at Ews (tarray tschar k) (zseq k (Vbyte Byte.zero)) ps;
         FEC_TABLES gv).


Definition Gprog := [fec_generate_math_tables_spec; fec_find_mod_spec; fec_gf_mult_spec; fec_matrix_transform_spec;
  fec_generate_weights_spec; rse_init_spec; fec_blk_encode_spec; fec_blk_decode_spec].

