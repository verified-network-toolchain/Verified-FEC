(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

Require Import VST.floyd.proofauto.

Require Import fpga.
Require Import ByteFacts.
Require Import ByteField.
Require Import ZSeq.
Require Import Preds.
Require Import ReedSolomonList.

(*Remaining constants - these should not affect correctness of anything as long as everything is consistent *)
Definition batches : Z := proj1_sig (opaque_constant 300).
Definition batches_eq : batches = 300%Z := proj2_sig (opaque_constant _).
Hint Rewrite batches_eq : rep_lia.
Definition max_packet_size : Z := proj1_sig (opaque_constant 100).
Definition max_packet_size_eq : max_packet_size = 100%Z := proj2_sig (opaque_constant _).
Hint Rewrite max_packet_size_eq : rep_lia.

Instance CompSpecs : compspecs.
make_compspecs prog. Defined.

Definition Vprog : varspecs.
mk_varspecs prog. Defined.

(** Field tables*)

Definition INDEX_TABLES gv :=
  (data_at Ews (tarray tuchar fec_n) (map Vubyte byte_pows) (gv _fec_2_index) *
   data_at Ews (tarray tuchar fec_n) (map Vubyte byte_logs) (gv _fec_2_power))%logic.

Definition mult_spec :=
  DECLARE _mult
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

Definition generate_field_tables_spec :=
  DECLARE _generate_field_tables
  WITH gv : globals
  PRE [ ]
    PROP ()
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at Ews (tarray tuchar fec_n) (zseq fec_n (Vubyte Byte.zero)) (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) (zseq fec_n (Vubyte Byte.zero)) (gv _fec_2_power))
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (INDEX_TABLES gv).

Definition initialize_spec :=
  DECLARE _initialize
  WITH gv : globals
  PRE [ ]
    PROP ()
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at Ews (tarray tuchar fec_n) (zseq fec_n (Vubyte Byte.zero)) (gv _fec_2_index);
         data_at Ews (tarray tuchar fec_n) (zseq fec_n (Vubyte Byte.zero)) (gv _fec_2_power))
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.zero))
    SEP (INDEX_TABLES gv).

(** start_batch *)

Definition buffer_vals (b: list (list (list byte))) : list (list (list val)) :=
  map (fun x => map (fun y => map Vubyte y) x) b.

Definition start_batch_spec :=
  DECLARE _start_batch
  WITH gv : globals, buffer : list (list (list byte)), batchnum : Z, k : Z, h : Z, batch_size : Z,
    buffer' : list (list (list byte))
  PRE [ tuint, tuint, tuint, tuint ]
    PROP (0 <= k < fec_k; 0 <= h < fec_h; 0 <= batchnum < batches; 0 <= batch_size < max_packet_size)
    PARAMS (Vint (Int.repr batchnum); Vint (Int.repr k); Vint (Int.repr h); Vint (Int.repr batch_size))
    GLOBALS (gv)
    SEP (data_at Ews (tarray (tarray (tarray tuchar max_packet_size) fec_h) batches) 
          (buffer_vals buffer) (gv _parity_buffers))
  POST [ tint ]
    PROP (buffer_filled buffer' batchnum nil empty_packets batch_size;
          old_new_buffers buffer buffer' batchnum)
    RETURN (Vint (Int.zero))
    SEP (data_at Ews (tarray (tarray (tarray tuchar max_packet_size) fec_h) batches) 
          (buffer_vals buffer') (gv _parity_buffers)).

(** encode_packet *)

Definition _encode_packet_spec :=
  DECLARE _encode_packet
  WITH gv : globals, old_buffer : list (list (list byte)), batchnum : Z, j : Z, packet_size : Z, packet : list byte,
    batch_size : Z, packets : list (list byte), indices : list Z, packet_ptr: val,
    new_buffer : list (list (list byte))
  PRE [ tuint, tuint, tuint, tptr tuchar ]
    PROP (0 <= batchnum < batches; 0 <= j < fec_k; packet_size <= batch_size; ~ In j indices;
          buffer_filled old_buffer batchnum indices packets batch_size)
    PARAMS (Vint (Int.repr batchnum); Vint (Int.repr j); Vint (Int.repr packet_size); packet_ptr)
    GLOBALS (gv)
    SEP (data_at Ews (tarray tuchar packet_size) (map Vubyte packet) packet_ptr;
         data_at Ews (tarray (tarray (tarray tuchar max_packet_size) fec_h) batches) 
          (buffer_vals old_buffer) (gv _parity_buffers))
  POST [ tint ]
    PROP (buffer_filled new_buffer batchnum (j :: indices) (upd_Znth j packets packet) batch_size;
          old_new_buffers old_buffer new_buffer batchnum)
    RETURN (Vint (Int.zero))
    SEP (data_at Ews (tarray tuchar packet_size) (map Vubyte packet) packet_ptr;
         data_at Ews (tarray (tarray (tarray tuchar max_packet_size) fec_h) batches) 
          (buffer_vals new_buffer) (gv _parity_buffers)).

(** encode_parity *)
Definition _encode_parity_spec:=
  DECLARE _encode_parity
  WITH gv : globals, buffer : list (list (list byte)), batchnum : Z, packet_size : Z, i : Z,
    batch_size : Z, packets : list (list byte), indices : list Z, parity_ptr: val, parity: list val
  PRE [ tuint, tuint, tuint, tptr tuchar ]
    PROP (0 <= batchnum < batches; 0 <= i < fec_h; packet_size <= batch_size;
          Forall (fun p => Zlength p <= packet_size) packets; Zlength indices = fec_k;
          buffer_filled buffer batchnum indices packets batch_size)
    PARAMS (Vint (Int.repr batchnum); Vint (Int.repr packet_size); Vint (Int.repr i); parity_ptr)
    GLOBALS (gv)
    SEP (data_at Ews (tarray tuchar packet_size) parity parity_ptr;
         data_at Ews (tarray (tarray (tarray tuchar max_packet_size) fec_h) batches) 
          (buffer_vals buffer) (gv _parity_buffers))
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.zero))
    SEP (data_at Ews (tarray tuchar packet_size) 
          (map Vubyte  (Znth i (encoder_list fec_h fec_k packet_size packets))) parity_ptr;
         data_at Ews (tarray (tarray (tarray tuchar max_packet_size) fec_h) batches) 
          (buffer_vals buffer) (gv _parity_buffers)).


Definition Gprog := [mult_spec; generate_field_tables_spec].

