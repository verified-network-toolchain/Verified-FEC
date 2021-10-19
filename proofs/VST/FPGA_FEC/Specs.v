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

