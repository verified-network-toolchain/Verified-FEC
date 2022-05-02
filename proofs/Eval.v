(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

Require Import Specs.
Require Import ReedSolomonList.
Require Import Verif_decode.
Require Import Verif_encode.
Require Import ReedSolomon.

(* VST/CompCert require several axioms. Some are related to the real numbers; some are
  standard (propositional and functional extensionality, law of the excluded middle, and [eq_rect_eq].
  We do not add any axioms beyond these. *)

(* VST Specs: *)
Require Import String.
Local Open Scope string_scope.

Goal True.

idtac "Encoder VST Spec Axioms:".
idtac " ".
Print Assumptions fec_blk_encode_spec.
idtac " ".
idtac "Decoder VST Spec Axioms:".
idtac " ".
Print Assumptions fec_blk_decode_spec.
idtac " ".

(* VST funspec proofs: *)
idtac "Encoder VST Proof Axioms:".
idtac " ".
Print Assumptions body_fec_blk_encode.
idtac " ".
idtac "Decoder VST Proof Axioms:".
idtac " ".
Print Assumptions body_fec_blk_decode.
idtac " ".

(* Decoder correctness theorem *)
idtac "Decoder Correctness Theorem Axioms:".
idtac " ".
Print Assumptions decoder_list_correct.
idtac " ".

(* The high-level correctness theorem (using only MathComp and no VST) requires no axioms: *)
idtac "High-level correctness theorem axioms:".
idtac " ".
Print Assumptions decoder_correct.
idtac " ".

Abort.




