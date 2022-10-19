Require Import AbstractEncoderDecoder.
Require Import DecoderGeneric.
Require Import VST.floyd.functional_base.
Require Import ByteFacts.
Require Import Block.


From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.

Definition triv_upd_time : Z -> fpacket -> list block -> Z :=
  fun z _ _ => z.

Definition triv_timeout : Z -> block -> bool :=
  fun _ _ => true.

Definition decoder_one_step_nto :=
  decoder_one_step_gen triv_upd_time triv_timeout.

Definition decoder_multiple_steps_nto:=
  decoder_multiple_steps_gen triv_upd_time triv_timeout.
Definition decoder_all_steps_nto:=
  decoder_all_steps_gen triv_upd_time triv_timeout.