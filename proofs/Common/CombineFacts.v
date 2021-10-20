(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)
Require Import VST.floyd.functional_base.
(** Facts about [combine]*)
(*This function is in the standard library, but we need a few results about how functions like Znth, Zlength,
  and sublist work with combine*)
(* This file is separate because we don't want CommonVST to depend on the rest of the files *)
Lemma combine_Zlength: forall {A B : Type} (l1: list A) (l2: list B),
  Zlength l1 = Zlength l2 ->
  Zlength (combine l1 l2) = Zlength l1.
Proof.
  intros A B l1 l2 Hlen. rewrite !Zlength_correct in *. rewrite combine_length. lia.
Qed.

Lemma combine_Znth: forall {A B: Type} `{Inhabitant A} `{Inhabitant B} (l1 : list A) (l2: list B) i,
  Zlength l1 = Zlength l2 ->
  0 <= i < Zlength l1 ->
  Znth i (combine l1 l2) = (Znth i l1, Znth i l2).
Proof.
  intros. rewrite <- !nth_Znth. apply combine_nth. rewrite <- !ZtoNat_Zlength; lia.
  lia. lia. rewrite combine_Zlength; lia.
Qed. 

Lemma combine_sublist: forall {A B: Type} `{Inhabitant A} `{Inhabitant B} (lo hi : Z) (l1 : list A) (l2: list B),
  Zlength l1 = Zlength l2 ->
  0 <= lo <= hi ->
  hi <= Zlength l1 ->
  combine (sublist lo hi l1) (sublist lo hi l2) = sublist lo hi (combine l1 l2).
Proof.
  intros A B Hinh1 Hinh2 lo hi l1 l2 Hlen Hhilo Hhi.
  assert (Hsublen: Zlength (combine (sublist lo hi l1) (sublist lo hi l2)) = hi - lo). {
   rewrite combine_Zlength by (rewrite !Zlength_sublist; lia). list_solve. }
  apply Znth_eq_ext. rewrite Hsublen. rewrite Zlength_sublist; try lia.
  rewrite combine_Zlength; lia.
  intros i Hi. rewrite Hsublen in Hi. rewrite combine_Znth by list_solve.
  rewrite !Znth_sublist by lia. rewrite combine_Znth by lia. reflexivity.
Qed.

Lemma combine_app: forall {A B: Type} `{Inhabitant A} `{Inhabitant B} (l1 l3: list A) (l2 l4: list B),
  Zlength l1 = Zlength l2 ->
  Zlength l3 = Zlength l4 ->
  combine (l1 ++ l3) (l2 ++ l4) = combine l1 l2 ++ combine l3 l4.
Proof.
  intros A B Hin1 Hin2 l1 l3 l2 l4 Hlen1 Hlen3.
  apply Znth_eq_ext.
  - rewrite !combine_Zlength by list_solve. rewrite !Zlength_app. rewrite !combine_Zlength; list_solve.
  - intros i Hilen. rewrite combine_Zlength in Hilen by list_solve. rewrite combine_Znth by list_solve.
    assert (0 <= i < Zlength l1 \/ Zlength l1 <= i < Zlength l1 + Zlength l3) by list_solve.
    destruct H as [Hfst | Hsnd].
    + rewrite !Znth_app1; try lia. rewrite combine_Znth by lia. reflexivity.
      rewrite combine_Zlength; lia.
    + rewrite !Znth_app2; try lia. rewrite combine_Znth; try lia. all: rewrite combine_Zlength; try lia.
      rewrite Hlen1. reflexivity.
Qed.