(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
(*Functions for working with arrays and memory in VST that are generic*)

(*These first two are not directly related to VST but are used in the later proofs*)
Lemma Zlength_concat: forall {A: Type} (n m : Z) (l: list (list A)),
  Zlength l = n ->
  Forall (fun x => Zlength x = m) l ->
  Zlength (concat l) = n * m.
Proof.
  intros A m n l. revert m. induction l; intros.
  - list_solve.
  - simpl. rewrite Zlength_app. rewrite (IHl (m-1)). 2: list_solve.
    assert (Zlength a = n). inversion H0; subst; reflexivity. rewrite H1. lia. inversion H0; auto.
Qed. 

Lemma lt_plus_lt: forall z1 z2 z3, 
  0 <= z1 -> 
  z1 + z2 < z3 -> 
  z2 < z3.
Proof.
  intros z1 z2 z3 Hz1 Hz12. rewrite Z.lt_add_lt_sub_r in Hz12. lia.
Qed.

Lemma typed_false_not_true: forall a b, typed_false a b -> ~(typed_true a b).
Proof.
  intros a b F T.
  unfold typed_true in T; unfold typed_false in F; rewrite T in F; inversion F.
Qed. 

(** Facts about [combine]*)
(*This function is in the standard library, but we need a few results about how functions like Znth, Zlength,
  and sublist work with combine*)
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

Section VSTFacts.

Context {Comp : compspecs}.

Lemma remove_upd_Znth: forall {A: Type} (l: list A) (i : Z) (x: A),
  0 <= i < Zlength l ->
  remove_nth i (upd_Znth i l x) = remove_nth i l.
Proof. 
  intros. unfold remove_nth.
  rewrite sublist_upd_Znth_l by lia.
  rewrite Zlength_upd_Znth, sublist_upd_Znth_r by lia. 
  reflexivity.
Qed. 

(* We want a similar definition for when only some of the data exists, and the others are null pointers*)

Definition iter_sepcon_options (ptrs: list val) (contents: list (option (list byte))) : mpred :=
  iter_sepcon (fun (x: option (list byte) * val) => let (o, ptr) := x in
    match o with
      | None => emp
      | Some l => data_at Ews (tarray tuchar (Zlength l)) (map Vubyte l) ptr
    end) (combine contents ptrs).

Lemma iter_sepcon_options_remove_one: forall ptrs contents i l,
  Zlength ptrs = Zlength contents ->
  0 <= i < Zlength contents ->
  Znth i contents = Some l ->
  iter_sepcon_options ptrs contents = 
    (data_at Ews (tarray tuchar (Zlength l)) (map Vubyte l) (Znth i ptrs) *
    iter_sepcon_options (remove_nth i ptrs) (remove_nth i contents))%logic.
Proof.
  intros ptrs contents i l Hlens Hi Hnth. unfold iter_sepcon_options. rewrite (iter_sepcon_remove_one _ _ i).
  destruct (Znth i (combine contents ptrs)) as [o ptr] eqn : Hnth'.
  rewrite combine_Znth in Hnth' by auto. inversion Hnth'; subst. rewrite Hnth.
  rewrite combine_remove_nth by lia. reflexivity. rewrite combine_Zlength; lia.
Qed.

End VSTFacts.
