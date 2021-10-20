(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

(*A computable version of the weight matrix. The regular weight matrix uses mathcomp operations, so it is
  not computable. But we want to prove that a statically-allocated array literal is equivalent to the weight
  matrix, so we need to compute concrete values*)

Require Import VST.floyd.functional_base.
From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.matrix.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import ListMatrix.
Require Import ByteField.
Require Import VandermondeByte.
Require Import CombineFacts.
Require Import ZSeq.

(*First, we need a computable version of Restricted Gaussian Elimination. We want this to be reasonably fast*)
(*So we don't call mk_lmatrix in a loop, which is very slow, since it traverses all n^2 elements each time (and calls
  get at each one). We use direct list ops to make it faster *)

Section GaussElim.

Local Open Scope ring_scope.

Variable pows : seq byte.
Variable logs : seq byte.
Variable invs : seq byte.

Definition binv_fast b := Znth (Byte.unsigned b) invs.

Lemma binv_fast_correct: forall b,
  invs = byte_invs ->
  binv_fast b = b^-1.
Proof.
  move => b Hinv. rewrite /binv_fast Hinv byte_invs_elts; try rep_lia. by rewrite Byte.repr_unsigned.
Qed. 

Notation bmul_fast := (byte_mul_fast pows logs).

(*[all_cols_one]*)

Definition all_cols_one_fast (mx: lmatrix B) c :=
  map (fun (row: seq byte) => let inv := Znth c row in map (fun x => (bmul_fast (binv_fast inv) x)) row) mx.

Lemma all_cols_one_fast_wf: forall m n mx c,
  wf_lmatrix mx m n ->
  wf_lmatrix (all_cols_one_fast mx c) m n.
Proof.
  move => m n mx c. rewrite /wf_lmatrix /rect /all_cols_one_fast !Zlength_map //.
  move => [Hm [Hn Hall]]. repeat split => [//|]. move: Hall. rewrite !Forall_Znth !Zlength_map.
  move => Hall i Hi. rewrite Znth_map // Zlength_map. by apply Hall.
Qed.

(*[sub_all_rows]*)

Fixpoint combineWith {A B C: Type} (s1 : seq A) (s2: seq B) (f: A -> B -> C) : seq C :=
  match s1, s2 with
  | h1 :: t1, h2 :: t2 => f h1 h2 :: combineWith t1 t2 f
  | _, _ => nil
  end.

(*So we don't need to prove separate properties about this *)
Lemma combineWith_equiv: forall {A B C} s1 s2 (f: A -> B -> C),
  combineWith s1 s2 f = map (fun (t: A * B) => let (x, y) := t in f x y) (combine s1 s2).
Proof.
  move => A B C s1 s2 f. move: s2. elim : s1 => [//= | h t /= IH s2].
  case : s2 => [//= | h1 t1]. by rewrite map_cons IH.
Qed.

Definition sub_all_rows_fast (mx: lmatrix B) r :=
  (*Slightly slower, but we don't know what row r is when we are mapping*)
  let old_row := Znth r mx in
  let new_mx := map (fun (row: seq byte) => combineWith old_row row Byte.xor) mx in
  upd_Znth r new_mx old_row.

Lemma sub_all_rows_fast_wf: forall m n mx r,
  0 <= r < m ->
  wf_lmatrix mx m n ->
  wf_lmatrix (sub_all_rows_fast mx r) m n.
Proof.
  move => m n mx r Hr. rewrite /wf_lmatrix/rect/sub_all_rows_fast !Zlength_upd_Znth !Zlength_map. move => [Hm [Hn Hall]].
  repeat split => [//|]. move: Hall. rewrite !Forall_Znth Zlength_upd_Znth Zlength_map. 
  move => Hall i Hi. case (Z.eq_dec i r) => [Heq /= | Hneq /=].
  - rewrite Heq upd_Znth_same //. by apply Hall; subst. by rewrite Zlength_map; subst.
  - rewrite upd_Znth_diff // ?Zlength_map //; [|by subst]. rewrite Znth_map // combineWith_equiv
    Zlength_map combine_Zlength // !Hall //; lia.
Qed.

(* [gauss_all_steps_list]*)
Definition gauss_all_steps_list_fast m (mx: lmatrix B) :=
  fold_left (fun acc r => let A1 := (all_cols_one_fast acc r) in sub_all_rows_fast A1 r) (Ziota 0 m) mx.

Lemma gauss_all_steps_list_fast_wf: forall m n mx,
  wf_lmatrix mx m n ->
  wf_lmatrix (gauss_all_steps_list_fast m mx) m n.
Proof.
  move => m n mx Hwf. apply mx_foldl_wf' => [mx' i Hi Hwf'| //|x].
  - rewrite /=. apply sub_all_rows_fast_wf => [//|]. by apply all_cols_one_fast_wf.
  - rewrite Ziota_In; try lia. move: Hwf. rewrite /wf_lmatrix/rect. list_solve.
Qed.

Section Correct.

Variable Hpows: pows = byte_pows.
Variable Hlogs: logs = byte_logs.
Variable Hinvs: invs = byte_invs.

Lemma all_cols_one_fast_correct: forall m n mx c,
  0 <= c < n ->
  wf_lmatrix mx m n ->
  all_cols_one_fast mx c = all_cols_one_partial m n mx c m.
Proof.
  move => m n mx c Hc Hwf. apply (lmatrix_to_mx_inj (all_cols_one_fast_wf c Hwf)). by apply all_cols_one_partial_wf.
  rewrite all_cols_one_list_equiv // -matrixP => x y. rewrite GaussRestrict.all_cols_one_noif_val !mxE /all_cols_one_fast /get.
  have: wf_lmatrix mx m n by []. rewrite /wf_lmatrix /rect; move => [Hm [Hn Hall]].
  rewrite !Znth_map.
  - rewrite byte_mul_fast_correct // binv_fast_correct // GRing.mulrC /= Z2Nat.id //. lia.
  - move: Hall. rewrite Forall_Znth. move ->. by apply Z_ord_bound. rewrite Hm. apply Z_ord_bound. list_solve.
  - rewrite Hm. apply Z_ord_bound. list_solve.
Qed.

Lemma sub_all_rows_fast_correct: forall m n mx r,
  0 <= r < m ->
  wf_lmatrix mx m n ->
  sub_all_rows_fast mx r = sub_all_rows_partial m n mx r m.
Proof.
  move => m n mx r Hr Hwf. apply (lmatrix_to_mx_inj (sub_all_rows_fast_wf Hr Hwf)). by apply sub_all_rows_partial_wf.
  rewrite sub_all_rows_equiv // -matrixP => x y. rewrite GaussRestrict.sub_all_rows_noif_val !mxE /sub_all_rows_fast /get.
  have: wf_lmatrix mx m n by []. rewrite /wf_lmatrix /rect; move => [Hm [Hn Hall]]. subst.
  case : (x == Z_to_ord Hr) /eqP => [Hxr | Hxr].
  - rewrite Hxr /= Z2Nat.id; try lia. by rewrite upd_Znth_same // Zlength_map.
  - have Hm: 0 <= Zlength mx by list_solve.
    rewrite upd_Znth_diff // ?Zlength_map //.
    + rewrite Znth_map //. 
      * move: Hall; rewrite Forall_Znth => Hall.
        rewrite combineWith_equiv Znth_map. rewrite combine_Znth //=; try(rewrite !Hall; try lia; by apply Z_ord_bound).
        by rewrite baddC Z2Nat.id; try lia.
        rewrite combine_Zlength; rewrite !Hall; try lia; by apply Z_ord_bound.
      * by apply Z_ord_bound.
    + by apply Z_ord_bound.
    + move => Hxr'. have//: x = Z_to_ord Hr. apply ord_inj. by rewrite /= -Hxr' Nat2Z.id.
Qed.

Lemma gauss_all_steps_fast_correct: forall m n mx,
  m <= n ->
  wf_lmatrix mx m n ->
  gauss_all_steps_list_fast m mx = gauss_all_steps_list_partial m n mx m.
Proof.
  move => m n mx Hmn Hwf. rewrite /gauss_all_steps_list_fast /gauss_all_steps_list_partial.
  have: forall x, In x (Ziota 0 m) -> 0 <= x < m. { move => x. move: Hwf. rewrite /wf_lmatrix/rect => Hwf.
    apply Ziota_In; try lia. list_solve. }
  move: mx Hwf. elim :(Ziota 0 m) => [//= |h t /= IH mx Hwf Hin].
  have Hh: 0 <= h < m. apply Hin. by left.
  rewrite (@all_cols_one_fast_correct m n) //; try lia.
  rewrite (@sub_all_rows_fast_correct m n) //; try lia.
  apply IH. apply sub_all_rows_partial_wf. by []. by apply all_cols_one_partial_wf.
  move => x Hint. apply Hin. by right. by apply all_cols_one_partial_wf.
Qed.

End Correct.

End GaussElim.

Definition test := mk_lmatrix 10 10 (fun x y => Byte.mul (Byte.repr (x + 1)) (Byte.repr (y + 1))).

Eval vm_compute in test.
Definition powlog := populate_pows_logs_fast Byte.modulus.
Definition invs pows logs := populate_invs_fast pows logs Byte.modulus.
Eval vm_compute in
  let (pows, logs) := powlog in
  let inv := invs pows logs in
   (all_cols_one_fast pows logs inv test 0).
Eval vm_compute in
  let (pows, logs) := powlog in
  let inv := invs pows logs in
   (sub_all_rows_fast test 2).
Eval vm_compute in
  let (pows, logs) := powlog in
  let inv := invs pows logs in
   (gauss_all_steps_list_fast pows logs inv 10 test).
