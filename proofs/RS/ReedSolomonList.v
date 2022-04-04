(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

Require Import VST.floyd.functional_base.

From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import VandermondeByte.
Require Import ListMatrix.
Require Import ByteFacts.
Require Import ReedSolomon.
Require Import ZSeq.
Require Import CommonSSR.
Require Import Vandermonde.
Require Import Gaussian.
Require Import GaussRestrict.
Require Import ByteField.

Lemma NoDup_app: forall {A: Type} (l1 l2:list A),
  NoDup l1 ->
  NoDup l2 ->
  (forall x, In x l1 -> ~In x l2) ->
  NoDup (l1 ++ l2).
Proof.
  intros A l1; induction l1; intros.
  - simpl. assumption.
  - simpl. inversion H; subst. constructor. intro.
    apply in_app_or in H2. destruct H2. contradiction. apply (H1 a). left. reflexivity. assumption.
    apply IHl1. assumption. assumption. intros. apply H1. right. assumption.
Qed.


Section Encoder.

(* The ListMatrix version of the encoder*)
Definition encoder_list (h k c : Z) (packets : lmatrix B) : lmatrix B :=
  lmatrix_multiply h k c (submatrix (fec_n - 1) weight_mx h k) 
      (extend_mx k c packets).

(*Lift the above into ssreflect matrices and operations*)
Lemma encoder_spec : forall (h k c : Z) (packets: lmatrix B) (Hh: h <= fec_max_h) (Hk: k <= fec_n - 1),
  0 <= h ->
  0 <= k ->
  0 <= c ->
  Zlength packets = k ->
  Forall (fun x => Zlength x <= c) packets ->
  lmatrix_to_mx h c (encoder_list h k c packets) = encoder (le_Z_N Hh) (le_Z_N Hk)
    (lmatrix_to_mx fec_max_h (fec_n - 1) weight_mx) 
    (lmatrix_to_mx k c (extend_mx k c packets)).
Proof.
  move => h k c packets Hh Hk Hn0 Hk0 Hc0 Hlen Hin. rewrite /encoder_list /encoder.
  have Hwf: wf_lmatrix weight_mx fec_max_h (fec_n - 1) by apply weight_mx_wf. 
  rewrite lmatrix_multiply_correct.
  by rewrite (@submatrix_to_mx _ (fec_max_h) (fec_n - 1) _ _ _ Hh Hk).
  by apply submatrix_wf.
  by apply extend_mx_wf. 
Qed.

Lemma encoder_wf: forall (h k c: Z) (packets: lmatrix B),
  0 <= h ->
  0 <= c ->
  wf_lmatrix (encoder_list h k c packets) h c.
Proof.
  move => h k c packets Hh Hc. by apply lmatrix_multiply_wf.
Qed. 

End Encoder.

Section Decoder.

(** Intermediate functions*)

(*Get lost and found packets*)
Definition find_lost_found_aux (f: byte -> bool) (g: Z -> byte) (base: list byte) pack l : list byte :=
  fold_left (fun acc x => if f (Znth x pack) then acc ++ [:: g x] else acc) l base.

Lemma find_lost_found_aux_bound: forall f g base pack l b,
  Forall (fun x => 0 <= Byte.unsigned (g x) < b) l ->
  Forall (fun x => 0 <= Byte.unsigned x < b) base ->
  Forall (fun x => 0 <= Byte.unsigned x < b) (find_lost_found_aux f g base pack l).
Proof.
  move => f g base pack l b.
  rewrite /find_lost_found_aux !Forall_forall. move : base.
  elim : l => [ //= | h t /= IH base Hbase Hg x].
  case Hh: (f (Znth h pack)); apply IH; rewrite //= => z Hin.
  - apply Hbase. by right.
  - apply in_app_or in Hin. case: Hin => [Hzbase | Hzg].
    + by apply Hg.
    + case : Hzg => [Hzg | //]. subst. apply Hbase. by left.
  - apply Hbase. by right.
Qed.

Lemma find_lost_found_aux_app: forall f g base pack l1 l2,
  find_lost_found_aux f g base pack (l1 ++ l2) =
  find_lost_found_aux f g (find_lost_found_aux f g base pack l1) pack l2.
Proof.
  move => f g base pack l1 l2. by rewrite /find_lost_found_aux fold_left_app.
Qed.

(*Almost exactly same as parities, is there some way to duplicate, like f is function from Z to
  some type w 2 constructors*)
Lemma find_lost_found_aux_NoDup: forall f g pack base l,
  NoDup base ->
  (forall x y, In x base -> In y l -> g y <> x) ->
  NoDup l ->
  (forall x y, In x l -> In y l -> g x = g y -> x = y) ->
  NoDup (find_lost_found_aux f g base pack l).
Proof.
  move => f g pack base l. move: base. elim : l => [//= | h t /= IH base Hnob Hbl Hnol Hinj].
  case Hfh : (f (Znth h pack)).
  - apply IH. apply NoDup_app. by []. constructor. by []. constructor.
    move => x Hinx. rewrite /= => Hinh. case : Hinh => [Hfh' | Hfalse]; rewrite //.
    have: g h <> x. apply Hbl. by []. by left. by rewrite Hfh'.
    move => x y Hinx Hiny.
    apply in_app_or in Hinx. case : Hinx => [Hinx | [Hxh | Hfalse]]; rewrite //.
    apply Hbl. by []. by right. subst. move => Hf. apply Hinj in Hf. 
    subst. by move: Hnol; rewrite NoDup_cons_iff => [[Hnotin H]]. by right. by left.
    by move: Hnol; rewrite NoDup_cons_iff => [[Hnotin Ht]].
    move => x y Hinx Hiny Hf. apply Hinj. by right. by right. by [].
  - apply IH. by []. move => x y Hinx Hiny. apply Hbl. by []. by right.
    by move: Hnol; rewrite NoDup_cons_iff => [[Hnotin H]].
    move => x y Hinx Hiny Hf. apply Hinj. by right. by right. by [].
Qed.

Lemma find_lost_found_aux_NoDup': forall f g pack l,
  NoDup l ->
  (forall x y, In x l -> In y l -> g x = g y -> x = y) ->
  NoDup (find_lost_found_aux f g nil pack l).
Proof.
  move => f g pack l Hno Hinj. apply find_lost_found_aux_NoDup; try by [].
  constructor.
Qed.

Lemma find_lost_found_aux_in: forall f stats l x b,
  b <= Byte.modulus ->
  Forall (fun x => 0 <= x < b) l ->
  In x (find_lost_found_aux f Byte.repr [::] stats l) ->
  0 <= Byte.unsigned x < b.
Proof.
  move => f stats l x b Hb Hl Hin.
  have Htriv: (Forall (fun x : byte => 0 <= Byte.unsigned x < b) [::]) by [].
  have Hl': (Forall (fun x : Z => 0 <= Byte.unsigned (Byte.repr x) < b) l). move: Hl.
    rewrite !Forall_Znth => Hall i Hi. have Hnth: 0 <= Znth i l < b by apply Hall.
    rewrite Byte.unsigned_repr //; rep_lia. 
  pose proof (@find_lost_found_aux_bound f Byte.repr [::] stats l b Hl' Htriv) as Hall.
  by move: Hall; rewrite Forall_forall => /(_ _ Hin).
Qed.

Lemma find_lost_found_aux_in_spec: forall f base pack l x,
  Forall (fun x => 0 <= x <= Byte.max_unsigned) l ->
  In x (find_lost_found_aux f Byte.repr base pack l) <-> 
  In x base \/ (In (Byte.unsigned x) l /\ f (Znth (Byte.unsigned x) pack)).
Proof.
  move => f base pack l x. move : base. elim : l => [//= base Hbound | h t /= IH base Hbound].
  - by split => [Hin | [Hin | [Hfalse Hf]]]; try left.
  - have Hhbound: 0 <= h <= Byte.max_unsigned by apply Forall_inv in Hbound.
    apply Forall_inv_tail in Hbound. case Hfh : (f (Znth h pack)).
    + rewrite IH // in_app_iff /= binop_lemmas2.or_False or_assoc. apply or_iff_compat_l.
      split.
      * move => [Hxh | [Hin Hh]].
        -- subst. rewrite !Byte.unsigned_repr; try rep_lia. split. by left. by [].
        -- split. by right. by [].
      * move => [[Hxh | Hin] Hf].
        -- subst. rewrite Byte.repr_unsigned. by left.
        -- right. by split.
    + rewrite IH //. apply or_iff_compat_l. split.
      * move => [Hin Hf]. split. by right. by [].
      * move => [[Hhx | Hin] Hf]. subst. by rewrite Hf in Hfh. by split.
Qed.  

Lemma find_lost_found_aux_plus_1: forall f g base pack c,
  0 <= c ->
  find_lost_found_aux f g base pack (Ziota 0 (c+1)) =
    if f (Znth c pack) then  (find_lost_found_aux f g base pack (Ziota 0 c)) ++ [:: g c] else
     (find_lost_found_aux f g base pack (Ziota 0 c)).
Proof.
  move => f g base pack c Hc. by rewrite /find_lost_found_aux Ziota_plus_1 // fold_left_app.
Qed.

Lemma find_lost_found_aux_Zlength': forall f g base pack l,
  Zlength (find_lost_found_aux f g base pack l) <= Zlength base + Zlength l.
Proof.
  move => f g base pack l. move: base. elim : l => [//= base | h t /= IH base].
  - list_solve.
  - case : (f (Znth h pack)).
    + apply (Z.le_trans _ _ _ (IH (base ++ [:: g h]))). rewrite Zlength_app /=. list_solve.
    + apply (Z.le_trans _ _ _ (IH base)). list_solve.
Qed.

Lemma find_lost_found_aux_Zlength: forall f g pack l,
  Zlength (find_lost_found_aux f g nil pack l) <= Zlength l.
Proof.
  move => f g pack l. pose proof (@find_lost_found_aux_Zlength' f g [::] pack l). list_solve.
Qed.

(*First, get the lost packets*)
(*Use Byte.signed bc stats is really list of signed bytes, everything else unsigned bytes*)
Definition find_lost (stats: list byte) (k: Z) : list byte :=
  find_lost_found_aux (fun x => Z.eq_dec (Byte.signed x) 1%Z) Byte.repr nil stats (Ziota 0 k).

Lemma find_lost_bound: forall l k,
  0 <= k <= Byte.max_unsigned ->
  Forall (fun x => 0 <= Byte.unsigned x < k) (find_lost l k).
Proof.
  move => l k Hk. apply find_lost_found_aux_bound => [|//].
  rewrite Forall_Znth => i. rewrite Zlength_Ziota //; try lia.
  move => Hi. rewrite Byte.unsigned_repr Znth_Ziota; rep_lia.
Qed. 

Lemma byte_repr_inj: forall x y,
  0 <= x <= Byte.max_unsigned ->
  0 <= y <= Byte.max_unsigned ->
  Byte.repr x = Byte.repr y ->
  x = y.
Proof.
  move => x y Hx Hy Hrepr. apply (congr1 Byte.unsigned) in Hrepr.
  rewrite !Byte.unsigned_repr in Hrepr; rep_lia.
Qed.

Lemma find_lost_NoDup: forall l k,
  0 <= k <= Byte.max_unsigned ->
  NoDup (find_lost l k).
Proof.
  move => l k Hk. apply find_lost_found_aux_NoDup'; try by [].
  apply Ziota_NoDup. move => x y. rewrite !Ziota_In; try lia.
  move => Hx Hy. apply byte_repr_inj; rep_lia.
Qed. 

Lemma find_lost_plus_1: forall l k,
  0 <= k ->
  find_lost l (k + 1) = if (Z.eq_dec (Byte.signed (Znth k l)) 1%Z) then
  (find_lost l k) ++ [ :: Byte.repr k] else (find_lost l k).
Proof.
  move => l k Hk. by rewrite /find_lost find_lost_found_aux_plus_1.
Qed.

Lemma find_lost_Zlength: forall l k,
  0 <= k ->
  Zlength (find_lost l k) <= k.
Proof.
  move => l k Hk. rewrite /find_lost. have Hkiota: k = Zlength (Ziota 0 k) by rewrite Zlength_Ziota; lia.
  rewrite {2}Hkiota. apply find_lost_found_aux_Zlength.
Qed.

(*the first part of the found array*)
Definition find_found (stats: list byte) (k: Z) : list byte :=
  find_lost_found_aux (fun x => negb (Z.eq_dec (Byte.signed x) 1%Z)) Byte.repr nil stats (Ziota 0 k).

Lemma find_found_bound: forall l k,
  0 <= k <= Byte.max_unsigned ->
  Forall (fun x => 0 <= Byte.unsigned x < k) (find_found l k).
Proof.
  move => l k Hk. apply find_lost_found_aux_bound => [|//].
  rewrite Forall_Znth => i. rewrite Zlength_Ziota //; try lia.
  move => Hi. rewrite Byte.unsigned_repr Znth_Ziota; rep_lia.
Qed. 

Lemma find_found_NoDup: forall l k,
  0 <= k <= Byte.max_unsigned ->
  NoDup (find_found l k).
Proof.
  move => l k Hk. apply find_lost_found_aux_NoDup'; try by [].
  apply Ziota_NoDup. move => x y. rewrite !Ziota_In; try lia.
  move => Hx Hy. apply byte_repr_inj; rep_lia.
Qed. 

Lemma find_found_plus_1: forall l k,
  0 <= k ->
  find_found l (k + 1) = if (Z.eq_dec (Byte.signed (Znth k l)) 1%Z) then (find_found l k) else
  (find_found l k) ++ [ :: Byte.repr k] .
Proof.
  move => l k Hk. rewrite /find_found find_lost_found_aux_plus_1 //.
  by case : (Z.eq_dec (Byte.signed (Znth k l)) 1).
Qed.

Lemma find_found_Zlength: forall l k,
  0 <= k ->
  Zlength (find_found l k) <= k.
Proof.
  move => l k Hk. rewrite /find_found. have Hkiota: k = Zlength (Ziota 0 k) by rewrite Zlength_Ziota; lia.
  rewrite {2}Hkiota. apply find_lost_found_aux_Zlength.
Qed.

(*Lost and found are complements*)
Lemma find_lost_found_comp_nat: forall stats k,
  0 <= k <= Byte.max_unsigned ->
  map Z.to_nat (map Byte.unsigned (find_found stats k)) =
  nat_comp (Z.to_nat k) (map Z.to_nat (map Byte.unsigned (find_lost stats k))).
Proof.
  move => stats k. rewrite /find_found /find_lost /Ziota /=.
  move => Hk. have: (Z.to_nat k <= Z.to_nat Byte.max_unsigned)%coq_nat by lia. rewrite {Hk}.
  elim : (Z.to_nat k) => [//= | n IH Hbound].
  rewrite nat_comp_plus_one !iota_plus_1 /= !map_cat /= !add0n !find_lost_found_aux_app /=.
  case: (Z.eq_dec (Byte.signed (Znth (Z.of_nat n) stats)) 1) => [/= Hn1 | /= Hn0].
  - have->:n
    \in [seq Z.to_nat i
           | i <- [seq Byte.unsigned i
                     | i <- find_lost_found_aux (fun x : byte => Z.eq_dec (Byte.signed x) 1) Byte.repr
                              [::] stats [seq Z.of_nat y | y <- iota 0 n] ++ [:: 
                            Byte.repr (Z.of_nat n)]]]. {
    rewrite !map_cat /= Byte.unsigned_repr; try rep_lia. by rewrite Nat2Z.id mem_cat in_cons eq_refl orbT. }
    rewrite !map_cat /= Byte.unsigned_repr; try rep_lia. rewrite Nat2Z.id nat_comp_app. apply IH. lia.
  - have->:n
    \in [seq Z.to_nat i
           | i <- [seq Byte.unsigned i
                     | i <- find_lost_found_aux (fun x : byte => Z.eq_dec (Byte.signed x) 1) Byte.repr
                              [::] stats [seq Z.of_nat y | y <- iota 0 n]]] = false. {
    apply /negPf /negP; rewrite in_mem_In in_map_iff => [[x [Hxn Hinx]]].
    subst. move: Hinx; rewrite in_map_iff => [[y [Hyn Hiny]]]. subst.
    apply (@find_lost_found_aux_in _ _ _ _  (Byte.unsigned y)) in Hiny. lia. rep_lia.
    rewrite Forall_forall => x.  rewrite in_map_iff => [[x' [Hx' Hin]]]. subst. move: Hin.
    rewrite -in_mem_In mem_iota add0n => /andP[/leP Hx0 /ltP Hxx]. lia. }
    rewrite !map_cat /= Byte.unsigned_repr; try rep_lia. rewrite Nat2Z.id IH //. lia.
Qed.

Lemma find_lost_found_comp: forall stats k,
  0 <= k <= Byte.max_unsigned ->
  byte_ord_list (find_found stats k) k =
  (ord_comp (byte_ord_list (find_lost stats k) k)).
Proof.
  (*do widen_ord stuff separately*)
  move => stats k Hk. rewrite {1}/byte_ord_list {1}/Z_ord_list /ord_comp find_lost_found_comp_nat.
  f_equal. f_equal. pose proof (find_lost_bound stats Hk) as Hbound.
   have[H0k | H0k]: k = 0%Z \/ 0 < k by lia.
  - subst. by [].
  - apply Znth_eq_ext.
    + by rewrite !Zlength_map byte_ord_list_Zlength.
    + move => i. rewrite !Zlength_map => Hi.
      have Hinhab: Inhabitant 'I_(Z.to_nat k). apply (ord_zero H0k).
      rewrite !Znth_map //=.
      * rewrite byte_ord_list_Znth' //. lia.
      * by rewrite byte_ord_list_Zlength.
      * by rewrite Zlength_map.
  - by [].
Qed.

(*The following is weaker but needed in the decoder correctness*)
Lemma find_lost_found_in: forall l k x,
  k <= Byte.max_unsigned ->
  0 <= Byte.unsigned x < k ->
  In x (find_found l k) <-> ~ In x (find_lost l k).
Proof.
  move => l k x Hk Hxk.
  have Hiota: Forall (fun x0 : Z => 0 <= x0 <= Byte.max_unsigned) (Ziota 0 k). 
    rewrite Forall_Znth Zlength_Ziota; try lia. move => i Hi. rewrite Znth_Ziota; try lia.
  rewrite !find_lost_found_aux_in_spec //= !binop_lemmas2.False_or.
  have Hin: In (Byte.unsigned x) (Ziota 0 k) by rewrite Ziota_In; lia.
  have Hand: forall (P Q: Prop), P -> ((P /\ Q) <-> Q) by tauto. rewrite !Hand {Hand} //.
  symmetry. apply rwN. apply idP.
Qed.

(*This is probably true without the assumption, but the proof becomes easier*)
Lemma find_lost_found_Zlength: forall l k,
  0 <= k <= Byte.max_unsigned ->
  Zlength (find_found l k) + Zlength (find_lost l k) = k.
Proof.
  move => l k Hk. have Hk': 0 <= k <= Byte.max_unsigned by []. apply (find_lost_found_comp l) in Hk.
  apply (congr1 (@Zlength _)) in Hk. move: Hk.
  rewrite byte_ord_list_Zlength; last first. by apply find_found_bound.
  move ->. rewrite Zlength_correct -size_length ord_comp_size_uniq.
  rewrite size_length -ZtoNat_Zlength byte_ord_list_Zlength; last first. by apply find_lost_bound.
  pose proof (@find_lost_Zlength l k (proj1 Hk')). rewrite Nat2Z.inj_sub; rep_lia.
  apply byte_ord_list_uniq. by apply find_lost_NoDup.
Qed.

(*Parities are represented as a list (option (list byte)), representing whether the parity packet is there
  or not. We will translate this into Vundef or Vptr as needed*)

Definition find_parity_aux (f: Z -> byte) (par: list (option (list byte))) (base : list byte) (l: list Z) :=
  fold_left (fun acc x => match (Znth x par) with
                          | None => acc
                          | Some _ => acc ++ [:: f x]
                          end) l base.

Lemma find_parity_aux_base_Zlength: forall f par base l,
  Zlength (find_parity_aux f par base l) = Zlength base + Zlength (find_parity_aux f par [::] l).
Proof.
  move => f par base l. move: base. elim : l => [//= b | h t /= IH base].
  - list_solve.
  - case Hh: (Znth h par) => [o |].
    + rewrite IH. rewrite (IH [:: f h]). rewrite Zlength_app. lia.
    + apply IH.
Qed.

Lemma find_parity_aux_Zlength: forall f1 f2 par base l,
  Zlength (find_parity_aux f1 par base l) = Zlength (find_parity_aux f2 par base l).
Proof.
  move => f1 f2 par base l. move: base. elim : l => [//= | h t /= IH base].
  case Hh: (Znth h par) => [o |].
  - by rewrite /= find_parity_aux_base_Zlength (find_parity_aux_base_Zlength _ _ (base ++ [:: f2 h])) !Zlength_app 
    !Zlength_cons !Zlength_nil IH.
  - by apply IH.
Qed.

Lemma find_parity_aux_map: forall (f: Z -> byte) par b1 b2 l,
  Forall (fun x => 0 <= x <= Byte.max_unsigned) l ->
  map (fun x => f (Byte.unsigned x)) b1 = b2 ->
  map (fun x => f (Byte.unsigned x)) (find_parity_aux Byte.repr par b1 l) = find_parity_aux f par b2 l.
Proof.
  move => f par b1 b2 l. move: b1 b2. elim : l => [//= | h t /= IH b1 b2 Hbound Hb12].
  have Hhbound: (0 <= h <= Byte.max_unsigned) by apply Forall_inv in Hbound. apply Forall_inv_tail in Hbound.
  apply IH => [//|]. case Hh : (Znth h par) => [o |//].
  by rewrite map_cat /= Hb12 Byte.unsigned_repr.
Qed.

Lemma find_parity_aux_map': forall f par l,
  Forall (fun x : Z => 0 <= x <= Byte.max_unsigned) l ->
  map (fun x => f (Byte.unsigned x)) (find_parity_aux Byte.repr par nil l) = find_parity_aux f par nil l.
Proof.
  move => f par l Hl. by apply find_parity_aux_map.
Qed.

Lemma find_parity_aux_bound: forall f pars base l a b,
  Forall (fun x => a <= Byte.unsigned (f x) < b) l ->
  Forall (fun x => a <= Byte.unsigned x < b) base ->
  Forall (fun x => a <= Byte.unsigned x < b) (find_parity_aux f pars base l).
Proof.
  move => f pars base l a b. rewrite /find_parity_aux !Forall_forall. move : base.
  elim : l => [ //= | h t /= IH base Hf Hbase x].
  case Hh: (Znth h pars) => [y /= | //=]; apply IH; rewrite //= => z Hin.
  - apply Hf. by right.
  - apply in_app_or in Hin. case : Hin => [Hin | Hzh].
    + by apply Hbase.
    + case : Hzh => [Hzh | //]. subst. apply Hf. by left.
  - apply Hf. by right.
Qed. 

Lemma find_parity_aux_NoDup: forall f par base l,
  NoDup base ->
  (forall x y, In x base -> In y l -> f y <> x) ->
  NoDup l ->
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup (find_parity_aux f par base l).
Proof.
  move => f par base l. move: base. elim : l => [//= | h t /= IH base Hnob Hbl Hnol Hinj].
  case : (Znth h par) => [a /= | //=].
  - apply IH. apply NoDup_app. by []. constructor. by []. constructor.
    move => x Hinx. rewrite /= => Hinh. case : Hinh => [Hfh | Hfalse]; rewrite //.
    have: f h <> x. apply Hbl. by []. by left. by rewrite Hfh.
    move => x y Hinx Hiny.
    apply in_app_or in Hinx. case : Hinx => [Hinx | [Hxh | Hfalse]]; rewrite //.
    apply Hbl. by []. by right. subst. move => Hf. apply Hinj in Hf. 
    subst. by move: Hnol; rewrite NoDup_cons_iff => [[Hnotin H]]. by right. by left.
    by move: Hnol; rewrite NoDup_cons_iff => [[Hnotin Ht]].
    move => x y Hinx Hiny Hf. apply Hinj. by right. by right. by [].
  - apply IH. by []. move => x y Hinx Hiny. apply Hbl. by []. by right.
    by move: Hnol; rewrite NoDup_cons_iff => [[Hnotin H]].
    move => x y Hinx Hiny Hf. apply Hinj. by right. by right. by [].
Qed.

(*The real result we wanted (we needed the stronger claim for the IH)*)
Lemma find_parity_aux_NoDup': forall f par l,
  NoDup l ->
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup (find_parity_aux f par nil l).
Proof.
  move => f par l Hno Hinj. apply find_parity_aux_NoDup; try by [].
  constructor.
Qed.

Lemma find_parity_aux_in_iff: forall par base l x,
  Forall (fun x => 0 <= x <= Byte.max_unsigned) l ->
  In x (find_parity_aux Byte.repr par base l) <-> 
  In x base \/ (In (Byte.unsigned x) l /\ exists p, Znth (Byte.unsigned x) par = Some p).
Proof.
  move => par base l x. move: base. elim : l => [//= base | h t /= IH base Hbound].
  - by split => [ Hin //| [Hin // | [Hfalse Hex //]]]; left.
  - have Hhbound: 0 <= h <= Byte.max_unsigned by apply Forall_inv in Hbound.
    apply Forall_inv_tail in Hbound. case Hnth : (Znth h par) => [c |]; rewrite IH //=.
    + rewrite in_app_iff /= or_assoc binop_lemmas2.or_False. apply or_iff_compat_l. split.
      * move => [Hxh | [Hint Hex]]. 
        -- subst. rewrite Byte.unsigned_repr; try rep_lia. split. by left. by exists c.
        -- split. by right. by [].
      * move => [[Hxh | Hin] Hex].
        -- subst. rewrite Byte.repr_unsigned. by left.
        -- right. by split.
    + apply or_iff_compat_l. split.
      * move => [Hin Hex]. split. by right. by [].
      * move => [[Hhx | Hin] [p Hex]]. subst. by rewrite Hex in Hnth. split. by []. by exists p.
Qed. 

(*Unfortunately, the above isn't general enough for [find_parity_found] (though we do need it elsewhere)*)
Lemma find_parity_aux_in_found: forall par base l max_n x,
  Forall (fun x => 0 <= (max_n - 1 - x) <= Byte.max_unsigned) l ->
  In x (find_parity_aux (fun x => Byte.repr(max_n - 1 - x)) par base l) ->
  In x base \/ In (max_n - 1 - Byte.unsigned x) l /\ exists p, Znth (max_n - 1 - Byte.unsigned x) par = Some p.
Proof.
  move => par base l max_n x. move: base. elim : l => [//= base Hbound Hin | h t /= IH base Hbound].
  - by left.
  - have Hhbound: 0 <= (max_n - 1 - h) <= Byte.max_unsigned by (apply Forall_inv in Hbound).
    apply Forall_inv_tail in Hbound. case Hh: (Znth h par) => [l|]; move => Hin; apply IH in Hin => [|//]; last first. 
    + case : Hin => [Hbase | [Hint Hex]].
      * by left.
      * right. split. by right. by [].
    + case : Hin => [Hbaseh | [Hint Hex]]; last first. right. split. by right. by [].
      apply in_app_or in Hbaseh. case : Hbaseh => [Hbase | [Hxh | Hf //]].
      by left. right. subst. split. left. rewrite Byte.unsigned_repr; rep_lia.
      exists l. rewrite Byte.unsigned_repr; [|rep_lia]. 
      by have->: (max_n - 1 - (max_n - 1 - h)) = h by lia.
Qed.
  

Lemma find_parity_aux_plus_1: forall f par base c,
  0 <= c ->
  find_parity_aux f par base (Ziota 0 (c + 1)) =
  match (Znth c par) with
  | None => find_parity_aux f par base (Ziota 0 c)
  | Some _ => find_parity_aux f par base (Ziota 0 c) ++ [:: f c]
  end.
Proof.
  move => f par base c Hc. by rewrite /find_parity_aux Ziota_plus_1 // fold_left_app.
Qed.

Lemma find_parity_aux_Zlength_bound': forall f par base l,
  Zlength (find_parity_aux f par base l) <= Zlength base + Zlength l.
Proof.
  move => f par base l. move: base. elim : l => [//= base | /= h t IH base].
  - list_solve.
  - case : (Znth h par) => [x |].
    + apply (Z.le_trans _ _ _ (IH (base ++ [:: f h]))). rewrite Zlength_app; list_solve.
    + apply (Z.le_trans _ _ _ (IH base)). list_solve.
Qed.

Lemma find_parity_aux_Zlength_bound: forall f par l,
  Zlength (find_parity_aux f par [::] l) <= Zlength l.
Proof.
  move => f par l. pose proof (@find_parity_aux_Zlength_bound' f par [::] l); list_solve.
Qed.

(*The parity row array*)

Definition find_parity_rows (par: list (option (list byte))) (c: Z) :=
  find_parity_aux Byte.repr par nil (Ziota 0 c).

Lemma find_parity_rows_bound: forall par c,
  0 <= c <= Byte.max_unsigned ->
  Forall (fun x => 0 <= Byte.unsigned x < c) (find_parity_rows par c).
Proof.
  move => par c Hc.
  apply find_parity_aux_bound; rewrite //=. rewrite Forall_Znth => i.
  rewrite Zlength_Ziota; try lia. move => Hi. rewrite Byte.unsigned_repr Znth_Ziota; rep_lia.
Qed.

Lemma find_parity_rows_NoDup: forall par c,
  0 <= c <= Byte.max_unsigned ->
  NoDup (find_parity_rows par c).
Proof.
  move => par c Hc. apply find_parity_aux_NoDup'.
  apply Ziota_NoDup. move => x y. rewrite !Ziota_In; try lia.
  move => Hx Hy. apply byte_repr_inj; rep_lia.
Qed.

Lemma find_parity_rows_plus_1: forall par c,
  0 <= c ->
  find_parity_rows par (c+1) =
  match (Znth c par) with
  | None => find_parity_rows par c
  | Some _ => find_parity_rows par c ++ [:: Byte.repr c]
  end.
Proof.
  move => par c Hc. by rewrite /find_parity_rows find_parity_aux_plus_1.
Qed.

Lemma find_parity_rows_Zlength: forall par c,
  0 <= c ->
  Zlength (find_parity_rows par c) <= c.
Proof.
  move => par c Hc. rewrite /find_parity_rows. have Hciota: c = Zlength (Ziota 0 c) by rewrite Zlength_Ziota; lia.
  rewrite {2}Hciota. apply find_parity_aux_Zlength_bound.
Qed.
  
(*The second part of the "found" array*)

Definition find_parity_found (par: list (option (list byte))) (max_n : Z) (c: Z)  :=
  find_parity_aux (fun x => Byte.repr (max_n - 1 - x)) par nil (Ziota 0 c).

Lemma find_parity_found_bound: forall par c max_n,
  0 <= c < max_n ->
  max_n <= Byte.max_unsigned ->
  Forall (fun x => 0 <= Byte.unsigned x < max_n) (find_parity_found par max_n c).
Proof.
  move => par c max_n Hc Hn.
  apply find_parity_aux_bound; rewrite //=. rewrite Forall_Znth => i.
  rewrite Zlength_Ziota; try lia. move => Hi. rewrite Byte.unsigned_repr Znth_Ziota; rep_lia.
Qed.

(*This is more general, but we need version above for compatibility with other similar bounds*)
Lemma find_parity_found_bound': forall par c max_n,
  0 <= c < max_n ->
  max_n <= Byte.max_unsigned ->
  Forall (fun x => max_n - c <= Byte.unsigned x < max_n) (find_parity_found par max_n c).
Proof.
  move => par c max_n Hc Hn.
  apply find_parity_aux_bound; rewrite //=. rewrite Forall_Znth => i.
  rewrite Zlength_Ziota; try lia. move => Hi. rewrite Byte.unsigned_repr Znth_Ziota; rep_lia.
Qed.

Lemma find_parity_found_NoDup: forall par c max_n,
  0 <= c < max_n->
  max_n <= Byte.max_unsigned ->
  NoDup (find_parity_found par max_n c).
Proof.
  move => par c max_n Hc Hn. apply find_parity_aux_NoDup'.
  apply Ziota_NoDup. move => x y. rewrite !Ziota_In; try lia.
  move => Hx Hy Hrepr. apply byte_repr_inj in Hrepr; rep_lia.
Qed.

Lemma find_parity_found_plus_1: forall par c max_n,
  0 <= c ->
  find_parity_found par max_n (c+1)  =
  match (Znth c par) with
  | None => find_parity_found par max_n c
  | Some _ => find_parity_found par max_n c ++ [:: Byte.repr (max_n - 1 - c) ]
  end.
Proof.
  move => par c max_n Hc. by rewrite /find_parity_found find_parity_aux_plus_1.
Qed.

Lemma find_parity_found_Zlength: forall par c max_n,
  0 <= c ->
  Zlength (find_parity_found par max_n c) <= c.
Proof.
  move => par c max_n Hc. rewrite /find_parity_found. have Hciota: c = Zlength (Ziota 0 c) by rewrite Zlength_Ziota; lia.
  rewrite {2}Hciota. apply find_parity_aux_Zlength_bound.
Qed.

Lemma find_parity_found_in: forall par c max_n x,
  0 <= c < max_n->
  max_n - 1 <= Byte.max_unsigned ->
  In x (find_parity_found par max_n c) ->
  exists l, Znth (max_n - 1 - Byte.unsigned x) par = Some l.
Proof.
  move => par c max_n x Hc Hn Hin. apply find_parity_aux_in_found in Hin.
  - case : Hin => [Hf // | [Hin Hex] //].
  - rewrite Forall_Znth. rewrite Zlength_Ziota; try lia. move => i Hi.
    rewrite Znth_Ziota; lia.
Qed.

Lemma find_parity_found_Znth_some: forall par c max_n i,
  0 <= c < max_n->
  max_n - 1 <= Byte.max_unsigned ->
  0 <= i < Zlength (find_parity_found par max_n c) ->
  exists l, Znth (max_n - 1 - Byte.unsigned (Znth i (find_parity_found par max_n c))) par = Some l.
Proof.
  move => par c max_n i Hc Hn Hi. apply (find_parity_found_in Hc Hn).
  by apply Znth_In.
Qed.

(*The relationship between these two functions*)
Lemma find_parity_rows_found_Zlength: forall par c max_n,
  Zlength (find_parity_found par max_n c) = Zlength (find_parity_rows par c).
Proof.
  move => par c max_n.
  apply find_parity_aux_Zlength.
Qed.

Lemma find_parity_rows_found_map: forall par c max_n,
  0 <= c <= Byte.modulus ->
  map (fun x => Byte.repr (max_n - 1 - Byte.unsigned x)) (find_parity_rows par c) = find_parity_found par max_n c.
Proof.
  move => par c max_n Hc. remember (fun x => Byte.repr (max_n - 1 - x)) as f.
  have->: (fun x => Byte.repr (max_n - 1 - Byte.unsigned x)) = (fun x => f (Byte.unsigned x)).
    by rewrite Heqf.
  rewrite find_parity_aux_map' //. by subst.
  rewrite Forall_Znth => i. rewrite Zlength_Ziota; try lia. move => Hic.
  rewrite Znth_Ziota; rep_lia.
Qed.

Lemma find_parity_rows_found_Znth: forall par c max_n i,
  0 <= c < max_n->
  max_n <= Byte.max_unsigned ->
  0 <= i < Zlength (find_parity_rows par c) ->
  Byte.unsigned (Znth i (find_parity_found par max_n c)) = max_n - 1 - Byte.unsigned (Znth i (find_parity_rows par c)).
Proof.
  move => par c max_n i Hc Hn Hi. rewrite -find_parity_rows_found_map; try rep_lia. rewrite Znth_map //.
  rewrite Byte.unsigned_repr; try rep_lia. have Hc': 0 <= c <= Byte.max_unsigned  by rep_lia.
  pose proof (find_parity_rows_bound par Hc') as Hbound.
  move : Hbound. rewrite Forall_Znth => /(_ i Hi). rep_lia.
Qed.

Lemma forall_lt_leq_trans: forall n m l,
  n <= m ->
  Forall (fun x => 0 <= Byte.unsigned x < n) l ->
  Forall (fun x => 0 <= Byte.unsigned x < m) l.
Proof.
  move => n m l Hnm. apply Forall_impl. move => a Ha. lia. 
Qed. 


(*The parity packet is a list of option (list Z)'s, since some are lost in transit. We need to convert to 
  a matrix*)
Definition fill_missing (c: Z) (l: list (option (list byte))) : lmatrix B :=
  map (fun x => match x with
                | None => (zseq c Byte.zero) 
                | Some l => l
                end) l.

Lemma fill_missing_some: forall c l i p,
  0 <= i < Zlength l ->
  Znth i l = Some p ->
  Znth i (fill_missing c l) = p.
Proof.
  move => c l i p Hlen Hith. by rewrite Znth_map // Hith.
Qed. 

Lemma fill_missing_mx_some: forall c l i j p,
  Znth i l = Some p ->
  0 <= j < c ->
  0 <= i < Zlength l ->
  Zlength p = c ->
  get (fill_missing c l) i j = Znth j p.
Proof.
  move => c l i j p Hith Hj Hilen Hlenp.
  rewrite /get. by rewrite !(fill_missing_some _ Hilen Hith).
Qed.

(** The Decoder  *)
(*First, we will do everything in terms of list matrices, then bring back to packets of variable length*)
(*The "map Byte.unsigned" is not super elegant, but it needs to be done somewhere, since we are ultimately indexing
  by Znth which uses Z*)
Definition decode_list_mx (k c : Z) (packets: list (list B)) (parities: list (option (list byte))) 
  (stats: list byte) (i:Z) : lmatrix B :=
  (*populate all of the "arrays"*)
  let lost := find_lost stats k in
  let found1 := find_found stats k in 
  let row := find_parity_rows parities i in
  let found2 := find_parity_found parities (fec_n - 1) i  in
  let found := found1 ++ found2 in
  let input := extend_mx k c packets in
  let parmx := fill_missing c parities in
  let xh := Zlength lost in
  (*step 1: find w' and v*)
  let w' := submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1) (map Byte.unsigned row) 
    (map Byte.unsigned (rev lost)) in
  let v := find_invmx_list w' xh in
  (*step 2: find w'', d, and s*)
  let w'' := submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) (map Byte.unsigned row) (map Byte.unsigned found) in
  let d' := col_mx_list (submx_rows_cols_list input (k - xh) c (map Byte.unsigned found1) (Ziota 0 c))
              (submx_rows_cols_list parmx xh c (map Byte.unsigned row) (Ziota 0 c)) (k-xh) xh c in
  let s := lmatrix_multiply xh k c w'' d' in
  (*step 3: find missing packets and fill in*)
  let d := lmatrix_multiply xh xh c v s in
  fill_rows_list k c xh input d (map Byte.unsigned (rev lost)).


Lemma max_h_n: ((Z.to_nat fec_max_h <= Z.to_nat (fec_n - 1)))%N.
Proof.
  apply /leP. rep_lia.
Qed.

Lemma k_bound_proof: forall k,
  (k <= (fec_n - 1) - fec_max_h) ->
  (Z.to_nat k <= Z.to_nat (fec_n - 1) - Z.to_nat fec_max_h)%N.
Proof.
  move => k Hk.  apply /leP.
  have->: (Z.to_nat (fec_n - 1) - Z.to_nat fec_max_h)%N = (Z.to_nat (fec_n - 1) - Z.to_nat fec_max_h)%coq_nat by [].
  rep_lia.
Qed.

(*We will need this a few times - the list of powers in the Vandermonde matrix*)
Definition weight_list := (rev [seq (@GRing.exp B bx i) | i <- iota 0 (Z.to_nat (fec_n - 1))]).

Lemma weight_list_size: size weight_list = Z.to_nat (fec_n - 1).
Proof.
  by rewrite /weight_list size_rev size_map size_iota.
Qed.

Lemma h_pos: 0 < fec_max_h.
Proof.
  rep_lia.
Qed.

Lemma n_pos: 0 < fec_n - 1.
Proof.
  rep_lia.
Qed.

Lemma weight_mx_spec: lmatrix_to_mx fec_max_h (fec_n - 1) weight_mx =
   weights (Z.to_nat fec_max_h) (Z.to_nat (fec_n - 1)) weight_list.
Proof.
  rewrite /weight_mx /weight_list gauss_restrict_list_equiv. rep_lia.
  move => Hhn. rewrite /weights gaussian_elim_restrict_noop_equiv. f_equal. by rewrite weight_mx_list_spec; try rep_lia.
  apply /leP. rep_lia. move => Hh. rewrite weight_mx_list_spec; try rep_lia. apply vandermonde_strong_inv.
  apply /ltP. rep_lia.
  apply weight_matrix_wf; rep_lia.
Qed.

Lemma weight_list_uniq: uniq weight_list.
Proof.
  rewrite /weight_list rev_uniq power_list_uniq //=. apply /leP. rep_lia.
Qed.

(*We need this both for correctness and for the the VST proof*)
Lemma strong_inv_list_partial: forall k xh h stats parities,
  0 < xh ->
  0 <= h ->
  h <= fec_max_h ->
  0 <= k <= (fec_n - 1) - fec_max_h ->
  Zlength (find_parity_rows parities h) = Zlength (find_lost stats k) ->
  Zlength (find_parity_rows parities h) = xh ->
  all_strong_inv_list xh xh (submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1) 
    (map Byte.unsigned (find_parity_rows parities h)) (map Byte.unsigned (rev (find_lost stats k)))) 0%Z.
Proof.
  move => k xh h stats parities Hxh Hh Hhmax Hkn Hlens Hlenxh.
  rewrite /all_strong_inv_list. case : (range_le_lt_dec 0 0 xh); try lia.
  move => Hxh0. case : (Z_le_lt_dec xh xh); try lia. move => Hxhtriv.
  remember (find_parity_rows parities h) as row.
  have Hallrow: Forall (fun x => 0 <= Byte.unsigned x < h) row.
    rewrite Heqrow. apply find_parity_rows_bound. rep_lia.
  have Hallrow': Forall (fun x => 0 <= Byte.unsigned x < fec_max_h) row.
    eapply Forall_impl. 2: apply Hallrow. rewrite /=. lia.
  have Halllost: Forall (fun x => 0 <= Byte.unsigned x < k) (find_lost stats k).
    apply find_lost_bound; rep_lia.
  have Halllost': Forall (fun x => 0 <= Byte.unsigned x < fec_n - 1) (find_lost stats k).
    eapply Forall_impl. 2: apply Halllost. rewrite /=. lia. 
  apply Forall_rev in Halllost. apply Forall_rev in Halllost'. rewrite -rev_rev in Halllost.
  rewrite -rev_rev in Halllost'.
  rewrite (@submx_rows_cols_rev_list_spec _ _ fec_max_h (fec_n - 1)) //=; try rep_lia.
  move => Hmaxh Hn. rewrite weight_mx_spec /weights /submx_rows_cols_rev. 
  have Hhnat: (0 < Z.to_nat fec_max_h)%N by (apply /ltP; rep_lia).
  have Hhn: (Z.to_nat fec_max_h <= Z.to_nat (fec_n - 1))%N by (apply /leP; rep_lia).
  (*Need to switch defaults for applying theorem*)
  rewrite (submx_rows_cols_default _ (ord_zero Hmaxh) (ord_zero Hn) (Ordinal Hhnat) ( widen_ord Hhn (Ordinal Hhnat))).
  + have->: (le_Z_N Hxhtriv) = (leqnn (Z.to_nat xh)) by apply bool_irrelevance.
    have H0xh: (0 < Z.to_nat xh)%N by (apply /ltP; lia). have->: Z_to_ord Hxh0 = Ordinal H0xh by apply ord_inj.
    (* for folding all_strong_inv -> strong_inv*)
    have->: forall (F: fieldType) (m n: nat) (A: 'M[F]_(m, n)) (H0m: (0 < m)%N) (Hmn: (m <= n)%N),
      all_strong_inv A Hmn (Ordinal H0m) = strong_inv A H0m Hmn. { move => F m n A H0m Hmn.
      by rewrite /all_strong_inv. }
    have->: H0xh = ord_nonzero (Ordinal H0xh) by apply bool_irrelevance.
    apply any_submx_strong_inv; rewrite //=.
    * by rewrite weight_list_uniq. 
    * apply weight_list_size.
    * apply byte_ord_list_uniq. subst. apply find_parity_rows_NoDup. rep_lia.
    * rewrite map_inj_uniq. 2: { apply rev_ord_inj. }
      apply byte_ord_list_uniq. rewrite rev_rev. apply NoDup_rev. apply find_lost_NoDup; rep_lia.
    * by rewrite size_map !size_length -!ZtoNat_Zlength !byte_ord_list_Zlength // Hlens rev_rev Zlength_rev.
    * by rewrite size_length -ZtoNat_Zlength byte_ord_list_Zlength // Hlenxh.
    * move => x /mapP[y Hyin Hxy]. subst. rewrite /=. 
      apply Z_ord_list_In in Hyin. move: Hyin. rewrite in_map_iff => [[y' [Hy' Hiny']]]. 
      move: Halllost; rewrite Forall_forall => Hallost. apply Hallost in Hiny'.
      rewrite leq_subRL. 2: apply /ltP; lia. rewrite addnC -leq_subRL. 2: apply /leP; lia. apply /ltP.
      have->:(Z.to_nat (fec_n - 1) - Z.to_nat fec_max_h)%N = (Z.to_nat (fec_n - 1) - Z.to_nat fec_max_h)%coq_nat by [].
      lia. apply Z_byte_list_bound. eapply Forall_impl; [| apply Halllost].
      move => a /=. lia.
  + by rewrite size_length -ZtoNat_Zlength byte_ord_list_Zlength // Hlenxh.
  + by rewrite size_map size_length -ZtoNat_Zlength byte_ord_list_Zlength // rev_rev Zlength_rev -Hlens Hlenxh.
  + by apply Z_byte_list_bound.
  + by apply Z_byte_list_bound.
Qed.

(*Trivial case of xh = 0*)
Lemma decode_list_mx_zero: forall k c packets parities stats i,
  0 <= k ->
  0 <= c ->
  Zlength (find_lost stats k) = 0%Z ->
  lmatrix_to_mx k c (decode_list_mx k c packets parities stats i) = 
  lmatrix_to_mx k c (extend_mx k c packets).
Proof.
  move => k c packets parities stats i Hk Hc Hlen0.
  rewrite /decode_list_mx /=. rewrite !Hlen0 /=.
  rewrite fill_rows_list_0 //=. by apply extend_mx_wf.
Qed.

(*First, we prove that this is equivalent to the mathcomp decoder*)
(*LOTS of ordinals and dependent types in here, eventually we will be able to just have a few bounds hypotheses
  that can be solved with [lia]*)
Lemma decode_list_mx_equiv: forall k c h xh packets parities stats (Hk: 0 < k <= (fec_n - 1) - fec_max_h) (Hc: 0 < c)
  (Hh: 0 < h <= fec_max_h) (Hxh: xh <= k) (i: Z),
  0 <= i <= h ->
  let lost := find_lost stats k in
  let row := find_parity_rows parities i in
  Zlength lost = xh ->
  Zlength row = xh ->
  Zlength parities = h ->
  lmatrix_to_mx k c (decode_list_mx k c packets parities stats i) = 
    decoder_mult max_h_n (k_bound_proof (proj2 Hk)) weight_list_size (ord_zero h_pos) (ord_zero n_pos)
      (ord_zero (proj1 Hk)) (ord_zero Hc) (lmatrix_to_mx k c (extend_mx k c packets))
      (lmatrix_to_mx h c (fill_missing c parities))
      (byte_ord_list (rev lost) k) (byte_ord_list row h)
      (le_Z_N (proj2 Hh)) (ord_zero (proj1 Hh)) (le_Z_N Hxh).
Proof.
  move => k c h xh packets parities stats Hk Hc Hh Hxh i Hih. rewrite /=.
  remember (find_parity_rows parities i) as row.
  remember (find_parity_found parities (fec_n - 1) i) as foundp.
  move => Hlenlost Hlenfound Hlenpar.
  have: xh = 0%Z \/ 0 < xh by list_solve. move => [Hxh0 | Hxh0].
  - subst. rewrite (@decode_list_mx_zero k c) //; try lia.
    rewrite decoder_mult_0 //. rewrite size_length -ZtoNat_Zlength.
    rewrite Z_ord_list_Zlength. all: try (rewrite Hxh0; lia).
    rewrite Zlength_map rev_rev Zlength_rev; lia.
    apply Z_byte_list_bound. rewrite rev_rev. apply Forall_rev. apply find_lost_bound; rep_lia.
  - (*Things we will need to know about the lists*)
    have Hlostbound: Forall (fun x => 0 <= Byte.unsigned x < k) (find_lost stats k) by (apply find_lost_bound; rep_lia).
    have Hrowbound: Forall (fun x => 0 <= Byte.unsigned x < i) row. {
      subst. apply find_parity_rows_bound; rep_lia. }
    have Hfoundbound: Forall (fun x => 0 <= Byte.unsigned x < k) (find_found stats k) by apply find_found_bound; rep_lia.
    have Hfoundpbound: Forall (fun x => 0 <= Byte.unsigned x < fec_n - 1) foundp.
      subst. apply find_parity_found_bound; rep_lia. 
    have Hrowbound': Forall (fun x : byte => 0 <= Byte.unsigned x < h) row. {
      eapply Forall_impl. 2: apply Hrowbound. rewrite /=. lia. }
    have Hrowbound'': Forall (fun x : byte => 0 <= Byte.unsigned x < fec_max_h) row. {
      eapply Forall_impl. 2: apply Hrowbound. rewrite /=. lia. }
    (*have Hxh0: 0 <= xh by list_solve.*)
    (*have Hlenlost': Zlength (rev (find_lost stats k)) = xh  by rewrite rev_rev Zlength_rev.*)
    rewrite /decode_list_mx Hlenlost /decoder_mult fill_rows_list_spec //; try lia.
    move => Hk0. f_equal.
    rewrite lmatrix_multiply_correct. 2: { apply right_submx_wf; rep_lia. }
    2 : { apply lmatrix_multiply_wf; rep_lia. }
    2 : {  by apply ord_inj. }
    rewrite find_invmx_list_spec. 2 : {
      apply strong_inv_list_partial; try lia. by subst. by subst. }
    2 : { rewrite map_rev rev_rev. apply NoDup_rev. apply NoDup_map_inj.
          move => b1 b2 Hinb1 Hinb2. apply byte_unsigned_inj. apply find_lost_NoDup; rep_lia. }
    2: by rewrite map_rev rev_rev; apply Forall_rev; apply Z_byte_list_bound.
    2: by rewrite Zlength_map rev_rev Zlength_rev.
    f_equal.
    + rewrite (@submx_rows_cols_rev_list_spec _ _ (fec_max_h) (fec_n - 1) xh xh) //; try lia.
      * move => Hh0 Hn0. f_equal. f_equal.
        -- apply weight_mx_spec.
        -- subst. by apply byte_ord_list_widen. 
        -- apply byte_ord_list_widen. by rewrite rev_rev; apply Forall_rev.
        -- by apply ord_inj.
        -- by apply ord_inj.
      * subst. by apply Z_byte_list_bound.
      * have Hkn: k <= fec_n - 1 by lia. apply Z_byte_list_bound.
        rewrite rev_rev. apply Forall_rev. by apply (forall_lt_leq_trans Hkn). 
    + rewrite lmatrix_multiply_correct. 2: { apply submx_rows_cols_rev_list_wf; lia. }
      2 : { have Hkxh: k = (k - xh) + xh by lia. rewrite {5}Hkxh. apply col_mx_list_wf; lia. }
      rewrite (@submx_rows_cols_rev_list_spec _ _ fec_max_h) //; try lia.
      2 : {  subst; by apply Z_byte_list_bound. }
      2 : { subst. rewrite map_cat Forall_app. split; apply Z_byte_list_bound.
            have Hkn: (k <= fec_n - 1) by lia. by apply (forall_lt_leq_trans Hkn). by []. }
      move => Hh0 Hn0. f_equal.
      * f_equal.
        -- apply weight_mx_spec.
        -- subst; by apply byte_ord_list_widen.
        -- rewrite byte_ord_list_fold byte_ord_list_app. f_equal.
          ++ rewrite (byte_ord_list_widen (k_leq_n (k_bound_proof (proj2 Hk)))) // find_lost_found_comp //.
             f_equal. apply ord_comp_rev. rep_lia.
          ++ have Hinhab: Inhabitant 'I_(Z.to_nat (fec_n - 1)) by apply (ord_zero Hn0).
             have Hfoundpbound': Forall (fun x => 0 <= Byte.unsigned x < fec_n - 1) (find_parity_found parities (fec_n - 1) i ) by subst.
             apply Znth_eq_ext. 
             ** rewrite Zlength_map !Z_ord_list_Zlength //. subst. by rewrite !Zlength_map find_parity_rows_found_Zlength.
                by apply Z_byte_list_bound. by apply Z_byte_list_bound.
             ** move => i'. rewrite !byte_ord_list_Zlength //  => Hi'.
                have Hinhabh: Inhabitant 'I_(Z.to_nat h). apply (ord_zero (proj1 Hh)).
                rewrite Znth_map //.
                { have Hilen: 0 <= i' < Zlength row. subst. by rewrite find_parity_rows_found_Zlength in Hi'.
                  rewrite !Z_ord_list_Znth' //; try lia. by apply Z_byte_list_bound.
                  by rewrite Zlength_map. by apply Z_byte_list_bound. by rewrite Zlength_map.
                  move => Hbound1 Hlen1 Hbound2 Hlen2.
                  apply ord_inj. subst. rewrite /= !Znth_map // find_parity_rows_found_Znth //=; try rep_lia.
                  have->: (Z.to_nat (fec_n - 1) - 1 - Z.to_nat (Byte.unsigned (Znth i' (find_parity_rows parities i))))%N =
                        ((Z.to_nat (fec_n - 1) - 1)%coq_nat - Z.to_nat (Byte.unsigned (Znth i' (find_parity_rows parities i))))%coq_nat by [].
                  rewrite !Z2Nat.inj_sub; rep_lia.
                }
                { subst. rewrite Z_ord_list_Zlength //. rewrite find_parity_rows_found_Zlength in Hi'.
                  by rewrite Zlength_map. by apply Z_byte_list_bound.
                }
        -- by apply ord_inj.
        -- by apply ord_inj.
      * rewrite (@lmatrix_to_mx_cast _ k ((k - xh) + xh) c c). lia. move => Hkxh.
        rewrite col_mx_list_spec; try lia. move => Hkxh0 Hxh0'. rewrite castmx_twice.
        rewrite (@submx_rows_cols_list_equiv _ _ k c (k-xh) c) //=; try lia.
        2: { by apply Z_byte_list_bound. }
        2 : { rewrite Forall_forall => y. rewrite Ziota_In; lia. }
        rewrite -matrixP => x y.
        rewrite !castmxE /= !mxE /=.
        pose proof (splitP (cast_ord (esym (etrans (Logic.eq_sym (Z2Nat.inj_add (k - xh) xh Hkxh0 Hxh0')) (Z_to_nat_eq Hkxh))) x)).
        case : X => [j /= Hj | k' /= Hk'].
        { rewrite !mxE /=. pose proof (splitP (cast_ord (esym (subnK (le_Z_N Hxh))) x)).
          case : X => [j' /= Hj' | k'' /= Hk''].
          { rewrite !mxE /=. f_equal; f_equal. rewrite byte_ord_list_fold find_lost_found_comp //.
            rewrite -Hj Hj' /=. have->:(ord_zero Hk0 = (ord_zero (proj1 Hk))) by apply ord_inj.
            f_equal. by rewrite ord_comp_rev. rep_lia.
            rewrite Z_ord_list_iota //. lia. }
          { have /ltP Hx: (x < Z.to_nat (k - xh))%N by rewrite Hj.
            move: Hk''; have->: (Z.to_nat k - Z.to_nat xh + k'')%N = ((Z.to_nat k - Z.to_nat xh)%coq_nat + k'')%coq_nat by [] => Hk''. 
            lia. }
        }
        { pose proof (splitP (cast_ord (esym (subnK (le_Z_N Hxh))) x)).
          case : X => [j' /= Hj' | k'' /= Hk''].
          { have /ltP Hx: (x < (Z.to_nat k - Z.to_nat xh)%coq_nat)%N by rewrite Hj'.
            move: Hk'; have->:(Z.to_nat (k - xh) + k')%N = (Z.to_nat (k - xh) + k')%coq_nat by [] => Hk'. lia.
          }
          { rewrite !mxE !mk_lmatrix_get; try lia. f_equal.
            have->:(nat_of_ord k'') = Z.to_nat (Z.of_nat k'') by rewrite Nat2Z.id.
            have->: k' = k''. move: Hk'' => /eqP Hx. move: Hx. rewrite Hk' Z2Nat.inj_sub; try lia.
            have->: (Z.to_nat k - Z.to_nat xh)%coq_nat = (Z.to_nat k - Z.to_nat xh)%N by [].
            rewrite eqn_add2l => /eqP Hx. by apply ord_inj.
            rewrite -Z_ord_list_Znth //. by subst. lia. by apply Z_byte_list_bound. rewrite nth_ord_enum Znth_Ziota //=. lia.
            apply Z_ord_bound; lia. apply Z_ord_bound; lia. apply Z_ord_bound; lia. }
        }
Qed.

(*Are the parity packets valid? To be valid, we require that all the "Some" entries are the actual rows produced
  by the encoder. It's a bit awkward to state this in Coq*)

Definition parities_valid k c parities data :=
  forall i j, 0 <= i < Zlength parities -> 0 <= j < c ->
    match (Znth i parities) with
      | Some par => Znth j par = Znth j (Znth i (encoder_list (Zlength parities) k c data))
      | _ => True
    end.

(*The correctness theorem for the decoder, at the matrix level. We will convert this back to list(list Z) and give
  more convenient preconditions for clients of the VST code*)
Lemma decoder_list_mx_correct:forall k c h xh data packets parities stats i,
  0 < k <= fec_n - 1 - fec_max_h ->
  0 < c ->
  0 < h <= fec_max_h ->
  xh <= h ->
  xh <= k ->
  0 <= i <= h ->
  Zlength (find_lost stats k) = xh ->
  Zlength (find_parity_rows parities i) = xh ->
  Zlength parities = h ->
  Zlength stats = k ->
  Zlength packets = k ->
  Zlength data = k ->
  Forall (fun l => Zlength l <= c) data ->
  (forall l, In (Some l) parities -> Zlength l = c) ->
  (forall i, 0 <= i < k -> Byte.signed (Znth i stats) <> 1%Z -> Znth i packets = Znth i data) ->
  parities_valid k c parities data ->
  lmatrix_to_mx k c (decode_list_mx k c packets parities stats i) = (lmatrix_to_mx k c (extend_mx k c data)).
Proof.
  move => k c h xh data packets parities stats i Hkn Hc Hhh Hxhh Hxhk Hih Hlostlen Hrowslen Hparlen Hstatslen Hpacklen 
    Hdatalen Hdatalens Hparlens Hfound Hpars.
  (*Things we need multiple times*)
  have Hstatsun: uniq (byte_ord_list (rev (find_lost stats k)) k). { apply byte_ord_list_uniq.
    rewrite rev_rev. apply NoDup_rev.  apply find_lost_NoDup. rep_lia. }
  have Hrowsun : uniq (byte_ord_list (find_parity_rows parities i) h). { apply byte_ord_list_uniq.
     apply find_parity_rows_NoDup. rep_lia. }
  have Hstatssz: size (byte_ord_list (rev (find_lost stats k)) k) = Z.to_nat xh. { rewrite size_length 
    -ZtoNat_Zlength byte_ord_list_Zlength //= rev_rev. by rewrite Zlength_rev Hlostlen. apply Forall_rev.
    apply find_lost_bound; rep_lia. }
  have Hrowbound: Forall (fun x : byte => 0 <= Byte.unsigned x < h) (find_parity_rows parities i). {
    eapply Forall_impl. 2: apply find_parity_rows_bound. rewrite /=. lia. rep_lia. }
  have Hrowssz: size (byte_ord_list (find_parity_rows parities i) h) = Z.to_nat xh. { rewrite size_length -ZtoNat_Zlength
    byte_ord_list_Zlength. by rewrite Hrowslen. by [].  }
  rewrite (@decode_list_mx_equiv _ _ _ _ packets parities stats Hkn Hc Hhh Hxhk) // decoder_equivalent //=.
  - rewrite (decoder_correct (data:=(lmatrix_to_mx k c (extend_mx k c data))) max_h_n weight_list_uniq weight_list_size (ord_zero h_pos) (ord_zero n_pos) 
        (ord_zero (proj1 Hkn)) (ord_zero Hc) (le_Z_N Hxhh) ) //.
    + move => x y. rewrite !mxE !extend_mx_spec; try (apply Z_ord_bound; lia).
       have /ltP Hx: ((nat_of_ord x) < Z.to_nat k)%N by [].  
      rewrite byte_ord_list_notin //=. 2: rewrite rev_rev; apply Forall_rev; apply find_lost_bound; rep_lia. 2: rep_lia.
      rewrite rev_rev -in_rev.
      rewrite -find_lost_found_in; try rep_lia. 2: rewrite Byte.unsigned_repr; rep_lia. 
      rewrite find_lost_found_aux_in_spec /= => [[Hfalse // | [Htriv Hstats]] |].
      rewrite Byte.unsigned_repr in Hstats; try rep_lia.
      have Hstatsx: Byte.signed (Znth (Z.of_nat x) stats) <> 1%Z
        by move : Hstats; case : (Z.eq_dec (Byte.signed (Znth (Z.of_nat x) stats)) 1%Z).
      apply Hfound in Hstatsx. by rewrite Hstatsx. lia. rewrite Forall_forall => a.
      rewrite Ziota_In; rep_lia. 
    + move => x y. have /ltP Hxh: ((nat_of_ord x) < Z.to_nat h)%N by []. 
      rewrite byte_ord_list_In //. 2: rep_lia.
      rewrite find_parity_aux_in_iff /= => [[ Hfalse // | [Htriv [p Hnthx]]]|].
      rewrite Byte.unsigned_repr in Hnthx; try rep_lia.
      rewrite mxE. have Hx: (0 <= Z.of_nat x < h) by (apply Z_ord_bound; lia).
      have Hx': (0 <= Z.of_nat x < Zlength parities) by lia.
      have  Hy: (0 <= Z.of_nat y < c) by (apply Z_ord_bound; lia).
      move: Hpars; rewrite /parities_valid => /(_ (Z.of_nat x) (Z.of_nat y) Hx' Hy).
      rewrite Hnthx /= (fill_missing_mx_some Hnthx) //=.
      * move ->. have [Henc [ Hc0 Hinenc]]: wf_lmatrix (encoder_list (Zlength parities) k c data) (Zlength parities) c. {
          apply lmatrix_multiply_wf; lia. }
        rewrite -(@matrix_to_mx_get _ _ _ (encoder_list h k c data)) //=. by rewrite Hparlen. 
        rewrite -Henc in Hx'.
        have Hkn': k <= fec_n - 1  by lia. 
        have->: (k_leq_n (k_bound_proof (proj2 Hkn))) = le_Z_N Hkn' by  apply bool_irrelevance.
        rewrite -weight_mx_spec. by apply encoder_spec; try lia.
      * apply Hparlens; rewrite -Hnthx. apply Znth_In. lia.
      * rewrite Forall_forall. move => a. rewrite Ziota_In; rep_lia.
  - apply weight_list_uniq.
Qed.

(*For the decoder preconditions, we don't want to explicitly mention [find_lost] and [find_parity_rows], especially
  since only the length is important. So we will use [filter] instead, which should be easier to reason about*)
Lemma find_lost_found_aux_Zlength_base: forall f g base pack l,
  Zlength (find_lost_found_aux f g base pack l) = Zlength base + Zlength (find_lost_found_aux f g [::] pack l).
Proof.
  move => f g base pack l. move: base. elim : l => [//= base| h t /= IH base].
  - list_solve.
  - rewrite IH (IH (if f (Znth h pack) then [:: g h] else [::])). case Hf: (f (Znth h pack)).
    + rewrite Zlength_app. lia.
    + list_solve.
Qed.

(*Need a pretty strong IH, so use sublists*)
Lemma find_lost_found_aux_filter_sublist: forall f g pack (hi : nat),
  (Z.of_nat hi <= Zlength pack) ->
  Zlength (find_lost_found_aux f g [::] pack (Ziota 0 (Z.of_nat hi))) = 
  Zlength (filter f (sublist 0 (Z.of_nat hi) pack)).
Proof.
  move => f g pack hi. elim : hi => [//= | hi IH Hlen].
  have->: (Z.of_nat hi.+1) = (Z.of_nat hi + 1)%Z by lia. rewrite Ziota_plus_1; try lia.
  rewrite sublist_last_1; try lia. rewrite find_lost_found_aux_app find_lost_found_aux_Zlength_base /= filter_cat /=.
  rewrite IH //. rewrite Zlength_app !Z.add_0_l //.
  case Hf: (f (Znth (Z.of_nat hi) pack)); list_solve.
  lia.
Qed.

(*Now we can state the precondition in terms of filter, so a client doesn't need to know anything about
  [find_lost]*)

Lemma find_lost_filter: forall stats k,
  k = Zlength stats ->
  Zlength (find_lost stats k) = Zlength (filter (fun x => Z.eq_dec (Byte.signed x) 1) stats).
Proof.
  move => stats k Hk. have Hk0: 0 <= k by list_solve.
  have ->: k = Z.of_nat (Z.to_nat k) by lia. rewrite find_lost_found_aux_filter_sublist; try lia.
  rewrite sublist_same //. lia.
Qed.

(*Similar thing for parities*)

Lemma find_parity_aux_app: forall f par base l1 l2,
  find_parity_aux f par base (l1 ++ l2) =
  find_parity_aux f par (find_parity_aux f par base l1) l2.
Proof.
  move => f par b l1 l2. by rewrite /find_parity_aux fold_left_app.
Qed.

Lemma find_parity_aux_base: forall f par base l1,
  find_parity_aux f par base l1 = base ++ find_parity_aux f par [::] l1.
Proof.
  move => f par base l1. move : base. elim : l1 => [//= base | /= h t IH base].
  - by rewrite cats0. 
  - rewrite IH (IH (match Znth h par with  | Some _ => [:: f h]  | None => [::] end)). 
    case Hh: (Znth h par) => [o /= | //]. by rewrite -catA.
Qed.

Lemma find_parity_aux_app': forall f par base l1 l2,
  find_parity_aux f par base (l1 ++ l2) =
  find_parity_aux f par base l1 ++ find_parity_aux f par [::] l2.
Proof.
  move => f par base l1 l2. by rewrite find_parity_aux_app find_parity_aux_base.
Qed.

Lemma find_parity_aux_filter_sublist: forall f (par : seq (option (seq byte))) (hi: nat),
  (Z.of_nat hi <= Zlength par) ->
  Zlength (find_parity_aux f par [::] (Ziota 0 (Z.of_nat hi))) = 
  Zlength (filter isSome (sublist 0 (Z.of_nat hi) par)).
Proof.
  move => f par hi. elim : hi => [//= | hi IH Hlen].
  have->: (Z.of_nat hi.+1) = (Z.of_nat hi + 1)%Z by lia. rewrite Ziota_plus_1; try lia.
  rewrite sublist_last_1; try lia. rewrite find_parity_aux_app find_parity_aux_base_Zlength /= filter_cat /=.
  rewrite IH //. 2: lia. rewrite Zlength_app !Z.add_0_l //.
  by case Hf: (Znth (Z.of_nat hi) par).
Qed.

(*Now we can state the precondition in terms of filter, so a client doesn't need to know anything about
  [find_parity_rows]*)
Lemma find_parity_rows_filter: forall parities i,
  0 <= i <= Zlength parities ->
  Zlength (find_parity_rows parities i) = Zlength (filter isSome (sublist 0 i parities)).
Proof.
  move => pars i Hi. 
  have ->: i = Z.of_nat (Z.to_nat i) by lia. rewrite find_parity_aux_filter_sublist; lia.
Qed.

(*We also use this for an injectivity lemma we will need in the VST proof*)
Lemma find_parity_rows_inj_aux: forall parities i j,
  0 <= i <= j ->
  Zlength (find_parity_rows parities i) <= Zlength (find_parity_rows parities j).
Proof.
  move => par i j Hij. rewrite /find_parity_rows.
  rewrite (Ziota_leq Hij) find_parity_aux_app (find_parity_aux_base_Zlength _ _ (find_parity_aux Byte.repr par [::] (Ziota 0 i))).
  list_solve.
Qed.

Lemma find_parity_rows_inj: forall parities i j,
  0 <= i ->
  0 <= j ->
  Zlength (find_parity_rows parities i) < Zlength (find_parity_rows parities j) ->
  i < j.
Proof.
  move => parities i j Hi Hj Hlens.
  have [Hij // | Hij]: (i < j \/ j <= i) by lia.
  have Hij': 0 <= j <= i by lia. 
  pose proof (@find_parity_rows_inj_aux parities _ _ Hij'). lia.
Qed.

(*Want to prove that if we have find_parity_rows (or found) for i and j, if the lengths are the same,
  so are the lists. This way, we don't need some condition on the decoder input that makes i unique*)

Lemma find_parity_aux_eq: forall f parities base i j,
  0 <= i <= j->
  Zlength (find_parity_aux f parities base (Ziota 0 i)) = Zlength (find_parity_aux f parities base (Ziota 0 j)) <->
  (find_parity_aux f parities base (Ziota 0 i)) = (find_parity_aux f parities base (Ziota 0 j)).
Proof.
  move => f par base i j Hij. rewrite (Ziota_leq Hij) find_parity_aux_app' Zlength_app.
  split.
  - move => Hlen. have Hnil: Zlength (find_parity_aux f par [::] (Ziota i (j - i))) = 0 by list_solve.
    apply Zlength_nil_inv in Hnil. by rewrite Hnil cats0.
  - move => /esym Happ. apply cat_extra in Happ. rewrite Happ. list_solve.
Qed.

Lemma find_parity_aux_eq': forall f parities base i j,
  0 <= i ->
  0 <= j ->
  Zlength (find_parity_aux f parities base (Ziota 0 i)) = Zlength (find_parity_aux f parities base (Ziota 0 j)) <->
  (find_parity_aux f parities base (Ziota 0 i)) = (find_parity_aux f parities base (Ziota 0 j)).
Proof.
  move => f par base i j Hi Hj. 
  have [Hij | Hji]: (0 <= i <= j \/ 0 <= j <= i) by lia.
  - by apply find_parity_aux_eq.
  - by split; move => H; symmetry; apply find_parity_aux_eq.
Qed.

Lemma find_parity_rows_eq: forall parities i j,
  0 <= i ->
  0 <= j ->
  Zlength (find_parity_rows parities i) = Zlength (find_parity_rows parities j) <->
  find_parity_rows parities i = find_parity_rows parities j.
Proof.
  move => par i j Hi Hj. by apply find_parity_aux_eq'.
Qed.

Lemma find_parity_found_eq: forall parities max i j,
  0 <= i ->
  0 <= j ->
  Zlength (find_parity_found parities max i) = Zlength (find_parity_found parities max j) <->
  find_parity_found parities max i = find_parity_found parities max j.
Proof.
  move => par max i j Hi Hj. by apply find_parity_aux_eq'.
Qed.


(** Final Definition of Decoder and Correctness*)

(*Our final decoder definition does everything in terms of lists and bytes, making it useful for VST*)
Definition decoder_list k c packets parities stats lens i :=
  crop_mx (decode_list_mx k c packets parities stats i) lens.

Lemma decoder_list_correct_0: forall k c packets parities stats lens i,
  0 <= c ->
  k = Zlength stats ->
  k = Zlength packets ->
  k = Zlength lens ->
  (forall i, 0 <= i < k -> Znth i lens = Zlength (Znth i packets)) ->
  Forall (fun x => Zlength x <= c) packets ->
  Zlength (filter (fun x => Z.eq_dec (Byte.signed x) 1) stats) = 0 ->
  decoder_list k c packets parities stats lens i = packets.
Proof.
  move => k c packets parities stats lens i Hc Hkstat Hkpack Hklens Hlens Hlenbound. 
  rewrite /decoder_list -(@find_lost_filter _ k) // => Hlen.
  have Hk: 0 <= k by list_solve.
  pose proof (@decode_list_mx_zero k c packets parities stats i Hk Hc Hlen) as Hmx.
  apply lmatrix_to_mx_inj in Hmx.
  - rewrite Hmx Hkpack crop_extend //. lia. by rewrite -Hkpack.
  - apply fill_rows_list_wf; lia.
  - apply extend_mx_wf; list_solve.
Qed.

Definition pad_packets (packets : list(list byte)) lens c :=
  crop_mx (extend_mx (Zlength packets) c packets) lens.

(*Spec for [pad_packets]*)

(*In general, we get the original packet padded with some extra zeroes based on lengths array*)
Lemma pad_packets_nth: forall (packets: list (list byte)) lens c i,
  0 <= i < Zlength packets ->
  Zlength (Znth i packets) <= Znth i lens <= c ->
  Znth i (pad_packets packets lens c) = (Znth i packets) ++ zseq ((Znth i lens) - Zlength (Znth i packets)) Byte.zero.
Proof.
  move => packets lens c i Hi Hlen.
  have Hc: 0 <= c by list_solve.
  pose proof (extend_mx_wf packets Hc (Zlength_nonneg packets)) as [Hextlen [_ Hextlens]].
  have Hpadlen: Zlength (Znth i (pad_packets packets lens c)) = Znth i lens. {
    rewrite /pad_packets crop_mx_length; try lia.
    move: Hextlens. rewrite Forall_Znth Hextlen => /(_ i Hi) ->. list_solve. }
  apply Znth_eq_ext.
  - rewrite Hpadlen Zlength_app zseq_Zlength; try lia. by rewrite Zplus_minus. (*lia should solve*)
  - rewrite Hpadlen => j Hj.  rewrite /pad_packets /crop_mx Znth_map; rewrite ?Zlength_Ziota; try lia.
    rewrite Hextlen Znth_Ziota; try lia. have->:0+i = i by lia.
    rewrite /extend_mx /mk_lmatrix mkseqZ_Znth; try lia.
    rewrite Znth_sublist; try lia. rewrite Z.add_0_r mkseqZ_Znth; try lia.
    case : (Z_lt_le_dec j (Zlength (Znth i packets))) => Hjlen/=.
    + by rewrite Znth_app1.
    + rewrite Znth_app2; simpl in *; try lia. by rewrite zseq_Znth; try lia.
Qed.

Theorem decoder_list_correct_full: forall k c h xh (data packets : list (list byte)) 
  (parities : list (option (list byte))) (stats : list byte) (lens : list Z) (parbound: Z),
  0 < k <= fec_n - 1 - fec_max_h ->
  0 < c ->
  0 < h <= fec_max_h ->
  xh <= h ->
  xh <= k ->
  0 <= parbound <= h ->
  Zlength (filter (fun x => Z.eq_dec (Byte.signed x) 1) stats) = xh ->
  Zlength (filter isSome (sublist 0 parbound parities)) = xh ->
  Zlength parities = h ->
  Zlength stats = k ->
  Zlength packets = k ->
  Zlength data = k ->
  Forall (fun l => Zlength l <= c) data ->
  (forall i, 0 <= i < k -> Byte.signed (Znth i stats) <> 1%Z -> Znth i packets = Znth i data) ->
  (forall l, In (Some l) parities -> Zlength l = c) ->
  parities_valid k c parities data ->
  decoder_list k c packets parities stats lens parbound = pad_packets data lens c.
Proof.
  move => k c h xh data packets parities stats lens parbound Hknh Hc Hh Hxhh Hxhk Hbp Hstatsxh Hparsxh Hparlen
    Hstatlen Hpacklen Hdatalen Hdatac Hpackdata Hparlens Hparvalid.
  rewrite /decoder_list. 
  have Hmx: lmatrix_to_mx k c (decode_list_mx k c packets parities stats parbound) = 
    (lmatrix_to_mx k c (extend_mx (F:=B) k c data)). { 
    apply (decoder_list_mx_correct Hknh Hc Hh Hxhh); try by [].
    - by rewrite find_lost_filter.
    - rewrite find_parity_rows_filter. apply Hparsxh. lia. }
  apply lmatrix_to_mx_inj in Hmx. 
  - rewrite /pad_packets. f_equal. rewrite Hmx. f_equal. lia.
  - apply fill_rows_list_wf; lia.
  - apply extend_mx_wf; lia.
Qed.



(*If the lengths array is correct (rather than an overestimate), we get the original packet*)
Lemma pad_packets_full: forall (packets: list (list byte)) lens c i,
  0 <= i < Zlength packets ->
  Zlength (Znth i packets) = Znth i lens ->
  Zlength (Znth i packets) <= c ->
  Znth i (pad_packets packets lens c) = Znth i packets.
Proof.
  move => packets lens c i Hi Hlen Hc.
  rewrite pad_packets_nth; try lia. 
  by rewrite Hlen Z.sub_diag /zseq /= cats0.
Qed.

(*As a corollary, if all the lengths are correct, we exactly recover the original data*)
Theorem decoder_list_correct: forall k c h xh (data packets : list (list byte)) 
  (parities : list (option (list byte))) (stats : list byte) (lens : list Z) (parbound: Z),
  0 < k <= fec_n - 1 - fec_max_h ->
  0 < c ->
  0 < h <= fec_max_h ->
  xh <= h ->
  xh <= k ->
  0 <= parbound <= h ->
  Zlength (filter (fun x => Z.eq_dec (Byte.signed x) 1) stats) = xh ->
  Zlength (filter isSome (sublist 0 parbound parities)) = xh ->
  Zlength parities = h ->
  Zlength stats = k ->
  Zlength packets = k ->
  Zlength data = k ->
  Zlength lens = k ->
  (forall i, 0 <= i < k -> Znth i lens = Zlength (Znth i data)) ->
  Forall (fun l => Zlength l <= c) data ->
  (forall i, 0 <= i < k -> Byte.signed (Znth i stats) <> 1%Z -> Znth i packets = Znth i data) ->
  (forall l, In (Some l) parities -> Zlength l = c) ->
  parities_valid k c parities data ->
  decoder_list k c packets parities stats lens parbound = data.
Proof.
  move => k c h xh data packets parities stats lens parbound Hknh Hc Hh Hxhh Hxhk Hbp Hstatsxh Hparsxh Hparlen
    Hstatlen Hpacklen Hdatalen Hlenslen Hlens Hdatac Hpackdata Hparlens Hparvalid.
  rewrite (decoder_list_correct_full (h:=h)(xh:=xh)(data:=data)); try by [].
  rewrite /pad_packets. rewrite crop_extend; try by []. lia. by rewrite Hdatalen Hlenslen.
  by rewrite Hdatalen.
Qed.

End Decoder.