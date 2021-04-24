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
Definition encode_list_mx (h k c : Z) (packets : lmatrix B) : lmatrix B :=
  list_lmatrix_multiply h k c (submatrix (fec_n - 1) weight_mx h k) 
      (extend_mx k c packets).

(*Lift the above into ssreflect matrices and operations*)
Lemma encoder_spec : forall (h k c : Z) (packets: lmatrix B) (Hh: h <= fec_max_h) (Hk: k <= fec_n - 1),
  0 <= h ->
  0 <= k ->
  0 <= c ->
  Zlength packets = k ->
  Forall (fun x => Zlength x <= c) packets ->
  lmatrix_to_mx h c (encode_list_mx h k c packets) = encoder (le_Z_N Hh) (le_Z_N Hk)
    (lmatrix_to_mx fec_max_h (fec_n - 1) weight_mx) 
    (lmatrix_to_mx k c (extend_mx k c packets)).
Proof.
  move => h k c packets Hh Hk Hn0 Hk0 Hc0 Hlen Hin. rewrite /encode_list_mx /encoder.
  have Hwf: wf_lmatrix weight_mx fec_max_h (fec_n - 1) by apply weight_mx_wf. 
  rewrite list_lmatrix_multiply_correct.
  by rewrite (@submatrix_to_mx _ (fec_max_h) (fec_n - 1) _ _ _ Hh Hk).
  by apply submatrix_wf.
  by apply extend_mx_wf. 
Qed.

End Encoder.

Section Decoder.

(** Intermediate functions*)

(*Get lost and found packets*)
Definition find_lost_found_aux (f: Z -> bool) (g: Z -> Z) base pack l : list Z :=
  fold_left (fun acc x => if f (Znth x pack) then acc ++ [:: g x] else acc) l base.

Lemma find_lost_found_aux_bound: forall f g base pack l b,
  (forall x, In x l -> 0 <= g x < b) ->
  (forall x, In x base -> 0 <= x < b) ->
  Forall (fun x => 0 <= x < b) (find_lost_found_aux f g base pack l).
Proof.
  move => f g base pack l b Hg Hbase. 
  rewrite /find_lost_found_aux Forall_forall. move : base Hbase Hg.
  elim : l => [ //= | h t /= IH base Hbase Hg x].
  case Hh: (f (Znth h pack)); apply IH; rewrite //=.
  - move => z Hin. apply in_app_or in Hin. case : Hin => [Hin | [Hzh | Hfalse]]; rewrite //.
    + by apply Hbase.
    + subst. apply Hg. by left.
  - move => z Hin. apply Hg. by right.
  - move => z Hin. apply Hg. by right.
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
  (forall x, In x l -> 0 <= x < b) ->
  In x (find_lost_found_aux f id [::] stats l) ->
  0 <= x < b.
Proof.
  move => f stats l x b Hl Hin.
  have Htriv: (forall x : Z, In x [::] -> 0 <= x < b) by [].
  pose proof (@find_lost_found_aux_bound f id [::] stats l b Hl Htriv) as Hall.
  by move: Hall; rewrite Forall_forall => /(_ _ Hin).
Qed.

Lemma find_lost_found_aux_in_spec: forall f base pack l x,
  In x (find_lost_found_aux f id base pack l) <-> In x base \/ (In x l /\ f (Znth x pack)).
Proof.
  move => f base pack l x. move : base. elim : l => [//= base | h t /= IH base].
  - by split => [Hin | [Hin | [Hfalse Hf]]]; try left.
  - case Hfh : (f (Znth h pack)).
    + rewrite IH in_app_iff /= binop_lemmas2.or_False or_assoc. apply or_iff_compat_l.
      split.
      * move => [Hxh | [Hin Hh]].
        -- subst. split. by left. by [].
        -- split. by right. by [].
      * move => [[Hxh | Hin] Hf].
        -- subst. by left.
        -- right. by split.
    + rewrite IH. apply or_iff_compat_l. split.
      * move => [Hin Hf]. split. by right. by [].
      * move => [[Hhx | Hin] Hf]. subst. by rewrite Hf in Hfh. by split.
Qed.  

(*First, get the lost packets*)
Definition find_lost (stats: list Z) (k: Z) : list Z :=
  find_lost_found_aux (fun x => Z.eq_dec x 1%Z) id nil stats (Ziota 0 k).

Lemma find_lost_bound: forall l k,
  0 <= k ->
  Forall (fun x : Z => 0 <= x < k) (find_lost l k).
Proof.
  move => l k Hk. apply find_lost_found_aux_bound; try by [].
  move => x. rewrite Ziota_In; lia. 
Qed.

Lemma find_lost_NoDup: forall l k,
  NoDup (find_lost l k).
Proof.
  move => l k. apply find_lost_found_aux_NoDup'; try by [].
  apply Ziota_NoDup.
Qed.

(*the first part of the found array*)
Definition find_found (stats: list Z) (k: Z) : list Z :=
  find_lost_found_aux (fun x => negb (Z.eq_dec x 1%Z)) id nil stats (Ziota 0 k).

Lemma find_found_bound: forall l k,
  0 <= k ->
  Forall (fun x : Z => 0 <= x < k) (find_found l k).
Proof.
  move => l k Hk. apply find_lost_found_aux_bound; try by []. move => x. by rewrite Ziota_In; lia.
Qed.

Lemma find_found_NoDup: forall l k,
  NoDup (find_found l k).
Proof.
  move => l k. apply find_lost_found_aux_NoDup'; try by [].
  apply Ziota_NoDup.
Qed.

(*Lost and found are complements*)
Lemma find_lost_found_comp_nat: forall stats k,
  map (Z.to_nat) (find_found stats k) =
  nat_comp (Z.to_nat k) (map Z.to_nat (find_lost stats k)).
Proof.
  move => stats k. rewrite /find_found /find_lost /Ziota /=.
  elim : (Z.to_nat k) => [//= | n IH]. rewrite nat_comp_plus_one !iota_plus_1 /= !map_cat /= !add0n !find_lost_found_aux_app /=.
  case: (Z.eq_dec (Znth (Z.of_nat n) stats) 1) => [/= Hn1 | /= Hn0].
  - have->:n
    \in [seq Z.to_nat i
           | i <- find_lost_found_aux (fun x : Z => Z.eq_dec x 1) id [::] stats
                    [seq Z.of_nat y | y <- iota 0 n] ++ [:: Z.of_nat n]]
    by rewrite map_cat /= mem_cat Nat2Z.id in_cons eq_refl orbT.
    rewrite map_cat /= Nat2Z.id nat_comp_app. apply IH.
  - have->:n
    \in [seq Z.to_nat i
           | i <- find_lost_found_aux (fun x : Z => Z.eq_dec x 1) id [::] stats
                    [seq Z.of_nat y | y <- iota 0 n]] = false. {
    apply /negPf /negP; rewrite in_mem_In in_map_iff => [[x [Hxn Hinx]]].
    subst. apply (@find_lost_found_aux_in _ _ _ _  x) in Hinx. lia.
    move => y. rewrite in_map_iff => [[x' [Hx' Hin]]]. subst. move: Hin.
    rewrite -in_mem_In mem_iota add0n => /andP[/leP Hx0 /ltP Hxx]. lia. }
    by rewrite map_cat /= Nat2Z.id IH.
Qed.

Lemma find_lost_found_comp: forall stats k,
  0 <= k ->
  Z_ord_list (find_found stats k) k =
  (ord_comp (Z_ord_list (find_lost stats k) k)).
Proof.
  (*do widen_ord stuff separately*)
  move => stats k Hk. rewrite {1}/Z_ord_list /ord_comp find_lost_found_comp_nat.
  f_equal. f_equal. pose proof (find_lost_bound stats Hk) as Hbound.
   have[H0k | H0k]: k = 0%Z \/ 0 < k by lia.
  - subst. by [].
  - apply Znth_eq_ext.
    + by rewrite !Zlength_map Z_ord_list_Zlength.
    + move => i. rewrite Zlength_map => Hi.
      have Hinhab: Inhabitant 'I_(Z.to_nat k). apply (ord_zero H0k).
      rewrite !Znth_map //=.
      * by rewrite Z_ord_list_Znth'.
      * by rewrite Z_ord_list_Zlength.
Qed.

(*The following is weaker but needed in the decoder correctness*)
Lemma find_lost_found_in: forall l k x,
  0 <= x < k ->
  In x (find_found l k) <-> ~ In x (find_lost l k).
Proof.
  move => l k x Hxk. rewrite !find_lost_found_aux_in_spec /= !binop_lemmas2.False_or.
  have Hin: In x (Ziota 0 k) by rewrite Ziota_In; lia.
  have Hand: forall (P Q: Prop), P -> ((P /\ Q) <-> Q) by tauto. rewrite !Hand {Hand} //.
  symmetry. apply rwN. apply idP.
Qed.

Instance Inhabitant_option: forall {A: Type}, Inhabitant (option A).
intros A. apply None.
Defined.

(*Parities are represented as a list (option (list byte)), representing whether the parity packet is there
  or not. We will translate this into Vundef or Vptr as needed*)

Definition find_parity_aux (f: Z -> Z) (par: list (option (list byte))) (base : list Z) (l: list Z) :=
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

Lemma find_parity_aux_map: forall f par b1 b2 l,
  map f b1 = b2 ->
  map f (find_parity_aux id par b1 l) = find_parity_aux f par b2 l.
Proof.
  move => f par b1 b2 l. move: b1 b2. elim : l => [//= | h t /= IH b1 b2 Hb12].
  apply IH. case Hh : (Znth h par) => [o |].
  - by rewrite map_cat /= Hb12.
  - by [].
Qed.

Lemma find_parity_aux_map': forall f par l,
  map f (find_parity_aux id par nil l) = find_parity_aux f par nil l.
Proof.
  move => f par l. by apply find_parity_aux_map.
Qed.
  

Lemma find_parity_aux_bound: forall f pars base l b,
  (forall x, In x l -> 0 <= f x < b) ->
  (forall x, In x base -> 0 <= x < b) ->
  Forall (fun x : Z => 0 <= x < b) (find_parity_aux f pars base l).
Proof.
  move => f pars base l b Hf Hbase. rewrite /find_parity_aux Forall_forall. move : base Hbase Hf.
  elim : l => [ //= | h t /= IH base Hbase Hf x].
  case Hh: (Znth h pars) => [y /= | //=]; apply IH; rewrite //=.
  - move => z Hin. apply in_app_or in Hin. case : Hin => [Hin | Hzh].
    + by apply Hbase.
    + case : Hzh => [Hzh | Hfalse]; rewrite //. subst. apply Hf. by left.
  - move => z Hin. apply Hf. by right.
  - move => z Hin. apply Hf. by right.
Qed. 
(*maybe we don't need this*)
Lemma find_parity_aux_in: forall f par base l x,
  In x (find_parity_aux f par base l) ->
  In x base \/ exists y, f y = x /\ In y l.
Proof.
  move => f par base l x. move : base. elim : l => [//= base Hbase | h t /= IH base].
  by left. case Hh : (Znth h par) => [y /= | //=]. move => Hin. apply IH in Hin.
  case: Hin => [Hbaseh | Hxy].
  - apply in_app_or in Hbaseh. case : Hbaseh => [Hin | [Hxh | Hfalse]]; rewrite //.
    by left. right. exists h. split. by []. by left.
  - case Hxy => [y' [Hfxy' Hyt]]. right. exists y'. split. by []. by right.
  - move => Hin. apply IH in Hin. case : Hin => [Hin | [y [Hxy Hiny]]]. by left.
    right. exists y. split. by []. by right.
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
  In x (find_parity_aux id par base l) <-> In x base \/ (In x l /\ exists p, Znth x par = Some p).
Proof.
  move => par base l x. move: base. elim : l => [//= base | h t /= IH base].
  - by split => [ Hin //| [Hin // | [Hfalse Hex //]]]; left.
  - case Hnth : (Znth h par) => [c |]; rewrite IH /=.
    + rewrite in_app_iff /= or_assoc binop_lemmas2.or_False. apply or_iff_compat_l. split.
      * move => [Hxh | [Hint Hex]]. 
        -- subst. split. by left. by exists c.
        -- split. by right. by [].
      * move => [[Hxh | Hin] Hex].
        -- subst. by left.
        -- right. by split.
    + apply or_iff_compat_l. split.
      * move => [Hin Hex]. split. by right. by [].
      * move => [[Hhx | Hin] [p Hex]]. subst. by rewrite Hex in Hnth. split. by []. by exists p.
Qed. 

Definition find_parity_rows (par: list (option (list byte))) (c: Z) :=
  find_parity_aux id par nil (Ziota 0 c).

Lemma find_parity_rows_bound: forall par c,
  0 <= c ->
  Forall (fun x => 0 <= x < c) (find_parity_rows par c).
Proof.
  move => par c Hc.
  apply find_parity_aux_bound; rewrite //=.
  move => x. rewrite Ziota_In; lia.
Qed.

Lemma find_parity_rows_NoDup: forall par c,
  NoDup (find_parity_rows par c).
Proof.
  move => par c. apply find_parity_aux_NoDup'.
  apply Ziota_NoDup.
  by [].
Qed.

Definition find_parity_found (par: list (option (list byte))) (c: Z) (max_n : Z) :=
  find_parity_aux (fun x => max_n - 1 - x) par nil (Ziota 0 c).

Lemma find_parity_found_bound: forall par c max_n,
  0 <= c < max_n ->
  Forall (fun x => 0 <= x < max_n) (find_parity_found par c max_n).
Proof.
  move => par c max_n Hc. apply find_parity_aux_bound; try by [].
  move => x. rewrite Ziota_In; lia.
Qed.

Lemma find_parity_found_NoDup: forall par c max_n,
  0 <= c ->
  NoDup (find_parity_found par c max_n).
Proof.
  move => par c max_n Hc. apply find_parity_aux_NoDup'.
  apply Ziota_NoDup. move => x y. rewrite !Ziota_In; lia.
Qed.

(*The relationship between these two functions*)
Lemma find_parity_rows_found_Zlength: forall par c max_n,
  Zlength (find_parity_found par c max_n) = Zlength (find_parity_rows par c).
Proof.
  move => par c max_n.
  apply find_parity_aux_Zlength.
Qed.

Lemma find_parity_rows_found_map: forall par c max_n,
  map (fun x => max_n - 1 - x) (find_parity_rows par c) = find_parity_found par c max_n.
Proof.
  move => par c max_n. apply find_parity_aux_map'.
Qed.

Lemma find_parity_rows_found_Znth: forall par c max_n i,
  0 <= i < Zlength (find_parity_rows par c) ->
  Znth i (find_parity_found par c max_n) = max_n - 1 - Znth i (find_parity_rows par c).
Proof.
  move => par c max_n i Hi. by rewrite -find_parity_rows_found_map Znth_map.
Qed.

Lemma forall_lt_leq_trans: forall n m (l: list Z),
  n <= m ->
  Forall (fun x : Z => 0 <= x < n) l ->
  Forall (fun x : Z => 0 <= x < m) l.
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
Definition decode_list_mx (k c : Z) (packets: list (list B)) (parities: list (option (list byte))) 
  (stats: list Z) : lmatrix B :=
  (*populate all of the "arrays"*)
  let lost := find_lost stats k in
  let found1 := find_found stats k in 
  let row := find_parity_rows parities (Zlength parities) in
  let found2 := find_parity_found parities (Zlength parities) (fec_n - 1) in
  let found := found1 ++ found2 in
  let input := extend_mx k c packets in
  let parmx := fill_missing c parities in
  let xh := Zlength lost in
  (*step 1: find w' and v*)
  let w' := submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1) row lost in
  let v := find_invmx_list w' xh in
  (*step 2: find w'', d, and s*)
  let w'' := submx_rows_cols_rev_list weight_mx xh k (fec_n - 1) row found in
  let d' := col_mx_list (submx_rows_cols_list input (k - xh) c found1 (Ziota 0 c))
              (submx_rows_cols_list parmx xh c row (Ziota 0 c)) (k-xh) xh c in
  let s := list_lmatrix_multiply xh k c w'' d' in
  (*step 3: find missing packets and fill in*)
  let d := list_lmatrix_multiply xh xh c v s in
  fill_rows_list k c xh input d lost.


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

Lemma weight_mx_spec: lmatrix_to_mx fec_max_h (fec_n - 1) weight_mx =
   weights (Z.to_nat fec_max_h) (Z.to_nat (fec_n - 1)) weight_list.
Proof.
  rewrite /weight_mx /weight_list gauss_restrict_rows_equiv. rep_lia.
  move => Hhn. rewrite /weights gaussian_elim_equiv. f_equal. by rewrite weight_mx_list_spec; try rep_lia.
  apply /leP. rep_lia. move => Hh. rewrite weight_mx_list_spec; try rep_lia. apply vandermonde_strong_inv.
  apply /ltP. rep_lia.
  apply weight_matrix_wf; rep_lia.
Qed.

Lemma h_pos: 0 < fec_max_h.
Proof.
  rep_lia.
Qed.

Lemma n_pos: 0 < fec_n - 1.
Proof.
  rep_lia.
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
  strong_inv_list xh xh (submx_rows_cols_rev_list weight_mx xh xh (fec_n - 1) 
    (find_parity_rows parities h) (find_lost stats k)) 0%Z.
Proof.
  move => k xh h stats parities Hxh Hh Hhmax Hkn Hlens Hlenxh.
  rewrite /strong_inv_list. case : (range_le_lt_dec 0 0 xh); try lia.
  move => Hxh0. case : (Z_le_lt_dec xh xh); try lia. move => Hxhtriv.
  remember (find_parity_rows parities h) as row.
  have Hallrow: Forall (fun x => 0 <= x < h) row.
    rewrite Heqrow. by apply find_parity_rows_bound.
  have Hallrow': Forall (fun x => 0 <= x < fec_max_h) row.
    eapply Forall_impl. 2: apply Hallrow. rewrite /=. lia.
  have Halllost: Forall (fun x => 0 <= x < k) (find_lost stats k).
    apply find_lost_bound; lia.
  have Halllost': Forall (fun x => 0 <= x < fec_n - 1) (find_lost stats k).
    eapply Forall_impl. 2: apply Halllost. rewrite /=. lia.
  rewrite (@submx_rows_cols_rev_list_spec _ _ fec_max_h (fec_n - 1)) //=; try rep_lia.
  move => Hmaxh Hn. rewrite weight_mx_spec /weights /submx_rows_cols_rev. 
  have Hhnat: (0 < Z.to_nat fec_max_h)%N by (apply /ltP; rep_lia).
  have Hhn: (Z.to_nat fec_max_h <= Z.to_nat (fec_n - 1))%N by (apply /leP; rep_lia).
  (*Need to switch defaults for applying theorem*)
  rewrite (submx_rows_cols_default _ (ord_zero Hmaxh) (ord_zero Hn) (Ordinal Hhnat) ( widen_ord Hhn (Ordinal Hhnat))).
  + have->: (le_Z_N Hxhtriv) = (leqnn (Z.to_nat xh)) by apply ProofIrrelevance.proof_irrelevance.
    apply any_submx_strong_inv; rewrite //=.
    * by rewrite weight_list_uniq. 
    * apply weight_list_size.
    * apply Z_ord_list_uniq. eapply Forall_impl. 2: apply Hallrow. move => a; rewrite /=. lia.
      subst. apply find_parity_rows_NoDup.
    * rewrite map_inj_uniq. 2: { apply rev_ord_inj. }
      apply Z_ord_list_uniq. eapply Forall_impl. 2: apply find_lost_bound; lia. rewrite //=.
      lia. apply find_lost_NoDup.
    * by rewrite size_map !size_length -!ZtoNat_Zlength !Z_ord_list_Zlength // Hlens.
    * by rewrite size_length -ZtoNat_Zlength Z_ord_list_Zlength // Hlenxh.
    * move => x /mapP[y Hyin Hxy]. subst. rewrite /=. 
      apply Z_ord_list_In in Hyin. 2: eapply Forall_impl. 3: apply Halllost. 2: rewrite /=; lia.
      move: Halllost; rewrite Forall_forall => Hallost. apply Hallost in Hyin.
      rewrite leq_subRL. 2: apply /ltP; lia. rewrite addnC -leq_subRL. 2: apply /leP; lia. apply /ltP.
      have->:(Z.to_nat (fec_n - 1) - Z.to_nat fec_max_h)%N = (Z.to_nat (fec_n - 1) - Z.to_nat fec_max_h)%coq_nat by [].
      lia.
  + by rewrite size_length -ZtoNat_Zlength Z_ord_list_Zlength // Hlenxh.
  + by rewrite size_map size_length -ZtoNat_Zlength Z_ord_list_Zlength // -Hlens Hlenxh.
Qed.

(*Trivial case of xh = 0*)
Lemma decode_list_mx_zero: forall k c h packets parities stats,
  Zlength (find_lost stats k) = Zlength (find_parity_rows parities h) ->
  Zlength (find_lost stats k) = 0%Z ->
  lmatrix_to_mx k c (decode_list_mx k c packets parities stats) = 
  lmatrix_to_mx k c (extend_mx k c packets).
Proof.
  move => k c h packets parities stats Hlens Hlen0.
  rewrite /decode_list_mx /=. rewrite !Hlen0 /=.
  by rewrite /fill_rows_list /=.
Qed.

(*First, we prove that this is equivalent to the mathcomp decoder*)
(*LOTS of ordinals and dependent types in here, eventually we will be able to just have a few bounds hypotheses
  that can be solved with [lia]*)
Lemma decode_list_mx_equiv: forall k c h xh packets parities stats (Hk: 0 < k <= (fec_n - 1) - fec_max_h) (Hc: 0 < c)
  (Hh: 0 < h <= fec_max_h) (Hxh: xh <= k),
  let lost := find_lost stats k in
  let row := find_parity_rows parities h in
  Zlength lost = xh ->
  Zlength row = xh ->
  Zlength parities = h ->
  lmatrix_to_mx k c (decode_list_mx k c packets parities stats) = 
    decoder_mult max_h_n (k_bound_proof (proj2 Hk)) weight_list_size (ord_zero h_pos) (ord_zero n_pos)
      (ord_zero (proj1 Hk)) (ord_zero Hc) (lmatrix_to_mx k c (extend_mx k c packets))
      (lmatrix_to_mx h c (fill_missing c parities))
      (Z_ord_list lost k) (Z_ord_list row h)
      (le_Z_N (proj2 Hh)) (ord_zero (proj1 Hh)) (le_Z_N Hxh).
Proof.
  move => k c h xh packets parities stats Hk Hc Hh Hxh. rewrite /=.
  remember (find_parity_rows parities h) as row.
  remember (find_parity_found parities h (fec_n - 1)) as foundp.
  move => Hlenlost Hlenfound Hlenpar.
  have: xh = 0%Z \/ 0 < xh by list_solve. move => [Hxh0 | Hxh0].
  - subst. rewrite (@decode_list_mx_zero k c (Zlength parities)) //.
    rewrite decoder_mult_0 //. rewrite size_length -ZtoNat_Zlength.
    rewrite Z_ord_list_Zlength. all: try (rewrite Hxh0; lia).
    apply find_lost_bound; lia.
  - (*Things we will need to know about the lists*)
    have Hlostbound: Forall (fun x : Z => 0 <= x < k) (find_lost stats k) by (apply find_lost_bound; lia).
    have Hrowbound: Forall (fun x : Z => 0 <= x < h) row. {
      subst. apply find_parity_rows_bound. lia. }
    have Hfoundbound: Forall (fun x : Z => 0 <= x < k) (find_found stats k). apply find_found_bound; lia.
    have Hfoundpbound: Forall (fun x : Z => 0 <= x < fec_n - 1) foundp.
      subst. apply find_parity_found_bound. lia. 
    (*have Hxh0: 0 <= xh by list_solve.*)
    rewrite /decode_list_mx Hlenpar Hlenlost /decoder_mult fill_rows_list_spec //; try lia.
    move => Hk0. f_equal.
    rewrite list_lmatrix_multiply_correct. 2: { apply right_submx_wf; rep_lia. }
    2 : { apply list_lmatrix_multiply_wf; rep_lia. }
    2 : { by apply ord_inj. }
    rewrite find_invmx_list_spec. 2 : {
      apply strong_inv_list_partial; try lia. by subst. by subst. } 
    f_equal.
    + rewrite (@submx_rows_cols_rev_list_spec _ _ (fec_max_h) (fec_n - 1) xh xh) //; try lia.
      * move => Hh0 Hn0. f_equal. f_equal.
        -- apply weight_mx_spec.
        -- subst; by apply Z_ord_list_widen.
        -- by apply Z_ord_list_widen.
        -- by apply ord_inj.
        -- by apply ord_inj.
      * subst. by apply (forall_lt_leq_trans (proj2 Hh)).
      * have Hkn: k <= fec_n - 1 by lia. by apply (forall_lt_leq_trans Hkn). 
    + rewrite list_lmatrix_multiply_correct. 2: { apply submx_rows_cols_rev_list_wf; lia. }
      2 : { have Hkxh: k = (k - xh) + xh by lia. rewrite {5}Hkxh. apply col_mx_list_wf; lia. }
      rewrite (@submx_rows_cols_rev_list_spec _ _ fec_max_h) //; try lia.
      2 : {  subst; by apply (forall_lt_leq_trans (proj2 Hh)). }
      2 : { subst. rewrite Forall_app. split =>[|//]. have Hkn: (k <= fec_n - 1) by lia. by apply (forall_lt_leq_trans Hkn). }
      move => Hh0 Hn0. f_equal.
      * f_equal.
        -- apply weight_mx_spec.
        -- subst; by apply Z_ord_list_widen.
        -- rewrite Z_ord_list_app. f_equal.
          ++ rewrite (Z_ord_list_widen (k_leq_n (k_bound_proof (proj2 Hk)))) // find_lost_found_comp //. lia.
          ++ have Hinhab: Inhabitant 'I_(Z.to_nat (fec_n - 1)) by apply (ord_zero Hn0).
             have Hfoundpbound': Forall (fun x : Z => 0 <= x < fec_n - 1) (find_parity_found parities h (fec_n - 1)) by subst.
             apply Znth_eq_ext. 
             ** rewrite Zlength_map !Z_ord_list_Zlength //. subst. by rewrite find_parity_rows_found_Zlength.
             ** move => i. rewrite !Z_ord_list_Zlength //  => Hi.
                have Hinhabh: Inhabitant 'I_(Z.to_nat h). apply (ord_zero (proj1 Hh)).
                rewrite Znth_map //.
                { have Hilen: 0 <= i < Zlength row. subst. by rewrite find_parity_rows_found_Zlength in Hi.
                  rewrite !Z_ord_list_Znth' //; try lia. apply ord_inj. subst. rewrite /= find_parity_rows_found_Znth //=.
                  have->: (Z.to_nat (fec_n - 1) - 1 - Z.to_nat (Znth i (find_parity_rows parities (Zlength parities))))%N =
                        ((Z.to_nat (fec_n - 1) - 1)%coq_nat - Z.to_nat (Znth i (find_parity_rows parities (Zlength parities))))%coq_nat by [].
                  rewrite !Z2Nat.inj_sub; try lia. move: Hrowbound; rewrite Forall_Znth => /(_ i Hilen). lia.
                }
                { subst. rewrite Z_ord_list_Zlength //. by rewrite find_parity_rows_found_Zlength in Hi.
                }
        -- by apply ord_inj.
        -- by apply ord_inj.
      * rewrite (@lmatrix_to_mx_cast _ k ((k - xh) + xh) c c). lia. move => Hkxh.
        rewrite col_mx_list_spec; try lia. move => Hkxh0 Hxh0'. rewrite castmx_twice.
        rewrite (@submx_rows_cols_list_equiv _ _ k c (k-xh) c) //=; try lia.
        2: { rewrite Forall_forall => y. rewrite Ziota_In; lia. }
        rewrite -matrixP => x y.
        rewrite !castmxE /= !mxE /=.
        pose proof (splitP (cast_ord (esym (etrans (Logic.eq_sym (Z2Nat.inj_add (k - xh) xh Hkxh0 Hxh0')) (Z_to_nat_eq Hkxh))) x)).
        case : X => [j /= Hj | k' /= Hk'].
        { rewrite !mxE /=. pose proof (splitP (cast_ord (esym (subnK (le_Z_N Hxh))) x)).
          case : X => [j' /= Hj' | k'' /= Hk''].
          { rewrite !mxE /=. f_equal; f_equal. rewrite find_lost_found_comp //.
            rewrite -Hj Hj' /=. have->:(ord_zero Hk0 = (ord_zero (proj1 Hk))) by apply ord_inj. by []. lia.
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
          { rewrite !mxE /=. rewrite !mk_lmatrix_get; try lia. f_equal.
            have->:(nat_of_ord k'') = Z.to_nat (Z.of_nat k'') by rewrite Nat2Z.id.
            have->: k' = k''. move: Hk'' => /eqP Hx. move: Hx. rewrite Hk' Z2Nat.inj_sub; try lia.
            have->: (Z.to_nat k - Z.to_nat xh)%coq_nat = (Z.to_nat k - Z.to_nat xh)%N by [].
            rewrite eqn_add2l => /eqP Hx. by apply ord_inj.
            rewrite -Z_ord_list_Znth //. by subst. lia. rewrite nth_ord_enum Znth_Ziota //=. lia.
            apply Z_ord_bound; lia. apply Z_ord_bound; lia. apply Z_ord_bound; lia. }
        }
Qed.

(*Are the parity packets valid? To be valid, we require that all the "Some" entries are the actual rows produced
  by the encoder. It's a bit awkward to state this in Coq*)

Definition parities_valid k c parities data :=
  forall i j, 0 <= i < Zlength parities -> 0 <= j < c ->
    match (Znth i parities) with
      | Some par => Znth j par = Znth j (Znth i (encode_list_mx (Zlength parities) k c data))
      | _ => True
    end.

(*The correctness theorem for the decoder, at the matrix level. We will convert this back to list(list Z) and give
  more convenient preconditions for clients of the VST code*)
Lemma decoder_list_mx_correct:forall k c h xh data packets parities stats,
  0 < k <= fec_n - 1 - fec_max_h ->
  0 < c ->
  0 < h <= fec_max_h ->
  xh <= h ->
  xh <= k ->
  Zlength (find_lost stats k) = xh ->
  Zlength (find_parity_rows parities h) = xh ->
  Zlength parities = h ->
  Zlength stats = k ->
  Zlength packets = k ->
  Zlength data = k ->
  Forall (fun l => Zlength l <= c) data ->
  (forall l, In (Some l) parities -> Zlength l = c) ->
  (forall i, 0 <= i < k -> Znth i stats <> 1%Z -> Znth i packets = Znth i data) ->
  parities_valid k c parities data ->
  lmatrix_to_mx k c (decode_list_mx k c packets parities stats) = (lmatrix_to_mx k c (extend_mx k c data)).
Proof.
  move => k c h xh data packets parities stats Hkn Hc Hhh Hxhh Hxhk Hlostlen Hrowslen Hparlen Hstatslen Hpacklen 
    Hdatalen Hdatalens Hparlens Hfound Hpars.
  (*Things we need multiple times*)
  have Hstatsun: uniq (Z_ord_list (find_lost stats k) k). { apply Z_ord_list_uniq. eapply Forall_impl.
    2: { apply find_lost_bound; lia. } move => a. rewrite /=. lia. apply find_lost_NoDup. }
  have Hrowsun : uniq (Z_ord_list (find_parity_rows parities h) h). { apply Z_ord_list_uniq. eapply Forall_impl.
    2: { apply find_parity_rows_bound; lia. } move => a. rewrite /=; lia. apply find_parity_rows_NoDup. }
  have Hstatssz: size (Z_ord_list (find_lost stats k) k) = Z.to_nat xh. { rewrite size_length -ZtoNat_Zlength Z_ord_list_Zlength //=.
    by rewrite Hlostlen. apply find_lost_bound; lia. }
  have Hrowssz: size (Z_ord_list (find_parity_rows parities h) h) = Z.to_nat xh. { rewrite size_length -ZtoNat_Zlength
    Z_ord_list_Zlength. by rewrite Hrowslen. apply find_parity_rows_bound; lia. }
  rewrite (@decode_list_mx_equiv _ _ _ _ packets parities stats Hkn Hc Hhh Hxhk) // decoder_equivalent //=.
  - rewrite (decoder_correct (data:=(lmatrix_to_mx k c (extend_mx k c data))) max_h_n weight_list_uniq weight_list_size (ord_zero h_pos) (ord_zero n_pos) 
        (ord_zero (proj1 Hkn)) (ord_zero Hc) (le_Z_N Hxhh) ) //.
    + move => x y. rewrite !mxE !extend_mx_spec; try (apply Z_ord_bound; lia). 
      rewrite Z_ord_list_notin //=. 2: apply find_lost_bound; lia. rewrite -find_lost_found_in. 2: apply Z_ord_bound; lia.
      rewrite find_lost_found_aux_in_spec /= => [[Hfalse // | [Htriv Hstats]]].
      have Hstatsx: Znth (Z.of_nat x) stats <> 1%Z. by move : Hstats; case : (Z.eq_dec (Znth (Z.of_nat x) stats) 1%Z).
      apply Hfound in Hstatsx. 2: apply Z_ord_bound; lia. by rewrite Hstatsx.
    + move => x y. rewrite Z_ord_list_In. 2: apply find_parity_rows_bound; lia.
      rewrite find_parity_aux_in_iff /= => [[ Hfalse // | [Htriv [p Hnthx]]]].
      rewrite mxE. have Hx: (0 <= Z.of_nat x < h) by (apply Z_ord_bound; lia).
      have Hx': (0 <= Z.of_nat x < Zlength parities) by lia.
      have  Hy: (0 <= Z.of_nat y < c) by (apply Z_ord_bound; lia).
      move: Hpars; rewrite /parities_valid => /(_ (Z.of_nat x) (Z.of_nat y) Hx' Hy).
      rewrite Hnthx /= (fill_missing_mx_some Hnthx) //=.
      * move ->. have [Henc [ Hc0 Hinenc]]: wf_lmatrix (encode_list_mx (Zlength parities) k c data) (Zlength parities) c. {
          apply list_lmatrix_multiply_wf; lia. }
        rewrite -(@matrix_to_mx_get _ _ _ (encode_list_mx h k c data)) //=. by rewrite Hparlen. 
        rewrite -Henc in Hx'.
        have Hkn': k <= fec_n - 1  by lia. 
        have->: (k_leq_n (k_bound_proof (proj2 Hkn))) = le_Z_N Hkn' by  apply bool_irrelevance.
        rewrite -weight_mx_spec. by apply encoder_spec; try lia.
      * apply Hparlens; rewrite -Hnthx. apply Znth_In. lia.
  - apply weight_list_uniq.
Qed.


(*For the decoder preconditions, we don't want to explicitly mention [find_lost] and [find_parity_rows], especially
  since only the length is important. So we will use [filter] instead, which should be easier to reason about*)
Lemma find_lost_found_aux_Zlength: forall f g base pack l,
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
  rewrite sublist_last_1; try lia. rewrite find_lost_found_aux_app find_lost_found_aux_Zlength /= filter_cat /=.
  rewrite IH //. rewrite Zlength_app !Z.add_0_l //.
  case Hf: (f (Znth (Z.of_nat hi) pack)); list_solve.
  lia.
Qed.

(*Now we can state the precondition in terms of filter, so a client doesn't need to know anything about
  [find_lost]*)
Lemma find_lost_filter: forall stats k,
  k = Zlength stats ->
  Zlength (find_lost stats k) = Zlength (filter (fun x => Z.eq_dec x 1) stats).
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
Lemma find_parity_rows_filter: forall parities h,
  Zlength parities = h ->
  Zlength (find_parity_rows parities h) = Zlength (filter isSome parities).
Proof.
  move => pars h Hh. have Hh0: 0 <= h by list_solve.
  have ->: h = Z.of_nat (Z.to_nat h) by lia. rewrite find_parity_aux_filter_sublist; try lia.
  rewrite sublist_same //. lia.
Qed.

(** Final Definition of Decoder and Correctness*)

(*Our final decoder definition does everything in terms of lists and bytes, making it useful for VST*)
Definition decoder_list k c packets parities stats lens :=
  crop_mx (decode_list_mx k c packets parities stats) lens.

Theorem decoder_list_correct: forall k c h xh (data packets : list (list byte)) 
  (parities : list (option (list byte))) (stats lens : list Z),
  0 < k <= fec_n - 1 - fec_max_h ->
  0 < c ->
  0 < h <= fec_max_h ->
  xh <= h ->
  xh <= k ->
  Zlength (filter (fun x => Z.eq_dec x 1) stats) = xh ->
  Zlength (filter isSome parities) = xh ->
  Zlength parities = h ->
  Zlength stats = k ->
  Zlength packets = k ->
  Zlength data = k ->
  Zlength lens = k ->
  (forall i, 0 <= i < k -> Znth i lens = Zlength (Znth i data)) ->
  Forall (fun l => Zlength l <= c) data ->
  (forall i, 0 <= i < k -> Znth i stats <> 1%Z -> Znth i packets = Znth i data) ->
  (forall l, In (Some l) parities -> Zlength l = c) ->
  parities_valid k c parities data ->
  decoder_list k c packets parities stats lens = data.
Proof.
  move => k c h xh data packets parities stats lens Hknh Hc Hh Hxhh Hxhk Hstatsxh Hparsxh Hparlen
    Hstatlen Hpacklen Hdatalen Hlenslen Hlens Hdatac Hpackdata Hparlens Hparvalid.
  rewrite /decoder_list. 
  have Hmx: lmatrix_to_mx k c (decode_list_mx k c packets parities stats) = 
    (lmatrix_to_mx k c (extend_mx (F:=B) k c data)). { 
    apply (decoder_list_mx_correct Hknh Hc Hh Hxhh); try by [].
    - by rewrite find_lost_filter.
    - by rewrite find_parity_rows_filter. }
  apply lmatrix_to_mx_inj in Hmx. 
  - rewrite Hmx -Hdatalen crop_extend //; try lia; rewrite Hdatalen //; lia. 
  - apply fill_rows_list_aux_wf. apply extend_mx_wf; lia.
  - apply extend_mx_wf; lia.
Qed.

End Decoder.