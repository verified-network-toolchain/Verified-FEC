(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.poly.
Require Import LinIndep.
Require Import Gaussian.
Require Import GaussRestrict.
Require Import CommonSSR.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section RemNth.

(*Remove the (n+1)st position from a list*)
Definition rem_nth {A : eqType} (l : seq A) (n: nat) :=
  take n l ++ (drop (n.+1) l).

Lemma rem_nth_outside {A: eqType} (l: list A) n :
  size l <= n -> rem_nth l n = l.
Proof.
  move => Hsz. rewrite /rem_nth. rewrite take_oversize =>[//|//].
  rewrite drop_oversize. by rewrite cats0. by apply (leq_trans Hsz).
Qed.

Lemma rem_nth_size {A : eqType} (l : list A) n :
  n < size l -> size (rem_nth l n) = (size l).-1.
Proof.
  move => Hsz. rewrite /rem_nth size_cat size_take Hsz size_drop.
  have Halt: (n + (size l - n.+1).+1)%nat = size l. rewrite subnSK =>[|//].
  rewrite subnKC. by []. by rewrite ltnW. rewrite -{2}Halt.
  by rewrite -(addn1 (size l - n.+1)) addnA addn1 -pred_Sn.
Qed.

Lemma rem_nth_mem {A: eqType} (l: list A) n x :
  x \in (rem_nth l n) -> x \in l.
Proof.
  rewrite /rem_nth mem_cat => /orP[Hfst | Hsnd].
  - by apply mem_take in Hfst.
  - by apply mem_drop in Hsnd. 
Qed.

Lemma rem_nth_nth {A : eqType} (l : list A) n (y : A) (i : nat) :
  nth y (rem_nth l n) i = if i < n then nth y l i else nth y l (i.+1).
Proof.
  rewrite /rem_nth nth_cat. rewrite size_take.
  case Hnbounds: (n < size l).
  - case Hin: (i < n).
    + by rewrite nth_take.
    + rewrite nth_drop. rewrite -addn1 addnC addnA subnK. by rewrite addn1.
      by rewrite leqNgt Hin.
  - have {Hnbounds} Hnsz: size l <= n by rewrite leqNgt Hnbounds.
    case Hil: (i < size l).
    + have Hin: i < n by apply (ltn_leq_trans Hil Hnsz). rewrite Hin. 
      by rewrite nth_take.
    + have {Hil} Hisz: size l <= i by rewrite leqNgt Hil. rewrite nth_drop.
      rewrite nth_default.
      case Hin: (i < n). by rewrite nth_default. rewrite nth_default. by [].
      by apply (leq_trans Hisz).
      apply (leq_trans Hnsz). have Hge0: (0 <= i - size l)%nat. {
      rewrite leq_eqVlt in Hisz.
      rewrite leq_eqVlt. move : Hisz => /orP[Hisz | Hisz].
      * by rewrite eq_sym subn_eq0 leq_eqVlt eq_sym Hisz.
      * by rewrite subn_gt0 Hisz orbT. }
      rewrite -{1}(addn0 n). by apply leq_add.
Qed.

Lemma drop_split {A : eqType} (l : seq A) (n : nat) y :
  n < size l ->  drop n l = nth y l n :: drop (n.+1) l.
Proof.
  move => Hnsz. rewrite -addn1 addnC -drop_drop.
  remember (drop n l) as d. move : Heqd; case d.
  move => Hdrop.
  have: (size (drop n l) = (size l - n)%nat) by rewrite size_drop.
  rewrite -Hdrop /=.
  have Hszpos: (0 < size l - n) by rewrite subn_gt0 Hnsz. move => Hz.
  rewrite Hz in Hszpos.
  by rewrite ltnn in Hszpos.
  move => h t Hdrop. rewrite /=. rewrite drop0 Hdrop.
  have: nth y (drop n l) 0 = h by rewrite -Hdrop /=. rewrite nth_drop addn0.
  by move->.
Qed. 

Lemma rem_nth_subseq {A : eqType} (l : seq A) (n : nat) (y : A) :
  subseq (rem_nth l n) l.
Proof.
  have /orP[Hnin | Hnout] : (n < size l) || (size l <= n).
    by apply ltn_leq_total. 
  - rewrite /rem_nth. have: l = take n l ++ drop n l by rewrite cat_take_drop.
    rewrite (drop_split y Hnin). move => Hl. rewrite {3}Hl. 
    rewrite subseq_cat2l. apply subseq_cons.
  - rewrite rem_nth_outside. apply subseq_refl. by [].
Qed. 

Lemma rem_nth_uniq {A : eqType} (l : seq A) (n : nat) (y : A) :
  uniq l -> uniq (rem_nth l n).
Proof. move => Huniq. by apply (subseq_uniq (rem_nth_subseq l n y)). Qed.

Lemma subseq_rem' {A : eqType} (l1 l2 : seq A) (y : A) :
  subseq l1 l2 -> uniq l2 -> y \notin l1 -> y \in l2 -> subseq l1 (rem y l2).
Proof.
  move: l1. elim : l2 => [l1 Hsub Hun Hy Hyin //= | /= h t IH l1].
  case : l1 => [//= Ht Hun Ht' Hy /= | h1 t1 /=]. apply sub0seq. 
  case Hhh: (h1 == h).
  - eq_subst Hhh. move => Hsub /andP[Hnotin Hun] Hynot Hyin.
    case Hhy: (h == y). eq_subst Hhy. move: Hynot.
    by rewrite in_cons Bool.negb_orb eq_refl.
    rewrite /= eq_refl. apply IH. by []. by []. move: Hynot.
    by rewrite in_cons eq_sym Hhy.
    move: Hyin. by rewrite in_cons eq_sym Hhy.
  - move => Hsub /andP[Hnotin Hun] Hynot Hyin.  case Hhy: (h == y).
    eq_subst Hhy. by [].
    rewrite /= Hhh. apply IH. by []. by []. by []. move: Hyin.
    by rewrite in_cons eq_sym Hhy.
Qed. 

Lemma rem_nth_rem {A : eqType} (l : seq A) (n : nat) (y : A) (x : A) :
  uniq l -> n < size l -> nth x l n = y -> rem_nth l n = rem y l.
Proof.
  move => Hun Hsz Hnth.
  rewrite remE /rem_nth. subst. by rewrite !index_uniq.
Qed. 

(*Put these together*)
Lemma rem_nth_subseq'{A : eqType} (l1 l2 : seq A) (n : nat) (y : A) :
  subseq l1 l2 -> uniq l2 -> nth y l2 n \notin l1 -> subseq l1 (rem_nth l2 n).
Proof.
  move => Hsub Hun Hnotin.
  have /orP[Hnin | Hnout] : (n < size l2) || (size l2 <= n).
    by apply ltn_leq_total.
  - rewrite (@rem_nth_rem _ _ _ (nth y l2 n) y Hun Hnin).
    apply subseq_rem'; try by [].
    by apply mem_nth. by [].
  - by rewrite rem_nth_outside.
Qed.
    
End RemNth.


Section GenericVandermonde.

Variable F : fieldType.

Local Open Scope ring_scope.

(*Sometimes this is defined as the transpose of a vandermonde mx. In our case, 
  we want each column to contain the powers of a given element*)
Definition vandermonde (m n: nat) (l: list F) : 'M[F]_(m, n) :=
  \matrix_(i < m, j < n) (nth 0 l j) ^+ i.

(*Proof idea: suffices to show rows linearly independent. 
  If c1r1 + c2r2 +... + cnrn = 0,
  then poly c1 + c2x + ... + cnx^(n-1) has roots at each elt in column.
  Since there are n columns, poly has n roots => identically zero*)
Lemma vandermonde_unitmx n l :
  uniq l -> n = size l -> vandermonde n n l \in unitmx.
Proof.
  move => Huniq Hlen. rewrite unitmx_iff_lin_indep_rows.
  rewrite /rows_lin_indep /vandermonde. move => c Hzero.
  have: forall (j: 'I_n), \sum_(i < n) c i * (nth 0 l j) ^+ i = 0. {
  move => j. rewrite -{3}(Hzero j). apply eq_big =>[//|]. move => i H{H}. by
  rewrite mxE. }
  move => {}Hzero.
  (*Polys require functions from nat -> F, so we need the following*)
  remember (fun (n: nat) => 
              match (insub n) with |Some n' => c n' | None => 0 end) as c'. 
  remember (\poly_(i < n) c' i) as p. 
  have Hroots: forall (j: 'I_n), p.[l`_j] = 0. { move => j.
    have Hsz: size p <= n by rewrite Heqp; apply size_poly. 
    rewrite (horner_coef_wide _ Hsz) -{4}(Hzero j) 
            -(big_mkord (fun _ => true) (fun i => p`_i * l`_j ^+ i))
           (big_nth j) ordinal_enum_size big_nat_cond 
           (big_nat_cond _ _ 0 n (fun _ => true)).
    apply eq_big => [//| i /andP[/andP[H{H} Hin] H{H}]].
    have->: (nth j (index_enum (ordinal n)) i) = (nth j (index_enum (ordinal n)) (Ordinal Hin))
    by apply (elimT eqP). rewrite !ordinal_enum. rewrite Heqp coef_poly Hin /=. 
    by have->: c' i = c (Ordinal Hin) by rewrite Heqc' insubT /=. }
  have Hallroot: all (root p) l. { apply /allP => x Hxin. rewrite /root. apply /eqP.
    have <-: nth 0 l (index x l) = x by rewrite nth_index.
    have Hidx: (index x l) < n by rewrite Hlen index_mem.
    have ->: l`_(index x l) = l`_(Ordinal Hidx) by []. apply Hroots. }
  (*Therefore, p is the 0 polynomial*)
  have Hp: p = 0. apply (roots_geq_poly_eq0 Hallroot Huniq).
    by rewrite -Hlen Heqp size_poly.
  move => x. have: p`_x = 0 by rewrite Hp; apply coef0.
  rewrite Heqp coef_poly. have Hxn: x < n by []. rewrite Hxn Heqc' insubT /=.
  have->//:@Sub nat (fun x => x < n) _ x Hxn = x.
  apply /eqP. by have: x == x by rewrite eq_refl.
Qed.

(*Now we want to use submatrices defined by lists of rows and columns. So we need to convert
  a function to a list and vice versa*)

Definition fn_to_list {A} (n : nat) (f : 'I_n -> A) : list A :=
  map f (ord_enum n).

Lemma fn_to_list_nth {A} (n : nat) (f : 'I_n -> A) (i : 'I_n) (x : A) :
  nth x (fn_to_list f) i = f i.
Proof.
  rewrite /fn_to_list. rewrite (nth_map i). by rewrite nth_ord_enum.
  by rewrite size_ord_enum.
Qed.

Lemma fn_to_list_size {A} (n : nat) (f : 'I_n -> A) : size (fn_to_list f) = n.
Proof. by rewrite size_map size_ord_enum. Qed.

Lemma fn_to_list_uniq {A : eqType} (n : nat) (f : 'I_n -> A) :
  injective f -> uniq (fn_to_list f).
Proof.
  move => Hinj. rewrite map_inj_uniq //. apply ord_enum_uniq.
Qed.

(*If we select some of the columns (cols), this list is unique, and the 
  original list was unique, this is injective*)
Lemma sublist_cols_uniq m n (l : list F) (cols : list 'I_n) (y : 'I_n) :
  uniq l -> uniq cols -> size l = n -> size cols = m ->
  injective (fun (x: 'I_m) => nth 0 l (nth y cols x)).
Proof.
  move => Hunl Hunc Hsz Hm i j /eqP Heq. subst.
  rewrite nth_uniq in Heq; try by [].
  have {}Heq: nth y cols i == nth y cols j by []. (*get rid of nat_of_ord*)
  rewrite (@nth_uniq _ y cols i j) in Heq; try by []. by apply /eqP.
Qed.

(*A corollary: If we have a vandermonde matrix with m rows and n columns, 
  m <= n and unique elements, then if we take any m columns, that submatrix 
  is invertible*)
Lemma vandermonde_cols_unitmx  m n l (cols : list 'I_n) (y : 'I_n) :
  uniq l -> uniq cols -> n = size l -> m = size cols -> m <= n ->
  colsub (fun (x: 'I_m) => (nth y cols x))  (vandermonde m n l) \in unitmx.
Proof.
  move => Hunl Hunc Hszl Hszc Hmn.
  have->: colsub (fun x : 'I_m => nth y cols x) (vandermonde m n l) = 
    vandermonde m m (fn_to_list (fun (x : 'I_m) => nth 0 l (nth y cols x))). {
    rewrite -matrixP => i j /=. by rewrite !mxE /= fn_to_list_nth. }
  apply vandermonde_unitmx.
  - apply fn_to_list_uniq. by apply sublist_cols_uniq.
  - by rewrite fn_to_list_size.
Qed.

(*From the above, we can take any m columns after gaussian elimination and 
  the result is still invertible*)
Lemma vandermonde_gauss_cols_unitmx m n l (cols : list 'I_n) (y: 'I_n) :
  uniq l -> uniq cols -> n = size l -> m = size cols -> m <= n ->
  colsub (fun (x: 'I_m) => (nth y cols x)) (gaussian_elim (vandermonde m n l)) 
    \in unitmx.
Proof.
  move => Hunl Hunc Hszl Hszc Hmn.
  have Hre: row_equivalent (vandermonde m n l)
           (gaussian_elim (vandermonde m n l)) by apply gaussian_elim_row_equiv.
  rewrite (@row_equivalent_unitmx_iff _ _ _ (
    colsub (fun x : 'I_m => nth y cols x) (vandermonde m n l))).
  by apply vandermonde_cols_unitmx.
  apply colsub_row_equivalent. by apply row_equivalent_sym.
Qed.

(** Proving Strong Invertibility for the Weight Matrix (Row-reduced Vandermonde
   matrix)*)
(*The weight matrix is formed by row-reducing the [vandermonde_powers] matrix. 
  Then we take some (dynamically chosen) z columns and z rows to invert. 
  So we need to prove a much more general claim: for an m X n row-reduced 
  Vandermonde matrix with m <= n, if we take z rows and z columns (z <= m) 
  from among the last (n-m) columns, then the resulting submatrix is invertible. 
  We will do this in several pieces*)
Section RowRedVandermonde.

(*Allows us to specify a submatrix by a list of rows and columns (we will need 
  uniqueness and some additional length properties to use this*)
Definition submx_rows_cols {m n : nat} (m' n' : nat) (A : 'M[F]_(m, n)) 
                           (rows : seq 'I_m) (cols : seq 'I_n)  (xm: 'I_m) 
                           (xn : 'I_n) := 
  mxsub (fun (x : 'I_m') => nth xm rows x) (fun x : 'I_n' => nth xn cols x) A.

(*Take columns from the end instead of beginning (because the weight matrix is 
  backwards)*)
Definition submx_rows_cols_rev {m n : nat} (m' n' : nat) (A : 'M[F]_(m, n)) 
                               (rows : seq 'I_m) (cols : seq 'I_n)
                               (xm: 'I_m) (xn : 'I_n) := 
  submx_rows_cols m' n' A rows (map (fun x => rev_ord x) cols) xm xn.

(*The default doesn't matter as long as our lists are long enough*)
Lemma submx_rows_cols_default m n m' n' (A: 'M[F]_(m, n)) rows cols 
                             xm xn xm' xn' :
  m' <= size rows -> n' <= size cols ->
  submx_rows_cols m' n' A rows cols xm xn = 
  submx_rows_cols m' n' A rows cols xm' xn'.
Proof.
  move => Hm' Hn'. rewrite -matrixP => x y. rewrite !mxE.
  f_equal; apply set_nth_default. 
  have Hx: x < m' by []. by apply (ltn_leq_trans Hx).
  have Hy: y < n' by []. by apply (ltn_leq_trans Hy).
Qed.

(*First, we give an alternate definition for [strong_inv] based on this*)

(*The general case is not as useful, we show the result only when the 
  underlying matrix is [submx_rows_cols]*)
Lemma submx_remove_col_list {m n} m' n' (Hmn' : m' <= n') (A : 'M[F]_(m, n)) 
                            (rows : seq 'I_m) (cols : seq 'I_n) (xm : 'I_m)
                            (xn : 'I_n)  r j :
  submx_remove_col (submx_rows_cols m' n' A rows cols xm xn) Hmn' r j =
  submx_rows_cols r r A (take r rows) (rem_nth (take r.+1 cols) j) xm xn.
Proof.
  rewrite -matrixP => x y. rewrite !mxE.
  rewrite nth_take // rem_nth_nth !nth_take //=. f_equal.
  case Hyj: (y < j) => //.
  - by rewrite -(addn1 y) -(addn1 r) ltn_add2r.
  - by rewrite (ltn_trans (ltn_ord y)).
Qed.

Lemma submx_add_row_list {m n} m' n' (Hmn' : m' <= n') (A : 'M[F]_(m, n))  
  (rows : seq 'I_m) (cols : seq 'I_n) (xm : 'I_m) (xn : 'I_n)  r j :
  nat_of_ord r <= size rows ->
  submx_add_row (submx_rows_cols m' n' A rows cols xm xn) Hmn' r j =
  submx_rows_cols r.+1 r.+1 A ((take r rows) ++ 
    [:: nth xm rows j]) (take r.+1 cols) xm xn.
Proof.
  move => Hr.
  rewrite -matrixP => x y. rewrite !mxE /= !nth_take //= nth_cat.
  have->: size (take r rows) = r. rewrite size_take.
  move : Hr; rewrite leq_eqVlt => /orP[/eqP Hr | Hr].
  by rewrite Hr ltnn. by rewrite Hr. 
  f_equal. have: x <= r by rewrite -ltnS.
  rewrite leq_eqVlt => /orP[/eqP Hxr | Hxr]. 
  - by rewrite Hxr ltnn subnn /=.
  - by rewrite Hxr nth_take /=.
Qed.

(*To prove the invertibility of this submatrix, we will need to expand this to 
  cover more columns. First we need to get a list of the rows that are not 
  included in [rows].*)

(*The complement of a nat list, up to bound n*)
Definition nat_comp (n : nat) (l : seq nat) : seq nat :=
  foldl (fun acc x => if x \in l then acc else acc ++ [:: x]) nil (iota 0 n).

Lemma nat_comp_plus_one n l :
  nat_comp n.+1 l =
  if n \in l then nat_comp n l else (nat_comp n l ++ [:: n]).
Proof. by rewrite /nat_comp iota_plus_1 foldl_cat /= !add0n. Qed.

Lemma nat_comp_bound n l i : i \in (nat_comp n l) -> i < n.
Proof.
  elim : n l i => [l i Hin /= | /= n IH l i].
  - by rewrite ltn0.
  - rewrite nat_comp_plus_one. case Hnin : (n \in l).
    + move => Hin. apply IH in Hin. by apply (ltn_trans Hin).
    + rewrite mem_cat in_cons => /orP[Hincomp | /orP[/eqP Hin | Hf]].
      * apply IH in Hincomp. by apply (ltn_trans Hincomp).
      * by subst.
      * by [].
Qed.

Lemma in_nat_comp n l i : i < n -> i \in (nat_comp n l) = (i \notin l).
Proof.
  elim : n l i => [l i Hi /= | n IH l i Hi].
  - by rewrite ltn0 in Hi.
  - rewrite nat_comp_plus_one.
    have /orP Hlt: (i == n) || (i < n). rewrite ltnS in Hi.
    by rewrite -leq_eqVlt.
    case : Hlt => [/eqP Heq | Hlt].
    + subst. case Hin: (n \in l).
      * case Hincomp: (n \in nat_comp n l).
        -- apply nat_comp_bound in Hincomp. by rewrite ltnn in Hincomp.
        -- by [].
      * by rewrite mem_cat in_cons eq_refl /= orbT.
    + case Hnin: (n \in l).
      * by apply IH.
      * rewrite mem_cat in_cons. have->: (i == n = false) by apply ltn_eqF.
        rewrite /= in_nil orbF.
        by apply IH.
Qed.

Lemma in_nat_comp' n l i : i \in (nat_comp n l) = (i < n) && (i \notin l).
Proof.
  case Hincom: (i \in nat_comp n l).
  - have Hin : i < n by apply (nat_comp_bound Hincom).
    by rewrite Hin andTb -(in_nat_comp l Hin).
  - case Hin : (i < n).
    + rewrite in_nat_comp in Hincom =>[|//]. by rewrite Hincom.
    + by [].
Qed.

Lemma nat_comp_eq_mem n (l1 l2 : seq nat) :
  (l1 =i l2) -> nat_comp n l1 = nat_comp n l2.
Proof.
  move => Hl12. elim : n => [//= | n IH /=].
  rewrite !nat_comp_plus_one !IH. by move: Hl12 => /(_ n) ->.
Qed. 

Lemma nat_comp_undup n (l : seq nat) : nat_comp n l = nat_comp n (undup l).
Proof. symmetry. apply nat_comp_eq_mem. apply mem_undup. Qed.

Lemma nat_comp_uniq n l : uniq (nat_comp n l).
Proof.
  elim : n l => [l //= | n IH l /=].
  rewrite nat_comp_plus_one.
  case Hn : (n \in l).
  - apply IH.
  - rewrite cat_uniq /= orbF andbT IH /=.  case Hcon: (n\in nat_comp n l).
    + apply nat_comp_bound in Hcon. by rewrite ltnn in Hcon.
    + by [].
Qed. 

Lemma nat_comp_app_notin n l1 l2 :
  (forall x, x \in l2 -> (n <= x)%N) -> nat_comp n l1 = nat_comp n (l1 ++ l2).
Proof.
  elim : n => [//= | n /= IH Hin].
  rewrite !nat_comp_plus_one mem_cat.
  have->:n \in l2 = false. 
  case Hn: (n \in l2) =>[//|//]. apply Hin in Hn.
  by rewrite ltnn in Hn. rewrite orbF !IH //. move => x Hin'.
  apply ltnW. by apply Hin.
Qed.

Lemma nat_comp_app n l1 : nat_comp n (l1 ++ [:: n]) = nat_comp n l1.
Proof.
  rewrite -nat_comp_app_notin //.
  move => x. rewrite in_cons => /orP[/eqP Hxn | Hinf].
  subst. by rewrite leqnn. by [].
Qed.

(*Now, we need to wrap this in Ordinals*)
Definition ord_comp {n : nat} (l : list 'I_n) : list 'I_n :=
  pmap insub (nat_comp n (map (@nat_of_ord n) l)).

Lemma in_ord_comp n (l : list 'I_n) (i : 'I_n) :
  (i \in (ord_comp l)) = (i \notin l).
Proof.
  rewrite /ord_comp mem_pmap_sub /= in_nat_comp'.
  have Hin: i < n by []. rewrite Hin andTb. rewrite mem_map //. apply ord_inj.
Qed.

Lemma uniq_ord_comp n (l : seq 'I_n) : uniq (ord_comp l).
Proof. rewrite /ord_comp. apply pmap_sub_uniq. apply nat_comp_uniq. Qed.

Lemma uniq_ord_comp_cat n (l : seq 'I_n) : uniq l -> uniq (l ++ ord_comp l).
Proof.
  rewrite cat_uniq /=. move ->. rewrite uniq_ord_comp andbT /=. 
  apply /hasP. move => [x Hxin Hmem].
  have Hxin': x \in l by [].
  rewrite in_ord_comp in Hxin. by rewrite Hxin' in Hxin.
Qed.

(*Now, we need to know that if we take a list l of 'I_n's and take
  l ++ (ord_comp rows), this is a permutation of ord_enum m*)
Lemma ord_comp_app_perm {n : nat} (l : seq 'I_n) :
  uniq l -> perm_eq (l ++ (ord_comp l)) (ord_enum n).
Proof.
  move => Hun. apply uniq_perm.
  - by apply uniq_ord_comp_cat.
  - apply ord_enum_uniq.
  - move => x. rewrite mem_cat. rewrite mem_ord_enum.
    case Hx: (x \in ord_comp l). by rewrite orbT. rewrite orbF.
    rewrite in_ord_comp in Hx. move : Hx. by case : (x \in l).
Qed.

Lemma ord_comp_cat_size n (l : seq 'I_n) :
  uniq l -> size (l ++ ord_comp l) = n.
Proof.
  move => Hun. by rewrite (perm_size (ord_comp_app_perm Hun)) size_ord_enum.
Qed.

Lemma ord_comp_size_uniq n (l : seq 'I_n) :
  uniq l -> size (ord_comp l) = (n - size l)%N.
Proof.
  move => Hun.
  have Hsz: (size (ord_comp l) + size l)%N = n.
    by rewrite addnC -size_cat ord_comp_cat_size.
  have<-: ((size (ord_comp l) + size l) - size l)%N = (n - size l)%N.
    by rewrite Hsz.
  rewrite -subnBA. by rewrite subnn subn0. by rewrite leqnn.
Qed.

(*The first main piece:
  Proof idea: we will show that the [submx_rows_cols] we care about is 
  invertible iff an expanded submatrix which includes additional rows and 
  columns is invertible. This expanded submatrix adds (some of) the missing rows
  and the corresponding column. Because the underlying mx is row-reduced, for 
  each column i that we add, there is a 1 at position i and 0 at all other 
  places. Thus, we can "peel off" these lists by using the cofactor expansion 
  for determinants, and our original submatrix is still included. We prove this 
  general claim by induction on the list of additional columns. (the base case 
  is essentially trivial)
  We need a lot of preconditions to make sure all of the pieces relate to each
  other.*)
Lemma added_rows_unitmx_iff {m n} (Hmn : m <= n) (xm : 'I_m) (xn : 'I_n) 
                            (l : seq F) (rows : seq 'I_m) (cols : seq 'I_n)
                            (added_cols : seq 'I_n) (all_rows : seq 'I_m) z k :
  uniq l ->  n = size l ->
  (forall x, x \in cols -> m <= x) -> 
  (*only consider submatrices in last n - m columns, clearly not true otherwise*)
  uniq rows ->
  size cols = size rows ->
  size cols = z ->
  (forall x, x \in added_cols -> x < m) ->
  uniq (added_cols ++ cols) ->
  size (added_cols ++ cols) = k ->
  uniq (all_rows) ->
  subseq rows all_rows ->
  size (added_cols ++ cols) = size all_rows ->
  (forall x, (widen_ord Hmn x) \in added_cols = 
    (x \in all_rows) && (x \notin rows)) -> (*we add the same rows and columns*) 
  (submx_rows_cols z z (gaussian_elim (vandermonde m n l)) rows cols xm xn 
    \in unitmx) = 
  (submx_rows_cols k k (gaussian_elim (vandermonde m n l)) all_rows 
    (added_cols ++ cols) xm xn \in unitmx).
Proof.
  move => Hunl Hszl Hinc Hunr Hszcr Hszc. 
  rewrite !unitmxE !GRing.unitfE. (*work with determinants for cofactors*)
  move : k all_rows.  (*need these to be generalized for induction*) 
  elim : added_cols => 
    [/= k all_rows Hinadd Hunc Hszadd Hunall Hsubs Hszall Hrowcol /= | 
    /= h t IH k all_rows Hinadd Hunadd Hszadd Hunall Hsubs Hszaddall Hrowcol].
  - have->: rows = all_rows. apply size_subseq_leqif in Hsubs; move: Hsubs.
    rewrite /leqif -Hszcr Hszall eq_refl; 
    move  => [Htriv Hrows]. apply /eqP. by rewrite -Hrows. by subst.
  - (*expand determinant along cofactor*)
    have Hk: 0 < k. move: Hszadd <-. apply ltn0Sn.
    rewrite (expand_det_col (submx_rows_cols k k 
       (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn)
      (Ordinal Hk)). 
    (*now, need to show that all but 1 entry in the sum is 0*)
    have Hhm: h < m. apply Hinadd. by rewrite in_cons eq_refl.
     have Hvan: (colsub (widen_ord Hmn) (vandermonde m n l) \in unitmx). {
        have->: colsub (widen_ord Hmn) (vandermonde m n l) = 
                vandermonde m m (take m l). {
          rewrite -matrixP => x y. rewrite !mxE. by rewrite nth_take. }
        apply vandermonde_unitmx. by apply take_uniq. rewrite size_takel //.
        by subst. }
    have Hinner i :
       submx_rows_cols k k (gaussian_elim (vandermonde m n l)) 
         all_rows (h :: t ++ cols) xm xn i (Ordinal Hk) = 
       if (nat_of_ord (nth xm all_rows i) == nat_of_ord h) then 1 else 0. {
      rewrite mxE /=. 
      by apply (gaussian_elim_identity_val Hvan). }
    (*work with the summation - can we do this nicely at all?*)
    have->: (\sum_i
      submx_rows_cols k k (gaussian_elim (vandermonde m n l)) all_rows 
        (h :: t ++ cols) xm xn i (Ordinal Hk) *
      cofactor (submx_rows_cols k k (gaussian_elim (vandermonde m n l)) 
        all_rows (h :: t ++ cols) xm xn) i
        (Ordinal Hk)) =
    (\sum_i
      if nat_of_ord (nth xm all_rows (nat_of_ord i)) == (nat_of_ord h) then 
      submx_rows_cols k k (gaussian_elim (vandermonde m n l)) all_rows
         (h :: t ++ cols) xm xn i (Ordinal Hk) *
      cofactor (submx_rows_cols k k (gaussian_elim (vandermonde m n l))
         all_rows (h :: t ++ cols) xm xn) i
      (Ordinal Hk) else 0). {
      apply eq_big. by []. move => i H{H}. rewrite Hinner. 
        case Hih : (nat_of_ord (nth xm all_rows (nat_of_ord i)) == 
          (nat_of_ord h)). by [].
        by rewrite GRing.mul0r. }
    rewrite {Hinner}.
    have Hallsz: size all_rows = k by subst.
    have Hhin: (Ordinal Hhm \in all_rows) && (Ordinal Hhm \notin rows).
      move : Hrowcol => /(_ (Ordinal Hhm)) /=.
      have->: widen_ord Hmn (Ordinal Hhm) = h by apply ord_inj.
      rewrite in_cons eq_refl orTb.
      move => Hhinfo. by symmetry in Hhinfo. apply (elimT andP) in Hhin.
      case : Hhin => [Hhall Hhrow].
    have [j Hj]: (exists (j: 'I_k), nat_of_ord (nth xm all_rows j) == 
                   nat_of_ord h).  {
      have Hj: (index (Ordinal Hhm) all_rows) < k. by rewrite -Hallsz index_mem.
      exists (Ordinal Hj). by rewrite nth_index. }
    (*Now we separate j from the rest of the sum, which is 0*)
    rewrite (@sum_remove_one _ _  _ _ j) // Hj. rewrite big1.
    2 : { move => i /andP[Htriv Hij]. 
          case Hih: (nat_of_ord (nth xm all_rows i) == (nat_of_ord h)).
      - have Hijeq: i == j. apply /eqP. apply ord_inj. apply /eqP. 
        rewrite -(@nth_uniq _ xm all_rows) //.
        apply /eqP. apply ord_inj. eq_subst Hj. rewrite Hj.
          by apply /eqP. by rewrite Hallsz.
        by rewrite Hallsz.
        by rewrite Hijeq in Hij.
      - by []. }
    rewrite GRing.add0r mxE /= (gaussian_elim_identity_val Hvan) // Hj 
            GRing.mul1r {Hvan} /cofactor.
    (*So now, we just need to prove that the determinant is zero when the 
      determinant of the new submatrix is.This is the matrix that we will
      use in the IH, but there's a decent amount to do to prove the 
      preconditions*)
    rewrite GRing.Theory.mulf_eq0 negb_or GRing.signr_eq0 /=.
    (*Have to prove this new matrix equivalent to the one we need for the IH*)
    have ->:(row' j
         (col' (Ordinal Hk)
            (submx_rows_cols k k (gaussian_elim (vandermonde m n l)) 
            all_rows (h :: t ++ cols) xm xn))) =
      (submx_rows_cols k.-1 k.-1 (gaussian_elim (vandermonde m n l)) 
        (rem_nth all_rows j) (t ++ cols) xm xn). {
      rewrite -matrixP => x y. rewrite !mxE /=. f_equal.
      rewrite rem_nth_nth /bump.
      case Hxj : (x < j). rewrite ltnNge in Hxj. case Hjx: (j <= x); try by [].
      by rewrite Hjx in Hxj.
      rewrite ltnNge in Hxj. apply negbFE in Hxj. by rewrite Hxj. }
    (*Now, we will apply the IH and deal with the many goals we have*)
    apply IH.
    + move => x Hinx. apply Hinadd. by rewrite in_cons Hinx orbT.
    + apply (elimT andP) in Hunadd. apply Hunadd.
    + apply /eqP. rewrite -eqSS Hszadd. apply /eqP. by rewrite prednK.
    + by apply rem_nth_uniq.
    + apply rem_nth_subseq' with (y:=xm); try by [].
      have->: nth xm all_rows j = Ordinal Hhm.  apply ord_inj. by eq_subst Hj.
      by [].
    + rewrite rem_nth_size. subst. by rewrite Hallsz -pred_Sn.
      by rewrite Hallsz.
    + move => x. rewrite (@rem_nth_rem _ _ j (Ordinal Hhm) xm) //=.
      2: by rewrite Hallsz.
      2: by ( apply ord_inj; apply (elimT eqP) in Hj; rewrite Hj). 
      case Hxh: (x == Ordinal Hhm).
      * eq_subst Hxh. rewrite Hhrow andbT. 
        have->: (widen_ord Hmn (Ordinal Hhm) \in t)  = false.
        apply (elimT andP) in Hunadd.
        case : Hunadd => [Hnotin Hunt]. move: Hnotin.
        rewrite mem_cat negb_or => /andP [Hnotht Hnotcol].
        have->: (widen_ord Hmn (Ordinal Hhm) = h) by apply ord_inj.
        move: Hnotht; by  case : (h \in t).
        by rewrite mem_rem_uniqF.
      * move : Hrowcol => /(_ x). rewrite in_cons.
        have->: (widen_ord Hmn x == h) = false.
        case Hxh': (widen_ord Hmn x == h). eq_subst Hxh'.
        have Hxm: (x == Ordinal Hhm). apply /eqP. by apply ord_inj.
        by rewrite Hxm in Hxh. by []. rewrite /=. move ->.
        rewrite rem_in_neq //. move : Hxh; by case : (x == Ordinal Hhm).
Qed.

(*The only remaining piece is that we required that the [rows] list is a subseq 
  of the [all_rows] (we needed this for the base case). We will want our 
  [all_rows] to be [ord_enum m], so this is only true if [rows] was sorted.
  So we need to prove that the invertibility of a submatrix defined by a list of
  rows is preserved if we permute the row list. This follows from row 
  equivalence, but requires a good amount of work to show*)

Lemma perm_eq_in {A : eqType} (l1 l2 : seq A) x :
  perm_eq (x :: l1) l2 ->
  exists s1 s2, l2 = s1 ++ x :: s2 /\ perm_eq l1 (s1 ++ s2) .
Proof.
  rewrite perm_sym => /perm_consP [i [u [Hhu Hperm]]].
  rewrite /rot in Hhu. 
  have /orP[Hnin | Hnout] :
     (i < size l2) || (size l2 <= i) by apply ltn_leq_total.
  - move: Hhu. rewrite (drop_nth x) //=; move => [Hhd Htl].
    exists (take i l2). exists (drop (i.+1) l2). split.
    by rewrite -Hhd -(drop_nth) // cat_take_drop. subst. eapply perm_trans.
    rewrite perm_sym. apply Hperm. by rewrite perm_catC perm_refl.
  - move: Hhu. rewrite drop_oversize //= take_oversize //=.
    move->. exists nil. exists u. rewrite /=. split. by []. by rewrite perm_sym.
Qed. 

(*This is a stronger claim than we originally needed - for the IH, we need to 
  add the extra [p] list. This lemma is quite annoying to prove because of all
  the appends and casework*)
Lemma permute_rows_row_equiv {m n} (A : 'M[F]_(m, n)) m' n' 
    (r1 r2 p: list 'I_m) (cols: list 'I_n) (xm: 'I_m) (xn: 'I_n) :
  perm_eq r1 r2 ->
  m' = size (p ++ r1) ->
  m' = size(p ++ r2) ->
  row_equivalent (submx_rows_cols m' n' A (p ++ r1) cols xm xn) 
    (submx_rows_cols m' n' A (p ++ r2) cols xm xn).
Proof.
  move: r2 p. elim: r1 => [r2 p /= | /= h t IH r2 p Hperm Hsz1 Hsz2].
  - rewrite perm_sym. move => /perm_nilP Hperm. subst. constructor.
  - apply perm_eq_in in Hperm. move: Hperm => [s1 [s2 [Hr2 Hperm]]].
    have->:p ++ h :: t = (p ++ h :: nil) ++ t by rewrite -catA.
    (*now, depends on if s1 = nil (in which case this is easy, or not, 
     in which case we need to swap h and h1)*)
    move: Hr2 Hperm; case : s1 =>[//= Hr1 Hperm | //= h1 t1 Hr1 Hperm].
    + subst. have->:p ++ h :: s2 = (p ++ h :: nil) ++ s2 by rewrite -catA.
      apply (IH  s2 (p ++ h :: nil)). by []. all: by rewrite -catA /=.
    + rewrite Hr1.
      apply (@row_equivalent_trans _ _ _ _ 
         (submx_rows_cols m' n' A (p ++ h :: t1 ++ h1 :: s2) cols xm xn)).
      * have->: (p ++ h :: t1 ++ h1 :: s2) = 
                (p ++ h :: nil) ++ (t1 ++ h1 :: s2) by rewrite -catA.
        apply IH. rewrite (perm_trans Hperm) //.
          by rewrite perm_sym perm_catC /= perm_cons perm_catC perm_refl.
        all:  rewrite -catA //=. subst. rewrite Hsz2 !size_cat /=.
        apply /eqP. by rewrite eqn_add2l !size_cat /=.
      * (*this is RE because this swap is actually a row swap*)
        have Hih1: (size p) < m'. subst. rewrite size_cat /= -ltn_subLR.
        by rewrite subnn ltn0Sn.
        by rewrite leqnn.
        have Hih: (size (p ++ h1 :: t1)) < m'. subst. rewrite Hsz2.
        rewrite !size_cat /= ltn_add2l
          -add1n -(add1n (size (t1 ++ h :: s2))) !leq_add2l size_cat -ltn_subLR.
          by rewrite subnn /= ltn0Sn. by rewrite leqnn.
        (*need these two so we can create Ordinals of type 'I_z*)
        have->: (submx_rows_cols m' n' A (p ++ h1 :: t1 ++ h :: s2) cols xm xn) = 
          xrow (Ordinal Hih) (Ordinal Hih1)
            (submx_rows_cols m' n' A (p ++ h :: t1 ++ h1 :: s2) cols xm xn). {
          rewrite -matrixP => x y. rewrite xrow_val !mxE.
          have Hih': nat_of_ord (Ordinal Hih) = size (p ++ h1 :: t1) by [].
          have Hih1': nat_of_ord (Ordinal Hih1) = size p by [].
          (*To reduce duplication*)
         have Hnth: forall v v' v'', 
            (nth xm (p ++ v :: t1 ++ v' :: s2) (size (p ++ v'' :: t1))) = v'. { 
           move => v' v'' v'''. rewrite nth_cat.
          have->:size (p ++ v''' :: t1) < size p = false.
           apply leq_gtF. rewrite size_cat /= -leq_subLR subnn leqW //.
           rewrite size_cat -addnBAC. 2: by rewrite leqnn.
           by rewrite subnn add0n /= nth_cat ltnn subnn /=. }
           case Hxh : (x == Ordinal Hih).
         - eq_subst Hxh. by rewrite Hih' Hih1' Hnth !nth_cat ltnn subnn.
         - case Hxh1: (x == Ordinal Hih1).
           + eq_subst Hxh1. by rewrite Hih1' Hih' Hnth !nth_cat ltnn subnn.
           + (*Now need to show these are equivalent at all other locations - 
               this is annoying*)
             rewrite !nth_cat. case Hxp: (x < size p) =>[//|/=]. 
             have->: (h1 :: t1 ++ h :: s2) = (h1:: t1) ++ (h :: s2) by [].
             have->: (h :: t1 ++ h1 :: s2) = (h :: t1) ++ (h1 :: s2) by [].
             rewrite !nth_cat /=.
             have Hpos: 0 < x - size p. rewrite subn_gt0. move: Hxp. 
               rewrite ltnNge Bool.negb_false_iff leq_eqVlt => 
                   /orP[Hpxeq | Hpxlt].
               (*contradiction, x = Ordinal Hih*)
               have Hxord: x == Ordinal Hih1. eq_subst Hpxeq. apply /eqP.
               by apply ord_inj.
               by rewrite Hxord in Hxh1. by [].
            case Hxt1: (x - size p < (size t1).+1).
             * by rewrite -(prednK Hpos) /=.
             * have Hpos': 0 < (x - size p - (size t1).+1).  move: Hxt1.
               rewrite ltnNge Bool.negb_false_iff leq_eqVlt => 
                   /orP[Hpxeq | Hpxlt].
               have Hord: nat_of_ord x == (size p + (size t1).+1)%N.
               rewrite -(@subnK (size p) x). 2: apply ltnW;
                 by rewrite -subn_gt0.
               apply (elimT eqP) in Hpxeq. rewrite Hpxeq addnABC.
               rewrite (addnC (size p - size p)%N).
               rewrite subnn addn0 subnK //. by rewrite leqNgt Hxp.
               by rewrite leqnn. by rewrite leqNgt Hxp.
               have Hxord: x == Ordinal Hih. apply /eqP. apply ord_inj.
              eq_subst Hord. rewrite Hord.
               rewrite Hih'. by rewrite size_cat /=.
               by rewrite Hxord in Hxh. 
               by rewrite subn_gt0. 
               by rewrite -(prednK Hpos') /=. }
        apply ero_row_equiv. constructor.
Qed.

(*The easy corollary of above. This is what we wanted*)
Lemma perm_eq_row_equiv {m n} (A : 'M[F]_(m, n)) m' n' (r1 r2 : list 'I_m) 
                                   (cols: list 'I_n) (xm: 'I_m) (xn: 'I_n) :
  perm_eq r1 r2 -> m' = size r1 ->  m' = size r2 ->
  row_equivalent (submx_rows_cols m' n' A r1 cols xm xn) 
                 (submx_rows_cols m' n' A r2 cols xm xn).
Proof.
  move => Hperm Hsz1 Hsz2.
  rewrite -(cat0s r1) -(cat0s r2). by apply permute_rows_row_equiv.
Qed.

(*As a corollary (that we will need later), we show that if we flip the rows 
  of an n x n matrix, this does not change invertibility*)
Definition flip_rows {m n} (A : 'M[F]_(m, n)) : 'M[F]_(m, n) :=
  \matrix_(i < m, j < n) A (rev_ord i) j.

Lemma submx_rows_cols_whole m n (A : 'M[F]_(m, n)) (xm : 'I_m) (xn : 'I_n) :
  A = submx_rows_cols m n A (ord_enum m) (ord_enum n) xm xn.
Proof. rewrite -matrixP => x y. by rewrite mxE !nth_ord_enum. Qed.

(*We need the column result here*)
Lemma matrix_zero_cols {n} (A B : 'M[F]_(n, 0)) : A = B.
Proof.
  rewrite -matrixP /eqrel. move => x y. have: y < 0 by []. by rewrite ltn0.
Qed.

Lemma flip_rows_row_equiv {m n} (A : 'M[F]_(m, n)) :
  row_equivalent A (flip_rows A).
Proof.
  have: 0 <= m by []. rewrite leq_eqVlt => /orP[/eqP H0 | Hmpos].
  - subst. rewrite {1}(matrix_zero_rows A (flip_rows A)). constructor.
  - have: 0 <= n by []. rewrite leq_eqVlt => /orP[/eqP H0 | Hnpos].
    + subst. rewrite {1}(matrix_zero_cols A (flip_rows A)). constructor. 
    + rewrite {1}(submx_rows_cols_whole A (pred_ord Hmpos) (pred_ord Hnpos) ).
      have->: flip_rows A = 
              submx_rows_cols m n A (rev (ord_enum m)) (ord_enum n) 
                 (pred_ord Hmpos) (pred_ord Hnpos). {
        rewrite -matrixP => x y.
        have Hsz: size (ord_enum m) = m by rewrite size_ord_enum.
        rewrite !mxE nth_rev // Hsz //=.
        have Hsub: m - x.+1 < m by apply rev_ord_proof. 
        have->: (m - x.+1)%nat = nat_of_ord (Ordinal Hsub) by []. 
        rewrite !nth_ord_enum. f_equal.
        by apply ord_inj. }
      apply perm_eq_row_equiv.
      * by rewrite perm_sym perm_rev.
      * by rewrite size_ord_enum.
      * by rewrite size_rev size_ord_enum.
Qed.

Lemma flip_rows_unitmx {n} (A : 'M[F]_n) :
  A \in unitmx = (flip_rows A \in unitmx).
Proof. apply (row_equivalent_unitmx_iff (flip_rows_row_equiv A)). Qed.

(*The result we want - any submatrix of a RR Vandermonde mx made of z unique 
  rows and z unique columns from the last (n - m) columns is invertible.
  To prove this, we use [added_rows_unitmx_iff] and add all missing rows and the
  corresponding columns. This gives us a submatrix that is actually just m 
  columns of the RR Vandermonde mx, which we know is invertible from 
  [vandermonde_gauss_cols_unitmx]*)
Lemma any_submx_unitmx {m n} (Hmn : m <= n) (Hm : 0 < m) z (l : list F) 
                      (rows : list 'I_m) (cols : list 'I_n) :
  uniq l ->  size l = n ->
  uniq rows -> uniq cols ->
  size rows = size cols -> size rows = z ->
  (forall x, x \in cols -> m <= x) ->
  (submx_rows_cols z z (gaussian_elim (vandermonde m n l)) 
    rows cols (Ordinal Hm) (widen_ord Hmn (Ordinal Hm)) \in unitmx).
Proof.
  move => Hunl Hszl Hunr Hunc Hszrc Hz Hinc.
  (*Need this in multiple places*)
  have Hunc':  uniq ([seq widen_ord Hmn i | i <- ord_comp rows] ++ cols). {
    rewrite cat_uniq Hunc map_inj_uniq //=. rewrite uniq_ord_comp andbT /=.
    apply /hasP. move => [x Hxin Hmem]. 
    have Hxin': x \in [seq widen_ord Hmn i | i <- ord_comp rows] by [].
    apply (elimT mapP) in Hxin'. move: Hxin' => [y Hyin Hxy]. subst.
    apply Hinc in Hxin. have Hym: y < m by [].
    have Hy: nat_of_ord (widen_ord Hmn y) = nat_of_ord y by [].
    rewrite Hy in Hxin.
    rewrite ltnNge in Hym. by rewrite Hxin in Hym.
    move => x y Hxy. eapply widen_ord_inj. apply Hxy. }
  rewrite (@added_rows_unitmx_iff _ _ _ _ _ _ _ _ (map (widen_ord Hmn) 
    (ord_comp rows)) (rows ++ (ord_comp rows)) _ m) //=.
  - (*We need to 1. replace rows by (ord_enum m), which is a permutations, 
      then 2. prove equivalent to a colmx that is therefore invertible*)
    rewrite (@row_equivalent_unitmx_iff _ _ _ 
        (submx_rows_cols m m (gaussian_elim (vandermonde m n l)) (ord_enum m)
    ([seq widen_ord Hmn i | i <- ord_comp rows] ++ cols) 
      (Ordinal Hm) (widen_ord Hmn (Ordinal Hm)))).
    2: { apply perm_eq_row_equiv. by apply ord_comp_app_perm.
         by rewrite ord_comp_cat_size. by rewrite size_ord_enum. }
    have->: submx_rows_cols m m (gaussian_elim (vandermonde m n l)) (ord_enum m)
      ([seq widen_ord Hmn i | i <- ord_comp rows] ++ cols) 
        (Ordinal Hm) (widen_ord Hmn (Ordinal Hm)) =
      colsub (fun (x: 'I_m) => (nth (widen_ord Hmn (Ordinal Hm)) 
        ([seq widen_ord Hmn i | i <- ord_comp rows] ++ cols) x))
         (gaussian_elim (vandermonde m n l)). {
      rewrite -matrixP => x y. by rewrite !mxE nth_ord_enum. }
    (*Now we can simply WTS that these m columns of the vandermonde mx are 
      invertible, which we proved before*)
    apply vandermonde_gauss_cols_unitmx; try by [].
    rewrite size_cat size_map -Hszrc addnC -size_cat.
      by rewrite ord_comp_cat_size.
  - by subst.
  - move => x Hinx. apply (elimT mapP) in Hinx. move: Hinx => [y Hyin Hxy].
    subst.
    have->: nat_of_ord (widen_ord Hmn y) = y by []. by [].
  - rewrite size_cat size_map -Hszrc addnC -size_cat.
    by rewrite ord_comp_cat_size.
  - by apply uniq_ord_comp_cat.
  - by rewrite prefix_subseq.
  - by rewrite !size_cat size_map Hszrc addnC.
  - move => x. rewrite mem_map. rewrite mem_cat !in_ord_comp.
    by case Hx: (x \in rows). move => i j Hw. apply (widen_ord_inj Hw).
Qed.

Lemma add_sub_1 n m : n.+1 = m -> n = m.-1.
Proof. by move => <-. Qed.

Lemma if_lt_succ n m : n < m -> (if n.+1 < m then n.+1 else m) = n.+1.
Proof.
  rewrite leq_eqVlt => /orP[/eqP Hnm | Hnm].
  - by rewrite Hnm ltnn.
  - by rewrite Hnm.
Qed. 

(*As a corollary of this result, [strong_inv] is satisfied for this submatrix*)
Lemma any_submx_strong_inv {m n} (Hmn : m <= n) (Hm : 0 < m) z (l : list F)
                          (rows : list 'I_m) (cols : list 'I_n) (r : 'I_z) :
  uniq l -> size l = n ->
  uniq rows -> uniq cols ->
  size rows = size cols -> size rows = z ->
  (forall x, x \in cols -> m <= x) ->
  strong_inv (submx_rows_cols z z 
     (gaussian_elim (vandermonde m n l)) rows cols (Ordinal Hm)
      (widen_ord Hmn (Ordinal Hm)))
    (ord_nonzero r) (leqnn _).
Proof.
  move => Hunl Hszl Hunr Hunc Hszrc Hszr Hincols.
  have H0n: 0 < n by apply (ltn_leq_trans Hm).
  rewrite /strong_inv. move => r' Hr'. split; move => j Hjr'.
  - rewrite submx_remove_col_list. apply any_submx_unitmx; try by [].
    + by apply take_uniq.
    + apply rem_nth_uniq. apply (Ordinal H0n). by apply take_uniq.
    + rewrite size_take Hszr (ltn_ord r') rem_nth_size.
      by rewrite size_take -Hszrc Hszr if_lt_succ.
      rewrite size_take -Hszrc Hszr if_lt_succ //. by apply (ltn_trans Hjr').
    + by rewrite size_take Hszr (ltn_ord r').
    + move => x Hin. apply rem_nth_mem in Hin. apply mem_take in Hin.
      by apply Hincols.
  - rewrite submx_add_row_list. apply any_submx_unitmx; try by [].
    + rewrite cat_uniq take_uniq //= orbF andbT -has_pred1 has_take_leq /=.
      case Hfind: (find (pred1 (nth (Ordinal Hm) rows j)) rows < r') => [//|//].
      move : Hfind. rewrite /pred1 /=. 
      remember (find [pred x | x == nth (Ordinal Hm) rows j] rows ) as f.
      rewrite -Heqf.
      have : nth (Ordinal Hm) rows f == nth (Ordinal Hm) rows j.
      rewrite Heqf. 
      pose proof (@nth_find _ (Ordinal Hm) [pred x | x == nth (Ordinal Hm) 
                       rows j] rows) as Hfind.
      rewrite /= in Hfind. apply Hfind. rewrite has_pred1 mem_nth //=.
      by rewrite Hszr.
      rewrite nth_uniq. move => /eqP Hfj. by rewrite Hfj ltnNge Hjr'.
      by rewrite Heqf -has_find has_pred1 mem_nth //= Hszr. by rewrite Hszr.
      by []. rewrite Hszr. by apply ltnW.
    + by apply take_uniq.
    + by rewrite size_cat size_take /= Hszr (ltn_ord r') size_take -Hszrc Hszr 
                 if_lt_succ //= addn1.
    + by rewrite size_cat size_take /= Hszr (ltn_ord r') addn1.
    + move => x Hin. apply mem_take in Hin. by apply Hincols.
    + rewrite Hszr. by apply ltnW.
Qed.

End RowRedVandermonde.

End GenericVandermonde.
