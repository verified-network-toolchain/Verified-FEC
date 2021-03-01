From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.poly.
Require Import LinIndep.
Require Import Gaussian. (*TODO: maybe move summation things to common file*)
Require Import CommonSSR.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(*TODO: maybe move to CommonSSR*)
Section RemNth.

(*Remove the (n+1)st position from a list*)
Definition rem_nth {A: eqType} (l: seq A) (n: nat) :=
  take n l ++ (drop (n.+1) l).

Lemma rem_nth_outside: forall {A: eqType} (l: list A) n,
  size l <= n ->
  rem_nth l n = l.
Proof.
  move => A l n Hsz. rewrite /rem_nth. rewrite take_oversize =>[//|//].
  rewrite drop_oversize. by rewrite cats0. by apply (leq_trans Hsz).
Qed.

Lemma rem_nth_size: forall {A: eqType} (l: list A) n,
  n < size l ->
  size (rem_nth l n) = (size l).-1.
Proof.
  move => A l n Hsz. rewrite /rem_nth size_cat size_take Hsz size_drop.
  have Halt: (n + (size l - n.+1).+1)%nat = size l. rewrite subnSK =>[|//].
  rewrite subnKC. by []. by rewrite ltnW. rewrite -{2}Halt.
  by rewrite -(addn1 (size l - n.+1)) addnA addn1 -pred_Sn.
Qed.

Lemma rem_nth_nth: forall {A: eqType} (l: list A) n (y: A) (i: nat),
  nth y (rem_nth l n) i = if i < n then nth y l i else nth y l (i.+1).
Proof.
  move => A l n y i. rewrite /rem_nth nth_cat. rewrite size_take.
  case Hnbounds: (n < size l).
  - case Hin: (i < n).
    + by rewrite nth_take.
    + rewrite nth_drop. rewrite -addn1 addnC addnA subnK. by rewrite addn1.
      by rewrite leqNgt Hin.
  - have {Hnbounds} Hnsz: size l <= n by rewrite leqNgt Hnbounds. case Hil: (i < size l).
    + have Hin: i < n by apply (ltn_leq_trans Hil Hnsz). rewrite Hin. by rewrite nth_take.
    + have {Hil} Hisz: size l <= i by rewrite leqNgt Hil. rewrite nth_drop. rewrite nth_default.
      case Hin: (i < n). by rewrite nth_default. rewrite nth_default. by [].
      by apply (leq_trans Hisz).
      apply (leq_trans Hnsz). have Hge0: (0 <= i - size l)%nat. {
      rewrite leq_eqVlt in Hisz.
      rewrite leq_eqVlt. move : Hisz => /orP[Hisz | Hisz].
      * by rewrite eq_sym subn_eq0 leq_eqVlt eq_sym Hisz.
      * by rewrite subn_gt0 Hisz orbT. }
      rewrite -{1}(addn0 n). by apply leq_add.
Qed.

Lemma drop_split: forall {A: eqType} (l: seq A) (n: nat) y,
  n < size l ->
  drop n l = nth y l n :: drop (n.+1) l.
Proof.
  move => A l n y Hnsz. rewrite -addn1 addnC -drop_drop.
  remember (drop n l) as d. move : Heqd; case d.
  move => Hdrop. have: (size (drop n l) = (size l - n)%nat) by rewrite size_drop. rewrite -Hdrop /=.
  have Hszpos: (0 < size l - n) by rewrite subn_gt0 Hnsz. move => Hz. rewrite Hz in Hszpos.
  by rewrite ltnn in Hszpos.
  move => h t Hdrop. rewrite /=. rewrite drop0 Hdrop.
  have: nth y (drop n l) 0 = h by rewrite -Hdrop /=. rewrite nth_drop addn0. by move->.
Qed. 


Lemma rem_nth_subseq: forall {A: eqType} (l: seq A) (n: nat) (y: A),
  subseq (rem_nth l n) l.
Proof.
  move => A l n y.
  have /orP[Hnin | Hnout] : (n < size l) || (size l <= n) by apply ltn_leq_total. 
  - rewrite /rem_nth. have: l = take n l ++ drop n l by rewrite cat_take_drop.
    rewrite (drop_split y Hnin). move => Hl. rewrite {3}Hl. 
    rewrite subseq_cat2l. apply subseq_cons.
  - rewrite rem_nth_outside. apply subseq_refl. by [].
Qed. 

Lemma rem_nth_uniq: forall {A: eqType} (l: seq A) (n: nat) (y: A),
  uniq l ->
  uniq (rem_nth l n).
Proof.
  move => A l n y Huniq.
  by apply (subseq_uniq (rem_nth_subseq l n y)).
Qed.

Lemma subseq_rem': forall {A: eqType} (l1 l2: seq A) (y: A),
  subseq l1 l2 ->
  uniq l2 ->
  y \notin l1 ->
  y \in l2 ->
  subseq l1 (rem y l2).
Proof.
  move => A l1 l2 y. move: l1. elim : l2 => [l1 Hsub Hun Hy Hyin //= | /= h t IH l1].
  case : l1 => [//= Ht Hun Ht' Hy /= | h1 t1 /=]. apply sub0seq. 
  case Hhh: (h1 == h).
  - eq_subst Hhh. move => Hsub /andP[Hnotin Hun] Hynot Hyin.
    case Hhy: (h == y). eq_subst Hhy. move: Hynot. by rewrite in_cons Bool.negb_orb eq_refl.
    rewrite /= eq_refl. apply IH. by []. by []. move: Hynot. by rewrite in_cons eq_sym Hhy.
    move: Hyin. by rewrite in_cons eq_sym Hhy.
  - move => Hsub /andP[Hnotin Hun] Hynot Hyin.  case Hhy: (h == y). eq_subst Hhy. by [].
    rewrite /= Hhh. apply IH. by []. by []. by []. move: Hyin. by rewrite in_cons eq_sym Hhy.
Qed. 

Lemma rem_nth_rem: forall {A: eqType} (l: seq A) (n: nat) (y: A) (x: A),
  uniq l ->
  n < size l ->
  nth x l n = y ->
  rem_nth l n = rem y l.
Proof.
  move => A l n y x Hun Hsz Hnth.
  rewrite remE /rem_nth. subst. by rewrite !index_uniq.
Qed. 

(*Put these together*)
Lemma rem_nth_subseq': forall {A: eqType} (l1 l2: seq A) (n : nat)(y: A),
  subseq l1 l2 ->
  uniq l2 ->
  nth y l2 n \notin l1 ->
  subseq l1 (rem_nth l2 n).
Proof.
  move => A l1 l2 n y Hsub Hun Hnotin.
  have /orP[Hnin | Hnout] : (n < size l2) || (size l2 <= n) by apply ltn_leq_total.
  - rewrite (@rem_nth_rem _ _ _ (nth y l2 n) y Hun Hnin). apply subseq_rem'; try by [].
    by apply mem_nth. by [].
  - by rewrite rem_nth_outside.
Qed.
    


(*

Lemma rem_nth_subseq': forall {A: eqType} (l1 l2: seq A) (n : nat)(y: A),
  subseq l1 l2 ->
  uniq l2 ->
  nth y l2 n \notin l1 ->
  subseq l1 (rem_nth l2 n).
Proof.
  move => A l1 l2 n y Hsub Hun Hnth.
  apply (introT (subseq_uniqP (rem_nth_uniq n y Hun))).
  apply (elimT (subseq_uniqP Hun)) in Hsub. rewrite {1}Hsub.
  Search filter mem. move : Hnth Hun . rewrite {Hsub}. move: l2. elim : l1 => [//= l2 Hnotin Hun | /= h t IH l2 Hnotin Hun ].
  - Search filter mem.
 => l1.

eq_in_filter

  Search map.
  Search ([ seq _ <- _ | mem (?l1) _]).
  assert ([seq x <- l2 | mem l1 x] = 
  
  rewrite /=.
  f_equal.
    rewrite mem_map.



 rewrite -map_comp.
  rewrite map_map.
  rewrite /=.
  apply /(subseq_uniqP Hun).
  have /orP[Hnin | Hnout] : (n < size l2) || (size l2 <= n) by apply ltn_leq_total. 
  - move: Hsub. rewrite /rem_nth. have: l2 = take n l2 ++ drop n l2 by rewrite cat_take_drop.
    rewrite (drop_split y Hnin). move => Hl. rewrite {1}Hl. Search subseq.
    pose proof subseq_rem. Search homomorphism_2. simpl in H.
    rewrite subseq_cat2l. apply subseq_cons.
  - rewrite rem_nth_outside. apply subseq_refl. by [].
Qed. 
  
  


subseq rows (rem_nth all_rows j)

*)
End RemNth.


Section GenericVandermonde.

Variable F : fieldType.

Local Open Scope ring_scope.

(*Sometimes this is defined as the transpose of a vandermonde mx. In our case, we want each column to
  contain the powers of a given element*)
Definition vandermonde (m n: nat) (l: list F) : 'M[F]_(m, n) :=
  \matrix_(i < m, j < n) (nth 0 l j) ^+ i.


(*Proof idea: suffices to show rows linearly independent. If c1r1 + c2r2 +... + cnrn = 0,
  then poly c1 + c2x + ... + cnx^(n-1) has roots at each elt in column. Since there are n columns,
  poly has n roots => identically zero*)
Lemma vandermonde_unitmx: forall n l,
  uniq l ->
  n = size l ->
  vandermonde n n l \in unitmx.
Proof.
  move => n l Huniq Hlen. rewrite unitmx_iff_lin_indep_rows.
  rewrite /rows_lin_indep /vandermonde. move => c Hzero.
  have: forall (j: 'I_n), \sum_(i < n) c i * (nth 0 l j) ^+ i = 0. {
  move => j. rewrite -{3}(Hzero j). apply eq_big =>[//|]. move => i H{H}. by
  rewrite mxE. }
  move => {}Hzero.
  (*Polys require functions from nat -> F, so we need the following*)
  remember (fun (n: nat) => match (insub n) with |Some n' => c n' | None => 0 end) as c'. 
  remember (\poly_(i < n) c' i) as p. 
  have Hroots: forall (j: 'I_n), p.[l`_j] = 0. { move => j.
    have Hsz: size p <= n by rewrite Heqp; apply size_poly. 
    rewrite (horner_coef_wide _ Hsz) -{4}(Hzero j) -(@big_mkord _ _ _ n (fun _ => true) (fun i => p`_i * l`_j ^+ i))
    (big_nth j) ordinal_enum_size big_nat_cond (big_nat_cond _ _ 0 n (fun _ => true)).
    apply eq_big => [//| i /andP[/andP[H{H} Hin] H{H}]].
    have->: (nth j (index_enum (ordinal_finType n)) i) = (nth j (index_enum (ordinal_finType n)) (Ordinal Hin))
    by apply (elimT eqP). rewrite !ordinal_enum. rewrite Heqp coef_poly Hin /=. 
    by have->: c' i = c (Ordinal Hin) by rewrite Heqc' insubT /=. }
  have Hallroot: all (root p) l. { rewrite all_in => x Hxin. rewrite /root. apply (introT eqP).
    have <-: nth 0 l (index x l) = x by apply nth_index.
    have Hidx: (index x l) < n by rewrite Hlen index_mem.
    have ->: l`_(index x l) = l`_(Ordinal Hidx) by []. apply Hroots. }
  (*Therefore, p is the 0 polynomial*)
  have Hp: p = 0. apply (roots_geq_poly_eq0 Hallroot Huniq). by rewrite -Hlen Heqp size_poly.
  move => x. have: p`_x = 0 by rewrite Hp; apply coef0.
  rewrite Heqp coef_poly. have Hxn: x < n by []. rewrite Hxn Heqc' insubT /=.
  have->: Ordinal Hxn = x. (apply (elimT eqP)). by have: x == x by rewrite eq_refl. by [].
Qed.

Definition fn_to_list {A} (n: nat) (f: 'I_n -> A) : list A :=
  map f (ord_enum n).

Lemma fn_to_list_nth: forall {A} (n: nat) (f: 'I_n -> A) (i: 'I_n) (x: A),
  nth x (fn_to_list f) i = f i.
Proof.
  move => A n f i x. rewrite /fn_to_list. rewrite (nth_map i). by rewrite nth_ord_enum.
  by rewrite size_ord_enum.
Qed.

Lemma fn_to_list_size: forall {A} (n: nat) (f: 'I_n -> A),
  size (fn_to_list f) = n.
Proof.
  move => A n f. by rewrite size_map size_ord_enum.
Qed.

Lemma fn_to_list_uniq: forall {A:eqType} (n: nat) (f: 'I_n -> A),
  injective f ->
  uniq (fn_to_list f).
Proof.
  move => A n f Hinj. rewrite map_inj_uniq //. apply ord_enum_uniq.
Qed.

(*If we select some of the columns (cols), this list is unique, and the original list was unique, this is
  injective*)
Lemma sublist_cols_uniq: forall m n (l: list F) (cols: list 'I_n) (y: 'I_n),
  uniq l ->
  uniq cols ->
  size l = n ->
  size cols = m ->
  injective (fun (x: 'I_m) => nth 0 l (nth y cols x)).
Proof.
  move => m n l cols y Hunl Hunc Hsz Hm i j /eqP Heq. subst. rewrite nth_uniq in Heq; try by [].
  have {}Heq: nth y cols i == nth y cols j by []. (*get rid of nat_of_ord*)
  rewrite (@nth_uniq _ y cols i j) in Heq; try by []. by apply /eqP.
Qed.

(*A corollary: If we have a vandermonde matrix with m rows and n columns, m <= n and unique elements, then
  if we take any m columns, that submatrix is invertible*)
Lemma vandermonde_cols_unitmx: forall m n l (cols: list 'I_n) (y: 'I_n),
  uniq l ->
  uniq cols ->
  n = size l ->
  m = size cols ->
  m <= n ->
  colsub (fun (x: 'I_m) => (nth y cols x))  (vandermonde m n l) \in unitmx.
Proof.
  move => m n l cols y Hunl Hunc Hszl Hszc Hmn.
  have->: colsub (fun x : 'I_m => nth y cols x) (vandermonde m n l) = 
    vandermonde m m (fn_to_list (fun (x : 'I_m) => nth 0 l (nth y cols x))). {
    rewrite -matrixP => i j /=. by rewrite !mxE /= fn_to_list_nth. }
  apply vandermonde_unitmx.
  - apply fn_to_list_uniq. by apply sublist_cols_uniq.
  - by rewrite fn_to_list_size.
Qed.

(*From the above, we can take any m columns after gaussian elimination and the result is still invertible*)
Lemma vandermonde_gauss_cols_unitmx: forall m n l (cols: list 'I_n) (y: 'I_n),
  uniq l ->
  uniq cols ->
  n = size l ->
  m = size cols ->
  m <= n ->
  colsub (fun (x: 'I_m) => (nth y cols x)) (gaussian_elim (vandermonde m n l)) \in unitmx.
Proof.
  move => m n l cols y Hunl Hunc Hszl Hszc Hmn.
  have Hre: row_equivalent (vandermonde m n l) (gaussian_elim (vandermonde m n l)) by apply gaussian_elim_row_equiv.
  rewrite (@row_equivalent_unitmx_iff _ _ _ (colsub (fun x : 'I_m => nth y cols x) (vandermonde m n l))).
  by apply vandermonde_cols_unitmx.
  apply colsub_row_equivalent. by apply row_equivalent_sym.
Qed.

(** Proving Strong Invertibility for the Weight Matrix (Row-reduced Vandermonde matrix)*)
(*The weight matrix is formed by row-reducing the [vandermonde_powers] matrix. Then we take some
  (dynamically chosen) z columns and z rows to invert. So we need to prove a much more general claim: for 
  an m X n [vandermonde_powers] matrix with m <= n, if we take z rows and z columns (z <= m) from among the
  last (n-m) columns, then the resulting submatrix is invertible. We will do this in several pieces*)
Section RowRedVandermonde.

(*TODO: could do this for general field although its not needed*)
(*Allows us to specify a submatrix by a list of rows and columns (we will need uniqueness and some additional
  length properties to use this*)
Definition submx_rows_cols {m n} z (A: 'M[F]_(m, n)) (rows: list 'I_m) (cols: list 'I_n) (xm : 'I_m) (xn: 'I_n) :=
  mxsub (fun (x: 'I_z) => nth xm rows x) (fun (x: 'I_z) => nth xn cols x) A.

(*To prove the invertibility of this submatrix, we will need to expand this to cover more columns. First we need
  to get a list of the rows that are not included in [rows]. This is more annoying than it seems*)

Fixpoint nat_comp (n: nat) (l: list nat) : list nat :=
  match n with
  | O => nil
  | n.+1 => if n \in l then nat_comp n l else (n :: nat_comp n l) 
  end.
(*
Fixpoint nat_comp (n: nat) (l: list nat) : list nat :=
  match n with
  | O => if 0%nat \in l then nil else 0%nat :: nil
  | n.+1 => if (n.+1) \in l then (n.+1 :: nat_comp n l) else nat_comp n l
  end.*)

Lemma nat_comp_bound: forall n l i,
  i \in (nat_comp n l) -> i < n.
Proof.
  move => n. elim : n => [l i Hin /= | /= n IH l i].
  - by rewrite ltn0.
  -  case Hnin : (n \in l).
    + move => Hin. apply IH in Hin. apply (ltn_trans Hin (ltnSn _)).
    + rewrite in_cons; move /orP => [Hin | Hrest].
      * eq_subst Hin. apply ltnSn.
      * apply IH in Hrest. apply (ltn_trans Hrest (ltnSn _)).
Qed.

Lemma in_nat_comp: forall n l i,
  i < n ->
  i \in (nat_comp n l) = (i \notin l).
Proof.
  move => n. elim : n => [l i Hi /= | n IH l i Hi /=].
  - by rewrite ltn0 in Hi.
  - have /orP Hlt: (i == n) || (i < n). rewrite ltnS in Hi. by rewrite -leq_eqVlt.
    case : Hlt => [Heq | Hlt].
    + eq_subst Heq. case Hin: (n \in l).
      * case Hincomp: (n \in nat_comp n l).
        -- apply nat_comp_bound in Hincomp. by rewrite ltnn in Hincomp.
        -- by [].
      * by rewrite in_cons eq_refl orTb.
    + case Hnin: (n \in l).
      * by apply IH.
      * rewrite in_cons. have->: (i == n = false) by apply ltn_eqF. rewrite orFb.
        by apply IH.
Qed.

Lemma in_nat_comp': forall n l i,
  i \in (nat_comp n l) = (i < n) && (i \notin l).
Proof.
  move => n l i. case Hincom: (i \in nat_comp n l).
  - have Hin : i < n by apply (nat_comp_bound Hincom).
    by rewrite Hin andTb -(in_nat_comp l Hin).
  - case Hin : (i < n).
    + rewrite in_nat_comp in Hincom =>[|//]. by rewrite Hincom.
    + by [].
Qed.

Lemma nat_comp_uniq: forall n l,
  uniq (nat_comp n l).
Proof.
  move => n. elim : n => [l //= | n IH l /=].
  case Hn : (n \in l).
  - apply IH.
  - rewrite /=. case Hcon: (n\in nat_comp n l).
    + apply nat_comp_bound in Hcon. by rewrite ltnn in Hcon.
    + by rewrite IH.
Qed. 

(*Now, we need to wrap this in Ordinals*)
Definition ord_comp {n: nat} (l: list 'I_n) : list 'I_n :=
  pmap insub (nat_comp n (map (@nat_of_ord n) l)).

Lemma in_ord_comp: forall n (l: list 'I_n) (i: 'I_n),
  (i \in (ord_comp l)) = (i \notin l).
Proof.
  move => n l i. rewrite /ord_comp mem_pmap_sub /= in_nat_comp'.
  have Hin: i < n by []. rewrite Hin andTb. rewrite mem_map //. apply ord_inj.
Qed.

(*Now we can define the expanded submatrix, it includes all rows and the same columns + the 
  columns corresponding to the missing rows*)
Definition submx_expand {m n} (Hmn: m <= n) (A: 'M[F]_(m, n)) (rows: list 'I_m) (cols : list 'I_n) 
  (xm : 'I_m) (xn: 'I_n) :=
  submx_rows_cols m A (ord_enum m) (cols ++ (map (widen_ord Hmn) (ord_comp rows))) xm xn.

(*TODO: move - this is *)
(*
Search sub_mem size.
Check mem_subseq.
Print subset.

Lemma in_subseq: forall {A: eqType} (s1 s2: seq A),
  uniq s1 ->
  uniq s2 ->
  (forall x, x \in s1 -> x \in s2) ->
  subseq s1 s2.
Proof. Print subseq.
  move => A s1 s2. move : s1. elim: s2 => [//= s1 | h t IH s1 /=].
  - case : s1. by []. move => h t HUn1 Hun2 Hin. have: h \in [::]. apply Hin. by rewrite in_cons eq_refl orTb.
    by [].
  - case : s1. by []. 
    move => h1 t1 Hun1 Hun2 Hin. rewrite cons_uniq in Hun1. apply (elimT andP) in Hun. case : Hun => [Hht Hunt]. 
    case Hhh: (h1 == h).
    + eq_subst Hhh. apply IH. by []. move => x Hint. have: x \in h :: t. apply Hin. by rewrite in_cons Hint orbT.
      rewrite in_cons. case Hxh: (x == h).
      * eq_subst Hxh. by rewrite Hint in Hht.
      * by [].
    + apply IH. rewrite cons_uniq. by rewrite Hht Hunt. move => x Hinx.
      case Hxh: (x == h1).
      * eq_subst Hxh. apply Hin in Hinx. rewrite in_cons in Hinx. by rewrite Hhh in Hinx.
      * 



        by [].
      rewrite in_cons in Hinx. rewrite /=.



 rewrite /=. 

  Search subseq size. case : (

 move => /(_ h). by [].

 rewrite /=. case : s1.


 move => 


 apply mem_subseq. in Hsub. apply Hsub.
Qed.

Lemma subseq_in: forall {A: eqType} (s1 s2: seq A),
  subseq s1 s2 -> forall x, x \in s1 -> x \in s2.
Proof.
  move => A s1 s2 Hsub. apply mem_subseq in Hsub. apply Hsub.
Qed.
*)

(*TODO: move*)
Lemma rem_in_neq: forall {A: eqType} (l : seq A) (y: A) (x: A),
  x != y ->
  (x \in (rem y l)) = (x \in l).
Proof.
  move => A l y x Hxy. elim : l => [//= | h t IH /=].
  case Hhy: (h == y).
  - eq_subst Hhy. rewrite in_cons. have->: (x == y = false). move : Hxy. by case (x == y).
    by [].
  - rewrite !in_cons. by rewrite IH.
Qed. 
(*Proof idea: we will show that the [submx_rows_cols] we care about is invertible iff the corresponding [submx_expand]
  is, where the larger matrix is formed from adding the columns corresponding to the rows missing. Because the LHS
  of the matrix is the identity, we can use the cofactor formula for determinants to peel off each of these columns,
  preserving invertibility. Finally, the larger matrix is invertible due to [vandermonde_gauss_cols_unitmx]*)
Lemma added_rows_unitmx_iff: forall {m n} (Hmn: m <= n)  (xm: 'I_m) (xn: 'I_n) (l: seq F) (rows: seq 'I_m) (cols: seq 'I_n)
  (added_cols: seq 'I_n) (all_rows: seq 'I_m) z k,
  uniq l ->
  n = size l ->
  (forall x, x \in cols -> m <= x) -> (*only consider submatrices in last n - m columns, clearly not true otherwise*)
  uniq rows ->
  size cols = size rows ->
  size cols = z ->
  (forall x, x \in added_cols -> x < m) ->
  uniq (added_cols ++ cols) ->
  size (added_cols ++ cols) = k ->
  uniq (all_rows) ->
  subseq rows all_rows ->
  size (added_cols ++ cols) = size all_rows ->
  (forall x, (widen_ord Hmn x) \in added_cols = (x \in all_rows) && (x \notin rows)) -> (*we add the same rows and columns*) 
  (submx_rows_cols z (gaussian_elim (vandermonde m n l)) rows cols xm xn \in unitmx) = 
  (submx_rows_cols k (gaussian_elim (vandermonde m n l)) all_rows (added_cols ++ cols) xm xn \in unitmx).
Proof.
  move => m n Hmn xm xn l rows cols added_cols all_rows z k Hunl Hszl Hinc Hunr Hszcr Hszc. 
  rewrite !unitmxE !GRing.unitfE. (*work with determinants for cofactors*)
  move : k all_rows.  (*need these to be generalized for induction*) 
  elim : added_cols => [/= k all_rows Hinadd Hunc Hszadd Hunall Hsubs Hszall Hrowcol /= | 
    /= h t IH k all_rows Hinadd Hunadd Hszadd Hunall Hsubs Hszaddall Hrowcol].
  - have->: rows = all_rows. apply size_subseq_leqif in Hsubs; move: Hsubs. rewrite /leqif -Hszcr Hszall eq_refl; 
    move  => [Htriv Hrows]. apply /eqP. by rewrite -Hrows. by subst.
  - (*expand determinant along cofactor*)
    have Hk: 0 < k. move: Hszadd <-. apply ltn0Sn.
    rewrite ( expand_det_col (submx_rows_cols k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn)
      (Ordinal Hk)). 
    (*now, need to show that all but 1 entry in the sum is 0*)
    have Hhm: h < m. apply Hinadd. by rewrite in_cons eq_refl.
     have Hvan: (colsub (widen_ord Hmn) (vandermonde m n l) \in unitmx). {
        have->: colsub (widen_ord Hmn) (vandermonde m n l) = vandermonde m m (take m l). {
          rewrite -matrixP => x y. rewrite !mxE. by rewrite nth_take. }
        apply vandermonde_unitmx. by apply take_uniq. rewrite size_takel //. by subst. }
    have Hinner: forall i, submx_rows_cols k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn i (Ordinal Hk) = 
      if (nat_of_ord (nth xm all_rows i) == nat_of_ord h) then 1 else 0. {
      move => i. rewrite mxE /=. 
      by apply (gaussian_elim_identity_val Hvan). }
    (*work with the summation - can we do this nicely at all?*)
    have->: (\sum_i
      submx_rows_cols k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn i (Ordinal Hk) *
      cofactor (submx_rows_cols k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn) i
        (Ordinal Hk)) =
    (\sum_i
      if nat_of_ord (nth xm all_rows (nat_of_ord i)) == (nat_of_ord h) then 
      submx_rows_cols k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn i (Ordinal Hk) *
      cofactor (submx_rows_cols k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn) i
      (Ordinal Hk) else 0). {
      apply eq_big. by []. move => i H{H}. rewrite Hinner. 
        case Hih : (nat_of_ord (nth xm all_rows (nat_of_ord i)) == (nat_of_ord h)). by [].
        by rewrite GRing.mul0r. }
    rewrite {Hinner}.
    have Hallsz: size all_rows = k by subst.
    have Hhin: (Ordinal Hhm \in all_rows) && (Ordinal Hhm \notin rows). move : Hrowcol => /(_ (Ordinal Hhm)) /=.
      have->: widen_ord Hmn (Ordinal Hhm) = h by apply ord_inj. rewrite in_cons eq_refl orTb.
      move => Hhinfo. by symmetry in Hhinfo. apply (elimT andP) in Hhin. case : Hhin => [Hhall Hhrow].
    have [j Hj]: (exists (j: 'I_k), nat_of_ord (nth xm all_rows j) == nat_of_ord h).  {
      have Hj: (index (Ordinal Hhm) all_rows) < k. by rewrite -Hallsz index_mem.
      exists (Ordinal Hj). by rewrite nth_index. }
    (*Now we separate j from the rest of the sum, which is 0*)
    rewrite (@sum_remove_one _ _  _ _ j) // Hj. rewrite big1.
    2 : { move => i /andP[Htriv Hij]. case Hih: (nat_of_ord (nth xm all_rows i) == (nat_of_ord h)).
      - have Hijeq: i == j. apply /eqP. apply ord_inj. apply /eqP. rewrite -(@nth_uniq _ xm all_rows) //.
        apply /eqP. apply ord_inj. eq_subst Hj. rewrite Hj. by apply /eqP. by rewrite Hallsz.
        by rewrite Hallsz.
        by rewrite Hijeq in Hij.
      - by []. }
    rewrite GRing.add0r mxE /= (gaussian_elim_identity_val Hvan) // Hj GRing.mul1r {Hvan} /cofactor.
    (*So now, we just need to prove that the determinant is zero when the determinant of the new submatrix is.
      This is the matrix that we will use in the IH, but there's a decent amount to do to prove the preconditions*)
    rewrite GRing.Theory.mulf_eq0 negb_or GRing.signr_eq0 /=.
    (*Have to prove this new matrix equivalent to the one we need for the IH*)
    have ->:(row' j
         (col' (Ordinal Hk)
            (submx_rows_cols k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn))) =
      (submx_rows_cols k.-1 (gaussian_elim (vandermonde m n l)) (rem_nth all_rows j) (t ++ cols) xm xn). {
      rewrite -matrixP => x y. rewrite !mxE /=. f_equal. rewrite rem_nth_nth /bump.
      case Hxj : (x < j). rewrite ltnNge in Hxj. case Hjx: (j <= x); try by []. by rewrite Hjx in Hxj.
      rewrite ltnNge in Hxj. apply negbFE in Hxj. by rewrite Hxj. }
    (*Now, we will apply the IH and deal with the many goals we have*)
    apply IH.
    + move => x Hinx. apply Hinadd. by rewrite in_cons Hinx orbT.
    + apply (elimT andP) in Hunadd. apply Hunadd.
    + apply /eqP. rewrite -eqSS Hszadd. apply /eqP. eapply Lt.S_pred. apply /ltP. apply Hk.
    + by apply rem_nth_uniq.
    + apply rem_nth_subseq' with (y:=xm); try by [].
      have->: nth xm all_rows j = Ordinal Hhm.  apply ord_inj. by eq_subst Hj. by [].
    + rewrite rem_nth_size. subst. by rewrite Hallsz -pred_Sn. by rewrite Hallsz.
    + move => x. rewrite (@rem_nth_rem _ _ j (Ordinal Hhm) xm) //=. 2: by rewrite Hallsz.
      2: by ( apply ord_inj; apply (elimT eqP) in Hj; rewrite Hj). 
      case Hxh: (x == Ordinal Hhm).
      * eq_subst Hxh. rewrite Hhrow andbT. 
        have->: (widen_ord Hmn (Ordinal Hhm) \in t)  = false. apply (elimT andP) in Hunadd.
        case : Hunadd => [Hnotin Hunt]. move: Hnotin. rewrite mem_cat negb_or => /andP [Hnotht Hnotcol].
        have->: (widen_ord Hmn (Ordinal Hhm) = h) by apply ord_inj. move: Hnotht; by  case : (h \in t).
        by rewrite mem_rem_uniqF.
      * move : Hrowcol => /(_ x). rewrite in_cons. have->: (widen_ord Hmn x == h) = false.
        case Hxh': (widen_ord Hmn x == h). eq_subst Hxh'. have Hxm: (x == Ordinal Hhm). apply /eqP. by apply ord_inj.
        by rewrite Hxm in Hxh. by []. rewrite /=. move ->. rewrite rem_in_neq //. move : Hxh; by case : (x == Ordinal Hhm).
Qed.

(*The hard part is done, just need 1 or 2 small corollaries until we have the result we need*)


End GenericVandermonde.

Require Import PolyField.
Require Import Poly.
Require Import Coq.ZArith.BinInt.
Require Import PolyMod.
Require Import Lia.
Require Import PrimitiveFacts (*for typeclass*).

Section PrimitiveVandermonde.

Local Open Scope ring_scope.

(*The specific Vandermonde matrix that we will actually use*)
Context (f: poly) `{Hprim: PrimPoly f}.


Definition F := @qpoly_fieldType f Hpos0 Hprim. (*Hpos (@f_irred f Hprim).*)

Definition qx : qpoly f := poly_to_qpoly f x.

(*Because the C code actually reverses the rows, we need rev of the natural choice 1, x, x^2, etc*)
Definition vandermonde_powers m n : 'M[F]_(m, n) := vandermonde m n (rev (map (fun i => (qx ^+ i)) (iota 0 n))).

(*Alternate definition, useful for rewriting*)
Lemma vandermonde_powers_val: forall (m n: nat) (i : 'I_m) (j: 'I_n),
  vandermonde_powers m n i j = (qx ^+ (i * (n - j - 1))).
Proof.
  move => m n i j. rewrite /vandermonde_powers /vandermonde mxE.
  have Hjsz: j < size (iota 0 n) by rewrite size_iota. rewrite -map_rev.
  have->: [seq qx ^+ i0 | i0 <- rev(iota 0 n)]`_j = qx ^+ (n - j - 1). {
  rewrite (nth_map 0%nat) => [|//]. rewrite nth_rev=>[|//]. rewrite size_iota nth_iota.
  by rewrite add0n -subnDA addn1. apply rev_ord_proof. by rewrite size_rev. }  
  by rewrite GRing.exprAC GRing.exprM.
Qed. 

(*Now we need to prove [strong_inv] for this matrix*)

(*Transform statement about x^n from ssreflect ring ops to polynomial functions*)
Lemma exp_monomial: forall (n: nat),
  (@GRing.exp F qx n) = poly_to_qpoly f (monomial n).
Proof.
  move => n. elim: n.
  - rewrite GRing.expr0. rewrite monomial_0.
    have->: (GRing.one F) = q1 (f:=f) by []. rewrite /q1 /r1 /poly_to_qpoly. exist_eq.
    rewrite pmod_refl =>[//|]. have <-: (0%Z = deg one) by rewrite deg_one. case: Hpos0. lia.
  - move => n IH.
    rewrite GRing.exprS IH.
    have ->: (ssralg.GRing.mul (R:=ssralg.GRing.Field.ringType F)) = qmul (f:=f) by [].
    rewrite /poly_to_qpoly /qmul /r_mul /poly_mult_mod /=. exist_eq. by rewrite monomial_expand -pmod_mult_distr.
Qed.
  
(*First, we need to know that x^i != x^j if i != j and i, j < 2 ^ (deg f) -1. We proved something very similar
  (but unfortunately a bit different due to how the C code works) in [PrimitiveFacts]*)
Lemma powers_unequal: forall (n m : nat), n != m ->
  (n < (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat) ->
  (m < (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat) ->
  (@ GRing.exp F qx n) != qx ^+ m.
Proof.
  have Hgen: forall n m, n < m ->
    (n < (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat) ->
  (m < (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat) ->
  (@ GRing.exp F qx n) != qx ^+ m. {
  move => m n Hnm Hn Hm.
  case Heq : (qx ^+ m == qx ^+ n) =>[|//].
  rewrite eq_sym -GRing.subr_eq0 in Heq.
  have /eqP Hn_split: n == (m + (n - m))%nat. rewrite addnC subnK. by []. by rewrite ltnW.
  move : Heq. have Hzero: (GRing.zero F = q0 (f:=f)) by []. have f_irred: irreducible f. eapply (f_irred). apply Hprim.
  (*move : Hprim => [f_pos f_prim f_notx].*) 
  rewrite Hn_split {Hn_split} GRing.exprD -{2}(GRing.mulr1 (qx ^+ m)) -GRing.mulrDr GRing.mulf_eq0 =>
  /orP[Hm0 | Hnm0].
  - have {}Hm0 : (@GRing.exp F qx m) = 0 by apply (elimT eqP). move : Hm0.
    rewrite Hzero exp_monomial /poly_to_qpoly /q0 /r0 => Hpoly. exist_inv Hpoly.
    have Hdiv: f |~ (monomial m). rewrite divides_pmod_iff. by []. 
    left. apply f_nonzero. apply Hpos0. exfalso. have Hirred: irreducible f by eapply f_irred.
    apply (irred_doesnt_divide_monomial f m Hpos Hirred Hnotx Hdiv).
  - have {}Hnm0: (@GRing.exp F qx (n - m)) + 1 = 0 by apply (elimT eqP). move: Hnm0. 
    rewrite exp_monomial Hzero.
    have ->: (GRing.one F = q1 (f:=f)) by []. 
    have ->: (GRing.add (V:=ssralg.GRing.Field.zmodType F)) = qadd (f:=f) by []. 
    rewrite /qadd /q1 /q0 /poly_to_qpoly /r_add /= /r0 => Hpoly; exist_inv Hpoly.
    move: Hpoly; rewrite /poly_add_mod. rewrite -(pmod_refl f one). rewrite -pmod_add_distr =>[Hmod].
    have Hdiv: ( f |~ nth_minus_one (n - m)). rewrite divides_pmod_iff. by []. left. 
    by apply f_nonzero. case: Hprim => [[Hdeg [Hir [Hn0 Hnodiv]]] f_notx].
    apply Hnodiv in Hdiv. case: Hdiv => [Hmn0 | Hlarge].
    + have: (n - m == 0)%nat by apply (introT eqP). by rewrite subn_eq0 leqNgt Hnm.
    + have Hnup: (n >= (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat)%coq_nat.
      have: (n - m <= n)%coq_nat. apply (elimT leP).  by rewrite leq_subr. lia.
      have Hnlow: (n < (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat)%coq_nat by apply (elimT ltP). lia.
    +  have<-:(0%Z = deg one) by rewrite deg_one. case: Hpos0; lia. } 
   move => n m Hnm Hn Hm.
   pose proof (ltn_total n m) as Hmntotal. move: Hmntotal => /orP[/orP[Hlt | Heq] |Hgt].
   - by apply Hgen.
   - by rewrite Heq in Hnm.
   - rewrite eq_sym. by apply Hgen.
Qed.

(*We need the above in order to prove our lists are uniq for proving the variable vandermonde submatrices invertible*)
Lemma power_list_uniq: forall (n: nat),
  n <= (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat ->
  uniq [seq (@GRing.exp F qx i) | i <- iota 0 n].
Proof.
  move => n Hn. rewrite map_inj_in_uniq. by rewrite iota_uniq.
  move => x y Hx Hy Hqxy.
  apply (elimT eqP). case Hxy: (x == y) =>[//|].
  have:  (@ GRing.exp F qx x) != qx ^+ y. apply powers_unequal. by rewrite Hxy.
  move : Hx. rewrite mem_iota add0n => /andP[H{H} Hx].
  by apply (ltn_leq_trans Hx).
  move : Hy. rewrite mem_iota add0n => /andP[H{H} Hy].
  by apply (ltn_leq_trans Hy). by rewrite Hqxy eq_refl.
Qed.

(*Now we deal with the matrices more directly*)

Lemma vandermonde_remove_col_list: forall m n (Hmn: m <= n) l (r:'I_m) (j: nat),
  submx_remove_col (@vandermonde F m n l) Hmn r j = vandermonde r r (rem_nth (take (r.+1) l) j).
Proof.
  move => m n Hmn l r j. rewrite /submx_remove_col /vandermonde -matrixP /eqrel => x y.
  rewrite !mxE. rewrite rem_nth_nth /=. case Hyj: (y < j).
  - rewrite /=. rewrite nth_take. by []. have Hyr: y < r by []. by apply (ltn_trans Hyr).
  - rewrite /=. rewrite nth_take. by []. by rewrite -(addn1 y) -(addn1 r) ltn_add2r.
Qed.

Lemma vandermonde_remove_col_unitmx: forall m n (Hmn: m <= n) (r: 'I_m) (j: nat),
  j < r ->
  (n <= (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat) ->
  submx_remove_col (vandermonde_powers m n) Hmn r j \in unitmx.
Proof.
  move => m n Hmn r j Hjr Hnbound.
  rewrite vandermonde_remove_col_list. apply vandermonde_unitmx.
  - apply rem_nth_uniq. apply 0. apply take_uniq. rewrite rev_uniq. by apply power_list_uniq.
  - have Hsz: size (take r.+1 (rev  [seq (@GRing.exp F qx i) | i <- iota 0 n])) = r.+1. {
    rewrite size_take size_rev size_map size_iota.
    have Hrm: r.+1 <= m by []. have: r.+1 <= n by apply (leq_trans Hrm Hmn).
    rewrite leq_eqVlt => /orP[/eqP Hr1n | Hr1n].
    + rewrite Hr1n. rewrite ltnn -Hr1n. apply pred_Sn.
    + rewrite Hr1n. apply pred_Sn. }
    rewrite rem_nth_size; rewrite Hsz. apply pred_Sn. by apply (ltn_trans Hjr).
Qed.

(* The row matrix is much more complicated.
  Let P be the original powers matrix. Then p_ij = x^i(n-j-1).
  So row i consists of x^i(n-1), x^i(n-2),..., x^i(n-r). We cannot simply take the transpose, because this
  is the reverse of a vandermonde matrix - every column goes in decreasing powers of x.
  So we proved a result that we can flip all the rows while preserving invertibility, allowing us to 
  get x^i(n-r), x^i(n-r+1),... in each column (after transpose). But this is still not good enough, since
  we start with some extra powers of x (ie, a column might be x^4, x^6, x^8,...). So before doing the above,
  we first scalar multiply each row i by p_ir^-1 = x^-(i(n-r-1)).
  So the transformations are as follows:
  p_{ij} = x^{i(n-j-1)}
  p1_{ij} = x^{i(r-j)} (scalar multiply)
  p2_{ij} = x^{j(r-i)} (transpose)
  p3_{ij} = x^{ji} (flip all rows (i -> r.+1 - i - 1)
  Finally, p3 is a vandermonde matrix, so it is invertible. Since all of these transformations preserve
  invertibility, p is also invertible. *)


Definition scalar_mult_last_inv {m n} (Hn: 0 < n) (A: 'M[F]_(m, n)) : 'M[F]_(m, n) :=
  foldr (fun (r: 'I_m) acc => sc_mul acc (A r (pred_ord Hn))^-1 r) A (ord_enum m).

Lemma scalar_mult_last_inv_val: forall {m n} (Hn: 0 < n) (A: 'M[F]_(m, n)) i j,
  scalar_mult_last_inv Hn A i j = (A i j) * (A i (pred_ord Hn))^-1.
Proof.
  move => m n Hn A i j. rewrite mx_row_transform.
  - by rewrite /sc_mul mxE eq_refl GRing.mulrC.
  - move => A' i' j' r Hir'. rewrite /sc_mul mxE. 
    by have->:(i' == r = false) by move: Hir'; case (i' == r).
  - move => A' B r Hin Hout j'. by rewrite /sc_mul !mxE eq_refl Hin.
  - apply ord_enum_uniq.
  - apply mem_ord_enum.
Qed.

Lemma qx_not_zero: qx != @GRing.zero F.
Proof.
  case Hx : (qx == 0) =>[|//].
  eq_subst Hx. move: Hx. have->: @GRing.zero F = q0 (f:=f) by []. move => Hx. exist_inv Hx.
  have: f = x. rewrite -divides_x. rewrite divides_pmod_iff. by []. left. by apply f_nonzero.
  case: Hpos0; lia. by move : Hprim => [f_prim f_notx] fx. 
Qed.

(*This is the big lemma that will allow us to prove the transpose of this matrix equivalent to a vandermonde mx*)
Lemma scalar_mult_last_inv_vandermonde_powers: forall {m n} (Hmn: m <= n) (r : 'I_m) y i j,
  r <= nat_of_ord y ->
  (scalar_mult_last_inv (ltn0Sn r) (submx_add_row (@vandermonde_powers m n) Hmn r y)) i j = 
    qx ^+ ((if i < r then nat_of_ord i else nat_of_ord y) * (r-j)).
Proof.
  move => m n Hmn r y i j Hry. rewrite scalar_mult_last_inv_val !mxE.
  have /eqP Hord: nat_of_ord (widen_ord (leq_trans (ltn_ord r) Hmn) j) == j by []. rewrite !Hord.
  have /eqP Hord' : nat_of_ord (widen_ord (leq_trans (ltn_ord r) Hmn) (pred_ord (ltn0Sn r))) == r by [].
  rewrite {Hord} !Hord' {Hord'} !nth_rev; rewrite !size_map size_iota.
  have Hnsub: forall p, n - p.+1 < n. { move => p. rewrite ltn_subrL ltn0Sn /=.
  have: 0 <= n by []. rewrite leq_eqVlt => /orP[Hn0 | //]. eq_subst Hn0.
  have Hrm: r < m by []. rewrite leqn0 in Hmn. eq_subst Hmn. by []. }
  rewrite !(nth_map 0%nat); try (by rewrite size_iota). rewrite !nth_iota; try (by rewrite Hnsub).
  rewrite !add0n.
  have Hsimpl: forall (z : nat),
  (@GRing.exp F qx (n - j.+1)) ^+ z / qx ^+ (n - r.+1) ^+ z = qx ^+ (z * (r - j)). {
  move => z. have: 0 <= z by []. rewrite leq_eqVlt => /orP[Hz0 | Hz].
  + eq_subst Hz0. rewrite -!GRing.exprM !muln0 mul0n !GRing.expr0. apply GRing.mulfV.
    apply GRing.oner_neq0.
  + have: j <= r by rewrite ltnSE. rewrite leq_eqVlt => /orP[Hjreq | Hlt].
    - eq_subst Hjreq. rewrite Hjreq subnn muln0 GRing.expr0. apply GRing.mulfV.
      rewrite -GRing.exprM. rewrite GRing.expf_neq0. by []. apply qx_not_zero.
    - rewrite -!GRing.exprM. rewrite -!GRing.Theory.expfB.
      2: { have Hjr1: j.+1 < r.+1 by []. rewrite ltn_mul2r Hz /=.
        apply ltn_sub2l.
        have Hrm: r.+1 <= m by []. have Hjm: j.+1 < m by apply (ltn_leq_trans Hjr1 Hrm).
        apply (ltn_leq_trans Hjm Hmn). by []. }
      rewrite -mulnBl subnBA. rewrite -addnABC. rewrite addnC -subnBA. 
      by rewrite subnn subn0 subSS mulnC. by rewrite leqnn.
      have Hjm: j < m by apply (ltn_trans Hlt). by apply (ltn_leq_trans Hjm Hmn). by [].
      have Hrm: r < m by []. by apply (ltn_leq_trans Hrm). }
  have: i <= r by rewrite ltnSE. rewrite leq_eqVlt => /orP[Hireq | Hlt].
  - eq_subst Hireq. rewrite Hireq ltnn. apply Hsimpl.
  - rewrite Hlt /=. apply Hsimpl.
  - have Hrm: r < m by []. by apply (ltn_leq_trans Hrm).
  - have Hjr: j <= r by rewrite -ltnS. have Hrm : r < m by [].
    have Hjm: j < m by apply (leq_ltn_trans Hjr Hrm). by apply (ltn_leq_trans Hjm).
Qed. 


(*The row matrix is a bit more complicated. The resulting matrix isn't Vandermonde, but
  if we transpose it and then flip all the rows, then it is. So we use the [flip_rows] result as well*)

Lemma vandermonde_powers_add_row_list: forall m n (Hmn: m <= n) (r j:'I_m),
  (r <= j) ->
  flip_rows ((scalar_mult_last_inv (ltn0Sn r) (submx_add_row (@vandermonde_powers m n) Hmn r j))^T) =
    vandermonde (r.+1) (r.+1) ((map (fun i => (qx ^+ i)) (iota 0 r)) ++ (qx ^+ j :: nil)).
Proof.
  move => m n Hmn r j Hrj. rewrite /flip_rows /vandermonde -matrixP /eqrel => x y.
  rewrite mxE mxE scalar_mult_last_inv_vandermonde_powers. 2: by []. rewrite  !mxE.
  have Hxn: x < n. have Hxr: x < r.+1 by []. rewrite ltnS in Hxr.
    have Hrm: r < m by []. have Hxm: x < m by apply (leq_ltn_trans Hxr Hrm).
    by apply (ltn_leq_trans Hxm Hmn).
  have Hx: (r - (r.+1 - x - 1))%nat = x.
    rewrite -subnDA addnC subnDA subn1 -pred_Sn. apply subKn. by rewrite -ltnS.
  have: y < r.+1 by []. rewrite ltnS leq_eqVlt => /orP[/eqP Hyr | Hyr].
  - rewrite Hyr ltnn. rewrite nth_cat.
    rewrite size_map size_iota ltnn subnn /=. by rewrite Hx -GRing.exprM.
  - rewrite Hyr /=. rewrite nth_cat size_map size_iota Hyr.
    rewrite !(nth_map 0%nat) /=. rewrite !nth_iota.
    rewrite !add0n. by rewrite Hx -GRing.exprM. by []. by rewrite size_iota.
Qed.

Lemma vandermonde_add_row_unitmx: forall m n (Hmn: m <= n) (r j:'I_m),
  (r <= j) ->
  (n <= (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat) ->
  submx_add_row (vandermonde_powers m n) Hmn r j \in unitmx.
Proof.
  move => m n Hmn r j Hrj Hn.
  (*lots of layers to show*)
  have Hinv: row_equivalent (submx_add_row (vandermonde_powers m n) Hmn r j)
    (scalar_mult_last_inv (ltn0Sn r) (submx_add_row (vandermonde_powers m n) Hmn r j)). {
  apply mx_row_transform_equiv. move => A' r'. apply ero_row_equiv. apply ero_sc_mul.
  rewrite !mxE /=. (*need to do it here to show that not zero*)
  have Hnr: n - r.+1 < n.  rewrite ltn_subrL ltn0Sn /=. have: 0 <= n by []. 
  rewrite leq_eqVlt => /orP[Hn0 | //]. eq_subst Hn0.
  have Hrm: r < m by []. rewrite leqn0 in Hmn. eq_subst Hmn. by [].
  rewrite nth_rev size_map size_iota. rewrite (nth_map 0%nat). rewrite nth_iota.
  rewrite add0n -!GRing.exprVn -GRing.exprM GRing.expf_neq0. by [].
  apply GRing.invr_neq0. apply qx_not_zero. by []. by rewrite size_iota.
  have Hrm: r < m by []. by apply (ltn_leq_trans Hrm). }
  apply row_equivalent_unitmx_iff in Hinv. rewrite Hinv {Hinv}.
  rewrite -unitmx_tr flip_rows_unitmx_iff vandermonde_powers_add_row_list =>[|//].
  apply vandermonde_unitmx.
  - rewrite cats1 rcons_uniq.
    have->: (qx ^+ j \notin [seq (@GRing.exp F qx i) | i <- iota 0 r]). {
      case Hin: (qx ^+ j \in [seq qx ^+ i | i <- iota 0 r]) =>[|//]. 
      apply (elimT mapP) in Hin. move : Hin => [i Hi Heq].
      move : Hi; rewrite mem_iota add0n => /andP[H{H} Hir].
      have: (@GRing.exp F qx j != qx ^+ i). {
      have Hjbound: j < (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat. {
        have Hjm: j < m by []. have Hjn: j < n by apply (ltn_leq_trans Hjm Hmn).
        apply (ltn_leq_trans Hjn Hn). }
      apply powers_unequal.
      + rewrite eq_sym. have: i < j by apply (ltn_leq_trans Hir Hrj). by rewrite ltn_neqAle => /andP[Hneq H{H}].
      + by [].
      + have Hij: i < j by apply (ltn_leq_trans Hir Hrj). apply (ltn_trans Hij Hjbound). }
      by rewrite Heq eq_refl. }
    rewrite /=. apply power_list_uniq.
    have Hrn: r < n. have Hrm: r < m. have Hjm: j < m by []. by apply (leq_ltn_trans Hrj Hjm).
    by apply (ltn_leq_trans Hrm Hmn). by apply (ltnW(ltn_leq_trans Hrn Hn)).
  - by rewrite size_cat /= size_map size_iota addn1.
Qed.

(*Finally, the result we want: The Vandermonde matrix consisting of powers of the primitive element
  satisfied [strong_inv 0]*)
Lemma vandermonde_strong_inv: forall m n (Hmn: m <= n) (Hm: 0 < m),
  (n <= (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat) ->
  strong_inv (vandermonde_powers m n) Hmn (Ordinal Hm).
Proof.
  move => m n Hmn Hm Hn. rewrite /strong_inv => r' H{H}.
  split; move => j Hrj.
  - by apply vandermonde_remove_col_unitmx.
  - by apply vandermonde_add_row_unitmx.
Qed.



(*When one [submx_rows_cols] is a submatrix of another:*)
(*TODO: don't need this*)
(*Definition submx_rows_cols_submx {m n} (Hmn: m <= n) (A: 'M[F]_(m, n)) (r1 r2 : list 'I_m) (c1 c2 : list 'I_n) :=
   subseq r1 r2 && subseq c1 c2.
*)






End PrimitiveVandermonde.