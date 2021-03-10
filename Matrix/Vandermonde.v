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

(*Now we want to use submatrices defined by lists of rows and columns. So we need to convert
  a function to a list and vice versa*)

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
  an m X n row-reduced Vandermonde matrix with m <= n, if we take z rows and z columns (z <= m) from among the
  last (n-m) columns, then the resulting submatrix is invertible. We will do this in several pieces*)
Section RowRedVandermonde.

(*Allows us to specify a submatrix by a list of rows and columns (we will need uniqueness and some additional
  length properties to use this*)
Definition submx_rows_cols {m n : nat} (m' n': nat) (A: 'M[F]_(m, n)) (rows: seq 'I_m) (cols: seq 'I_n)
  (xm: 'I_m) (xn : 'I_n) := mxsub (fun (x : 'I_m') => nth xm rows x) (fun x : 'I_n' => nth xn cols x) A.
(*Definition submx_rows_cols {m n} z (A: 'M[F]_(m, n)) (rows: list 'I_m) (cols: list 'I_n) (xm : 'I_m) (xn: 'I_n) :=
  mxsub (fun (x: 'I_z) => nth xm rows x) (fun (x: 'I_z) => nth xn cols x) A.*)
(*The default doesn't matter as long as our lists are long enough*)
Lemma submx_rows_cols_default: forall m n m' n' (A: 'M[F]_(m, n)) rows cols xm xn xm' xn',
  m' <= size rows ->
  n' <= size cols ->
  submx_rows_cols m' n' A rows cols xm xn = submx_rows_cols m' n' A rows cols xm' xn'.
Proof.
  move => m n m' n' A rows cols xm xn xm' xn' Hm' Hn'. rewrite -matrixP => x y. rewrite !mxE.
  f_equal; apply set_nth_default. 
  have Hx: x < m' by []. by apply (ltn_leq_trans Hx).
  have Hy: y < n' by []. by apply (ltn_leq_trans Hy).
Qed.

(*To prove the invertibility of this submatrix, we will need to expand this to cover more columns. First we need
  to get a list of the rows that are not included in [rows].*)

(*The complement of a nat list, up to bound n*)
Fixpoint nat_comp (n: nat) (l: list nat) : list nat :=
  match n with
  | O => nil
  | n.+1 => if n \in l then nat_comp n l else (n :: nat_comp n l) 
  end.

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

Lemma nat_comp_eq_mem: forall n (l1 l2 : seq nat),
  (l1 =i l2) ->
  nat_comp n l1 = nat_comp n l2.
Proof.
  move => n l1 l2 Hl12. elim : n => [//= | n IH /=]. by rewrite Hl12 IH.
Qed.

Lemma nat_comp_undup: forall n (l: seq nat),
  nat_comp n l = nat_comp n (undup l).
Proof.
  move => n l. symmetry. apply nat_comp_eq_mem. apply mem_undup.
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

Lemma uniq_ord_comp: forall n (l: seq 'I_n),
  uniq (ord_comp l).
Proof.
  move => n l. rewrite /ord_comp. apply pmap_sub_uniq. apply nat_comp_uniq.
Qed.

Lemma uniq_ord_comp_cat: forall n (l: seq 'I_n),
  uniq l ->
  uniq (l ++ ord_comp l).
Proof.
  move => n l. rewrite cat_uniq /=. move ->. rewrite uniq_ord_comp andbT /=. 
  apply /hasP. move => [x Hxin Hmem].
  have Hxin': x \in l by [].
  rewrite in_ord_comp in Hxin. by rewrite Hxin' in Hxin.
Qed.

(*Now, we need to know that if we take a list l of 'I_n's and take l ++ (ord_comp rows),
  this is a permutation of ord_enum m*)
Lemma ord_comp_app_perm: forall {n: nat} (l: seq 'I_n),
  uniq l ->
  perm_eq (l ++ (ord_comp l)) (ord_enum n).
Proof.
  move => n l Hun. apply uniq_perm.
  - by apply uniq_ord_comp_cat.
  - apply ord_enum_uniq.
  - move => x. rewrite mem_cat. rewrite mem_ord_enum.
    case Hx: (x \in ord_comp l). by rewrite orbT. rewrite orbF.
    rewrite in_ord_comp in Hx. move : Hx. by case : (x \in l).
Qed.

Lemma ord_comp_cat_size: forall n (l: seq 'I_n),
  uniq l ->
  size (l ++ ord_comp l) = n.
Proof.
  move => n l Hun. by rewrite (perm_size (ord_comp_app_perm Hun)) size_ord_enum.
Qed.

Lemma ord_comp_size_uniq: forall n (l: seq 'I_n),
  uniq l ->
  size (ord_comp l) = (n - size l)%N.
Proof.
  move => n l Hun.
  have Hsz: (size (ord_comp l) + size l)%N = n by rewrite addnC -size_cat ord_comp_cat_size.
  have<-: ((size (ord_comp l) + size l) - size l)%N = (n - size l)%N by rewrite Hsz.
  rewrite -subnBA. by rewrite subnn subn0. by rewrite leqnn.
Qed.


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

(*The first main piece:
  Proof idea: we will show that the [submx_rows_cols] we care about is invertible iff an expanded submatrix
  which includes additional rows and columns is invertible. This expanded submatrix adds (some of) the missing rows
  and the corresponding column. Because the underlying mx is row-reduced, for each column i that we add, there is
  a 1 at position i and 0 at all other places. Thus, we can "peel off" these lists by using the cofactor
  expansion for determinants, and our original submatrix is still included. We prove this general claim
  by induction on the list of additional columns. (the base case is essentially trivial)
  We need a lot of preconditions to make sure all of the pieces relate to each other.*)
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
  (submx_rows_cols z z (gaussian_elim (vandermonde m n l)) rows cols xm xn \in unitmx) = 
  (submx_rows_cols k k (gaussian_elim (vandermonde m n l)) all_rows (added_cols ++ cols) xm xn \in unitmx).
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
    rewrite ( expand_det_col (submx_rows_cols k k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn)
      (Ordinal Hk)). 
    (*now, need to show that all but 1 entry in the sum is 0*)
    have Hhm: h < m. apply Hinadd. by rewrite in_cons eq_refl.
     have Hvan: (colsub (widen_ord Hmn) (vandermonde m n l) \in unitmx). {
        have->: colsub (widen_ord Hmn) (vandermonde m n l) = vandermonde m m (take m l). {
          rewrite -matrixP => x y. rewrite !mxE. by rewrite nth_take. }
        apply vandermonde_unitmx. by apply take_uniq. rewrite size_takel //. by subst. }
    have Hinner: forall i, submx_rows_cols k k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn i (Ordinal Hk) = 
      if (nat_of_ord (nth xm all_rows i) == nat_of_ord h) then 1 else 0. {
      move => i. rewrite mxE /=. 
      by apply (gaussian_elim_identity_val Hvan). }
    (*work with the summation - can we do this nicely at all?*)
    have->: (\sum_i
      submx_rows_cols k k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn i (Ordinal Hk) *
      cofactor (submx_rows_cols k k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn) i
        (Ordinal Hk)) =
    (\sum_i
      if nat_of_ord (nth xm all_rows (nat_of_ord i)) == (nat_of_ord h) then 
      submx_rows_cols k k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn i (Ordinal Hk) *
      cofactor (submx_rows_cols k k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn) i
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
            (submx_rows_cols k k (gaussian_elim (vandermonde m n l)) all_rows (h :: t ++ cols) xm xn))) =
      (submx_rows_cols k.-1 k.-1 (gaussian_elim (vandermonde m n l)) (rem_nth all_rows j) (t ++ cols) xm xn). {
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

(*The only remaining piece is that we required that the [rows] list is a subseq of the [all_rows] (we needed this
  for the base case). We will want our [all_rows] to be [ord_enum m], so this is only true if [rows] was sorted.
  So we need to prove that the invertibility of a submatrix defined by a list of rows is preserved
  if we permute the row list. This follows from row equivalence, but requires a good amount of work to show*)

Lemma perm_eq_in: forall {A: eqType} (l1 l2 : seq A) x,
  perm_eq (x :: l1) l2 ->
  exists s1 s2, l2 = s1 ++ x :: s2 /\ perm_eq l1 (s1 ++ s2) .
Proof.
  move => A l1 l2 x. rewrite perm_sym => /perm_consP [i [u [Hhu Hperm]]].
  rewrite /rot in Hhu. 
  have /orP[Hnin | Hnout] : (i < size l2) || (size l2 <= i) by apply ltn_leq_total.
  - move: Hhu. rewrite (drop_nth x) //=; move => [Hhd Htl].
    exists (take i l2). exists (drop (i.+1) l2). split.
    by rewrite -Hhd -(drop_nth) // cat_take_drop. subst. eapply perm_trans.
    rewrite perm_sym. apply Hperm. by rewrite perm_catC perm_refl.
  - move: Hhu. rewrite drop_oversize //= take_oversize //=.
    move->. exists nil. exists u. rewrite /=. split. by []. by rewrite perm_sym.
Qed. 

(*This is a stronger claim than we originally needed - for the IH, we need to add the extra [p] list. This lemma
  is quite annoying to prove because of all the appends and casework*)
Lemma permute_rows_row_equiv: forall {m n} (A: 'M[F]_(m, n)) m' n' (r1 r2 p: list 'I_m) (cols: list 'I_n) (xm: 'I_m) (xn: 'I_n),
  perm_eq r1 r2 ->
  m' = size (p ++ r1) ->
  m' = size(p ++ r2) ->
  row_equivalent (submx_rows_cols m' n' A (p ++ r1) cols xm xn) (submx_rows_cols m' n' A (p ++ r2) cols xm xn).
Proof.
  move => m n A m' n' r1 r2 p cols xm xn. move: r2 p. elim: r1 => [r2 p /= | /= h t IH r2 p Hperm Hsz1 Hsz2].
  - rewrite perm_sym. move => /perm_nilP Hperm. subst. constructor.
  - apply perm_eq_in in Hperm. move: Hperm => [s1 [s2 [Hr2 Hperm]]].
    have->:p ++ h :: t = (p ++ h :: nil) ++ t by rewrite -catA.
    (*now, depends on if s1 = nil (in which case this is easy, or not, in which case we need to swap h and h1)*)
    move: Hr2 Hperm; case : s1 =>[//= Hr1 Hperm | //= h1 t1 Hr1 Hperm].
    + subst. have->:p ++ h :: s2 = (p ++ h :: nil) ++ s2 by rewrite -catA.
      apply (IH  s2 (p ++ h :: nil)). by []. all: by rewrite -catA /=.
    + rewrite Hr1. apply (@row_equivalent_trans _ _ _ _ (submx_rows_cols m' n' A (p ++ h :: t1 ++ h1 :: s2) cols xm xn)).
      * have->:(p ++ h :: t1 ++ h1 :: s2) = (p ++ h :: nil) ++ (t1 ++ h1 :: s2) by rewrite -catA.
        apply IH. rewrite (perm_trans Hperm) //. by rewrite perm_sym perm_catC /= perm_cons perm_catC perm_refl.
        all:  rewrite -catA //=. subst. rewrite Hsz2 !size_cat /=.
        apply /eqP. by rewrite eqn_add2l !size_cat /=.
      * (*this is RE because this swap is actually a row swap*)
        have Hih1: (size p) < m'. subst. rewrite size_cat /= -ltn_subLR. by rewrite subnn ltn0Sn.
        by rewrite leqnn.
        have Hih: (size (p ++ h1 :: t1)) < m'. subst. rewrite Hsz2. rewrite !size_cat /= ltn_add2l
          -add1n -(add1n (size (t1 ++ h :: s2))) !leq_add2l size_cat -ltn_subLR.
          by rewrite subnn /= ltn0Sn. by rewrite leqnn.
        (*need these two so we can create Ordinals of type 'I_z*)
        have->: (submx_rows_cols m' n' A (p ++ h1 :: t1 ++ h :: s2) cols xm xn) = 
          xrow (Ordinal Hih) (Ordinal Hih1) (submx_rows_cols m' n' A (p ++ h :: t1 ++ h1 :: s2) cols xm xn). {
          rewrite -matrixP => x y. rewrite xrow_val !mxE.
          have Hih': nat_of_ord (Ordinal Hih) = size (p ++ h1 :: t1) by [].
          have Hih1': nat_of_ord (Ordinal Hih1) = size p by [].
          (*To reduce duplication*)
         have Hnth: forall v v' v'', 
            (nth xm (p ++ v :: t1 ++ v' :: s2) (size (p ++ v'' :: t1))) = v'. { 
           move => v' v'' v'''. rewrite nth_cat. have->:size (p ++ v''' :: t1) < size p = false.
           apply leq_gtF. rewrite size_cat /= -leq_subLR subnn leqW //.
           rewrite size_cat -addnBAC. 2: by rewrite leqnn.
           by rewrite subnn add0n /= nth_cat ltnn subnn /=. }
           case Hxh : (x == Ordinal Hih).
         - eq_subst Hxh. by rewrite Hih' Hih1' Hnth !nth_cat ltnn subnn.
         - case Hxh1: (x == Ordinal Hih1).
           + eq_subst Hxh1. by rewrite Hih1' Hih' Hnth !nth_cat ltnn subnn.
           + (*Now need to show these are equivalent at all other locations - this is annoying*)
             rewrite !nth_cat. case Hxp: (x < size p) =>[//|/=]. 
             have->: (h1 :: t1 ++ h :: s2) = (h1:: t1) ++ (h :: s2) by [].
             have->: (h :: t1 ++ h1 :: s2) = (h :: t1) ++ (h1 :: s2) by [].
             rewrite !nth_cat /=.
             have Hpos: 0 < x - size p. rewrite subn_gt0. move: Hxp. 
               rewrite ltnNge Bool.negb_false_iff leq_eqVlt => /orP[Hpxeq | Hpxlt].
               (*contradiction, x = Ordinal Hih*)
               have Hxord: x == Ordinal Hih1. eq_subst Hpxeq. apply /eqP. by apply ord_inj.
               by rewrite Hxord in Hxh1. by [].
            case Hxt1: (x - size p < (size t1).+1).
             * by rewrite -(prednK Hpos) /=.
             * have Hpos': 0 < (x - size p - (size t1).+1).  move: Hxt1.
               rewrite ltnNge Bool.negb_false_iff leq_eqVlt => /orP[Hpxeq | Hpxlt].
               have Hord: nat_of_ord x == (size p + (size t1).+1)%N.
               rewrite -(@subnK (size p) x). 2: apply ltnW; by rewrite -subn_gt0.
               apply (elimT eqP) in Hpxeq. rewrite Hpxeq addnABC. rewrite (addnC (size p - size p)%N).
               rewrite subnn addn0 subnK //. by rewrite leqNgt Hxp. by rewrite leqnn. by rewrite leqNgt Hxp.
               have Hxord: x == Ordinal Hih. apply /eqP. apply ord_inj. eq_subst Hord. rewrite Hord.
               rewrite Hih'. by rewrite size_cat /=.
               by rewrite Hxord in Hxh. 
               by rewrite subn_gt0. 
               by rewrite -(prednK Hpos') /=. }
        apply ero_row_equiv. constructor.
Qed.

(*The easy corollary of above. This is what we wanted*)
(*TODO: see if we can use this instead of proving the reverse rows stuff*)
Lemma perm_eq_row_equiv: forall {m n} (A: 'M[F]_(m, n)) m' n' (r1 r2: list 'I_m) (cols: list 'I_n) (xm: 'I_m) (xn: 'I_n),
  perm_eq r1 r2 ->
  m' = size r1 ->
  m' = size r2 ->
  row_equivalent (submx_rows_cols m' n' A r1 cols xm xn) (submx_rows_cols m' n' A r2 cols xm xn).
Proof.
  move => m n A m' n' r1 r2 cols xm xn Hperm Hsz1 Hsz2.
  rewrite -(cat0s r1) -(cat0s r2). by apply permute_rows_row_equiv.
Qed.

(*As a corollary (that we will need later), we show that if we flip the rows of an n x n matrix, this does not change
  invertibility*)
Definition flip_rows {m n} (A: 'M[F]_(m, n)) : 'M[F]_(m, n) :=
  \matrix_(i < m, j < n) A (rev_ord i) j.

Lemma submx_rows_cols_whole: forall m n (A: 'M[F]_(m, n)) (xm: 'I_m) (xn: 'I_n),
  A = submx_rows_cols m n A (ord_enum m) (ord_enum n) xm xn.
Proof.
  move => m n A xm xn. rewrite -matrixP => x y. by rewrite mxE !nth_ord_enum.
Qed.

(*We need the column result here*)
Lemma matrix_zero_cols: forall {n} (A B: 'M[F]_(n, 0)), A = B.
Proof.
  move => n A B. rewrite -matrixP /eqrel. move => x y. have: y < 0 by []. by rewrite ltn0.
Qed.

Lemma flip_rows_row_equiv: forall {m n} (A: 'M[F]_(m, n)),
  row_equivalent A (flip_rows A).
Proof.
  move => m n A. have: 0 <= m by []. rewrite leq_eqVlt => /orP[/eqP H0 | Hmpos].
  - subst. rewrite {1}(matrix_zero_rows A (flip_rows A)). constructor.
  - have: 0 <= n by []. rewrite leq_eqVlt => /orP[/eqP H0 | Hnpos].
    + subst. rewrite {1}(matrix_zero_cols A (flip_rows A)). constructor. 
    + rewrite {1}(submx_rows_cols_whole A (pred_ord Hmpos) (pred_ord Hnpos) ).
      have->: flip_rows A = submx_rows_cols m n A (rev (ord_enum m)) (ord_enum n) (pred_ord Hmpos) (pred_ord Hnpos). {
        rewrite -matrixP => x y. have Hsz: size (ord_enum m) = m by rewrite size_ord_enum.
        rewrite !mxE nth_rev // Hsz //=. have Hsub: m - x.+1 < m by apply rev_ord_proof. 
        have->: (m - x.+1)%nat = nat_of_ord (Ordinal Hsub) by []. rewrite !nth_ord_enum. f_equal.
        by apply ord_inj. }
      apply perm_eq_row_equiv.
      * by rewrite perm_sym perm_rev.
      * by rewrite size_ord_enum.
      * by rewrite size_rev size_ord_enum.
Qed.

Lemma flip_rows_unitmx: forall {n} (A: 'M[F]_n),
  A \in unitmx = (flip_rows A \in unitmx).
Proof.
  move => n A. apply (row_equivalent_unitmx_iff (flip_rows_row_equiv A)).
Qed.

(*The result we want - any submatrix of a RR Vandermonde mx made of z unique rows and
   z unique columns from the last (n - m) columns is invertible.
  To prove this, we use [added_rows_unitmx_iff] and add all missing rows and the corresponding
  columns. This gives us a submatrix that is actually just m columns of the RR Vandermonde mx, which
  we know is invertible from [vandermonde_gauss_cols_unitmx]*)
Lemma any_submx_unitmx: forall {m n} (Hmn: m <= n) (Hm: 0 < m) z (l: list F) (rows: list 'I_m) (cols: list 'I_n),
  uniq l ->
  size l = n ->
  uniq rows ->
  uniq cols ->
  size rows = size cols ->
  size rows = z ->
  (forall x, x \in cols -> m <= x) ->
  (submx_rows_cols z z (gaussian_elim (vandermonde m n l)) rows cols (Ordinal Hm) (widen_ord Hmn (Ordinal Hm)) \in unitmx).
Proof.
  move => m n Hmn Hm z l rows cols Hunl Hszl Hunr Hunc Hszrc Hz Hinc.
  (*Need this in multiple places*)
  have Hunc':  uniq ([seq widen_ord Hmn i | i <- ord_comp rows] ++ cols). {
    rewrite cat_uniq Hunc map_inj_uniq //=. rewrite uniq_ord_comp andbT /=.
    apply /hasP. move => [x Hxin Hmem]. 
    have Hxin': x \in [seq widen_ord Hmn i | i <- ord_comp rows] by [].
    apply (elimT mapP) in Hxin'. move: Hxin' => [y Hyin Hxy]. subst.
    apply Hinc in Hxin. have Hym: y < m by [].
    have Hy: nat_of_ord (widen_ord Hmn y) = nat_of_ord y by []. rewrite Hy in Hxin.
    rewrite ltnNge in Hym. by rewrite Hxin in Hym.
    move => x y Hxy. eapply widen_ord_inj. apply Hxy. }
  rewrite (@added_rows_unitmx_iff _ _ _ _ _ _ _ _ (map (widen_ord Hmn) (ord_comp rows)) (rows ++ (ord_comp rows)) _ m) //=.
  - (*We need to 1. replace rows by (ord_enum m), which is a permutations, then 2. prove equivalent to
      a colmx that is therefore invertible*)
    rewrite (@row_equivalent_unitmx_iff _ _ _ (submx_rows_cols m m (gaussian_elim (vandermonde m n l)) (ord_enum m)
    ([seq widen_ord Hmn i | i <- ord_comp rows] ++ cols) (Ordinal Hm) (widen_ord Hmn (Ordinal Hm)))).
    2: { apply perm_eq_row_equiv. by apply ord_comp_app_perm. by rewrite ord_comp_cat_size. by rewrite size_ord_enum. }
    have->: submx_rows_cols m m (gaussian_elim (vandermonde m n l)) (ord_enum m)
      ([seq widen_ord Hmn i | i <- ord_comp rows] ++ cols) (Ordinal Hm) (widen_ord Hmn (Ordinal Hm)) =
      colsub (fun (x: 'I_m) => (nth (widen_ord Hmn (Ordinal Hm)) 
        ([seq widen_ord Hmn i | i <- ord_comp rows] ++ cols) x))
         (gaussian_elim (vandermonde m n l)). {
      rewrite -matrixP => x y. by rewrite !mxE nth_ord_enum. }
    (*Now we can simply WTS that these m columns of the vandermonde mx are invertible, which we proved before*)
    apply vandermonde_gauss_cols_unitmx; try by [].
    rewrite size_cat size_map -Hszrc addnC -size_cat. by rewrite ord_comp_cat_size.
  - by subst.
  - move => x Hinx. apply (elimT mapP) in Hinx. move: Hinx => [y Hyin Hxy]. subst.
    have->: nat_of_ord (widen_ord Hmn y) = y by []. by [].
  - rewrite size_cat size_map -Hszrc addnC -size_cat. by rewrite ord_comp_cat_size.
  - by apply uniq_ord_comp_cat.
  - by rewrite prefix_subseq.
  - by rewrite !size_cat size_map Hszrc addnC.
  - move => x. rewrite mem_map. rewrite mem_cat !in_ord_comp.
    by case Hx: (x \in rows). move => i j Hw. apply (widen_ord_inj Hw).
Qed.

End RowRedVandermonde.

End GenericVandermonde.

(** Results about the Weight Matrix*)


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
  have Hx: (r - (r.+1 - x.+1))%nat = x by rewrite subSS subKn // -ltnS. 
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
  rewrite -unitmx_tr flip_rows_unitmx vandermonde_powers_add_row_list =>[|//].
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

End PrimitiveVandermonde.