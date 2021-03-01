From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Require Import Gaussian.
Require Import CommonSSR.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section LinIndep.

Variable F : fieldType.

Local Open Scope ring_scope.

(*We want to define the notion that the rows of a matrix are linearly independent*)
(*cannot make bool unless field is finite, which is true in this case*)
Definition rows_lin_indep {m n} (A: 'M[F]_(m, n)) : Prop :=
  forall (c: 'I_m -> F),
  (forall (j : 'I_n), (\sum_(i < m) (c(i) * A i j)) = 0) ->
  forall (x: 'I_m), c x = 0.

(*For some reason, this doesn't exist in library*)
Lemma sum_change_cond: forall {I: eqType} (r: seq I) p1 p2 (f: I -> F),
  (forall x, x \in r -> p1 x = p2 x) ->
  \sum_(i <- r | p1 i) f i = \sum_(i <- r | p2 i) f i.
Proof.
  move => I r p1 p2 f Hp12. rewrite big_seq_cond. rewrite (big_seq_cond (fun i => p2 i)).
  apply eq_big. 2: by []. move => x. case Hin: (x \in r) => [|//].
  by rewrite Hp12.
Qed. 

(*We can add up a summation by picking one element, adding everything else, then adding this element separately*)
Lemma sum_remove_one: forall {n} (p : pred 'I_n) (f : 'I_n -> F) (x: 'I_n),
  p x ->
  \sum_(i < n | p i) (f i) = \sum_(i < n | (p i && (i != x))) (f i) + (f x).
Proof.
  move => n p f x Hpx. rewrite (big_nth x). rewrite !(big_nth x) /= /index_enum /= ordinal_enum_size.
  have Hxn: x <= n by apply ltnW.
  rewrite (@big_cat_nat _ _ _ x) => [/=|//|//]. 
  rewrite (@big_cat_nat _ _ _ x 0 n) => [/= | // | //].
  rewrite -GRing.addrA. f_equal.
  - apply sum_change_cond. move => i Hin.
    have Hix: i < x by move: Hin; rewrite mem_iota add0n subn0.
    have Hinlt: i < n by apply (ltn_trans Hix).
    have ->: (nth x (Finite.enum (ordinal_finType n)) i =
           (nth x (Finite.enum (ordinal_finType n)) (Ordinal Hinlt))) by [].
    rewrite ordinal_enum. have ->: Ordinal Hinlt != x. 
    rewrite ltn_neqAle in Hix. by move : Hix => /andP[Hixneq H{H}].
    by rewrite andbT.
  - rewrite big_ltn_cond =>[|//].
    rewrite (@big_ltn_cond _ _ _ x) => [|//].
    rewrite !ordinal_enum Hpx eq_refl /= GRing.addrC. f_equal.
    apply sum_change_cond. move => i Hiin.
    have Hin: i < n. move: Hiin. rewrite mem_iota subnKC. by move => /andP[H1 H2]. by [].
    have ->: nth x (Finite.enum (ordinal_finType n)) i = nth x (Finite.enum (ordinal_finType n)) (Ordinal Hin) by [].
    rewrite ordinal_enum. have ->: Ordinal Hin != x. have: i != x. move : Hiin; rewrite mem_iota ltn_neqAle
    => /andP[/andP[Hnneq H{H}] H{H}]. by rewrite eq_sym. by []. by rewrite andbT.
Qed. 

 
(*Row operations preserve linear independence*)

(*Scalar multiplication preserves linear independence*)
(*Idea: multiple c_r by k to preserve sum, does not change 0*)
Lemma sc_mul_lin_indep: forall {m n} (A: 'M[F]_(m, n)) k r,
  k != 0 ->
  rows_lin_indep A <-> rows_lin_indep (sc_mul A k r).
Proof.
  move => m n A k r Hk. rewrite /rows_lin_indep /sc_mul !/mxE.
  have Hinner: (forall (j : 'I_n) (c : 'I_m -> F),
  \sum_(i < m) c i * (\matrix_(i0, j0) (if i0 == r then k * A i0 j0 else A i0 j0)) i j =
  \sum_(i < m) c i *  (if i == r then k * A i j else A i j)). {
  move => j c. apply congr_big => [//|//|]. move => i H{H}; by rewrite mxE. }
  have Hinner_simpl: (forall (j : 'I_n) (c : 'I_m -> F),
     \sum_(i < m) c i * (if i == r then k * A i j else A i j) =
     (\sum_(i < m | i != r) c i * A i j) + (c r) * (k * A r j)). {
  move => j c. rewrite (@sum_remove_one _ _ _ r) => [|//].
  rewrite eq_refl. f_equal. 
  apply eq_big. by []. move => i /andP[H{H} Hir]. by have->: i == r = false by move: Hir; case: (i == r). }
  split.
  - move => Hlin c Hprod x.
    move : Hlin => /(_ (fun x => if x == r then c x * k else c x)) Hlin.
    have Hcond: (forall j : 'I_n, \sum_(i < m) (if i == r then c i * k else c i) * A i j = 0). {
    move => j. rewrite -{2}(Hprod j) Hinner Hinner_simpl.
    rewrite (@sum_remove_one _ _ _ r) =>[|//]. rewrite eq_refl GRing.mulrA. f_equal. 
    apply eq_big => [//|//]. move => i /andP[H{H} Hir]. by have ->: (i==r = false) by move: Hir; by case (i==r). }
    move : Hlin => /(_ Hcond x).
    case Hxr: (x == r).
    + move => Hp. have: (c x * k == 0) by apply (introT eqP).
      rewrite GRing.mulf_eq0. have->: (k == 0 = false) by move : Hk; by case: (k==0).
      by rewrite orbF => /eqP Hc.
    + by [].
  - move => Hlin c Hprod x.
    move : Hlin => /(_ (fun x => if x == r then c x * k^-1 else c x)) Hlin.
    have Hcond: (forall j : 'I_n, \sum_(i < m)  (if i == r then c i / k else c i) *
           (\matrix_(i0, j0) (if i0 == r then k * A i0 j0 else A i0 j0)) i j = 0). {
    move => j. rewrite -{2}(Hprod j) Hinner Hinner_simpl. rewrite eq_refl.
    rewrite (@sum_remove_one _ (fun _ => true) _ r) =>[|//]. rewrite -!GRing.mulrA.  rewrite (GRing.mulrA (k^-1))
    GRing.mulVf =>[|//]. rewrite GRing.mul1r. f_equal.
    apply eq_big => [//|//]. move => i Hir. by have ->: (i==r = false) by move: Hir; by case (i==r). }
    move : Hlin => /(_ Hcond x).
    case Hxr: (x == r).
    + move => Hp. have: (c x / k == 0) by apply (introT eqP).
      rewrite GRing.mulf_eq0 GRing.invr_eq0. have->: (k == 0 = false) by move : Hk; by case: (k==0).
      by rewrite orbF => /eqP Hc.
    + by [].
Qed.

(*Swapping rows preserves linear independence*)
(*Idea: switch c_r1 and c_r2, preserves sum but does not change 0*)
Lemma xrow_lin_indep: forall {m n} (A: 'M[F]_(m, n)) r1 r2,
  rows_lin_indep A <-> rows_lin_indep (xrow r1 r2 A).
Proof.
  move => m n A r1 r2. rewrite /rows_lin_indep.
  have Hinner: (forall (c: 'I_m -> F) (j: 'I_n),
    \sum_(i < m) (c i * xrow r1 r2 A i j) =
    \sum_(i < m) (fun (j: 'I_m) => if j == r1 then c r2 else if j == r2 then c r1 else c j) i * A i j). {
  move => c j. rewrite (@sum_remove_one _ _ _ r1) => [|//]. rewrite xrow_val eq_refl.
  rewrite (@sum_remove_one _ (fun _ => true) _ r1) =>[|//]. rewrite eq_refl.
  case Hr12: (r1 == r2).
  - eq_subst Hr12. f_equal. apply eq_big. by []. move => i /andP[H{H} Hir2].
    rewrite xrow_val. move: Hir2; by case: (i == r2).
  - have Hr12': (r2 != r1) by rewrite eq_sym Hr12. rewrite (@sum_remove_one _ _ _ r2) =>[|//].
    rewrite (@sum_remove_one _ (fun x => true && (x != r1)) _ r2) => [|//]. rewrite !eq_refl !xrow_val.
    have ->: (r2 == r1 = false) by rewrite eq_sym in Hr12. rewrite eq_refl.
    rewrite -!GRing.addrA (GRing.addrC (c r2 * A r1 j)). f_equal.
    apply eq_big. by []. move => i /andP[/andP[H{H} Hir1] Hir2].
    move: Hir1 Hir2. rewrite xrow_val. by case (i == r1); case: (i == r2). }
  split.
  - move => Hlin c. move: Hlin => /(_ (fun (j: 'I_m) => if j == r1 then c r2 else if j == r2 then c r1 else c j)) 
    Hlin Hprod x. 
    have Hcond: (forall j : 'I_n,
        \sum_(i < m) (if i == r1 then c r2 else if i == r2 then c r1 else c i) * A i j = 0). move => j.
    by rewrite -Hinner Hprod. move: Hlin => /(_ Hcond).
    case Hxr1: (x == r1).
    + eq_subst Hxr1. move => /(_ r2). case Hr12: (r2 == r1). by eq_subst Hr12. by rewrite eq_refl.
    + case Hxr2 : (x == r2). eq_subst Hxr2. move => /(_ r1). by rewrite eq_refl.
      move /(_ x). by rewrite Hxr1 Hxr2.
  - move => Hlin c. move: Hlin => /(_ (fun (j: 'I_m) => if j == r1 then c r2 else if j == r2 then c r1 else c j)) 
    Hlin Hprod x. 
    have Hcond: (forall j : 'I_n,
        \sum_(i < m) (if i == r1 then c r2 else if i == r2 then c r1 else c i) * xrow r1 r2 A i j = 0). { move => j.
    rewrite Hinner -{2}(Hprod j). apply eq_big. by []. move => i H{H}. case Hir1: (i == r1).
    - eq_subst Hir1. rewrite eq_refl. case Hr21: (r2 == r1) =>[|//]. by eq_subst Hr21.
    - case Hir2: (i == r2). eq_subst Hir2. by rewrite eq_refl. by []. }
    move: Hlin => /(_ Hcond).
    case Hxr1: (x == r1).
    + eq_subst Hxr1. move => /(_ r2). case Hr12: (r2 == r1). by eq_subst Hr12. by rewrite eq_refl.
    + case Hxr2 : (x == r2). eq_subst Hxr2. move => /(_ r1). by rewrite eq_refl.
      move /(_ x). by rewrite Hxr1 Hxr2.
Qed.

(*Adding multiple of row row to another preserves linear independence*)
Lemma add_mul_lin_indep: forall {m n} (A: 'M[F]_(m, n)) k r1 r2,
  r1 != r2 ->
  rows_lin_indep A <-> rows_lin_indep (add_mul A k r1 r2).
Proof.
  move =>m n A k r1 r2 Hr12. rewrite /rows_lin_indep.
  have Hinner: (forall (c: 'I_m -> F) (j: 'I_n),
    \sum_(i < m) (fun (j: 'I_m) => if j == r1 then c r1 - k * c r2 else c j)  i * add_mul A k r1 r2 i j =
    \sum_(i < m) c i * A i j). {
  move => c j. rewrite (@sum_remove_one _ _ _ r1) => [|//]. rewrite eq_refl /add_mul mxE.
  have Hr12f: r1 == r2 = false by move: Hr12; case (r1 == r2). rewrite Hr12f.
  rewrite (@sum_remove_one _ (fun _ => true) _ r1) =>[|//].
  rewrite (@sum_remove_one _ _ _ r2). 2: by rewrite eq_sym. rewrite eq_sym Hr12f mxE eq_refl -GRing.addrA.
  have ->: c r2 * (A r2 j + k * A r1 j) + (c r1 - k * c r2) * A r1 j = c r2 * A r2 j + c r1 * A r1 j. {
  rewrite GRing.mulrDl GRing.mulrDr -GRing.addrA. f_equal.
  by rewrite GRing.addrC (GRing.mulrC k) GRing.mulNr (GRing.mulrA _ k) -GRing.addrA GRing.addNr GRing.addr0. }
  rewrite (@sum_remove_one _ (fun i => true && (i != r1)) _ r2). 2: by rewrite eq_sym.
  rewrite -GRing.addrA. f_equal. apply eq_big =>[//|].
  move => i /andP[/andP[H{H} Hir1] Hir2]. rewrite mxE.
  have->: (i == r1 = false) by move: Hir1; case (i == r1).
  by have->: (i == r2 = false) by move: Hir2; case (i == r2). }
  split.
  - move => Hlin c. move: Hlin => /(_ (fun (j: 'I_m) => if j == r1 then c r1 + k * c r2 else c j)) 
    Hlin Hprod x. 
    have Hcond: (forall j : 'I_n, \sum_(i < m) (if i == r1 then c r1 + k * c r2 else c i) * A i j = 0). {
      move => j. rewrite -Hinner eq_refl -{2}(Hprod j). apply eq_big =>[//|]. move => i H{H}.
      case Hir1: (i == r1). rewrite /add_mul mxE. have Hr12f: r1 == r2 = false by move: Hr12; case (r1 == r2).
      rewrite eq_sym Hr12f. have ->: (i == r2 = false). case Hir2: (i == r2). eq_subst Hir1. eq_subst Hir2.
      by rewrite eq_refl in Hr12f. by []. rewrite -GRing.addrA (GRing.addrN (k * c r2)) GRing.addr0. by eq_subst Hir1.
      by rewrite /add_mul mxE. }
    move : Hlin => /(_ Hcond).
    case Hcr2: (c r2 == 0).
    + eq_subst Hcr2. move => /(_ x). rewrite Hcr2 GRing.mulr0 GRing.addr0. by case Hxr1 : (x == r1); eq_subst Hxr1.
    + move /(_ r2). have ->: (r2 == r1 = false) by move: Hr12; rewrite eq_sym; by case (r2 == r1).
      move => Hcr2'. rewrite Hcr2' in Hcr2. by rewrite eq_refl in Hcr2.
  - move => Hlin c. move: Hlin => /(_ (fun (j: 'I_m) => if j == r1 then c r1 - k * c r2 else c j)) 
    Hlin Hprod x.
    have Hcond:  (forall j : 'I_n,
        \sum_(i < m) (if i == r1 then c r1 - k * c r2 else c i) * add_mul A k r1 r2 i j = 0).
    move => j. by rewrite Hinner Hprod. move : Hlin => /(_ Hcond).
    case Hcr2: (c r2 == 0).
    + eq_subst Hcr2. move => /(_ x). rewrite Hcr2 GRing.mulr0 GRing.subr0. by case Hxr1 : (x == r1); eq_subst Hxr1.
    + move /(_ r2). have ->: (r2 == r1 = false) by move: Hr12; rewrite eq_sym; by case (r2 == r1).
      move => Hcr2'. rewrite Hcr2' in Hcr2. by rewrite eq_refl in Hcr2.
Qed.

(*We can put these together in the following results*)
Lemma ero_lin_indep: forall {m n} (A B : 'M[F]_(m, n)),
  (ero A B) ->
  rows_lin_indep A <-> rows_lin_indep B.
Proof.
  move => m n A B Hero. elim: Hero  => m' n' r1.
  - move => r2 A'. apply xrow_lin_indep.
  - move => k A' Hk. by apply sc_mul_lin_indep.
  - move => r2 k A' Hr12. by apply add_mul_lin_indep.
Qed.

Lemma row_equivalent_lin_indep: forall {m n} (A B : 'M[F]_(m, n)),
  row_equivalent A B ->
  rows_lin_indep A <-> rows_lin_indep B.
Proof.
  move => m n A B Hre. elim: Hre => m' n' A'.
  - by [].
  - move => B' C' Hero Hre IH. rewrite -IH. by apply ero_lin_indep.
Qed.

(*The crucial test (for our purposes). The rows of a matrix are linearly independent iff
  the rows of the row reduced matrix are linearly independent. For an n x n matrix, linear independence
  of a row reduced matrix occurs exactly when the matrix is the identity*)
Lemma gauss_elim_lin_indep: forall {m n} (A: 'M[F]_(m, n)),
  rows_lin_indep A <-> rows_lin_indep (gaussian_elim A).
Proof.
  move => m n A. apply row_equivalent_lin_indep. apply gaussian_elim_row_equiv.
Qed.

(*A matrix with a row of zeroes does not have linearly independent rows*)
Lemma row_zero_not_lin_indep: forall {m n} (A : 'M[F]_(m, n)) (r: 'I_m),
  (forall (c: 'I_n), A r c = 0) ->
  ~rows_lin_indep A.
Proof.
  move => m n A r Hzero. rewrite /rows_lin_indep => Hlin. move : Hlin => /(_ (fun x => if x == r then 1 else 0)).
  have Hcond: (forall j : 'I_n, \sum_(i < m) (if i == r then 1 else 0) * A i j = 0). {
   move => j. 
    have->: \sum_(i < m) (if i == r then 1 else 0) * A i j = \sum_(i < m) (if r == i then A i j else 0).
    apply eq_big =>[//|]. move => i H{H}. rewrite eq_sym. case : (r == i).
    by rewrite GRing.mul1r. by rewrite GRing.mul0r.
  rewrite sum_if. apply Hzero. }
  move => /(_ Hcond r). rewrite eq_refl. move => Honez. have: (GRing.one F) != 0 by rewrite GRing.oner_neq0.
  by rewrite Honez eq_refl.
Qed.

(*The identity matrix does have linearly independent rows*)
Lemma identity_lin_indep: forall n,
  @rows_lin_indep n n (1%:M).
Proof.
  move => n. rewrite /rows_lin_indep => c Hsum x.
  move : Hsum => /(_ x).
  have->: \sum_(i < n) c i * 1%:M i x = c x. {
  have->: \sum_(i < n) c i * 1%:M i x = \sum_(i < n) (if x == i then c i else 0).
  apply eq_big => [//|i H{H}]. rewrite id_A eq_sym. 
  case : (x == i). by rewrite GRing.mulr1. by rewrite GRing.mulr0.
  apply sum_if. } by [].
Qed.

(*Results about row echelon form.*)
(*These are pretty simple applications of results proved in Gaussian.v already. We can't directly use
  results from gaussian because we want specific results for n x n matrices, including those
  that are not necessarily invertible. TODO: maybe generalize to submatrices in Gaussian and combine*)

(*For an n x n matrix in row echelon form, it is either a diagonal matrix with all nonzero entries along the
  diagonal or it has a row of zeroes*)
Lemma row_echelon_diag_or_zeroes: forall {n} (A: 'M[F]_n),
  row_echelon A ->
  (forall (x y: 'I_n), (A x y == 0) = (x != y)) \/ (exists (r: 'I_n), forall (c: 'I_n), A r c = 0).
Proof.
  move => n A [[b [Hb Hzeroes]] [Hinc Hcols]].
  rewrite leq_eqVlt in Hb. move : Hb => /orP[/eqP Hb | Hbn].
  - subst. have Hinv: gauss_invar A n n. {
    rewrite /gauss_invar. repeat(split).
    + move => r' Hrn'. case Hlc: (lead_coef A r') =>[col |].
      * by exists col. 
      * have Hnr': (n <= r'). rewrite -Hzeroes. by apply (introT eqP).
        rewrite ltnNge in Hrn'. by rewrite Hnr' in Hrn'.
    + move => r1 r2 c1 c2 Hr12 Hr2n. by apply Hinc.
    + move => r' c' Hcn'. by apply Hcols.
    + move => r' c' Hnr'. have Hlt: r' < n by []. rewrite ltnNge in Hlt. by rewrite Hnr' in Hlt. }
    left. move => x y. have Hxn: (x < n) by []. have Hyn: (y < n) by [].
    apply (gauss_invar_square_id (leqnn n) (leqnn n) Hinv Hxn Hyn).
  - right. exists (Ordinal Hbn). rewrite -lead_coef_none_iff. apply (elimT eqP). by rewrite Hzeroes.
Qed.

(*Therefore, an n x n matrix in reduced row echelon form is either the identity or has a row of zeroes*)
Lemma red_row_echelon_id_or_zeroes: forall {n} (A: 'M[F]_n),
  red_row_echelon A ->
  (A = (1%:M)) \/ (exists (r: 'I_n), forall (c: 'I_n), A r c = 0).
Proof.
  move => n A [Hre Hlc].
  apply row_echelon_diag_or_zeroes in Hre. case: Hre => [Hdiag | Hzeroes].
  - left. rewrite -matrixP /eqrel => x y; rewrite id_A.
    have Hlcs: forall (r: 'I_n), lead_coef A r = Some r. { move => r. rewrite lead_coef_some_iff.
    split. by rewrite Hdiag eq_refl. move => x' Hxr'. apply (elimT eqP). rewrite Hdiag.
    move: Hxr'. rewrite ltn_neqAle => /andP [Hxr H{H}]. by rewrite eq_sym. }
    case Hxy : (x == y).
    + eq_subst Hxy. apply Hlc. apply Hlcs.
    + apply (elimT eqP). by rewrite Hdiag Hxy.
  - by right.
Qed.

(** Invertible Matrices *)

(*We give 2 necessary and sufficient conditions for invertibility:
  that A is row equivalent to the identity and that A has linearly independent rows*)

Lemma unitmx_iff_gauss_id: forall {n} (A: 'M[F]_n),
  A \in unitmx <-> gaussian_elim A = 1%:M.
Proof.
  move => n A. split.
  - move => Hinv.
    have Hred: red_row_echelon (gaussian_elim A) by apply gaussian_elim_rref.
    apply red_row_echelon_id_or_zeroes in Hred. case: Hred => [// | [r Hzero]].
    have Hginv: (gaussian_elim A) \in unitmx by rewrite -(row_equivalent_unitmx_iff (gaussian_elim_row_equiv A)).
    apply row_zero_not_unitmx in Hzero. by rewrite Hginv in Hzero.
  - rewrite (row_equivalent_unitmx_iff (gaussian_elim_row_equiv A)). move->. apply unitmx1.
Qed. 

Lemma unitmx_iff_lin_indep_rows: forall {n} (A: 'M[F]_n),
  A \in unitmx <-> rows_lin_indep A.
Proof.
  move => n A. rewrite gauss_elim_lin_indep unitmx_iff_gauss_id. split.
  - move ->. apply identity_lin_indep.
  - move => Hre. have Hred: red_row_echelon (gaussian_elim A) by apply gaussian_elim_rref.
    apply red_row_echelon_id_or_zeroes in Hred. case: Hred => [// | [r Hzero]].
    by apply row_zero_not_lin_indep in Hzero.
Qed. 


(** Flipping Rows*)
(*A similar result: If we flip all the rows of a matrix, the resulting matrix is invertible iff A is*)

(*Create ordinal for m - i if i : 'I_m*)
Lemma ord_sub_bound_lt {m} (i: 'I_m) : m - i - 1 < m.
Proof.
  rewrite -subnDA ltn_subLR. rewrite addnC addnA addn1.
  have Hmi: m <= m + i by rewrite -{1}(addn0 m) leq_add2l.
  by apply (leq_ltn_trans Hmi). by rewrite addn1.
Qed.

(*The ordinal (m - i -1) for i : 'I_m*)
Definition rev_ord {m} (i: 'I_m) : 'I_m := Ordinal (ord_sub_bound_lt i).

Lemma rev_ordK : forall m, involutive (@rev_ord m).
Proof.
  move => m x. rewrite /rev_ord /=.
  have: (m - (m - x - 1) - 1 == x)%N. rewrite -(subnDA x m 1%N). rewrite subKn. by rewrite addn1 subn1 -pred_Sn.
  by rewrite addn1. move => /eqP Hx. 
  have: (nat_of_ord(Ordinal (ord_sub_bound_lt (Ordinal (ord_sub_bound_lt x)))) == x) by rewrite -{3}Hx.
  move => /eqP Hord. by apply ord_inj.
Qed. 


(*The lemma we need (which ensures that we will not repeat rows when swapping*)
Lemma rev_ord_one_small: forall {m} (i: 'I_m), 
  (i < m %/ 2) ->  ~~(rev_ord i < m %/ 2).
Proof.
  move => m i Hi. have->: nat_of_ord (rev_ord i) = (m - i - 1)%N by []. 
  have Hi1: (i + 1 < m %/2 + 1) by rewrite ltn_add2r.
  have: (i + 1 <= m) by rewrite addn1. rewrite leq_eqVlt => /orP[/eqP Himeq | Himlt].
  + move: Hi1. by rewrite Himeq divn2 div_lt_bound -{1}Himeq addn1.
  + have Him: (m - (m %/ 2 + 1) < m - (i + 1)) by rewrite ltn_sub2l.
    rewrite !subnDA in Him.
    have Hlb: (m %/2 -1 <= m - m %/ 2 - 1). apply leq_sub2r. by rewrite divn2 sub_half_lower.
    case Hcon: (m - i - 1 < m %/ 2) => [|//].
    have Hlb': (m %/ 2 - 1 < m - i - 1) by apply (leq_ltn_trans Hlb).
    (*Need to know that m %/2 > 0*)
    have Hmdiv0: 0 < m %/ 2. rewrite divn2. apply div_2_pos. 
    have H1i: 1 <= i + 1 by rewrite -{1}(add0n 1%N) leq_add2r. apply (leq_ltn_trans H1i Himlt).
    (*finally, we can get the contradiction*)
    have: m %/ 2 <= m - i - 1. move: Hlb'. by rewrite ltn_subLR.
    by rewrite leqNgt Hcon.
Qed.

(*Every row will be accounted for*)
Lemma rev_ord_bound_total: forall {m} (i: 'I_m),
  (i < m %/ 2) || (rev_ord i < m %/ 2) || ((nat_of_ord i == m %/2) && (nat_of_ord (rev_ord i) == m %/2)).
Proof.
  move => m i.
  have->: nat_of_ord (rev_ord i) = (m - i - 1)%N by [].
  case Hi : (i < m %/ 2) => [//|/=].
  case Hrev: (m - i - 1 < m %/ 2) => [//|/=].
  have {}Hi: (m %/2 <= i) by rewrite leqNgt Hi.
  have {}Hrev: (m %/2 <= m - i - 1) by rewrite leqNgt Hrev.
  have: (m %/ 2 == (m - i - 1)%N). { rewrite -leq_both_eq Hrev /=.
  rewrite -(leq_add2r 1%N) in Hi. 
  have Hup: (m - (i + 1) <= m - (m %/ 2 + 1)) by rewrite leq_sub2l.
  rewrite !subnDA in Hup.
  have: m - m %/ 2 - 1 <= m %/2 + 1 - 1. apply leq_sub2r. by rewrite !divn2 sub_half_upper.
  rewrite addn1 (subn1 ((m %/ 2).+1)) -pred_Sn => Hm. by apply (leq_trans Hup). }
  rewrite eq_sym; move ->; rewrite andbT. 
  rewrite -leq_both_eq Hi andbT.
  move: Hrev. rewrite -subnDA. rewrite leq_subRL. 2: by rewrite addn1.
  rewrite addnC. rewrite -leq_psubRL. 2: by rewrite addn1. 
  move => Him. have Him1: i + 1 <= m %/2 + 1. rewrite !divn2. rewrite divn2 in Him.
  apply (leq_trans Him (sub_half_upper _)). by rewrite leq_add2r in Him1.
Qed.

(* The matrix we want to work with*)
Definition flip_rows {m n} (A: 'M[F]_(m, n)) : 'M[F]_(m, n) :=
  \matrix_(i < m, j < n) A (rev_ord i) j.

(*Need to show row equivalence*)
Definition flip_rows_iter_aux {m n} (A: 'M[F]_(m, n)) (l: list 'I_m) : 'M[F]_(m, n) :=
  foldr (fun r (acc : 'M[F]_(m, n)) => xrow r (rev_ord r) acc) A l.

Definition flip_rows_iter {m n} (A: 'M[F]_(m, n)) : 'M[F]_(m, n) :=
  flip_rows_iter_aux A (pmap insub (iota 0 (m %/ 2))).

Lemma flip_rows_iter_aux_notin_val : forall {m n} (A: 'M[F]_(m, n)) (l: list 'I_m) (x : 'I_m) (y : 'I_n),
  (*(forall x, x \in l -> x < m %/ 2) ->*)
  x \notin l ->
  rev_ord x \notin l ->
  flip_rows_iter_aux A l x y = A x y.
Proof.
  move => m n A l x y. elim: l => [Hnot Hnotrev //= | h t IH Hnot Hnotrev /=].
  rewrite xrow_val. move : Hnot Hnotrev. rewrite !in_cons !negb_or => /andP[Hxh Hxt] /andP[Hrevh Hrevt].
  have->: (x == h) = false by move : Hxh; case:(x == h).
  case Hhrev: (x == rev_ord h). have Hcon: h == rev_ord x. eq_subst Hhrev; by rewrite rev_ordK.
  by rewrite eq_sym in Hcon; rewrite Hcon in Hrevh. by apply IH.
Qed.

(*This lemma is quite annoying, because we have to be careful that we do not include the row and its corresponding one twice*)
Lemma flip_rows_iter_aux_in_val : forall {m n} (A: 'M[F]_(m, n)) (l: list 'I_m) (x : 'I_m) (y : 'I_n),
  uniq l ->
  (forall x, x \in l -> x < m %/ 2) ->
  (x \in l \/ rev_ord x \in l) ->
  flip_rows_iter_aux A l x y = A (rev_ord x) y.
Proof.
  move => m n A l x y. elim : l => [Huniq Hsmall Hin //= | h t IH Huniq Hsmall Hin /=].
  - by case : Hin; rewrite in_nil.
  - move : Huniq; rewrite /= => /andP[Hnoth Hnott]. rewrite xrow_val. case: Hin => [Hx | Hrevx].
    + move : Hx; rewrite in_cons => /orP[Hh | Ht].
      * rewrite Hh. eq_subst Hh. apply flip_rows_iter_aux_notin_val.
        -- case Hin : (rev_ord h \in t) =>[|//].
           have Hrevsmall: rev_ord h < m %/ 2. apply Hsmall. by rewrite in_cons Hin orbT.
           have Hhsmall: h < m %/ 2. apply Hsmall. by rewrite in_cons eq_refl. apply rev_ord_one_small in Hhsmall.
           by rewrite Hrevsmall in Hhsmall.
        -- by rewrite rev_ordK. 
      * case Hxh : (x == h). eq_subst Hxh. by rewrite Ht in Hnoth.
        case Hxhrev: (x == rev_ord h).
        -- eq_subst Hxhrev. have Hhsmall: h < m %/2. apply Hsmall. by rewrite in_cons eq_refl.
           apply rev_ord_one_small in Hhsmall.
           have Hrevsmall: rev_ord h < m %/ 2. apply Hsmall. by rewrite in_cons Ht orbT. 
           by rewrite Hrevsmall in Hhsmall.
        -- apply IH. by []. move => x' Hin. apply Hsmall. by rewrite in_cons Hin orbT. by left.
    + move: Hrevx; rewrite in_cons => /orP [Hrevh | Hrevt].
      * eq_subst Hrevh. case Hrev: (x == rev_ord x). eq_subst Hrev. rewrite -!Hrev.
        apply flip_rows_iter_aux_notin_val. by rewrite Hrev. by [].
        rewrite rev_ordK eq_refl. apply flip_rows_iter_aux_notin_val. by [].
        rewrite rev_ordK. have Hrevsmall: rev_ord x < m %/ 2. apply Hsmall. by rewrite in_cons eq_refl.
        apply rev_ord_one_small in Hrevsmall. rewrite rev_ordK in Hrevsmall.
        case Hxin: (x \in t) =>[|//]. rewrite -Hrevsmall. rewrite Hsmall. by []. by rewrite in_cons Hxin orbT.
      * case Hxh: (x == h).
        -- eq_subst Hxh. have Hhsmall: (h < m %/2). apply Hsmall. by rewrite in_cons eq_refl.
           apply rev_ord_one_small in Hhsmall. 
           have Hrevsmall: (rev_ord h < m %/ 2). apply Hsmall. by rewrite in_cons Hrevt orbT.
           by rewrite Hrevsmall in Hhsmall.
        -- case Hxrevh : (x == rev_ord h). eq_subst Hxrevh. rewrite rev_ordK in Hrevt. by rewrite Hrevt in Hnoth.
           apply IH. by []. move => x' Hinx'. apply Hsmall. by rewrite in_cons Hinx' orbT. by right.
Qed.

(*The first result we need: The nice way of writing this matrix is the same as the iterative way*)
Lemma flip_rows_iter_val: forall {m n} (A: 'M[F]_(m, n)),
  flip_rows_iter A = flip_rows A.
Proof.
  move => m n A. rewrite /flip_rows_iter /flip_rows -matrixP /eqrel => x y; rewrite mxE.
  have Hallin: forall x0 : 'I_m, x0 \in pmap insub (iota 0 (m %/ 2)) -> x0 < m %/ 2. { move => x'.
    by rewrite mem_pmap_sub /= mem_iota add0n. }
  have Hu: uniq (pmap insub (iota 0 (m %/ 2))). move => p s. apply pmap_sub_uniq. apply iota_uniq.
  pose proof (rev_ord_bound_total x) as Hx. move : Hx => /orP[/orP [Hx | Hrev] | /andP[Hx Hrev]].
  - apply flip_rows_iter_aux_in_val. apply Hu. apply Hallin. left.
    by rewrite mem_pmap_sub /= mem_iota add0n.
  - apply flip_rows_iter_aux_in_val. apply Hu. apply Hallin. right.
    by rewrite mem_pmap_sub /= mem_iota add0n.
  - rewrite flip_rows_iter_aux_notin_val. have Hxrevnat: nat_of_ord x == nat_of_ord (rev_ord x). eq_subst Hx.
    rewrite Hx. by rewrite eq_sym. have /eqP Heq: x == rev_ord x by []. by rewrite {1}Heq.
    rewrite mem_pmap_sub /= mem_iota add0n negb_and. eq_subst Hx. by rewrite Hx ltnn orbT.
    rewrite mem_pmap_sub /= mem_iota add0n negb_and. eq_subst Hrev.
    have Hrevnat :  nat_of_ord (rev_ord x) = (m - x - 1)%N by []. by rewrite -Hrevnat Hrev ltnn orbT.
Qed.

Lemma flip_rows_iter_aux_row_equiv: forall {m n} (A: 'M[F]_(m, n)) (l: list 'I_m),
  row_equivalent A (flip_rows_iter_aux A l).
Proof.
  move => m n A l. elim : l => [//= | h t IH/=].
  - apply row_equiv_refl.
  - apply (row_equivalent_trans IH). apply ero_row_equiv. apply ero_swap.
Qed.

Lemma flip_rows_row_equivalent: forall {m n} (A: 'M[F]_(m, n)),
  row_equivalent A (flip_rows A).
Proof.
  move => m n A. rewrite -flip_rows_iter_val. apply flip_rows_iter_aux_row_equiv.
Qed.

(*The second result we want: flipping the rows of a matrix does not affect its invertibility*)
Lemma flip_rows_unitmx_iff: forall {n} (A: 'M[F]_n),
  A \in unitmx <-> (flip_rows A) \in unitmx.
Proof.
  move => n A. by rewrite (row_equivalent_unitmx_iff (flip_rows_row_equivalent A)).
Qed. 

End LinIndep.
