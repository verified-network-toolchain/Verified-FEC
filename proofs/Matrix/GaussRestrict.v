(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Require Import Gaussian.
Require Import CommonSSR.
Require Import LinIndep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section Gauss.

Variable F : fieldType.

Local Open Scope ring_scope.


(** Restricted Gaussian Elimination*)

(*The C code presents a version of Gaussian elimination that does not use swaps and that requires all entries in
  the current column to be nonzero. We prove that this simplified version of Gaussian elimination is equivalent
  to the full thing as long as the input matrix satisfies several (fairly strong) invertibility properties*)

(*Alternate version (partial) - more accurate (let's see)*)
Definition all_cols_one_partial {m n} (A: 'M[F]_(m, n)) (c: 'I_n) : option 'M[F]_(m, n) :=
  foldr (fun x acc => if A x c == 0 then None else
                      match acc with
                      | None => None
                      | Some mx => Some(sc_mul mx (A x c)^-1 x)
                      end) (Some A) (ord_enum m).

(*Just the Some case (makes some of the reasoning a bit easier)*)
Definition all_cols_one_noif_gen {m n} (A: 'M[F]_(m, n)) (c: 'I_n) l :=
  foldr (fun x acc => sc_mul acc (A x c)^-1 x) A l.

Definition all_cols_one_noif {m n} (A: 'M[F]_(m, n)) (c: 'I_n) :=
  all_cols_one_noif_gen A c (ord_enum m).

(*None case*)
Lemma all_cols_one_partial_none: forall {m n} (A: 'M[F]_(m, n)) (c: 'I_n),
  all_cols_one_partial A c = None <-> exists r, A r c = 0.
Proof.
  move => m n A c. have->: (exists r, A r c = 0) <-> (exists r, r \in (ord_enum m) /\ A r c = 0).
  - split; move => [r Hr]; exists r.
    + split. by apply mem_ord_enum. by [].
    + apply Hr.
  - rewrite /all_cols_one_partial. elim : (ord_enum m) => [/= | h t IH /=].
    + split. by []. by move => [r [Hcon _]].
    + case Hahc: (A h c == 0).
      * split => [_|//]. exists h. split. by rewrite in_cons eq_refl. by apply /eqP.
      * case Hrest: (foldr
          (fun (x : 'I_m) (acc : option 'M_(m, n)) =>
           if A x c == 0
           then None
           else match acc with
                | Some mx => Some (sc_mul mx (A x c)^-1 x)
                | None => None
                end) (Some A) t) => [mx |].
        -- split => [//|[r [Hr Harc0]]]. move: Hr. rewrite in_cons => /orP[/eqP Hrh | Hrt].
          ++ move: Hahc. by rewrite -Hrh Harc0 eq_refl.
          ++ have: (exists r : ordinal_eqType m, r \in t /\ A r c = 0). exists r. by split. 
             by rewrite -IH Hrest.
        -- split => [_|//]. move: Hrest. rewrite IH => [[r [Hrt Hrac]]].
           exists r. split => [|//]. by rewrite in_cons Hrt orbT.
Qed.

Lemma all_cols_partial_some_iff: forall {m n} (A: 'M[F]_(m, n)) (c: 'I_n),
  all_cols_one_partial A c <-> forall r, A r c != 0.
Proof.
  move => m n A c. pose proof (all_cols_one_partial_none A c) as [Hn1 Hn2]. split.
  - move => Hcol r. apply /eqP. move => Harc. rewrite Hn2 in Hcol. by []. by exists r.
  - move => Hallz. apply contra_not in Hn1. by case Hc: (all_cols_one_partial A c).
    move => [r Hr]. move: Hallz => /(_ r). by rewrite Hr eq_refl.
Qed.

(*Some case*)
Lemma all_cols_one_partial_some: forall {m n} (A: 'M[F]_(m, n)) (c: 'I_n) mx,
  all_cols_one_partial A c = Some mx ->
  mx = all_cols_one_noif A c.
Proof.
  move => m n A c. rewrite /all_cols_one_partial /all_cols_one_noif. 
  elim : (ord_enum m) => [//= mx | h t IH /= mx].
  - by move => [Hamx].
  - case Hahc : (A h c == 0) => [//|].
    case Hrest: (foldr
      (fun (x : 'I_m) (acc : option 'M_(m, n)) =>
       if A x c == 0
       then None
       else match acc with
            | Some mx0 => Some (sc_mul mx0 (A x c)^-1 x)
            | None => None
            end) (Some A) t) => [mx' |//].
    move => [Hmx]. rewrite -Hmx. apply IH in Hrest. by rewrite Hrest.
Qed.

(* Need these 2 for a theorem in ListMatrix*)
Lemma all_cols_one_noif_notin: forall {m n} (A : 'M[F]_(m, n)) (c: 'I_n) x y l,
  x \notin l ->
  (all_cols_one_noif_gen A c l) x y = A x y.
Proof.
  move => m n A c x y l. rewrite /all_cols_one_noif_gen. elim : l => [Hin //=| h t IH Hin /=].
  rewrite /sc_mul mxE. have ->: x == h = false. case Hxh : (x == h) => [| //].
  move : Hin. by rewrite in_cons Hxh. rewrite IH. by []. move : Hin. rewrite in_cons negb_or.
  case : (x \notin t). by []. by rewrite andbF.
Qed.

Lemma all_cols_one_noif_gen_zero: forall {m n} (A : 'M[F]_(m, n)) (c: 'I_n) x y l,
  uniq l ->
  (forall (x: 'I_m), A x c != 0) ->
  ((all_cols_one_noif_gen A c l) x y == 0) = (A x y == 0).
Proof.
  move => m n A c x y l Hun Hz.
  case Hin : (x \in l).
  - rewrite mx_row_transform => [|||//|//].
    + have: A x c == 0 = false. move : (Hz x). by case : (A x c == 0).
      by rewrite /sc_mul mxE eq_refl GRing.mulf_eq0 GRing.invr_eq0; move ->.
    + move => A' i j r Hir. rewrite /sc_mul mxE. by have ->: i == r = false by move : Hir; case : (i == r).
    + move => A' B r Hin' Hout j. by rewrite /sc_mul !mxE eq_refl Hin'.
  -  rewrite all_cols_one_noif_notin. by []. by rewrite Hin.
Qed.

(*First, we define the intermediate functions and gaussian elimination steps*)
(*For this one in particular, we need a generalized version, since in the C proof, we need to reason about
  intermediate steps (namely, we need to know all entries in the rth column are nonzero*)
Lemma all_cols_one_noif_val: forall {m n} (A: 'M[F]_(m,n)) c i j,
  (all_cols_one_noif A c) i j = A i j / A i c.
Proof.
  move => m n A c i j. rewrite mx_row_transform. 
  - by rewrite /sc_mul mxE eq_refl GRing.mulrC.
  - move => A' i' j' r'.
    rewrite /sc_mul mxE /negb. by case: (i' == r').
  - move => A' B' r Hin Hout j'.
    by rewrite /sc_mul !mxE eq_refl !Hin.
  - apply ord_enum_uniq.
  - apply mem_ord_enum.
Qed.

Lemma all_cols_one_partial_val: forall {m n} (A: 'M[F]_(m, n)) c mx i j,
  all_cols_one_partial A c = Some mx ->
  mx i j = A i j / A i c.
Proof.
  move => m n A c mx i j Hpart. apply all_cols_one_partial_some in Hpart.
  by rewrite Hpart all_cols_one_noif_val.
Qed. 

Definition all_cols_one_noif_l_gen {m n} (A: 'M[F]_(m, n)) (c: 'I_n) (l: list 'I_m) :=
  foldl (fun acc x => sc_mul acc (A x c)^-1 x) A l.

Lemma all_cols_one_noif_gen_foldl: forall {m n}  (A: 'M[F]_(m, n)) (c: 'I_n) l,
  uniq l ->
  all_cols_one_noif_gen A c l = all_cols_one_noif_l_gen A c l.
Proof.
  move => m n A c l Hu. rewrite /all_cols_one_noif_gen /all_cols_one_noif_l_gen. 
  have {2}->: l = rev (rev l) by rewrite revK. rewrite foldl_rev.
  apply mx_row_transform_rev.
  - move => A' i' j' r'.
    rewrite /sc_mul mxE /negb. by case: (i' == r').
  - move => A' B' r Hin Hout j'. by rewrite /sc_mul !mxE eq_refl Hin.
  - by [].
Qed.

Definition all_cols_one_noif_l {m n} (A: 'M[F]_(m, n)) (c: 'I_n) :=
  all_cols_one_noif_l_gen A c (ord_enum m).

Definition sub_all_rows_noif {m n} (A: 'M[F]_(m, n)) (r : 'I_m) : 'M[F]_(m, n) :=
  foldr (fun x acc => if x == r then acc else add_mul acc (- 1) r x) A (ord_enum m).

Lemma sub_all_rows_noif_val: forall {m n} (A: 'M[F]_(m, n)) (r : 'I_m) i j,
  sub_all_rows_noif A r i j = if i == r then A i j else A i j - A r j.
Proof.
  move => m n A r i j. rewrite /sub_all_rows_noif. rewrite foldr_remAll. case : (i == r) /eqP => [-> | Hir].
  rewrite mx_row_transform_notin. by []. move => A' i' j' r'.
  rewrite /add_mul mxE //= /negb. by case : (i' == r').
  apply remAll_notin. 
  rewrite mx_row_transform.
  - by rewrite /add_mul mxE eq_refl GRing.mulN1r.
  - move => A' i' j' r'.
    rewrite /add_mul mxE /negb. by case H : (i' == r').
  - move => A' B' r' Hin Hout j'.
    rewrite !/add_mul !mxE !eq_refl !Hin.
    rewrite Hout => [//|]. apply remAll_notin.
  - rewrite -rem_remAll. apply rem_uniq. all: apply ord_enum_uniq.
  - apply remAll_in. by apply /eqP. by rewrite mem_ord_enum.
Qed.

Definition sub_all_rows_noif_l {m n} (A: 'M[F]_(m, n)) (r : 'I_m) : 'M[F]_(m, n) :=
  foldl (fun acc x => if x == r then acc else add_mul acc (- 1) r x) A (ord_enum m).

Lemma sub_all_rows_noif_foldl: forall {m n} (A: 'M[F]_(m,n)) r,
  sub_all_rows_noif A r = sub_all_rows_noif_l A r .
Proof.
  move => m n A r. rewrite /sub_all_rows_noif /sub_all_rows_noif_l foldr_remAll foldl_remAll /=. 
  have {2}->: (remAll r (ord_enum m)) = rev (rev (remAll r (ord_enum m))) by rewrite revK. rewrite foldl_rev.
  rewrite mx_row_transform_rev. by [].
  - move => A' i' j' r'. rewrite /add_mul mxE /negb. by case : (i' == r').
  - move => A' B' r' Hin Hout j'. 
    rewrite !/add_mul !mxE !eq_refl Hin. 
    rewrite Hout => [//|]. apply remAll_notin.
  - rewrite -rem_remAll. apply rem_uniq. all: apply ord_enum_uniq.
Qed.

(*In this version, we do not swap rows, we scalar multiply/subtract all rows, and we have r=c every time. Accordingly,
  we do not need to return all 3 elements, but instead know that the next value is r + 1*)
Definition gauss_one_step_restrict {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn : m <= n) : option 'M[F]_(m, n) :=
  match (all_cols_one_partial A (widen_ord Hmn r)) with
  | None => None
  | Some mx => Some(sub_all_rows_noif mx r)
  end.

(*This mirrors the C code, and will fail (ie, return None) sometimes. We will quantify these cases
  and prove that if it succeeds, it gives the same result as [gauss_one_step]*)

(*First, [gauss_one_step_restrict] gives Some iff the rth column contains all nonzero values*)
Lemma gauss_one_step_restrict_some_iff: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n),
  (gauss_one_step_restrict A r Hmn) <-> (forall (x : 'I_m), A x (widen_ord Hmn r) != 0).
Proof.
  move => m n A r Hmn. rewrite /gauss_one_step_restrict.
  case Hcol: (all_cols_one_partial A (widen_ord Hmn r)) => [mx/= |/=].
  - have: (all_cols_one_partial A (widen_ord Hmn r)) by rewrite Hcol. by rewrite all_cols_partial_some_iff.
  - have: ~is_true (isSome(all_cols_one_partial A (widen_ord Hmn r))) by rewrite Hcol. by rewrite all_cols_partial_some_iff.
Qed.

(*Second, if [gauss_one_step_restrict] gives Some, then it is equivalent to [gauss_one_step]*)
Lemma gauss_one_step_restrict_some_equiv_full: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n),
  gauss_one_step_restrict A r Hmn ->
  (gauss_one_step_restrict A r Hmn) = Some((gauss_one_step A r (widen_ord Hmn r)).1) /\
  (gauss_one_step A r (widen_ord Hmn r)).2 = insub r.+1.
Proof.
  move => m n A r Hmn Hsome. rewrite /gauss_one_step_restrict /gauss_one_step.
  have->:fst_nonzero A (widen_ord Hmn r) r = Some r. {
    rewrite fst_nonzero_some_iff. split => [//|].
    move : Hsome; rewrite gauss_one_step_restrict_some_iff => Hzero. split. by apply Hzero.
    move => x /andP[Hrx Hxr]. move: Hxr. by rewrite ltnNge Hrx. }
  split => [/=|//].
  case Hcol: (all_cols_one_partial A (widen_ord Hmn r)) => [mx | //]; last first.
  move: Hsome. by rewrite /gauss_one_step_restrict Hcol.
  f_equal. rewrite -matrixP => x y. apply all_cols_one_partial_some in Hcol. 
  rewrite Hcol sub_all_rows_noif_val sub_all_rows_val.
   move: Hsome; rewrite gauss_one_step_restrict_some_iff => Hzero. case Hxr: (x == r).
  - rewrite all_cols_one_noif_val all_cols_one_val/= !xrow_rr.
    by have->:A x (widen_ord Hmn r) == 0 = false by apply negbTE.
  - rewrite !all_cols_one_val !all_cols_one_noif_val/= !xrow_rr.
    have Hax0:A x (widen_ord Hmn r) == 0 = false by apply negbTE.
    rewrite Hax0 GRing.mulf_eq0 GRing.invr_eq0 !Hax0 /=.
    by have->: A r (widen_ord Hmn r) == 0 = false by apply negbTE.
Qed.

(*The more useful part*)
Lemma gauss_one_step_restrict_some_equiv: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n),
  gauss_one_step_restrict A r Hmn ->
  (gauss_one_step_restrict A r Hmn) = Some((gauss_one_step A r (widen_ord Hmn r)).1).
Proof.
  move => m n A r Hmn Hgaus. by apply gauss_one_step_restrict_some_equiv_full.
Qed.

(*Therefore, we want to characterize exactly when this version of Gaussian elimination gives us Some*)
(*This version of Gaussian elimination gives us Some if some specific conditions
  are met of the input matrix. Namely, we require the following:
  1. For any r, consider the submatrix consisting of the first r-1 rows and the first r columns, with
     one column before r removed. Then, this submatrix is invertible.
  2. For any r, consider the submatrix consisting of the first r-1 rows and the first r columns, along 
     with any one additional row. Then this submatrix is invertible.
  These conditions ensure that the rth column always contains all nonzero elements. We need to prove both
  that these conditions are preserved and that, if these conditions hold, then we do not hit None.
  First, we define the conditions*)
(*Working with the ordinals in the submatrices is a bit annoying. We define the following utilities to
  construct ordinals*)

(*The first submatrix - the definition is a bit awkward because of the ordinal proof obligations*)
Definition submx_remove_col {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: 'I_m) (j : 'I_m) : 'M[F]_(r, r) :=
  let Hrm := ltn_ord r in
  mxsub (fun (x: 'I_r) => widen_ord (ltnW Hrm) x)
        (fun (y : 'I_r) => if y < j then widen_ord (ltnW (ltn_leq_trans Hrm Hmn)) y
                           else ord_widen_succ (ltn_leq_trans Hrm Hmn) y) A.

(*The row submatrix*)
Definition submx_add_row {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: 'I_m) (j: 'I_m) : 'M[F]_(r.+1, r.+1) :=
  let Hrm := ltn_ord r in
  mxsub (fun (x : 'I_(r.+1)) => if x < r then widen_ord Hrm x else j) 
        (fun (y : 'I_(r.+1)) => widen_ord (leq_trans Hrm Hmn) y) A.

(*r-strong-invertibility refers to a specific r*)
Definition r_strong_inv {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: 'I_m) :=
  (forall j : 'I_m, j < r -> (submx_remove_col A Hmn r j) \in unitmx) /\
  (forall j : 'I_m, r <= j -> (submx_add_row A Hmn r j) \in unitmx).

(*Now, we want to prove the condition for a single step: if the gaussian invariant is satisfied, then
  A is strongly invertible iff all entries in column r are nonzero. We do this in two pieces, one each for 
  the row and column matrices*)
Lemma submx_remove_col_unitmx_cond: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) (j: 'I_m),
  gauss_invar A r r ->
  j < r ->
  (submx_remove_col A Hmn r j \in unitmx) = (A j (widen_ord Hmn r) != 0).
Proof.
  move => m n A Hmn r j Hinv Hjr.
  case : (A j (widen_ord Hmn r) == 0) /eqP => [Hzero /= | Hzero/=].
  - (*If A j r = 0, then the resulting submatrix has a row of zeroes*)
    have Hallzero: (forall (c: 'I_r), (submx_remove_col A Hmn r j) (Ordinal Hjr) c = 0). {
      move => c. rewrite /submx_remove_col mxE. case Hcx : (c < j).
      + apply (elimT eqP). rewrite (gauss_invar_square_id Hmn _ Hinv). rewrite !remove_widen.
        have: nat_of_ord j != nat_of_ord c. move : Hcx. rewrite ltn_neqAle => /andP[Hcx  H{H}].
        by rewrite eq_sym. by []. by apply ltnW. by []. by rewrite remove_widen.
      + case Hcr1 : (c.+1 == r).
        * have->: (widen_ord (ltnW (ltn_ord r)) (Ordinal Hjr) = j) by apply ord_inj. 
          by have->: ((ord_widen_succ (ltn_leq_trans (ltn_ord r) Hmn) c) = widen_ord Hmn r) by apply (elimT eqP).
        * apply (elimT eqP). rewrite (gauss_invar_square_id Hmn _ Hinv). rewrite !remove_widen.
          have: nat_of_ord j != c.+1. case : (nat_of_ord j == c.+1) /eqP => [Hx|//].
          move: Hcx. by rewrite Hx ltnSn. by []. 
          by (apply ltnW). by []. have: c.+1 < r.
          case (orP (ltn_total (c.+1) r)) => [/orP[Hlt' | Heq] | Hgt]. by []. by move: Heq Hcr1 ->.
          have Hcr: c < r by []. rewrite leqNgt in Hcr. by move : Hgt Hcr ->. by [].
      }
      have: submx_remove_col A Hmn r j \notin unitmx by apply (row_zero_not_unitmx Hallzero).
      by apply negbTE.
  - (*If A j r != 0, then the rows are linearly independent (or, if we reorder, we get a diagonal mx, not
      sure which is better to do - lets try lin indep first*)
    (* proof will be quite complicated - annotate with paper*)
    apply unitmx_iff_lin_indep_rows. rewrite /rows_lin_indep /= => c Hallcols x.
    (* For contradiction, assume that we have some x such that c_x != 0 *)
    apply /eqP. case  Hcx: (c x == 0) => [// | /=].
    (* Now, we need some y such that c_y != 0 and y != j (if x != j, this is obvious, otherwise,
       we need to use the fact that the r-1st column has coefficients that sum to 0*)
    have [y Hy]: exists (y: 'I_r), (c y != 0) && ((nat_of_ord y ) != (nat_of_ord j)). {
      case Hjx: (nat_of_ord j == nat_of_ord x).
      - have /orP [/existsP Hexy | /forallP Hnoy]: [exists y : 'I_r, (c y != 0) && (nat_of_ord y != nat_of_ord j)] || 
        [forall y : 'I_r, (nat_of_ord y != nat_of_ord j) ==> (c y == 0)]. {
        pose proof (orbN [exists y : 'I_r, (c y != 0) && (nat_of_ord y != nat_of_ord j)]) as Hex.
        move : Hex. rewrite negb_exists.
        have ->: [forall x0, ~~ ((c x0 != 0) && (nat_of_ord x0 != nat_of_ord j))] = 
          [forall y, (nat_of_ord y != nat_of_ord j) ==> (c y == 0)].
          apply eq_forallb => i /=. by rewrite negb_and implybE negbK orbC. by [].
        }
        apply Hexy. (* Need our r-th column contradiction*)
        have H0r: 0 < r by apply ord_nonzero.
        move: Hallcols => /(_ (pred_ord H0r)).
        have Hrj: r.-1 < j = false. case Hrj: (r.-1 < j) => [/=|//].
          move: Hrj. by rewrite (ltn_predK Hjr) leqNgt Hjr.
        rewrite (@sum_remove_one _ _ _ _ (Ordinal Hjr))//= big1/=.
        * rewrite mxE GRing.add0r /= Hrj. 
          have->: (widen_ord (ltnW (ltn_ord r)) (Ordinal Hjr)) = j by apply ord_inj.
          have->: (ord_widen_succ (ltn_leq_trans (ltn_ord r) Hmn) (pred_ord H0r) = (widen_ord Hmn r)).
            apply ord_inj. by rewrite /= (ltn_predK Hjr).
          have->: Ordinal Hjr = x. apply ord_inj. apply /eqP. by rewrite /= Hjx.
          move => /eqP Hzero'; move: Hzero'. by rewrite GRing.mulf_eq0 Hcx/= => /eqP Hcon.
        * move => i Hij. have->: c i = 0. apply /eqP. move: Hnoy => /(_ i).
          have->//=: (nat_of_ord i != nat_of_ord j) by apply nat_of_ord_neq in Hij.
          by rewrite GRing.mul0r.
      - exists x. by rewrite Hcx /= eq_sym Hjx.
    }
    (*Now we use the y to derive a contradiction from the yth column of A - all other entries are 0*)
    (*To avoid duplicating the proof for the y < j and y > j cases, we prove the following lemma*)
    have [col [Hycol Hcol]]: exists col, submx_remove_col A Hmn r j y col != 0 /\
      forall i, i != y -> submx_remove_col A Hmn r j i col == 0. {
      have Hrm: r <= m by apply ltnW.
      case (orP (ltn_total y j)) => [ /orP [Hgt | Heq] | Hlt].
      - exists y. split.
        + by rewrite mxE Hgt (gauss_invar_square_id Hmn Hrm Hinv)//= negbK.
        + move => i Hiy. by rewrite mxE Hgt (gauss_invar_square_id Hmn Hrm Hinv)//=.
      - move: Hy. apply (elimT eqP) in Heq. by rewrite Heq eq_refl //= andbF.
      - have Hypred: y.-1 < r. have Hpredlt: (y.-1 < y). rewrite ltn_predL. apply (ord_nonzero (Ordinal Hlt)).
        by apply (ltn_trans Hpredlt). exists (Ordinal Hypred).
        have Hypredj: y.-1 < j = false by rewrite (ltn_predK Hlt) leqNgt Hlt.
        split.
        + by rewrite mxE Hypredj (gauss_invar_square_id Hmn Hrm Hinv)//= (ltn_predK Hlt) // negbK.
        + move => i Hiy. by rewrite mxE Hypredj (gauss_invar_square_id Hmn Hrm Hinv)//= (ltn_predK Hlt).
    }
    (*Now we can get our contradiction*)
    move: Hallcols => /(_ col). rewrite (@sum_remove_one _ _ _ _  y)//= big1/=.
    + rewrite GRing.add0r => /eqP Hmul. move: Hmul. rewrite GRing.mulf_eq0.
      move: Hy => /andP[Hcy _]. by rewrite (negbTE Hcy) (negbTE Hycol).
    + move => i Hi. apply /eqP. by rewrite GRing.mulf_eq0 Hcol // orbT.
Qed.

(* The similar condition for the row matrices*)
Lemma submx_add_row_unitmx_cond: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) (j: 'I_m),
  gauss_invar A r r ->
  r <= j ->
  (submx_add_row A Hmn r j \in unitmx) = (A j (widen_ord Hmn r) != 0).
Proof.
  move => m n A Hmn r j Hinv Hjr.
   case : (A j (widen_ord Hmn r) == 0) /eqP => [Hzero /= | Hzero/=].
  - (*If A j r = 0, then the resulting submatrix has a row of zeroes*)
    move : Hinv; rewrite /gauss_invar; move => [Hleadbefore [Hincr [Hzcol Hzeros]]].
    have Hrsuc : r < r.+1 by [].
    case : (A j (widen_ord Hmn r) == 0) /eqP => [Hcontra|//].
    have Hallzero : (forall (c: 'I_(r.+1)), (submx_add_row A Hmn r j) (Ordinal Hrsuc) c = 0).
    move => c. rewrite /submx_add_row mxE. rewrite ltnn.
    have : c <= r by have : c < r.+1 by []. rewrite leq_eqVlt => /orP[Hcr | Hcr].
    have /eqP Heqord : (widen_ord (leq_trans (ltn_ord r) Hmn) c) == (widen_ord Hmn r) by [].
    by rewrite Heqord Hcontra. by apply Hzeros.
    have : submx_add_row A Hmn r j \notin unitmx by apply (row_zero_not_unitmx Hallzero).
    by apply negbTE.
  - (*Similar proof as the previous lemma - rows are linearly independent*)
    apply unitmx_iff_lin_indep_rows. rewrite /rows_lin_indep /= => c Hallcols x.
    (* For contradiction, assume that we have some x such that c_x != 0 *)
    apply /eqP. case  Hcx: (c x == 0) => [// | /=].
    (* Now, we need some y such that c_y != 0 and y != r (if x != r, this is obvious, otherwise,
       we need to use the fact that the rth column has coefficients that sum to 0*)
    have [y Hy]: exists (y: 'I_r.+1), (c y != 0) && ((nat_of_ord y ) != (nat_of_ord r)). {
      case Hxr: (nat_of_ord x == nat_of_ord r).
      - have /orP [/existsP Hexy | /forallP Hnoy]: [exists y : 'I_r.+1, (c y != 0) && (nat_of_ord y != nat_of_ord r)] || 
        [forall y : 'I_r.+1, (nat_of_ord y != nat_of_ord r) ==> (c y == 0)]. {
        pose proof (orbN [exists y : 'I_r.+1, (c y != 0) && (nat_of_ord y != nat_of_ord r)]) as Hex.
        move : Hex. rewrite negb_exists.
        have ->: [forall x0, ~~ ((c x0 != 0) && (nat_of_ord x0 != nat_of_ord r))] = 
          [forall y, (nat_of_ord y != nat_of_ord r) ==> (c y == 0)].
          apply eq_forallb => i /=. by rewrite negb_and implybE negbK orbC. by [].
        }
        apply Hexy. (* Need our r-th column contradiction*)
        have H0r: 0 < r.+1 by apply ord_nonzero.
        move: Hallcols => /(_ (pred_ord H0r)).
        (*have Hrj: r.-1 < j = false. case Hrj: (r.-1 < j) => [/=|//].
          move: Hrj. by rewrite (ltn_predK Hjr) leqNgt Hjr.*)
        rewrite (@sum_remove_one _ _ _ _ (Ordinal (ltnSn r)))//= big1/=.
        * rewrite mxE GRing.add0r /= ltnn.  
          have->: (widen_ord (leq_trans (ltn_ord r) Hmn) (pred_ord H0r)) = (widen_ord Hmn r) by apply ord_inj.
          have->: (Ordinal (ltnSn r)) = x. apply ord_inj. apply /eqP. by rewrite /= eq_sym Hxr.
          move => /eqP Hzero'; move: Hzero'. by rewrite GRing.mulf_eq0 Hcx/= => /eqP Hcon.
        * move => i Hij. have->: c i = 0. apply /eqP. move: Hnoy => /(_ i).
          have->//=: (nat_of_ord i != nat_of_ord r). by apply nat_of_ord_neq in Hij.
          by rewrite GRing.mul0r.
      - exists x. by rewrite Hcx /= Hxr.
    }
    (*This time we don't need the separate existence predicate because we don't need to case on the column*)
    move: Hallcols => /(_ y). have Hrm: r <= m by apply ltnW. have Hyr: y < r.
      have: y <= r by rewrite -ltnS. rewrite leq_eqVlt => /orP[/eqP Hyr | //]. move: Hy.
      by rewrite Hyr eq_refl andbF.
    rewrite (@sum_remove_one _ _ _ _  y)//= big1/=.
      + rewrite GRing.add0r => /eqP Hmul. move: Hmul. rewrite GRing.mulf_eq0.
        move: Hy => /andP[Hcy _]. 
        by rewrite (negbTE Hcy) /= mxE Hyr (gauss_invar_square_id Hmn Hrm Hinv) //= eq_refl.
      + move => i Hi. apply /eqP. rewrite GRing.mulf_eq0 mxE.
        (* only complication: if i = r, we need to use a different part of gauss invariant*)
        have: i <= r by rewrite -ltnS. rewrite leq_eqVlt => /orP[/eqP Hir | Hir].
        * rewrite Hir ltnn. move : Hinv => [_ [_ [_ Hzeros]]]. by rewrite Hzeros // eq_refl orbT.
        * by rewrite Hir (gauss_invar_square_id Hmn Hrm Hinv) //= Hi orbT.
Qed. 

(* Now we can prove that r-strong invertibility is exactly equivalent to the rth column containing
  all nonzero values at the rth step of Gaussian elimination*)
Lemma r_strong_inv_all_zeroes_iff: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m),
  gauss_invar A r r ->
  r_strong_inv A Hmn r <-> (forall (x : 'I_m), A x (widen_ord Hmn r) != 0).
Proof.
  move => m n A Hmn r Hinv. rewrite /r_strong_inv. split.
  - move => [Hcol Hrow] x. case (orP (ltn_leq_total x r)) => [Hxr | Hxr].
    + rewrite -submx_remove_col_unitmx_cond //. by apply Hcol.
    + rewrite -submx_add_row_unitmx_cond //. by apply Hrow.
  - move => Hzero. split; move => j Hjr.
    + by rewrite submx_remove_col_unitmx_cond.
    + by rewrite submx_add_row_unitmx_cond.
Qed.

(* Therefore, r-strong invertibility is equivalent to [gauss_one_step_restrict] giving Some, which by
  [gauss_one_step_restrict_some_equiv] is equivalent to regular Gaussian elimination*)
Lemma gauss_one_step_restrict_equiv_iff: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n),
  gauss_invar A r r ->
  gauss_one_step_restrict A r Hmn = Some((gauss_one_step A r (widen_ord Hmn r)).1) <->
  r_strong_inv A Hmn r.
Proof.
  move => m n A r Hmn Hinv. rewrite r_strong_inv_all_zeroes_iff //. split.
  - case Hg: (gauss_one_step_restrict A r Hmn) => [k |//].
    move => _. apply gauss_one_step_restrict_some_iff. by rewrite Hg.
  - rewrite -gauss_one_step_restrict_some_iff. apply gauss_one_step_restrict_some_equiv.
Qed.

(* Now we want to generalize this result to multiple steps of Gaussian elimination. We will need a stronger
  lemma to get the right induction hypothesis, so we define the notion of multi-strong-invertibility, where
  A is x-strongly invertible for all r <= x < r + s*)

Definition multi_strong_inv {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) (s: nat) :=
  forall (x: 'I_m), r <= x < r + s -> r_strong_inv A Hmn x.

Lemma multi_strong_inv_expand : forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) (Hr1m: r.+1 < m) (s: nat),
  multi_strong_inv A Hmn r s.+1 <-> r_strong_inv A Hmn r /\ multi_strong_inv A Hmn (Ordinal Hr1m) s.
Proof.
  move => m n A Hmn r Hr1m s. rewrite /multi_strong_inv. split.
  - move => Hinv. split. apply Hinv. by rewrite leqnn -ltn_subLR // subnn.
    move => x Hx. apply Hinv. move: Hx. rewrite /= => /andP[Hrx Hxr1s].
    have->/=: r <= x by apply ltnW. move: Hxr1s. by rewrite -(addn1 r) -addnA (add1n s).
  - move => [Hrinv Hinv] x /andP[Hrx Hxrs]. move: Hrx. rewrite leq_eqVlt => /orP[/eqP Hrx | Hrx].
    + by have->: x = r by apply ord_inj.
    + apply Hinv. by rewrite /= Hrx -(addn1 r) -addnA (add1n s).
Qed.

(* Analagously, we define a function to peform s steps of Restricted Gaussian Elimination*)
(*TODO: use bind instead?*)
(*This generic version helps for a few lemmas*)
Definition gauss_multiple_steps_restrict_body {m n} (Hmn: m <= n) o l :=
  foldl (fun oA r' => match (insub r') with
                       | Some r'' => match oA with
                                     | None => None
                                     | Some A' => match gauss_one_step_restrict A' r'' Hmn with
                                                  | None => None
                                                  | Some mx => Some mx
                                                 end
                                     end
                       | None => oA
                      end) o l.

Definition gauss_multiple_steps_restrict {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) r s : option 'M[F]_(m, n) :=
  gauss_multiple_steps_restrict_body Hmn (Some A) (iota r s).

(*A few utility lemmas*)
Lemma gauss_multiple_steps_restrict_body_none: forall {m n} (Hmn: m <= n) l,
  gauss_multiple_steps_restrict_body Hmn None l = None.
Proof.
  move => m n Hmn l. elim : l => [//= | h t /= IH]. case Hm : (h < m).
  - by rewrite insubT.
  - by rewrite insubF.
Qed.

Lemma gauss_multiple_steps_restrict_body_cat: forall {m n} (Hmn: m <= n) o l1 l2,
  gauss_multiple_steps_restrict_body Hmn o (l1 ++ l2) =
  gauss_multiple_steps_restrict_body Hmn (gauss_multiple_steps_restrict_body Hmn o l1) l2.
Proof.
  move => m n Hmn o l1 l2. by rewrite /gauss_multiple_steps_restrict_body foldl_cat.
Qed.

Lemma gauss_multiple_steps_restrict_body_extra: forall {m n} (Hmn: m <= n) o l,
  (forall x, x \in l -> m <= x) ->
  gauss_multiple_steps_restrict_body Hmn o l = o.
Proof.
  move => m n Hmn o l. elim : l => [//= | h t /= IH Hin].
  rewrite insubF.
  - apply IH. move => x Hinx. apply Hin. by rewrite in_cons Hinx orbT.
  - rewrite ltnNge. apply negbF. apply Hin. by rewrite in_cons eq_refl.
Qed.

Lemma gauss_multiple_steps_restrict_expand: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r : 'I_m) s,
  gauss_multiple_steps_restrict A Hmn r s.+1 = 
  match (gauss_one_step_restrict A r Hmn) with
   | None => None
   | Some mx => gauss_multiple_steps_restrict mx Hmn r.+1 s
  end.
Proof.
  move => m n A Hmn r s. rewrite /gauss_multiple_steps_restrict /= insubT//= => Hrm.
  have->: Ordinal Hrm = r by apply ord_inj. case Hone: (gauss_one_step_restrict A r Hmn) => [//= mx | //=].
  elim : (iota r.+1 s) => [// | h t IH /=]. case Hhm : (h < m). by rewrite insubT. by rewrite insubF.
Qed.

Lemma gauss_multiple_steps_restrict_overflow: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) r s,
   m <= r ->
  gauss_multiple_steps_restrict A Hmn r s = Some A.
Proof.
  move => m n A Hmn r s Hmr. apply gauss_multiple_steps_restrict_body_extra. move => x.
  rewrite mem_iota => /andP[Hrx _]. by apply (leq_trans Hmr).
Qed.

(*Two helper lemmas before the key preservation lemma that we need *)
Lemma mxsub_row_transform_equiv: forall {m n m' n'} (A: 'M[F]_(m,n)) (f : 'I_m' -> 'I_m) (g : 'I_n' -> 'I_n)
   (h: 'I_m -> 'M[F]_(m,n) -> 'M[F]_(m,n)) (l: seq 'I_m),
  (forall (A: 'M[F]_(m, n)) (r : 'I_m), row_equivalent (mxsub f g A) (mxsub f g (h r A))) ->
  row_equivalent (mxsub f g A) (mxsub f g (foldr h A l)).
Proof.
  move => m n m' n' A f g h l Hin. elim : l => [//=| x l IH //=].
  by constructor.
  apply (row_equivalent_trans IH). apply Hin.
Qed.

Lemma row_mx_fn_inj: forall {m} (r': 'I_m) (j: 'I_m) (Hj : r' <= j),
  injective (fun x : 'I_r'.+1 => if x < r' then widen_ord (ltn_ord r') x else j).
Proof.
  move => m r' j Hrj x y. case Hxr: (x < r'); case Hyr: (y < r').
  - apply widen_ord_inj.
  - have: (nat_of_ord (widen_ord (ltn_ord r') x) == x) by [].
    move => /eqP Hw Hxj. have: nat_of_ord x == j by rewrite -Hw -Hxj.
    have: x < j by apply (ltn_leq_trans Hxr). rewrite ltn_neqAle => /andP[Hneq H{H}]. move : Hneq.
    by case : (nat_of_ord x == j).
  - have: (nat_of_ord (widen_ord (ltn_ord r') y) == y) by [].
    move => /eqP Hw Hyj. have: nat_of_ord y == j by rewrite -Hw Hyj. have: y < j by apply (ltn_leq_trans Hyr).
    rewrite ltn_neqAle => /andP[Hneq H{H}]. move : Hneq. by case: (nat_of_ord y == j).
  - have: x < r'.+1 by []. have: y < r'.+1 by []. rewrite !ltnS leq_eqVlt. 
    move => /orP [/eqP Hyr'| Hcont]; rewrite leq_eqVlt. move => /orP[/eqP Hxr' | Hcont]. move => H{H}.
    apply (elimT eqP). by have: nat_of_ord x == nat_of_ord y by rewrite Hyr' Hxr'.
    by rewrite Hcont in Hxr. by rewrite Hcont in Hyr.
Qed. 

(* The key lemma that we need before our result: for all r_strong_inv for r' > r, one step of
  (restricted) Gaussian elimination does not affect this. We prove this by showing the relevant
  matrices are row equivalent and hence do not change invertibility*)
Lemma r_strong_inv_preserved: forall {m n} (A A': 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) (r' : 'I_m),
  r < r' ->
  gauss_one_step_restrict A r Hmn = Some A' ->
  r_strong_inv A Hmn r' <-> r_strong_inv A' Hmn r'.
Proof.
  move => m n A A' Hmn r r' Hrr' Hgauss.
  have Hsome: (gauss_one_step_restrict A r Hmn)
    by rewrite Hgauss. move: Hgauss. rewrite /gauss_one_step_restrict.
  case Hcol: (all_cols_one_partial A (widen_ord Hmn r)) => [mx|//].
  move => Hsub. rewrite /r_strong_inv.
  apply all_cols_one_partial_some in Hcol. rewrite Hcol in Hsub.
  case : Hsub => [Hsub]. 
  (*First part: col mx's are row equivalent*)
  have Hcols: (forall j : 'I_m, j < r' -> 
    row_equivalent (submx_remove_col A Hmn r' j) (submx_remove_col A' Hmn r' j)). {
    move => j Hjr'. rewrite /submx_remove_col/= -Hsub.
    eapply row_equivalent_trans; last first.
    - apply mxsub_row_transform_equiv. move => A'' r''. case Hrr'' : (r'' == r). constructor.
      apply mxsub_add_mul_row_equiv. move => x y. apply widen_ord_inj. by rewrite eq_sym Hrr''.
      have Hlt: r < r' by []. exists (Ordinal Hlt).
      have: nat_of_ord (widen_ord (ltnW (ltn_ord r')) (Ordinal Hlt)) == r.
      by rewrite remove_widen. by [].
    - apply mxsub_row_transform_equiv. move => A'' r''. apply mxsub_sc_mul_row_equiv.
      move => x y. apply widen_ord_inj. 
      apply GRing.invr_neq0. by apply gauss_one_step_restrict_some_iff.
  }
  have Hrows: (forall j : 'I_m, r' <= j -> 
    row_equivalent (submx_add_row A Hmn r' j)(submx_add_row A' Hmn r' j)). {
    move => j Hjr'. rewrite /submx_add_row/= -Hsub.
    eapply row_equivalent_trans; last first.
    - apply mxsub_row_transform_equiv. move => A'' r''. case Hrr'': (r'' == r). constructor.
      apply mxsub_add_mul_row_equiv. by apply row_mx_fn_inj. by rewrite eq_sym Hrr''.
      have Hltrr' : r.+1 <= r' by []. have Hsuc: r < r'.+1 by apply (ltn_trans Hltrr').
      exists (Ordinal Hsuc). have: Ordinal Hsuc < r' by []. move ->.
      have: nat_of_ord (widen_ord (ltn_ord r') (Ordinal Hsuc)) == r by []. by [].
    - apply mxsub_row_transform_equiv. move => A'' r''. apply mxsub_sc_mul_row_equiv. by apply row_mx_fn_inj.
      apply GRing.invr_neq0. by apply gauss_one_step_restrict_some_iff.
  }
  (* Now the needed result follows from repeated application of this*)
  split => [[Hcolu Hrowu]|[Hcolu Hrowu]]; split; move => j Hrj.
  - rewrite -(row_equivalent_unitmx_iff (Hcols j Hrj)). by apply Hcolu.
  - rewrite -(row_equivalent_unitmx_iff (Hrows j Hrj)). by apply Hrowu.
  - rewrite (row_equivalent_unitmx_iff (Hcols j Hrj)). by apply Hcolu.
  - rewrite (row_equivalent_unitmx_iff (Hrows j Hrj)). by apply Hrowu.
Qed.

(* A corollary: if we have multi_strong_inv for any r' > r, this is preserved *)
Lemma multi_strong_inv_preserved: forall {m n} (A A': 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) (r' : 'I_m) s,
  r < r' ->
  gauss_one_step_restrict A r Hmn = Some A' ->
  multi_strong_inv A Hmn r' s <-> multi_strong_inv A' Hmn r' s.
Proof.
  move => m n A A' Hmn r r' s Hrr' Hgauss. rewrite /multi_strong_inv. split; move => Hinv x /andP[Hrx Hxr].
  - rewrite -r_strong_inv_preserved. apply Hinv. by rewrite Hrx Hxr. by apply (ltn_leq_trans Hrr'). by [].
  - rewrite r_strong_inv_preserved. apply Hinv. by rewrite Hrx Hxr. by apply (ltn_leq_trans Hrr'). by [].
Qed. 

(*The lemma we want to show:[gauss_multiple_steps_restrict A r s] equals [gauss_multiple_steps A r s] iff
  [multi_strong_inv A r s] holds (as long as A satisfies the Gaussian invariant) *)
Lemma gauss_multiple_steps_restrict_equiv_iff: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n) s,
  gauss_invar A r r ->
  (gauss_multiple_steps_restrict A Hmn r s = Some(gauss_multiple_steps A (Some r) (Some (widen_ord Hmn r)) s)) 
  <-> multi_strong_inv A Hmn r s.
Proof.
  move => m n A r Hmn s Hinv. move: A r Hinv. elim : s => [/= A r Hinv | s' IH A r Hinv].
  - rewrite /gauss_multiple_steps_restrict/=. split => [_|//]. rewrite /multi_strong_inv => x.
    rewrite addn0 => /andP[Hrx Hxr]. move: Hxr. by rewrite ltnNge Hrx.
  - split.
    + (*equality -> multi_strong_inv*)
      rewrite /= gauss_multiple_steps_restrict_expand. case Hone: (gauss_one_step_restrict A r Hmn) => [mx |//].
      have Hsome: (gauss_one_step_restrict A r Hmn) by rewrite Hone. apply gauss_one_step_restrict_some_equiv_full in Hsome.
      case : Hsome => [Hg1  Hg2]. assert (Hg1' := Hg1). assert(Hg2' := Hg2). 
      case Hgone : (gauss_one_step A r (widen_ord Hmn r)) => [A' or]. move: Hg1. move: Hg2.
      rewrite !Hgone/=. move ->. rewrite Hone => [[Hmxa]]. rewrite -!Hmxa. 
      (*Now need to deal with ordinals in order to apply the IH*)
      case Hr1m: (r.+1 < m); last first. 
      * (*overflow*)
        move => _. rewrite /multi_strong_inv. move => x /andP[Hrx Hxrs]. move: Hrx.
        rewrite leq_eqVlt => /orP[/eqP Hrx | Hrx].
        -- have->: x = r by apply ord_inj. by apply gauss_one_step_restrict_equiv_iff.
        -- have: r.+1 <= m by []. rewrite leq_eqVlt Hr1m orbF eq_sym => Hr1x. 
           have: m <= x. have Hmr1: m <= r.+1 by rewrite leq_eqVlt Hr1x /=. by apply (leq_trans Hmr1).
           rewrite leqNgt. by have->: x < m by [].
      * rewrite insubT /=. have->:(insub (r.+1)) = Some (widen_ord Hmn (Ordinal Hr1m)).
        rewrite insubT. by apply (ltn_leq_trans Hr1m). move => Hr1n/=. f_equal. by apply ord_inj.
        have Hr1: r.+1 = nat_of_ord (Ordinal Hr1m) by []. rewrite {1}Hr1 {Hr1}.
        rewrite IH/=.
        -- (*Get strong_inv r.+1 from IH, r_strong_inv from preservation*)
           move => Hall. apply (multi_strong_inv_expand _ _ Hr1m). split. by apply gauss_one_step_restrict_equiv_iff.
           rewrite multi_strong_inv_preserved. apply Hall. 2: apply Hone. by [].
        -- have Hinv': gauss_invar A r (widen_ord Hmn r) by apply Hinv. apply gauss_one_step_invar in Hinv'.
           move: Hinv'. rewrite Hgone Hmxa/=. move: Hg2'. rewrite Hgone/=. move ->.
           by rewrite ord_bound_convert_plus.
    + (*multi_strong_inv -> equality*)
      rewrite /= gauss_multiple_steps_restrict_expand. move => Hall.
      have Hrstr: r_strong_inv A Hmn r. { move: Hall. rewrite /multi_strong_inv => /(_ r) Hrinv. apply Hrinv.
      have Hs0: 0 < s'.+1 by []. by rewrite leqnn /= -ltn_psubLR // subnn. }
      have Honeq: gauss_one_step_restrict A r Hmn = Some (gauss_one_step A r (widen_ord Hmn r)).1
        by apply gauss_one_step_restrict_equiv_iff.
      rewrite Honeq.
      case Hgone: (gauss_one_step A r (widen_ord Hmn r)) => [A' or]. rewrite /=.
      have Hor: or = insub r.+1. { have Hg: (gauss_one_step_restrict A r Hmn) by rewrite Honeq.
        apply gauss_one_step_restrict_some_equiv_full in Hg. rewrite Hgone in Hg. case : Hg => [_ Hor /=].
        by rewrite -Hor. }
      rewrite Hor.
      (*Need to case on r.+1 to deal with ordinals*)
      case Hr1m: (r.+1 < m).
      * rewrite insubT/=. have->: insub r.+1 = Some (widen_ord Hmn (Ordinal Hr1m)). { rewrite insubT.
          by apply (ltn_leq_trans Hr1m). move => Hr1n. f_equal. by apply ord_inj. }
        have{1}->: r.+1 = nat_of_ord (Ordinal Hr1m) by []. apply IH.
        have Hinv': gauss_invar A r (widen_ord Hmn r) by apply Hinv. apply gauss_one_step_invar in Hinv'.
        move: Hinv'. by rewrite Hgone/= Hor insubT/=.
        move: Hall. rewrite (multi_strong_inv_expand _ _ Hr1m) => [[Hrstr' Hall]].
        rewrite Hgone in Honeq. rewrite /= in Honeq.
        rewrite -multi_strong_inv_preserved. apply Hall. 2: apply Honeq. by [].
      * rewrite insubF //= gauss_multiple_steps_row_none gauss_multiple_steps_restrict_overflow //.
        by rewrite leqNgt Hr1m.
Qed.

(* One final similar lemma, analagous to [gauss_one_step_restrict_some_equiv] *)
Lemma gauss_multiple_steps_restrict_some_equiv:
  forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n) s,
  gauss_multiple_steps_restrict A Hmn r s ->
  gauss_multiple_steps_restrict A Hmn r s = Some(gauss_multiple_steps A (Some r) (Some (widen_ord Hmn r)) s).
Proof.
  move => m n A r Hmn s. move: A r. elim : s => [//= A r | s' /= IH A r Hsome].
  rewrite gauss_multiple_steps_restrict_expand.
  case Hres: (gauss_one_step_restrict A r Hmn) => [mx /= | //].
  - have Hrsome: (gauss_one_step_restrict A r Hmn) by rewrite Hres.
    apply gauss_one_step_restrict_some_equiv_full in Hrsome.
    move: Hrsome. case Hg: (gauss_one_step A r (widen_ord Hmn r)) => [A' or]/=.
    rewrite Hres. move => [[Ha'] Hor]. rewrite Ha' Hor.
    case Hr1: (r.+1 < m).
    + rewrite insubT/=. have->: (insub r.+1) = Some (widen_ord Hmn (Ordinal Hr1)). {
        rewrite insubT. by apply (ltn_leq_trans Hr1). move => Hr1n. f_equal. by apply ord_inj. }
      have{1}->:r.+1 = nat_of_ord (Ordinal Hr1) by []. apply IH. move: Hsome.
      by rewrite gauss_multiple_steps_restrict_expand Hres Ha'.
    + by rewrite insubF //= gauss_multiple_steps_row_none gauss_multiple_steps_restrict_overflow // leqNgt Hr1.
  - move: Hsome. by rewrite gauss_multiple_steps_restrict_expand Hres.
Qed.

(* We need a few more results to give the full algorithm*)

(*We want to know that after [gauss_step_restrict] with input r, A r r = 1 (this is not true for previous LC's*)
Lemma gauss_one_step_restrict_lc_1: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) mx,
  gauss_invar A r r ->
  (gauss_one_step_restrict A r Hmn) = Some mx ->
  mx r (widen_ord Hmn r) = 1.
Proof.
  move => m n A Hmn r mx Hinv. rewrite /gauss_one_step_restrict.
  case Hcol: (all_cols_one_partial A (widen_ord Hmn r)) => [mx' |//].
  move => [Hsub]. rewrite -Hsub sub_all_rows_noif_val eq_refl (all_cols_one_partial_val _ _ Hcol) GRing.mulfV //.
  apply all_cols_partial_some_iff. by rewrite Hcol.
Qed.

(* We know that the result will be equivalent to [gauss_multiple_steps] but we also want to know that 
  [gauss_invar (gauss_multiple_steps_restrict A) (r + s) (r + s) ] holds so that we know more about the
  structure of the resulting matrix *)

Lemma gauss_one_step_restrict_invar: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) mx,
  gauss_invar A r r ->
  gauss_one_step_restrict A r Hmn = Some mx ->
  gauss_invar mx r.+1 r.+1.
Proof.
  move => m n A Hmn r mx Hinv Hgauss.
  have Hg: (gauss_one_step_restrict A r Hmn) by rewrite Hgauss.
  apply gauss_one_step_restrict_some_equiv_full in Hg.
  have Hinv': gauss_invar A r (widen_ord Hmn r) by [].
  apply gauss_one_step_invar in Hinv'. move: Hg Hinv'.
  case : (gauss_one_step A r (widen_ord Hmn r)) => [A' or]/=.
  rewrite Hgauss => [[[Hmxa]] Hor]. by rewrite Hmxa Hor ord_bound_convert_plus.
Qed.

(* We extend this to [gauss_multiple_steps_restrict]*)
Lemma gauss_multiple_steps_restrict_invar: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) s mx,
  r + s <= m ->
  gauss_invar A r r ->
  gauss_multiple_steps_restrict A Hmn r s = Some mx ->
  gauss_invar mx (r + s) (r + s).
Proof.
  move => m n A Hmn r s. move : A r. elim : s => [A r mx Hrs Hinv /=|s' IH A r mx Hrs Hinv /=].
  - rewrite /gauss_multiple_steps_restrict /= => [[Hmxa]]. by rewrite -Hmxa addn0.
  - rewrite gauss_multiple_steps_restrict_expand.
    case Hg: (gauss_one_step_restrict A r Hmn) => [mx' |//].
    have Hrs1: (r + s'.+1)%N = (r.+1 + s')%N by rewrite -(addn1 r) -addnA (add1n s').
    case Hr1m : (r.+1 < m).
    + have->: r.+1 = nat_of_ord (Ordinal Hr1m) by []. move => Hmult.
      apply IH in Hmult. move: Hmult. by rewrite Hrs1. by rewrite -Hrs1.
      rewrite /=. by apply (gauss_one_step_restrict_invar Hinv Hg).
    + (*need to know that s' = 0*)
      have Hrs1leq: r.+1 <= r + s'.+1 by rewrite -ltn_subLR // subnn //.
      have: m <= r.+1 by rewrite leqNgt Hr1m. rewrite leq_eqVlt => [/orP[/eqP Hmr1 | Hmr1]].
      * have->: s' = 0%N. { move: Hrs. rewrite Hrs1 -Hmr1 -leq_subRL // subnn leqn0. by apply /eqP. }
        rewrite /gauss_multiple_steps_restrict/= => [[Hmx']]. rewrite -Hmx' addn1.
        apply (gauss_one_step_restrict_invar Hinv Hg).
      * have: m < m by apply (ltn_leq_trans Hmr1). by rewrite ltnn.
Qed.

(* The last leading coefficient is 1 after multiple steps of restricted Gaussian elimination*)
Lemma gauss_multiple_steps_restrict_lc_1: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: 'I_m) s mx 
  (Hrs: r + s.-1 < m),
  0 < s ->
  gauss_invar A r r ->
  (gauss_multiple_steps_restrict A Hmn r s) = Some mx ->
  mx (Ordinal Hrs) (widen_ord Hmn (Ordinal Hrs)) = 1.
Proof.
  move => m n A Hmn r s mx Hrs H0s Hinv. rewrite /gauss_multiple_steps_restrict.
  have Hs: s = ((s.-1) + 1)%N by rewrite addn1 (ltn_predK H0s).
  have->: iota r s = iota r (s.-1 + 1)%N by rewrite {1}Hs.
  rewrite iotaD gauss_multiple_steps_restrict_body_cat /= insubT -/(gauss_multiple_steps_restrict A Hmn r s.-1) /=.
  case Hmult: (gauss_multiple_steps_restrict A Hmn r s.-1) => [A'/= | //].
  case Hone: (gauss_one_step_restrict A' (Ordinal Hrs) Hmn) => [mx'/= |//].
  move => [Hmx']. rewrite -Hmx'. eapply gauss_one_step_restrict_lc_1; last first.
  apply Hone. rewrite /=. apply (gauss_multiple_steps_restrict_invar (ltnW Hrs) Hinv Hmult) .
Qed.

Definition gauss_all_steps_restrict {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: nat) :=
  gauss_multiple_steps_restrict A Hmn r (n - r).

Definition all_strong_inv {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) :=
  multi_strong_inv A Hmn r (m - r).

(* Equivalence with non-restricted Gaussian elimination*)
Lemma gauss_all_steps_equiv: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: 'I_m),
  gauss_invar A r r ->
  all_strong_inv A Hmn r <->
  gauss_all_steps_restrict A Hmn r = 
    Some (gauss_all_steps A (Some r) (Some (widen_ord Hmn r))).
Proof.
  move => m n A Hmn r Hinv. rewrite /gauss_all_steps_restrict.
  have Hs: n <= (n - r) + nat_of_ord (widen_ord Hmn r). rewrite /= -subnA //.
    by rewrite subnn subn0. have Hrm: r <= m by apply ltnW. by apply (leq_trans Hrm).
  rewrite -(gauss_multiple_steps_equiv _ _ Hs) gauss_multiple_steps_restrict_equiv_iff //. 
  rewrite /all_strong_inv /multi_strong_inv. have->: (r + (m - r))%N = m. rewrite -addnBCA //. 
    by rewrite subnn addn0. by apply ltnW.
  have->:(r + (n - r))%N = n. rewrite -addnBCA //. by rewrite subnn addn0.
    have Hrm: r <= m by apply ltnW. by apply (leq_trans Hrm). split; move => Hstr x /andP[Hrx Hxmn].
  - apply Hstr. by rewrite Hrx andTb.
  - apply Hstr. by rewrite Hrx andTb (ltn_leq_trans Hxmn).
Qed.

(** Final Algorithm *)

(*Similarly, we wrap this into a nice definition which we can then prove results about to use in the C code
  which operates on the result of Gaussian elimination*)

(*In this case, we know all the leading coefficients are at position r (for row r). We provide a 
  generic upper bound because the last row is not needed*)
Definition mk_identity {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (b: nat) :=
  foldr (fun x acc => sc_mul acc (A x (widen_ord Hmn x))^-1 x) A (pmap insub (iota 0 b)).

Lemma mk_identity_val_in: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (b: nat) (i: 'I_m) (j: 'I_n),
  i < b ->
  mk_identity A Hmn b i j = (A i (widen_ord Hmn i))^-1 * A i j.
Proof.
  move => m n A Hmn b i j Hib. rewrite mx_row_transform.
  - by rewrite /sc_mul mxE eq_refl.
  - move => A' i' j' r' Hir'. rewrite /sc_mul mxE. by have ->: i' == r' = false by move : Hir'; by case : (i' == r').
  - move => A' B' r Hab Hnotin j'. by rewrite /sc_mul !mxE eq_refl Hab.
  - apply pmap_sub_uniq. apply iota_uniq.
  - by rewrite mem_pmap_sub /= mem_iota add0n.
Qed.

Lemma mk_identity_val_notin: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (b: nat) (i: 'I_m) (j: 'I_n),
  b <= i ->
  mk_identity A Hmn b i j = A i j.
Proof.
  move => m n A Hmn b i j Hbi. rewrite mx_row_transform_notin.
  - by [].
  - move => A' i' j' r Hir'. rewrite /sc_mul mxE.
    by (move : Hir'; case : (i' ==r)).
  - rewrite mem_pmap_sub /= mem_iota add0n negb_and. rewrite leqNgt in Hbi.
    by rewrite Hbi orbT.
Qed.

Lemma mk_identity_equiv: forall {m n} (A:'M[F]_(m, n)) (Hmn: m <= n) (Hm: m.-1 < m),
  (forall (r': 'I_m), lead_coef A r' = Some (widen_ord Hmn r')) ->
  A (Ordinal Hm) (widen_ord Hmn (Ordinal Hm)) = 1 ->
  mk_identity A Hmn (m.-1) = all_lc_1 A.
Proof.
  move => m n A Hmn Hm Hlc Hlast.
  have H0m: (0 < m) by rewrite -ltn_predL.
  rewrite -matrixP /eqrel => x y. 
  rewrite all_lc_1_val Hlc.
  have /orP[Hin | Hnotin]: ((x < m.-1) || (m.-1 <= x)) by rewrite orbC leq_eqVlt orbC orbA eq_sym ltn_total.
  - by rewrite mk_identity_val_in.
  - rewrite mk_identity_val_notin =>[|//]. 
    have Hxm: x <= m.-1 by rewrite -ltn_pred.
    have Hxm1 : nat_of_ord x == m.-1 by rewrite eqn_leq Hxm Hnotin.
    have /eqP Hxord: x == Ordinal Hm by []. by rewrite Hxord Hlast GRing.invr1 GRing.mul1r.
Qed. 

Definition mk_identity_l {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (b: nat) :=
  foldl (fun acc x => sc_mul acc (A x (widen_ord Hmn x))^-1 x) A (pmap insub (iota 0 b)).

Lemma mk_identity_foldl: forall {m n} (A: 'M[F]_(m, n)) Hmn b,
  mk_identity A Hmn b = mk_identity_l A Hmn b.
Proof.
  move => m n A Hmn b. rewrite /mk_identity /mk_identity_l.
  have {2}->: (pmap insub (iota 0 b)) = rev (rev ((pmap insub (iota 0 b)))). move => p s; by rewrite revK. rewrite foldl_rev.
  apply mx_row_transform_rev.
  - move => A' i j r Hir. rewrite /sc_mul mxE. move : Hir; by case : (i == r).
  - move => A' B' r Hab H{H} j. by rewrite /sc_mul !mxE eq_refl Hab.
  - apply pmap_sub_uniq. apply iota_uniq.
Qed.

(* The complete Restricted Gaussian Elimination algorithm*)

(* Finally, we can easily extend this to the full Gaussian elimination algorithm by setting r=0. We give
   a separate definition of (full) strong invertibility, the exact condition under which these two algorithms
   are equal *)
Definition strong_inv {m n} (A: 'M[F]_(m, n)) (H0m: 0 < m) (Hmn: m <= n) :=
  all_strong_inv A Hmn (Ordinal H0m).

(*The only complication is that we don't need to scalar multiply the last row*)
Definition gaussian_elim_restrict {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) :=
  match (gauss_all_steps_restrict A Hmn 0) with
  | Some mx => Some (mk_identity mx Hmn (m.-1))
  | None => None
  end.

Lemma gauss_multiple_steps_restrict_extra: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n),
  gauss_multiple_steps_restrict A Hmn 0 n = gauss_multiple_steps_restrict A Hmn 0 m.
Proof.
  move => m n A Hmn. rewrite /gauss_multiple_steps_restrict. 
  have Hn: n = (m + (n - m))%N by rewrite -addnBCA // subnn addn0.
  have->: (iota 0 n) = (iota 0 (m + (n - m))) by rewrite {1}Hn. rewrite iotaD gauss_multiple_steps_restrict_body_cat
    gauss_multiple_steps_restrict_body_extra //.
  move => x. by rewrite add0n mem_iota => /andP[Hxm _].
Qed. 

(* The full versions are equivalent iff [strong_inv] holds*)
Theorem gaussian_elim_equiv: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (Hm: 0 < m),
  strong_inv A Hm Hmn <-> gaussian_elim_restrict A Hmn = Some(gaussian_elim A).
Proof.
  move => m n A Hmn Hm. rewrite /strong_inv.
  rewrite gauss_all_steps_equiv; last first. apply gauss_invar_init.
  rewrite /gaussian_elim /gaussian_elim_restrict/=.
  case Hall: (gauss_all_steps_restrict A Hmn 0) => [mx |//]. split.
  - move : Hall. rewrite /gauss_all_steps_restrict subn0 gauss_multiple_steps_restrict_extra => Hall.
    move => [Hmx]. rewrite Hmx. f_equal.
    rewrite mk_identity_equiv/=.
    + f_equal. f_equal. rewrite insubT. f_equal. rewrite insubT. by apply (ltn_leq_trans Hm).
      move => H0n. f_equal. by apply ord_inj.
    + by apply pred_lt.
    + move => r'. apply (gauss_invar_square_lc Hmn (leqnn m)). rewrite -Hmx.
      have Hs: ((Ordinal Hm) + m) <= m by [].
      have Hinv: gauss_invar A (Ordinal Hm) (Ordinal Hm) by apply gauss_invar_init.
      apply (gauss_multiple_steps_restrict_invar Hs Hinv Hall). by [].
    + move => Hm1. rewrite -Hmx. have Hrs: ((Ordinal Hm) + m.-1 < m) by rewrite /= add0n.
      have->: Ordinal Hm1 = Ordinal Hrs by apply ord_inj.
      have Hinv: (gauss_invar A (Ordinal Hm) (Ordinal Hm)) by apply gauss_invar_init.
      apply (gauss_multiple_steps_restrict_lc_1 Hrs Hm Hinv Hall).
  - (*Easy, we can just ignore the all_lc_1 part*)
    move => _. rewrite -Hall. have{1}->: 0%N = nat_of_ord (Ordinal Hm) by [].
    rewrite -gauss_all_steps_equiv.
    + rewrite /all_strong_inv -gauss_multiple_steps_restrict_equiv_iff.
      * apply gauss_multiple_steps_restrict_some_equiv. move: Hall.
        rewrite /gauss_all_steps_restrict. rewrite !subn0 gauss_multiple_steps_restrict_extra/=.
        by move ->.
      * by apply gauss_invar_init.
    + by apply gauss_invar_init.
Qed.

(** Additional Results for VST/ListMatrix proofs*)

(* For the C proofs, we don't want the option present, since it makes things much more annoying (and we are
  only every dealing with the Some case anyway). So we define a version without Options and prove that,
  subject to strong invertibility conditions, it is equivalent*)

Definition gauss_one_step_restrict_noop {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n) :=
  sub_all_rows_noif (all_cols_one_noif A (widen_ord Hmn r)) r.

Lemma gauss_one_step_restrict_noop_equiv_aux: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n),
  gauss_invar A r r ->
  r_strong_inv A Hmn r ->
  gauss_one_step_restrict A r Hmn = Some(gauss_one_step_restrict_noop A r Hmn).
Proof.
  move => m n A r Hmn Hinv. rewrite /gauss_one_step_restrict /gauss_one_step_restrict_noop
  r_strong_inv_all_zeroes_iff// -all_cols_partial_some_iff. 
  case Hcol: (all_cols_one_partial A (widen_ord Hmn r)) => [mx /= |//=]. move => _.
  apply all_cols_one_partial_some in Hcol. by rewrite Hcol.
Qed.

Definition gauss_multiple_steps_restrict_noop {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r s: nat) :=
  foldl (fun mx r' => match insub r' with
                      | Some r'' => gauss_one_step_restrict_noop mx r'' Hmn
                      | None => mx
                      end) A (iota r s).

Lemma gauss_multiple_steps_restrict_noop_expand: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) (s: nat),
  gauss_multiple_steps_restrict_noop A Hmn r s.+1 = 
  gauss_multiple_steps_restrict_noop (gauss_one_step_restrict_noop A r Hmn) Hmn r.+1 s.
Proof.
  move => m n A Hmn r s. rewrite /gauss_multiple_steps_restrict_noop /= insubT // => Hrm /=.
  by have->: Ordinal Hrm = r by apply ord_inj.
Qed.

Lemma gauss_multiple_steps_restrict_noop_overflow: forall {m n} (A : 'M_(m, n)) (Hmn : m <= n) (r s : nat),
  m <= r -> gauss_multiple_steps_restrict_noop A Hmn r s = A.
Proof.
  move => m n A Hmn r s. move: A r. elim : s => [//= | s' /= IH A r Hmr].
  move: IH. rewrite /gauss_multiple_steps_restrict_noop => IH /=.
  rewrite insubF. apply IH. by apply (leq_trans Hmr). by rewrite ltnNge Hmr.
Qed. 

Lemma gauss_multiple_steps_restrict_noop_equiv: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) (s: nat),
  gauss_invar A r r ->
  multi_strong_inv A Hmn r s ->
  gauss_multiple_steps_restrict A Hmn r s = Some(gauss_multiple_steps_restrict_noop A Hmn r s).
Proof.
  move => m n A Hmn r s. move: A r. elim : s => [A r //= | s' /= IH A r Hinv Hstr].
  rewrite gauss_multiple_steps_restrict_expand gauss_multiple_steps_restrict_noop_expand.
  have Hg: (gauss_one_step_restrict A r Hmn = Some (gauss_one_step_restrict_noop A r Hmn)). {
    apply gauss_one_step_restrict_noop_equiv_aux. by []. move: Hstr. rewrite /multi_strong_inv => /(_ r) Hstr.
    apply Hstr. by rewrite leqnn /= -ltn_psubLR // subnn. }
  rewrite Hg.
  case Hr1: (r.+1 < m).
  - have->: r.+1 = (Ordinal Hr1) by []. apply IH. rewrite /=.
    apply (gauss_one_step_restrict_invar Hinv Hg).
    rewrite -multi_strong_inv_preserved. 3: apply Hg. 2: by [].
    move: Hstr. rewrite /multi_strong_inv/= -{2}(addn1 r) -addnA (add1n s').
    move => Hstr x /andP[Hrx Hxrs]. apply Hstr. rewrite Hxrs andbT. by apply ltnW.
  - rewrite gauss_multiple_steps_restrict_overflow.
    rewrite gauss_multiple_steps_restrict_noop_overflow //. all: by rewrite leqNgt Hr1.
Qed. 

(*Finally, for the C proofs, we will want a version which goes from row 0 to some row x < m (instead of the previous,
  which goes from r to m. We will define this (virtually identically, only the bounds for iota change) and prove that
  this is equivalent.*)
Definition gauss_all_steps_restrict_beg {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: nat) :=
  gauss_multiple_steps_restrict A Hmn 0 r.

Definition gauss_all_steps_restrict_beg_noop {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: nat) :=
  gauss_multiple_steps_restrict_noop A Hmn 0 r.

(*We need to know that all_strong_inv is preserved through multiple steps of Restricted Gaussian Elimination. This
  is not quite the same as we proved earlier, though we can use some existing results*)
Lemma all_strong_inv_preserved: forall {m n} (A A': 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) s (Hrs: r + s < m),
  gauss_invar A r r ->
  all_strong_inv A Hmn r ->
  gauss_multiple_steps_restrict A Hmn r s = Some A' ->
  all_strong_inv A' Hmn (Ordinal Hrs).
Proof.
  move => m n A A' Hmn r s. move: A A' r. elim : s => [//= A A' r Hrs Hinv Hstr | s' IH /= A A' r Hrs Hinv Hstr].
  - rewrite /gauss_multiple_steps_restrict/= => [[Haa]]. rewrite -Haa/=. have->//:(Ordinal Hrs) = r.
    apply ord_inj. by rewrite /= addn0.
  - rewrite gauss_multiple_steps_restrict_expand. case Hone: (gauss_one_step_restrict A r Hmn) => [mx/=|//].
    have Hrs1: (r + s'.+1)%N = (r.+1 + s')%N by rewrite -(addn1 r) -addnA (add1n s').
    case Hrm: (r.+1 < m); last first.
    + rewrite gauss_multiple_steps_restrict_overflow //=. move => [Hmxa]. rewrite -Hmxa.
      move: Hstr. rewrite /all_strong_inv /multi_strong_inv/= !subnKC//.
      * move => Hstr x /andP[Hrsx Hxm]. have Hrs1lt: r < r + s'.+1 by rewrite -ltn_psubLR // subnn.
        rewrite -r_strong_inv_preserved. 3: apply Hone. apply Hstr.
        rewrite Hxm andbT. apply ltnW. all: by apply (ltn_leq_trans Hrs1lt).
      * by apply ltnW.
      * by apply ltnW.
      * by rewrite leqNgt Hrm.
    + have{1}->:r.+1 = nat_of_ord (Ordinal Hrm) by [].
      have Hrs': (Ordinal Hrm) + s' < m by rewrite -Hrs1.  have->: (Ordinal Hrs) = (Ordinal Hrs') by apply ord_inj.
      move => Hmul. apply (IH mx A' (Ordinal Hrm) Hrs'). apply (gauss_one_step_restrict_invar Hinv Hone).
      2: by []. move: Hstr. rewrite /all_strong_inv /multi_strong_inv/= !subnKC//.
      move => Hstr x /andP[Hrx Hxm]. rewrite -r_strong_inv_preserved. 3: apply Hone.
      apply Hstr. by rewrite (ltnW Hrx). by []. by apply ltnW.
Qed.

Lemma gauss_all_steps_restrict_beg_strong: forall {m n } (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: nat) (Hm: 0 < m) mx 
  (Hr: r < m),
  strong_inv A Hm Hmn ->
  gauss_all_steps_restrict_beg A Hmn r = Some mx ->
  all_strong_inv mx Hmn (Ordinal Hr).
Proof.
  move => m n A Hmn r Hm mx Hr.
  rewrite /gauss_all_steps_restrict_beg => Hstr.
  have->: (0%N = Ordinal Hm) by []. move => Hg.
  have Hinv: gauss_invar A (Ordinal Hm) (Ordinal Hm). by apply gauss_invar_init.
  by apply (all_strong_inv_preserved Hinv).
Qed.

Lemma gauss_all_steps_restrict_both_dirs: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n),
  gauss_all_steps_restrict A Hmn 0 = gauss_all_steps_restrict_beg A Hmn m.
Proof.
  move => m n A Hmn. by rewrite /gauss_all_steps_restrict /gauss_all_steps_restrict_beg subn0
    gauss_multiple_steps_restrict_extra.
Qed.

Lemma gauss_all_steps_restrict_beg_noop_equiv: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (Hm: 0 < m) r,
  strong_inv A Hm Hmn -> 
  gauss_all_steps_restrict_beg A Hmn r = Some (gauss_all_steps_restrict_beg_noop A Hmn r).
Proof.
  move => m n A Hmn Hm r Hstr. rewrite /gauss_all_steps_restrict_beg /gauss_all_steps_restrict_beg_noop.
  have->:0%N = Ordinal Hm by []. apply gauss_multiple_steps_restrict_noop_equiv.
  apply gauss_invar_init. move: Hstr. rewrite /strong_inv /all_strong_inv /multi_strong_inv/= !add0n subn0.
  move => Hstr x Hx. by apply Hstr.
Qed.

Definition gaussian_elim_restrict_noop {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) :=
  mk_identity (gauss_all_steps_restrict_beg_noop A Hmn m) Hmn m.-1.

Lemma gaussian_elim_restrict_noop_equiv': forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (Hm: 0 < m),
  strong_inv A Hm Hmn ->
  gaussian_elim_restrict A Hmn = Some (gaussian_elim_restrict_noop A Hmn).
Proof.
  move => m n A Hmn Hm Hstr. rewrite /gaussian_elim_restrict /gaussian_elim_restrict_noop /gauss_all_steps_restrict
  /gauss_all_steps_restrict_beg_noop subn0 gauss_multiple_steps_restrict_extra.
  have->: 0%N = Ordinal Hm by []. rewrite gauss_multiple_steps_restrict_noop_equiv //.
  move: Hstr. by rewrite /strong_inv /all_strong_inv/= subn0.
Qed.

Lemma gaussian_elim_restrict_noop_equiv: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (Hm: 0 < m),
  strong_inv A Hm Hmn ->
  gaussian_elim_restrict_noop A Hmn = gaussian_elim A.
Proof.
  move => m n A Hmn Hm Hstr. have: gaussian_elim_restrict A Hmn = gaussian_elim_restrict A Hmn by [].
  have{1}->: gaussian_elim_restrict A Hmn = Some(gaussian_elim_restrict_noop A Hmn) by 
    apply (gaussian_elim_restrict_noop_equiv' Hstr).
  have->: gaussian_elim_restrict A Hmn = Some(gaussian_elim A) by rewrite -(gaussian_elim_equiv _ _ Hm).
  by move => [Hmx].
Qed.

(** Casting Matrices*)

Lemma mk_identity_castmx: forall m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N) (A: 'M[F]_(m, n)) x,
  castmx Heq (mk_identity A Hmn x) = mk_identity (castmx Heq A) (cast_leq Heq Hmn) x.
Proof.
  move => m n m' n' Heq Hmn A x. rewrite /mk_identity -(cast_seq_pmap (fst Heq)).
  apply foldr_castmx. move => x' A'. rewrite sc_mul_castmx. f_equal.
  rewrite castmxE /= !cast_ordK. f_equal. f_equal. by apply ord_inj.
Qed.

Lemma add_mul_castmx: forall m n m' n' (Heq: (m = m') * (n = n'))
  (A: 'M[F]_(m, n)) c (r1 r2: 'I_m),
  castmx Heq (add_mul A c r1 r2) =
  add_mul (castmx Heq A) c (cast_ord Heq.1 r1) (cast_ord Heq.1 r2).
Proof.
  move => m n m' n' Heq A c r1 r2. rewrite -matrixP => x y.
  by rewrite castmxE !mxE cast_ord_switch !castmxE !cast_ordK.
Qed.

Lemma sub_all_rows_noif_castmx: forall  m n m' n' (Heq: (m = m') * (n = n'))
  (A: 'M[F]_(m, n)) (x: 'I_m),
  castmx Heq (sub_all_rows_noif A x) = sub_all_rows_noif (castmx Heq A) (cast_ord Heq.1 x).
Proof.
  move => m n m' n' Heq A x. rewrite /sub_all_rows_noif -(cast_ord_enum (fst Heq)).
  apply foldr_castmx => x' A'.
  case: (x' == x) /eqP => Hx.
  - by have->: cast_ord Heq.1 x' == cast_ord Heq.1 x by rewrite Hx.
  - have->: cast_ord Heq.1 x' == cast_ord Heq.1 x = false.
    case Hx': (cast_ord Heq.1 x' == cast_ord Heq.1 x) =>[|//]. apply (elimT eqP) in Hx'.
    by apply cast_ord_inj in Hx'.
    apply add_mul_castmx.
Qed.

Lemma all_cols_one_noif_castmx: forall  m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N) 
  (A: 'M[F]_(m, n)) (x: 'I_n),
  castmx Heq (all_cols_one_noif A x) =
  all_cols_one_noif (castmx Heq A) (cast_ord Heq.2 x).
Proof.
  move => m n m' n' Heq Hmn A x. rewrite /all_cols_one_noif -(cast_ord_enum (fst Heq)).
  apply foldr_castmx => x' A'. by rewrite sc_mul_castmx castmxE !cast_ordK.
Qed. 

Lemma gauss_one_step_restrict_noop_castmx: forall  m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N) 
  (A: 'M[F]_(m, n)) (x: 'I_m),
  castmx Heq (gauss_one_step_restrict_noop A x Hmn) =
  gauss_one_step_restrict_noop (castmx Heq A) (cast_ord Heq.1 x) (cast_leq Heq Hmn).
Proof.
  move => m n m' n' Heq Hmn A x. rewrite /gauss_one_step_restrict_noop sub_all_rows_noif_castmx
  all_cols_one_noif_castmx //=. f_equal. f_equal. by apply ord_inj.
Qed.
 
(*foldl version, this time with a nat function for [gauss_all_steps_restrict]*)
Lemma foldl_castmx: forall m n m' n' (A: 'M[F]_(m, n)) (Heq: (m = m') * (n = n')) 
  (f: 'M[F]_(m, n) -> nat -> 'M[F]_(m, n)) (g:  'M[F]_(m', n') -> nat -> 'M[F]_(m', n')) (l: seq nat),
  (forall (x: nat) (A: 'M[F]_(m, n)), castmx Heq (f A x) = g (castmx Heq A) x) ->
  castmx Heq (foldl f A l) = foldl g (castmx Heq A)  l.
Proof.
  move => m n m' n' A Heq f g l Hfg. move : A. elim : l => [//= | h t IH A /=].
  by rewrite IH Hfg. 
Qed.

Lemma gauss_multiple_steps_restrict_noop_castmx: forall m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N) (A: 'M[F]_(m, n)) x y,
  castmx Heq (gauss_multiple_steps_restrict_noop A Hmn x y) =
  gauss_multiple_steps_restrict_noop (castmx Heq A) (cast_leq Heq Hmn) x y.
Proof.
  move => m n m' n' Heq Hmn A x y. apply foldl_castmx => x' A'.
  case Hx': (x' < m)%N.
  - rewrite !insubT. by rewrite -(fst Heq). move => Hxm'.
    rewrite gauss_one_step_restrict_noop_castmx /=. f_equal. by apply ord_inj.
  - rewrite !insubF //. by rewrite -Heq.1.
Qed.

(*The final result we need*)

Lemma castmx_gaussian_restrict: forall m n m' n' (A: 'M[F]_(m, n)) (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N),
  castmx Heq (gaussian_elim_restrict_noop A Hmn) = gaussian_elim_restrict_noop (castmx Heq A) (cast_leq Heq Hmn).
Proof.
  move => m n m' n' A Heq Hmn. rewrite /gaussian_elim_restrict_noop. rewrite -matrixP => x y.
  rewrite mk_identity_castmx. f_equal. f_equal. 2: by rewrite (fst Heq).
  rewrite /gauss_all_steps_restrict_beg_noop. rewrite gauss_multiple_steps_restrict_noop_castmx. f_equal.
  by rewrite Heq.1.
Qed.


(*We also need to know that [strong_inv] does not change if we cast a matrix*)

Lemma leq_subst: forall m n m' n',
  m = m' ->
  n = n' ->
  m <= n ->
  m' <= n'.
Proof.
  by move => m n m' n' -> ->.
Qed.

Lemma submx_remove_col_castmx: forall  {m n m' n'} (A: 'M[F]_(m, n)) (Hmm: m = m') (Hnn: n = n') (Hmn: m <= n) r' j,
  submx_remove_col A Hmn r' j =
  submx_remove_col (castmx (Hmm, Hnn) A) (leq_subst Hmm Hnn Hmn) (eq_ord Hmm r') (eq_ord Hmm j).
Proof.
  move => m n m' n' A Hmm Hnn Hmn r' j. rewrite -matrixP => x y /=. rewrite !mxE /=.
  rewrite castmxE /=. case Hyj: (y < j); f_equal; by apply ord_inj.
Qed.

Lemma submx_add_row_castmx: forall  {m n m' n'} (A: 'M[F]_(m, n)) (Hmm: m = m') (Hnn: n = n') (Hmn: m <= n) r' j,
  submx_add_row A Hmn r' j =
  submx_add_row (castmx (Hmm, Hnn) A) (leq_subst Hmm Hnn Hmn) (eq_ord Hmm r') (eq_ord Hmm j).
Proof.
  move => m n m' n' A Hmm Hnn Hmn r' j. rewrite -matrixP => x y /=. rewrite !mxE /=.
  rewrite castmxE /=. case Hyj: (x < r'); f_equal; by apply ord_inj.
Qed.

Lemma strong_inv_castmx: forall {m n m' n'} (A: 'M[F]_(m, n)) (Hmm: m = m') (Hnn: n = n') (Hmn: m <= n) (x: 'I_m),
  all_strong_inv A Hmn x <-> all_strong_inv (castmx (Hmm, Hnn) A) (leq_subst Hmm Hnn Hmn) (eq_ord Hmm x).
Proof.
  move => m n m' n' A Hmm Hnn Hmn x. rewrite /all_strong_inv /multi_strong_inv /r_strong_inv /= !subnKC; last first.
  by apply ltnW. subst. by apply ltnW. split; move => Hstr r' Hxr'.
  - remember (eq_ord (esym Hmm) r') as r.  move: Hstr => /(_ r). rewrite -{3}Hmm in Hxr'. rewrite Heqr /= => /(_ Hxr') => [[Hcol Hrow]].
    have ->: r' = eq_ord Hmm r by subst; apply ord_inj. rewrite /=.
    split; move => j Hjr;remember (eq_ord (esym Hmm) j) as j';  have ->:j = eq_ord Hmm j' by subst; apply ord_inj.
    + rewrite -submx_remove_col_castmx Heqr. apply Hcol. by subst.
    + rewrite -submx_add_row_castmx Heqr. apply Hrow. by subst.
  - remember (eq_ord Hmm r') as r.  move: Hstr => /(_ r). rewrite -{3}Hmm. rewrite Heqr /= => /(_ Hxr') => [[Hcol Hrow]].
    split; move => j Hjr;remember (eq_ord Hmm j) as j'.
    + move: Hcol => /(_ j'). move: Hjr. rewrite Heqj' /= => Hjr /(_ Hjr).
      by rewrite -submx_remove_col_castmx.
    + move: Hrow => /(_ j'). move: Hjr. rewrite Heqj' /= => Hjr /(_ Hjr).
      by rewrite -submx_add_row_castmx.
Qed.

Lemma castmx_twice: forall m1 m2 m3 n1 n2 n3 (A: 'M[F]_(m1, n1)) 
  (Hm12: m1 = m2) (Hm23: m2 = m3) (Hn12: n1 = n2) (Hn23: n2 = n3),
  castmx (Hm23, Hn23) (castmx (Hm12, Hn12) A) =
  castmx (etrans Hm12 Hm23, etrans Hn12 Hn23) A.
Proof.
  move => m1 m2 m3 n1 n2 n3 A Hm12 Hm23 Hn12 Hn23. rewrite -matrixP => x y.
  rewrite !castmxE /=. by f_equal; apply ord_inj.
Qed.

(** [strong_inv] for [rowmx]*)

(*We want to show that if strong_inv A holds, then strong_inv (row_mx A) holds*)

Lemma submx_remove_col_rowmx: forall m n (A B: 'M[F]_(m, n)) (Hmn: (m <= n)%N) (Hmn' : (m <= n + n)%N) r j,
  submx_remove_col A Hmn r j =
  submx_remove_col (row_mx A B) Hmn' r j.
Proof.
  move => m n A B Hmn Hmn' r j. rewrite -matrixP => x y.
  rewrite !mxE /=. case Hyj: (y < j)%N.
  - pose proof (splitP (widen_ord (ltnW (ltn_leq_trans (ltn_ord r) Hmn')) y)).
    case : X => [j' /= Hj' | k /= Hk].
    + f_equal. by apply ord_inj.
    + have Hny: (n <= y)%N by rewrite Hk leq_addr.
      have: (y < n)%N. have Hyr : (y < r)%N by [].
        have Hym: (y < m)%N by apply (ltn_trans Hyr). by apply (ltn_leq_trans Hym).
      by rewrite ltnNge Hny.
  - pose proof (splitP (ord_widen_succ (ltn_leq_trans (ltn_ord r) Hmn') y)).
    case : X => [j' /= Hj' | k /= Hk].
    + f_equal. by apply ord_inj.
    + have: (y.+1 < n)%N. have Hyr: (y < r)%N by [].
      have Hym: (y.+1 < m)%N by apply (leq_ltn_trans Hyr). by apply (ltn_leq_trans Hym).
      have: (n <= y.+1)%N. by rewrite Hk leq_addr. rewrite ltnNge. by move ->.
Qed. 

Lemma submx_add_row_rowmx: forall m n (A B: 'M[F]_(m, n)) (Hmn: (m <= n)%N) (Hmn' : (m <= n + n)%N) r j,
  submx_add_row A Hmn r j =
  submx_add_row (row_mx A B) Hmn' r j.
Proof.
  move => m n A B Hmn Hmn' r j. rewrite -matrixP => x y.
  rewrite !mxE /=. 
  pose proof (splitP (widen_ord (leq_trans (ltn_ord r) Hmn') y)).
  case : X => [j' /= Hj' | k /= Hk].
  - f_equal. by apply ord_inj.
  - have Hyr: (y < r.+1)%N by []. have Hrn : (r.+1 <= n)%N.
    have Hrm: (r.+1 <= m)%N by []. by apply (ltn_leq_trans Hrm).
    have Hyn: (y < n)%N. have Hyr': (y < r.+1)%N by []. by apply (ltn_leq_trans Hyr').
    have : (n <= y)%N by rewrite Hk leq_addr. by rewrite leqNgt Hyn.
Qed. 

Lemma strong_inv_row_mx: forall m n (A B: 'M[F]_(m, n)) (Hmn: (m <= n)%N) (Hmn' : (m <= n + n)%N) (r: 'I_m),
  all_strong_inv A Hmn r ->
  all_strong_inv (row_mx A B) Hmn' r.
Proof.
  move => m n A B Hmn Hmn' r. rewrite /all_strong_inv /multi_strong_inv /r_strong_inv => Hstr r' Hr'. split.
  - move => j Hj. rewrite -submx_remove_col_rowmx. move : Hstr => /(_ r' Hr') => [[Hcol Hrow]].
    by apply Hcol.
  - move => j Hj. rewrite -submx_add_row_rowmx. move : Hstr => /(_ r' Hr') => [[Hcol Hrow]].
    by apply Hrow.
Qed.

(*Finally, [strong_inv] is actually a stronger condition than invertibility*)

Lemma lt_subst: forall (n m p: nat),
  (n < m)%N ->
  m = p ->
  (n < p)%N.
Proof.
  move => n m p Hn Hmp. by rewrite -Hmp.
Qed.

Lemma strong_inv_unitmx: forall {n} (A: 'M[F]_n) (H: (n <= n)%N) (r: 'I_n),
  all_strong_inv A H r ->
  A \in unitmx.
Proof.
  move => n A H r. rewrite /all_strong_inv /multi_strong_inv /r_strong_inv subnKC; last first. by apply ltnW.
  have: (0 <= n)%N by []. rewrite leq_eqVlt => /orP[/eqP H0n | Hn].
  -  move => Hstr.
     have->: A = (1%:M)%R. subst. apply matrix_zero_rows. apply unitmx1.
  - have Hr: (r <= (pred_ord Hn))%N by rewrite /= -ltn_pred.
    have Htriv: r <= pred_ord Hn < n by rewrite Hr andTb. 
    move => /(_ (pred_ord Hn) Htriv) => [[Hcol Hrow]].
    move : Hrow => /(_ (pred_ord Hn) (leqnn _)).
    have Hpred: n = (pred_ord Hn).+1 by rewrite /= (ltn_predK Hn).
    have->: submx_add_row A H (pred_ord Hn) (pred_ord Hn) = (castmx (Hpred, Hpred) A) .
    { rewrite -matrixP => x y. rewrite !mxE castmxE /=. f_equal. 2: by apply ord_inj.
      case Hx: (x < n.-1)%N.
      - by apply ord_inj.
      - have Hxn: (x < (pred_ord Hn).+1)%N by [].
        have {}Hxn: (x < n)%N. apply (lt_subst Hxn). by []. (*no idea why rewriting directly gives dep type error*)
        have: (x <= n.-1)%N by rewrite -ltn_pred. rewrite leq_eqVlt => /orP[/eqP Hxn1 | Hcon].
        + by apply ord_inj.
        + by rewrite Hcon in Hx. }
    by rewrite unitmx_castmx.
Qed.

End Gauss.