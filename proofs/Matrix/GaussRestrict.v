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
Definition all_cols_one_noif {m n} (A: 'M[F]_(m, n)) (c: 'I_n) :=
  foldr (fun x acc => sc_mul acc (A x c)^-1 x) A (ord_enum m).

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
(*
(*First, we define the intermediate functions and gaussian elimination steps*)
(*For this one in particular, we need a generalized version, since in the C proof, we need to reason about
  intermediate steps (namely, we need to know all entries in the rth column are nonzero*)
Definition all_cols_one_noif {m n} (A: 'M[F]_(m, n)) (c: 'I_n) :=
  foldr (fun x acc => sc_mul acc (A x c)^-1 x) A (ord_enum m).
*)
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

(*TODO: see what foldl results I need about [all_cols_one_val]*)
Definition all_cols_one_noif_l {m n} (A: 'M[F]_(m, n)) (c: 'I_n) :=
  foldl (fun acc x => sc_mul acc (A x c)^-1 x) A (ord_enum m).

Lemma all_cols_one_noif_foldl: forall {m n}  (A: 'M[F]_(m, n)) (c: 'I_n) ,
  all_cols_one_noif A c = all_cols_one_noif_l A c.
Proof.
  move => m n A c. rewrite /all_cols_one_noif /all_cols_one_noif_l. 
  have {2}->: ord_enum m = rev (rev (ord_enum m)) by rewrite revK. rewrite foldl_rev.
  apply mx_row_transform_rev.
  - move => A' i' j' r'.
    rewrite /sc_mul mxE /negb. by case: (i' == r').
  - move => A' B' r Hin Hout j'. by rewrite /sc_mul !mxE eq_refl Hin.
  - apply ord_enum_uniq.
Qed.

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
(*TODO: use bind?*)
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

(*TODO: move*) 
Lemma xrow_rr : forall {m n } (A: 'M[F]_(m, n)) (r: 'I_m),
  xrow r r A = A.
Proof.
  move => m n A r. rewrite -matrixP => x y. rewrite xrow_val.
  case : (x == r) /eqP => [Hxr | Hxr//]. by rewrite Hxr.
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

(*old
Definition gauss_one_step_restrict {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn : m <= n) :=
  let c := widen_ord Hmn r in
  let A1 := all_cols_one_noif A c in
  sub_all_rows_noif A1 r.
*)
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

(*ALT: r-strong-invertibility refers to a specific r*)
Definition r_strong_inv {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: 'I_m) :=
  (forall j : 'I_m, j < r -> (submx_remove_col A Hmn r j) \in unitmx) /\
  (forall j : 'I_m, r <= j -> (submx_add_row A Hmn r j) \in unitmx).

(*

(*The condition we need to have at the beginning and preserve*)
(*Note that we only require the condition starting from a given r value. This is because the condition
  will only be partially preserved through the gaussian steps*)
Definition strong_inv {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: 'I_m) :=
  forall (r' : 'I_m), r <= r' ->
    (forall (j: 'I_m), j < r' -> (submx_remove_col A Hmn r' j) \in unitmx) /\
    (forall (j : 'I_m), r' <= j -> (submx_add_row A Hmn r' j) \in unitmx).*)

(*TODO: see*)
Lemma nat_of_ord_neq: forall {m} (x y : 'I_m),
  x != y ->
  nat_of_ord x != nat_of_ord y.
Proof.
  move => m x y Hxy. case: (nat_of_ord x == nat_of_ord y) /eqP => [/= Hyx | //].
  have Heq: x == y. apply /eqP. by apply ord_inj. by rewrite Heq in Hxy.
Qed.


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
          have->//=: (nat_of_ord i != nat_of_ord j). by apply nat_of_ord_neq in Hij.
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
(*
(*old again*)

(* The second part: show that one step of restricted gaussian elimination is equivalent to one step
  of regular gaussian elimination iff the current matrix has a row of all zeroes (and hence iff it
  is strongly invertible)*)
Lemma gauss_one_step_restrict_equiv_zeroes:  forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n),
  ((gauss_one_step_restrict A r Hmn, insub (r.+1)) = gauss_one_step A r (widen_ord Hmn r)) <->
  (forall (x : 'I_m), A x (widen_ord Hmn r) != 0).
Proof.
  move => m n A r Hmn. split.
  - (*If equal, then all zeroes*)
    rewrite /gauss_one_step_restrict /gauss_one_step.
    (* first, we know that [fst_nonzero A (widen_ord Hmn r) r] is not None, or else we get an easy contradiction*)
    case Hfst: (fst_nonzero A (widen_ord Hmn r) r) => [k |//]; last first.
    + move => [Ha Hr]; move : Hr. case Hr1 : (r.+1 < m). rewrite insubT => [[Hr]].
      have : nat_of_ord r = (nat_of_ord r).+1 by rewrite -{1}Hr /=. move => Hr'.
      exfalso. by apply (n_Sn (nat_of_ord r)).
      by rewrite insubF.
    + (*now, need to prove that A r r != 0 (ie: fst_nonzero A (widen_ord Hmn r) = Some r)*)
      move => [Heq]. have Hrr : A r (widen_ord Hmn r) != 0. {
        case Hrr0: (A r (widen_ord Hmn r) == 0) => [|//].
        (* Proof idea: know rth row of [all_cols_one_noif] is all zeroes, so that is true of
           [ sub_all_rows_no_if] mx, by equality true of [sub_all_rows] mx, but this cannot be*)
        have Hcols1: (forall x, (all_cols_one_noif A (widen_ord Hmn r)) r x = 0). {
          move => x. rewrite all_cols_one_noif_val. apply (elimT eqP) in Hrr0. 
          by rewrite Hrr0 GRing.invr0 GRing.mulr0. }
        have Hrows1: (forall x, (sub_all_rows_noif (all_cols_one_noif A (widen_ord Hmn r)) r) r x = 0). {
          move => x. by rewrite sub_all_rows_noif_val eq_refl Hcols1. }
        have Hk: A k (widen_ord Hmn r) != 0. { move: Hfst. by rewrite fst_nonzero_some_iff => [[_ [Htriv _]]]. }
        have Hswap1: (xrow k r A) r (widen_ord Hmn r) != 0. {
          rewrite xrow_val eq_refl. case : (r == k) /eqP => [Hrk | Hrk//]. by rewrite {1}Hrk. }
        have Hcols2: (all_cols_one (xrow k r A) (widen_ord Hmn r)) r (widen_ord Hmn r) != 0
          by rewrite all_cols_one_val /= (negbTE Hswap1) GRing.Theory.mulfV // GRing.oner_neq0.
        have: (sub_all_rows (all_cols_one (xrow k r A) (widen_ord Hmn r)) r (widen_ord Hmn r)) 
          r (widen_ord Hmn r) != 0 by rewrite sub_all_rows_val eq_refl. 
        by rewrite -Heq Hrows1 eq_refl.
      }
      (* Therefore, k == r*)
      have Hfst': fst_nonzero A (widen_ord Hmn r) r = Some r. {
        rewrite fst_nonzero_some_iff. repeat split.
        - by rewrite leqnn.
        - by [].
        - move => x /andP[Hxr Hrx]. move: Hrx. by rewrite ltnNge Hxr.
      }
      rewrite Hfst' in Hfst. case : Hfst => Hrk. rewrite {Hfst'}. rewrite -Hrk in Heq. rewrite {Hrk k}.
      rewrite xrow_rr in Heq.
      (*Idea: if A x r == 0, then [sub_all_rows_noif] x r != 0 (bc we subtract a nonzero value)
        but [sub_all_rows] x r == 0 (because we skip this entry entirely)*)
      move => x. case Haxr : (A x (widen_ord Hmn r) == 0) => [|//]. apply (elimT eqP) in Haxr.
      have Hcols1: (all_cols_one_noif A (widen_ord Hmn r)) x (widen_ord Hmn r) = 0
        by rewrite all_cols_one_noif_val Haxr GRing.invr0 GRing.mulr0.
      have Hxr: x == r = false. apply /eqP. move => Hxr. rewrite Hxr in Haxr.
        move : Hrr. by rewrite Haxr eq_refl.
      have Hrows1: (sub_all_rows_noif (all_cols_one_noif A (widen_ord Hmn r)) r) x (widen_ord Hmn r) != 0. {
        rewrite sub_all_rows_noif_val.  rewrite Hcols1 all_cols_one_noif_val GRing.Theory.mulfV // Hxr.
        apply /eqP. move => H10. have: (GRing.zero F) = 1.  apply (GRing.subr0_eq H10). rewrite {H10} => /eqP Hcon.
        move: Hcon. by rewrite eq_sym GRing.oner_eq0. }
      have Hcols2: (all_cols_one A (widen_ord Hmn r)) x (widen_ord Hmn r) = 0 
        by rewrite all_cols_one_val /= Haxr eq_refl.
      have Hrows2: (sub_all_rows (all_cols_one A (widen_ord Hmn r)) r (widen_ord Hmn r)) x (widen_ord Hmn r) = 0
        by rewrite sub_all_rows_val Hxr Hcols2 eq_refl.
      move: Hrows1. by rewrite Heq Hrows2 eq_refl.
  - (*Other direction: if all zeroes, then equal*)
    move => Hallz. rewrite /gauss_one_step_restrict /gauss_one_step.
    have->: fst_nonzero A (widen_ord Hmn r) r = Some r. { rewrite fst_nonzero_some_iff; repeat split.
      by rewrite leqnn. by rewrite Hallz. move => x /andP[Hxr Hrx]. move: Hrx. by rewrite ltnNge Hxr. }
    rewrite xrow_rr.
    have->//: sub_all_rows_noif (all_cols_one_noif A (widen_ord Hmn r)) r = 
      sub_all_rows (all_cols_one A (widen_ord Hmn r)) r (widen_ord Hmn r).
    (*First, this will be helpful*)
    have Hcols: all_cols_one_noif A (widen_ord Hmn r) = all_cols_one A (widen_ord Hmn r). {
      rewrite -matrixP => x y. by rewrite all_cols_one_noif_val all_cols_one_val/= (negbTE (Hallz x)). }
    rewrite -matrixP => x y. rewrite sub_all_rows_noif_val sub_all_rows_val.
    case Hxr : (x == r).
    + by rewrite all_cols_one_noif_val all_cols_one_val/= (negbTE (Hallz x)).
    + rewrite Hcols. have->//: all_cols_one A (widen_ord Hmn r) x (widen_ord Hmn r) == 0 = false.
      by rewrite all_cols_one_val/= (negbTE (Hallz x)) GRing.mulfV // GRing.oner_eq0.
Qed.

(* Now we give the condition in terms of strong invertibility*)
Lemma gauss_one_step_restrict_equiv_iff: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n),
  gauss_invar A r r ->
  ((gauss_one_step_restrict A r Hmn, insub (r.+1)) = gauss_one_step A r (widen_ord Hmn r)) <->
  r_strong_inv A Hmn r.
Proof.
  move => m n A r Hmn Hinv. by rewrite gauss_one_step_restrict_equiv_zeroes r_strong_inv_all_zeroes_iff.
Qed.

(* TODO: show preservation iff*)
*)

(* Now we want to generalize this result to multiple steps of Gaussian elimination. We will need a stronger
  lemma to get the right induction hypothesis, so we define the notion of all-strong-invertibility, where
  A is x-strongly invertible for all r <= x < r + s*)

Definition all_strong_inv {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) (s: nat) :=
  forall (x: 'I_m), r <= x < r + s -> r_strong_inv A Hmn x.

Lemma all_strong_inv_expand : forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) (Hr1m: r.+1 < m) (s: nat),
  all_strong_inv A Hmn r s.+1 <-> r_strong_inv A Hmn r /\ all_strong_inv A Hmn (Ordinal Hr1m) s.
Proof.
  move => m n A Hmn r Hr1m s. rewrite /all_strong_inv. split.
  - move => Hinv. split. apply Hinv. by rewrite leqnn -ltn_subLR // subnn.
    move => x Hx. apply Hinv. move: Hx. rewrite /= => /andP[Hrx Hxr1s].
    have->/=: r <= x by apply ltnW. move: Hxr1s. by rewrite -(addn1 r) -addnA (add1n s).
  - move => [Hrinv Hinv] x /andP[Hrx Hxrs]. move: Hrx. rewrite leq_eqVlt => /orP[/eqP Hrx | Hrx].
    + by have->: x = r by apply ord_inj.
    + apply Hinv. by rewrite /= Hrx -(addn1 r) -addnA (add1n s).
Qed.

(* Analagously, we define a function to peform s steps of Restricted Gaussian Elimination*)
(*TODO: use bind, this is ugly*)
Definition gauss_multiple_steps_restrict {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) r s : option 'M[F]_(m, n) :=
foldl (fun oA r' => match (insub r') with
                       | Some r'' => match oA with
                                     | None => None
                                     | Some A' => match gauss_one_step_restrict A' r'' Hmn with
                                                  | None => None
                                                  | Some mx => Some mx
                                                 end
                                     end
                       | None => oA
                      end) (Some A) (iota r s).

(*


Definition gauss_multiple_steps_restrict {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) r s :=
foldl (fun A' r' => match (insub r') with
                       | Some r'' => gauss_one_step_restrict A' r'' Hmn
                       | None => A'
                      end) A (iota r s).
*)

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

(*
Lemma gauss_multiple_steps_restrict_expand: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r : 'I_m) s,
  gauss_multiple_steps_restrict A Hmn r s.+1 = gauss_multiple_steps_restrict (gauss_one_step_restrict A r Hmn) Hmn r.+1 s.
Proof.
  move => m n A Hmn r s. rewrite /gauss_multiple_steps_restrict /= insubT //= => Hrm.
  by have->: Ordinal Hrm = r by apply ord_inj.
Qed.*)



(* There is a degenerate case: when all remaining rows consist of all zeroes, [gauss_multiple_steps_restrict]
   does not change these rows. We need to prove this because it causes a bit of a problem in the lemma we want *)
(*
Lemma gauss_one_step_restrict_all_zero: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n),
  (forall (c: 'I_n), A r c = 0) ->
  forall (rz : 'I_m), (forall c: 'I_n, A rz c = 0) -> (forall c: 'I_n, (gauss_one_step_restrict A r Hmn rz c = 0)).
Proof.
  move => m n A r Hmn Hzero rz Hrz c. rewrite /gauss_one_step_restrict sub_all_rows_noif_val.
  case: (rz == r) /eqP => [Hreq | Hreq]; rewrite !all_cols_one_noif_val.
  - by rewrite Hreq !Hzero // GRing.invr0 GRing.mul0r //.
  - by rewrite !Hzero GRing.mul0r GRing.subr0 Hrz GRing.mul0r.
Qed.

Lemma gauss_multiple_steps_restrict_overflow: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) r s,
   m <= r ->
  gauss_multiple_steps_restrict A Hmn r s = A.
Proof.
  move => m n A Hmn r s Hmr. move : A r Hmr. elim : s => [A r Hmr //= | s' IH /= A r Hmr].
  rewrite /gauss_multiple_steps_restrict /= insubF //.
  move: IH. rewrite /gauss_multiple_steps_restrict. move ->. by []. by apply (leq_trans Hmr).
  by rewrite ltnNge Hmr. 
Qed.

(*Suppose all the rest of the rows are zero. Then any rows that were all zeroes before are still all zero*)
Lemma gauss_multiple_steps_restrict_rest_all_zero: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n) s,
  (forall (r': 'I_m) (c: 'I_n), r <= r' -> A r' c = 0) ->
  forall (rz : 'I_m), (forall (c: 'I_n), A rz c = 0) -> 
    (forall (c: 'I_n), (gauss_multiple_steps_restrict A Hmn r s rz c) = 0).
Proof.
  move => m n A r Hmn s. move: A r. elim : s => [/= A r Hzero r' c Hr' | s' IH /= A r Hzero r' c Hr'].
  - by rewrite /gauss_multiple_steps_restrict /=.
  - rewrite gauss_multiple_steps_restrict_expand.
    case Hr1m : (r.+1 < m).
    + have->: r.+1 = nat_of_ord (Ordinal Hr1m) by []. rewrite IH //.
      * move => r'' c' /= Hr''. apply gauss_one_step_restrict_all_zero.
        -- move => c''. by apply Hzero.
        -- move => c''. apply Hzero. by apply ltnW.
      * move => c'. apply gauss_one_step_restrict_all_zero.
        -- move => c''. by apply Hzero.
        -- by [].
    + rewrite gauss_multiple_steps_restrict_overflow //. apply gauss_one_step_restrict_all_zero.
      * move => c'. by apply Hzero.
      * by [].
      * by rewrite leqNgt Hr1m.
Qed.

(*The corollary that we need: if all of the rest of the rows are zero, then they are still zero*)
Lemma gauss_multiple_steps_restrict_rest_all_zero': forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n) s,
  (forall (r': 'I_m) (c: 'I_n), r <= r' -> A r' c = 0) ->
  forall (r': 'I_m) (c: 'I_n), r <= r' -> gauss_multiple_steps_restrict A Hmn r s r' c = 0.
Proof.
  move => m n A r Hmn s Hrest r' c' Hr'. apply gauss_multiple_steps_restrict_rest_all_zero.
  - apply Hrest.
  - move => c. by apply Hrest.
Qed.*)

Lemma gauss_multiple_steps_restrict_overflow: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) r s,
   m <= r ->
  gauss_multiple_steps_restrict A Hmn r s = Some A.
Proof.
  move => m n A Hmn r s Hmr. move : A r Hmr. elim : s => [A r Hmr //= | s' IH /= A r Hmr].
  rewrite /gauss_multiple_steps_restrict /= insubF //.
  move: IH. rewrite /gauss_multiple_steps_restrict. move ->. by []. by apply (leq_trans Hmr).
  by rewrite ltnNge Hmr. 
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

(* A corollary: if we have all_strong_inv for any r' > r, this is preserved *)
Lemma all_strong_inv_preserved: forall {m n} (A A': 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m) (r' : 'I_m) s,
  r < r' ->
  gauss_one_step_restrict A r Hmn = Some A' ->
  all_strong_inv A Hmn r' s <-> all_strong_inv A' Hmn r' s.
Proof.
  move => m n A A' Hmn r r' s Hrr' Hgauss. rewrite /all_strong_inv. split; move => Hinv x /andP[Hrx Hxr].
  - rewrite -r_strong_inv_preserved. apply Hinv. by rewrite Hrx Hxr. by apply (ltn_leq_trans Hrr'). by [].
  - rewrite r_strong_inv_preserved. apply Hinv. by rewrite Hrx Hxr. by apply (ltn_leq_trans Hrr'). by [].
Qed. 

(*The lemma we want to show:[gauss_multiple_steps_restrict A r s] equals [gauss_multiple_steps A r s] iff
  [all_strong_inv A r s] holds (as long as A satisfies the Gaussian invariant) *)
Lemma gauss_multiple_steps_restrict_equiv_iff: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n) s,
  gauss_invar A r r ->
  (gauss_multiple_steps_restrict A Hmn r s = Some(gauss_multiple_steps A (Some r) (Some (widen_ord Hmn r)) s)) 
  <-> all_strong_inv A Hmn r s.
Proof.
  move => m n A r Hmn s Hinv. move: A r Hinv. elim : s => [/= A r Hinv | s' IH A r Hinv].
  - rewrite /gauss_multiple_steps_restrict/=. split => [_|//]. rewrite /all_strong_inv => x.
    rewrite addn0 => /andP[Hrx Hxr]. move: Hxr. by rewrite ltnNge Hrx.
  - split.
    + (*equality -> all_strong_inv*)
      rewrite /= gauss_multiple_steps_restrict_expand. case Hone: (gauss_one_step_restrict A r Hmn) => [mx |//].
      have Hsome: (gauss_one_step_restrict A r Hmn) by rewrite Hone. apply gauss_one_step_restrict_some_equiv_full in Hsome.
      case : Hsome => [Hg1  Hg2]. assert (Hg1' := Hg1). assert(Hg2' := Hg2). 
      case Hgone : (gauss_one_step A r (widen_ord Hmn r)) => [A' or]. move: Hg1. move: Hg2.
      rewrite !Hgone/=. move ->. rewrite Hone => [[Hmxa]]. rewrite -!Hmxa. 
      (*Now need to deal with ordinals in order to apply the IH*)
      case Hr1m: (r.+1 < m); last first. 
      * (*overflow*)
        move => _. rewrite /all_strong_inv. move => x /andP[Hrx Hxrs]. move: Hrx.
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
           move => Hall. apply (all_strong_inv_expand _ _ Hr1m). split. by apply gauss_one_step_restrict_equiv_iff.
           rewrite all_strong_inv_preserved. apply Hall. 2: apply Hone. by [].
        -- have Hinv': gauss_invar A r (widen_ord Hmn r) by apply Hinv. apply gauss_one_step_invar in Hinv'.
           move: Hinv'. rewrite Hgone Hmxa/=. move: Hg2'. rewrite Hgone/=. move ->.
           by rewrite ord_bound_convert_plus.
    + (*all_strong_inv -> equality*)
      rewrite /= gauss_multiple_steps_restrict_expand. move => Hall.
      have Hrstr: r_strong_inv A Hmn r. { move: Hall. rewrite /all_strong_inv => /(_ r) Hrinv. apply Hrinv.
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
        move: Hall. rewrite (all_strong_inv_expand _ _ Hr1m) => [[Hrstr' Hall]].
        rewrite Hgone in Honeq. rewrite /= in Honeq.
        rewrite -all_strong_inv_preserved. apply Hall. 2: apply Honeq. by [].
      * rewrite insubF //= gauss_multiple_steps_row_none gauss_multiple_steps_restrict_overflow //.
        by rewrite leqNgt Hr1m.
Qed.

(*TODO: extend this to the full algo after making sure we have the LC=1 part down, then see which lemmas and 
  definitions we need - most of them should no longer be needed*)

(* Finally, we can easily extend this to the full Gaussian elimination algorithm by setting r=0. We give
   a separate definition of (full) strong invertibility, the exact condition under which these two algorithms
   are equal *)
Definition strong_inv {m n} (A: 'M[F]_(m, n)) (H0m: 0 < m) (Hmn: m <= n) :=
  all_strong_inv A Hmn (Ordinal H0m).

(*Oh wait, we need to do LC's 1 first*)

(* The full restricted gaussian elimination algorithm*)

(*TODO: the theorem we want*)
Theorem gaussian_elim_equiv: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (Hm: 0 < m),
  strong_inv A Hmn (Ordinal Hm) <-> gaussian_elim_restrict A Hmn = Some(gaussian_elim A).


(*old stuff that may or may not be relevant:

(* The lemma we want to show: [gauss_multiple_steps_restrict A r s] equals [gauss_multiple_steps A r s] iff
  [all_strong_inv A r s] holds (as long as A satisfies the Gaussian invariant) *)
(*TODO: maybe theorem*)
Lemma gauss_multiple_steps_restrict_equiv_iff: forall {m n} (A: 'M[F]_(m, n)) (r: 'I_m) (Hmn: m <= n) s,
  colsub (widen_ord Hmn) A \in unitmx -> (*the first m x m submatrix is invertible*)
  gauss_invar A r r ->
  (gauss_multiple_steps_restrict A Hmn r s = gauss_multiple_steps A (Some r) (Some (widen_ord Hmn r)) s) 
  <-> all_strong_inv A Hmn r s.
Proof.
  move => m n A r Hmn s Hun Hinv. move : A Hun Hinv. elim : s => [/= A Hun Hinv |s' IH A Hun Hinv].
  - rewrite /gauss_multiple_steps_restrict/=. split => [_|//]. rewrite /all_strong_inv => x.
    rewrite addn0 => /andP[Hrx Hxr]. move: Hxr. by rewrite ltnNge Hrx.
  - (*rewrite gauss_multiple_steps_restrict_expand.*) split.
    + (*equality -> all_strong_inv*)
      Print gauss_one_step.
      (* If fst_nonzero A c r = None, hit degenerate case - all rest become zero and so gaussian_elim has
         rows of zeroes - contradicts invertibility hypothesis, since this is preserved *)
      (* To see why this is a problem - consider 2n x 2n matrix where bottom n x 2n is all zeroes - alg same on there
         but clearly not strong inv*)
      move => Hgausseq.
      have [k Hfst]: exists k, fst_nonzero A (widen_ord Hmn r) r = Some k. {
        case Hfst: (fst_nonzero A (widen_ord Hmn r) r) => [k' |].
        - by exists k'.
        - have Hresz: forall (r': 'I_m) (c: 'I_n), r <= r' -> gauss_multiple_steps_restrict A Hmn r s'.+1 r' c = 0. {
            move => r' c Hrr'. rewrite gauss_multiple_steps_restrict_expand.
            have Hrzero: forall c0 : 'I_n, gauss_one_step_restrict A r Hmn r' c0 = 0. {
              move => c'. rewrite /gauss_one_step_restrict sub_all_rows_noif_val.
              case Hrreq: (r' == r).
              - by rewrite all_cols_one_noif_val (fst_nonzero_none Hfst Hrr') GRing.invr0 GRing.mulr0.
              - by rewrite !all_cols_one_noif_val (fst_nonzero_none Hfst Hrr') (fst_nonzero_none Hfst (leqnn r))
                 !GRing.invr0 !GRing.mulr0 GRing.subrr. }
            case Hr1m : (r.+1 < m).
            + have->: r.+1 = nat_of_ord (Ordinal Hr1m) by [].
              apply gauss_multiple_steps_restrict_rest_all_zero.
              * move => r'' c' /= Hr''.
                rewrite /gauss_one_step_restrict sub_all_rows_noif_val.
                have->: r'' == r = false by apply gtn_eqF.
                by rewrite !all_cols_one_noif_val (fst_nonzero_none Hfst (leqnn r)) (fst_nonzero_none Hfst (ltnW Hr''))
                !GRing.invr0 !GRing.mulr0 GRing.subrr.
              * apply Hrzero. 
            + rewrite gauss_multiple_steps_restrict_overflow. apply Hrzero. by rewrite leqNgt Hr1m.
          }
          have Hcol: colsub (widen_ord Hmn) (gauss_multiple_steps A (Some r) (Some (widen_ord Hmn r)) s'.+1) \in unitmx
            by rewrite -gauss_multiple_steps_colsub_unitmx.
          have Hcol': colsub (widen_ord Hmn) (gauss_multiple_steps A (Some r) (Some (widen_ord Hmn r)) s'.+1) \notin unitmx.
            { apply (@row_zero_not_unitmx _ _ _ r). move => c. by rewrite -Hgausseq mxE Hresz. }
          by rewrite Hcol in Hcol'.
      }
      (* Next step: injectivity lemma*)

row_zero_not_unitmx
          
          Search unitmx 0.
          Search gauss_multiple_steps.

 Search (_ <= _) negb.


 rewrite /gauss_one_step_restrict sub_all_rows_noif_val.
          }
                have->: r'' == r = false by apply gtn_eqF.



 rewrite /=.
              by [].

 Search 0^-1.


 Check fst_nonzero_none. in Hfst.
      case Hfst: (fst_nonzero A c r).


      (* Need to know that we do not have all rows of zeroes on row r or below - if we do, then both are
         the same, I believe*)
      (*ugh - need to prove that gauss_one_step does not hit None case - if it does, all values in resulting col
        are 0 and they stay that way, in restrict - those turn into all zero rows and will be for the rest of it
        actually not confident*)
      (* 1 way - require that there is no row of zeroes in A - then we show that in gauss_all_steps, no row of zeroes
         in this (not true - need invertibility) - if None, get that all rows become zeroes - need separate lemma, if all rows after all zeroes,
         then matrix is unchanged (indirect) dont love it, but I think ok for now*)
      
      (* dont love requiring invertibility but i think we have to - otherwise can get to situation where we have
         row of zeroes for rest and then all bets are off*)

 Search (_ < _) negb.


 Search iota. 


 split.
  - (*equality -> all_strong_inv*)
    


(* Old proofs *)


(*Now, we show the crucial property that ensures that this condition is sufficient for the restricted
  Gaussian elimination: if a matrix satisfies [strong_inv] and the gaussian invariant,
  then all the entries in column r are nonzero.*)
Lemma strong_inv_nonzero_cols: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: 'I_m),
  gauss_invar A r r ->
  strong_inv A Hmn r ->
  (forall (x : 'I_m), A x (widen_ord Hmn r) != 0).
Proof.
  move => m n A Hmn r Hinv. 
  rewrite /strong_inv. move /(_ r). rewrite leqnn. move => Hstrong. apply rem_impl in Hstrong.
  move : Hstrong => [Hcol Hrow] x.
  (*We have 2 very different cases: if x < r or if x >= r*)
  case (orP (ltn_total r x)) => [ Hge | Hlt].
  - move : Hinv; rewrite /gauss_invar; move => [Hleadbefore [Hincr [Hzcol Hzero]]].
    have : r <= x. by rewrite leq_eqVlt orbC. move {Hge} => Hge.
    (*If x >= r and A x r = 0, then the submatrix with the added row x has a row of all zeroes, so
      it is not invertible*)
    have Hrsuc : r < r.+1 by [].
    case : (A x (widen_ord Hmn r) == 0) /eqP => [Hcontra|//].
    have Hallzero : (forall (c: 'I_(r.+1)), (submx_add_row A Hmn r x) (Ordinal Hrsuc) c = 0).
    move => c. rewrite /submx_add_row mxE. rewrite ltnn.
    have : c <= r by have : c < r.+1 by []. rewrite leq_eqVlt => /orP[Hcr | Hcr].
    have /eqP Heqord : (widen_ord (leq_trans (ltn_ord r) Hmn) c) == (widen_ord Hmn r) by [].
    by rewrite Heqord Hcontra. by apply Hzero.
    have : submx_add_row A Hmn r x \notin unitmx by apply (row_zero_not_unitmx Hallzero).
    move : Hrow. by move => /(_ x Hge) ->.
  - (*If x < r and A x r = 0, then the submatrix with column x removed has a row of all zeroes, so it
      is not invertible*)
    case Hcontra : (A x (widen_ord Hmn r) == 0) => [|//].
    have Hallzero: (forall (c: 'I_r), (submx_remove_col A Hmn r x) (Ordinal Hlt) c = 0).
    move => c. rewrite /submx_remove_col mxE. case Hcx : (c < x).
    + apply (elimT eqP). rewrite (gauss_invar_square_id Hmn _ Hinv). rewrite !remove_widen.
      have: nat_of_ord x != nat_of_ord c. move : Hcx. rewrite ltn_neqAle => /andP[Hcx  H{H}].
      by rewrite eq_sym. by []. by apply ltnW. by []. by rewrite remove_widen.
    + case Hcr1 : (c.+1 == r).
      * have: (widen_ord (ltnW (ltn_ord r)) (Ordinal Hlt) = x). apply (elimT eqP).
        have: (nat_of_ord (widen_ord (ltnW (ltn_ord r)) (Ordinal Hlt)) == nat_of_ord x) by []. by [].
        move ->. 
        have: ((ord_widen_succ (ltn_leq_trans (ltn_ord r) Hmn) c) = widen_ord Hmn r) by apply (elimT eqP).
        move ->. by apply (elimT eqP).
      * apply (elimT eqP). rewrite (gauss_invar_square_id Hmn _ Hinv). rewrite !remove_widen.
        have: nat_of_ord x != c.+1. case : (nat_of_ord x == c.+1) /eqP => [Hx|//].
        move: Hcx. by rewrite Hx ltnSn. by []. 
        by (apply ltnW). by []. have: c.+1 < r.
        case (orP (ltn_total (c.+1) r)) => [/orP[Hlt' | Heq] | Hgt]. by []. by move: Heq Hcr1 ->.
        have Hcr: c < r by []. rewrite leqNgt in Hcr. by move : Hgt Hcr ->. by [].
    + have: submx_remove_col A Hmn r x \notin unitmx. apply (row_zero_not_unitmx Hallzero).
      move : Hcol. move => /(_ x Hlt). by move ->.
Qed. 

(*Equivalence of the two gaussian step functions*)
Lemma gauss_one_step_equiv: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: 'I_m),
  gauss_invar A r r ->
  strong_inv A Hmn r ->
  (gauss_one_step_restrict A r Hmn, insub (r.+1), insub (r.+1)) = gauss_one_step A r (widen_ord Hmn r).
Proof.
  move => m n A Hmn r Hinv Hstrong. rewrite /gauss_one_step /gauss_one_step_restrict.
  have Hnz: (forall (x : 'I_m), A x (widen_ord Hmn r) != 0) by apply strong_inv_nonzero_cols. 
  have: fst_nonzero A (widen_ord Hmn r) r = Some r. rewrite fst_nonzero_some_iff.
  split. by rewrite leqnn. split. apply Hnz. move => x. by rewrite ltnNge andbN. move ->.
  rewrite all_cols_one_equiv. rewrite (@sub_all_rows_equiv _ _ _ _ (widen_ord Hmn r)). 
  have->: xrow r r A = A. rewrite -matrixP /eqrel. move => x y. rewrite xrow_val. 
  by case: (x == r) /eqP => [->|]. by [].
  move => x. rewrite all_cols_one_val /=.
  have Haxr: A x (widen_ord Hmn r) == 0 = false. apply negbTE. by apply Hnz. rewrite Haxr.
  rewrite GRing.mulfV. by rewrite GRing.oner_neq0. apply (negbT Haxr).
  apply Hnz.
Qed.

(*Preservation of [strong_inv] invariant *)

(*Now we want to show that [strong_inv] is preserved through [gauss_one_step_simpl]. We will make heavy use
  of [row_equivalent_unitmx_iff], so we need to know when submatrices are row equivalent. We do this in
  the following few lemmas*)

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

Lemma strong_inv_preserved: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r : 'I_m) (Hr: r.+1 < m),
  strong_inv A Hmn r ->
  gauss_invar A r r ->
  strong_inv (gauss_one_step_restrict A r Hmn) Hmn (Ordinal Hr).
Proof.
  move => m n A Hmn r Hr Hstr Hinv. rewrite /strong_inv. move => r' Hrr'. rewrite /gauss_one_step_restrict.
  have Hlerr': r <= r' by apply (leq_trans (leqnSn r)).
  split.
  - move => j Hjr'. rewrite -(@row_equivalent_unitmx_iff _ (submx_remove_col A Hmn r' j)).
    move : Hstr; rewrite /strong_inv; move /(_ r' Hlerr') => Hstr. by apply Hstr.
    rewrite /submx_remove_col /=.
    eapply row_equivalent_trans. 2:  apply mxsub_row_transform_equiv.
    apply mxsub_row_transform_equiv. 
    + move => A' r''. apply mxsub_sc_mul_row_equiv. move => x y. apply widen_ord_inj. 
      apply GRing.invr_neq0. by apply strong_inv_nonzero_cols.
    + move => A' r''. case Hrr'' : (r'' == r).  constructor.
      apply mxsub_add_mul_row_equiv. move => x y. apply widen_ord_inj. by rewrite eq_sym Hrr''.
      have Hlt: r < r' by []. exists (Ordinal Hlt).
      have: nat_of_ord (widen_ord (ltnW (ltn_ord r')) (Ordinal Hlt)) == r.
      by rewrite remove_widen. by [].
  - move => j Hjr'. rewrite -(@row_equivalent_unitmx_iff _ (submx_add_row A Hmn r' j)).
    move : Hstr; rewrite /strong_inv; move /(_ r' Hlerr') => Hstr. by apply Hstr.
    rewrite /submx_add_row /=. eapply row_equivalent_trans. 2 : apply mxsub_row_transform_equiv.
    apply mxsub_row_transform_equiv.
    + move => A' r''. apply mxsub_sc_mul_row_equiv. by apply row_mx_fn_inj.
      apply GRing.invr_neq0. by apply strong_inv_nonzero_cols.
    + move => A' r''. case Hrr'': (r'' == r). constructor.
      apply mxsub_add_mul_row_equiv. by apply row_mx_fn_inj. by rewrite eq_sym Hrr''.
      have Hltrr' : r.+1 <= r' by []. have Hsuc: r < r'.+1 by apply (ltn_trans Hltrr').
      exists (Ordinal Hsuc). have: Ordinal Hsuc < r' by []. move ->.
      have: nat_of_ord (widen_ord (ltn_ord r') (Ordinal Hsuc)) == r by []. by [].
Qed.

(*We want to know that after [gauss_step_restrict] with input r, A r r = 1 (this is not true for previous LC's*)
Lemma last_lc_1: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: 'I_m),
  strong_inv A Hmn r ->
  gauss_invar A r r ->
  (gauss_one_step_restrict A r Hmn) r (widen_ord Hmn r) = 1.
Proof.
  move => m n A Hmn r Hstr Hinv. rewrite /gauss_one_step_restrict.
  rewrite /sub_all_rows_noif foldr_remAll /=. 
  rewrite mx_row_transform_notin.
  - rewrite mx_row_transform.
    + rewrite /sc_mul mxE eq_refl. apply GRing.mulVf. by apply strong_inv_nonzero_cols.
    + move => A' i j r' Hir. rewrite /sc_mul mxE. by have ->: i == r' = false by move : Hir; by case (i == r').
    + move => A' B' r' Hab Hnotin j. rewrite /sc_mul !mxE eq_refl. by rewrite Hab.
    + apply ord_enum_uniq.
    + apply mem_ord_enum.
  - move => A' i j r' Hir. rewrite /add_mul mxE. by have ->: i == r' = false by move : Hir; by case (i == r').
  - apply remAll_notin.
Qed.

(*For the all-steps functions, we don't need to use Function since this time, we know that r and c increase by 1
  each time. Thus, we can fold over a list. We will need both directions*)
(*Note: although we will never hit the None case, it makes the proofs much easier if we can use [iota] rather 
  than a list of ordinals*)
Definition gauss_all_steps_restrict_aux {m n}  (A: 'M[F]_(m, n)) (Hmn: m <= n) a b :=
foldl (fun A' r' => match (insub r') with
                       | Some r'' => gauss_one_step_restrict A' r'' Hmn
                       | None => A'
                      end) A (iota a b).

(*The aux function allows us to prove generic results about applying multiple steps of Gaussian elimination.
  Going backward (r to m-r) helps prove equivalence with regular gaussian elim, while going forward (0 to r)
  will be useful in the C proofs*)

Lemma strong_inv_dep: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (x y: 'I_m),
  x == y ->
  strong_inv A Hmn x <-> strong_inv A Hmn y.
Proof.
  move => m n A Hmn x y /eqP Hxy. by subst.
Qed.  

Lemma gauss_one_step_restrict_invar: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) a (Ha: a < m) ,
  gauss_invar A a a ->
  strong_inv A Hmn (Ordinal Ha) ->
  gauss_invar (gauss_one_step_restrict A (Sub a Ha) Hmn) a.+1 a.+1.
Proof.
  move => m n A Hmn a Ha Hinv Hstr.
  have Hinv_ord: gauss_invar A (Ordinal Ha) (Ordinal Ha) by [].
  pose proof (gauss_one_step_equiv Hinv_ord Hstr) as Hstep.
  have Hinv_ord' : gauss_invar A (Ordinal Ha) ((widen_ord Hmn (Ordinal Ha))) by [].
  pose proof (gauss_one_step_invar Hinv_ord') as Hstep_inv. rewrite -Hstep in Hstep_inv.
  move : Hstep_inv; rewrite /=. 
  have ->: (@ord_bound_convert m (insub a.+1)) = a.+1. 
  have: a.+1 <= m by []. rewrite leq_eqVlt => /orP[/eqP Heq | Hlt]. subst. rewrite insubF. by [].
  by rewrite ltnn. by rewrite insubT.
  have ->: (@ord_bound_convert n (insub a.+1)) = a.+1. have: a.+1 <= n by rewrite (leq_trans Ha Hmn).
  rewrite leq_eqVlt => /orP[/eqP Heq | Hlt]. subst. rewrite insubF. by []. by rewrite ltnn.
  rewrite insubT. by []. by [].
Qed.

(*Need to separate out these next two lemmas, though they are similar, since [gauss_invar] may hold
  of m, while [strong_inv] needs r < m*)

Lemma gauss_all_steps_restrict_aux_inv: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (a b: nat) (Ha: a < m)
  (Hab : a + b <= m),
  gauss_invar A a a ->
  strong_inv A Hmn (Ordinal Ha) ->
  gauss_invar (gauss_all_steps_restrict_aux A Hmn a b) (a+b) (a+b).
Proof.
  move => m n A Hmn a b. 
  rewrite /gauss_all_steps_restrict_aux.
  move : a A. elim : b =>[a A Ha H0m Hinv Hstr/=|b IH a A Ha Hab Hinv Hstr /=].
  - by rewrite addn0.
  - have /eqP Hab1 : (a + b.+1 == a.+1 + b)%N by rewrite -(addn1 b) -(addn1 a) -(addnA a 1%N b) (addnC 1%N b).
    rewrite Hab1. rewrite insubT.
    have Hinv1 : (gauss_invar (gauss_one_step_restrict A (Sub a Ha) Hmn) a.+1 a.+1)
    by apply gauss_one_step_restrict_invar. 
    (*In this case: need to know if a.+1 = m*)
    have: a.+1 <= m by []. rewrite leq_eqVlt => /orP[/eqP Haeq | Ham1].
    + subst. have /eqP Hb0: (b == 0)%N. move : Hab. by rewrite addnS ltnS -{2}(addn0 a) leq_add2l leqn0.
      subst. rewrite /=. by rewrite addn0.
    + have Habm1 : a.+1 + b <= m by rewrite -Hab1. 
      have Hstr1: (strong_inv (gauss_one_step_restrict A (Sub a Ha) Hmn) Hmn (Ordinal Ham1)) by apply strong_inv_preserved.
      move : IH => /(_ (a.+1) (gauss_one_step_restrict A (Sub a Ha) Hmn) Ham1 Habm1 Hinv1 Hstr1) IH. by [].
Qed.

Lemma gauss_all_steps_restrict_aux_strong: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (a b: nat) (Ha: a < m)
  (Hab : a + b < m),
  gauss_invar A a a ->
  strong_inv A Hmn (Ordinal Ha) ->
  strong_inv (gauss_all_steps_restrict_aux A Hmn a b) Hmn (Ordinal Hab).
Proof.
  move => m n A Hmn a b. 
  rewrite /gauss_all_steps_restrict_aux.
  move : a A. elim : b =>[a A Ha H0m Hinv Hstr/=|b IH a A Ha Hab Hinv Hstr /=].
  - rewrite strong_inv_dep. apply Hstr.
    have: (a + 0 == a)%N. by rewrite addn0. by [].
  - have /eqP Hab1 : (a + b.+1 == a.+1 + b)%N by rewrite -(addn1 b) -(addn1 a) -(addnA a 1%N b) (addnC 1%N b).
    have Habm1 : a.+1 + b < m by rewrite -Hab1. have Ha1 : a.+1 < m.
    move : Habm1. rewrite addnC -ltn_subRL => Hint. apply (ltn_leq_trans Hint (leq_subr _ _)).
    have Hinv1 : (gauss_invar (gauss_one_step_restrict A (Sub a Ha) Hmn) a.+1 a.+1) by
    apply gauss_one_step_restrict_invar. 
    have Hstr1: (strong_inv (gauss_one_step_restrict A (Sub a Ha) Hmn) Hmn (Ordinal Ha1)) by apply strong_inv_preserved.
    rewrite insubT.
    move : IH => /(_ (a.+1) (gauss_one_step_restrict A (Sub a Ha) Hmn) Ha1 Habm1 Hinv1 Hstr1) IH.
    rewrite strong_inv_dep. apply IH. by have: (a + b.+1)%N == (a.+1 + b)%N by apply (introT eqP); rewrite Hab1.
Qed.

(*Finally, we want to know that the last row (a + b) has leading coefficient 1*)
Lemma gauss_all_steps_restrict_aux_lc_1: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (a b: nat) (Ha: a < m)
  (Hab : a + b.-1 < m),
  0 < b ->
  gauss_invar A a a ->
  strong_inv A Hmn (Ordinal Ha) ->
  (gauss_all_steps_restrict_aux A Hmn a b) (Ordinal Hab) (widen_ord Hmn (Ordinal Hab)) = 1.
Proof.
  move => m n A Hmn a b Ha Hab H0b Hinv Hstr. rewrite /gauss_all_steps_restrict_aux.
  have Hb: b = ((b.-1) + 1)%N by rewrite addn1 (ltn_predK H0b).
  have ->: (iota a b) = (iota a (b.-1 + 1)%N) by rewrite {1}Hb.
  rewrite iotaD foldl_cat /= insubT -/(gauss_all_steps_restrict_aux A Hmn a b.-1) /=.
  apply last_lc_1. apply (@gauss_all_steps_restrict_aux_strong _ _ _ _ _ _ Ha Hab Hinv Hstr).
  apply (gauss_all_steps_restrict_aux_inv (ltnW Hab) Hinv Hstr).
Qed. 

Definition gauss_all_steps_restrict_end {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: nat) :=
  gauss_all_steps_restrict_aux A Hmn r (m - r).

(*Equivalence with full version*)
Lemma gauss_all_steps_equiv: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: nat) (Hr: r < m),
  gauss_invar A r r ->
  strong_inv A Hmn (Ordinal Hr) ->
  gauss_all_steps_restrict_end A Hmn r = 
    gauss_all_steps A (Some (Ordinal Hr)) (Some (widen_ord Hmn (Ordinal Hr))).
Proof.
  move => m n A Hmn r. remember (m - r)%N as x. move : A r Heqx. elim: x.
  - move => A r Hmr Hr Hinv Hstrong. have: (m - r)%N == 0%N. rewrite eq_sym. by apply (introT eqP).
    rewrite subn_eq0 leqNgt. move => Hrm. by rewrite Hr in Hrm.
  - move => n' IH A r Hmrn1 Hr Hinv Hstrong.
    rewrite gauss_all_steps_equation /gauss_all_steps_restrict_end /gauss_all_steps_restrict_aux.
    have: iota r (m - r) = r :: iota r.+1 n' by rewrite /iota -Hmrn1. move ->. rewrite /= insubT.
    have Hstep: gauss_one_step A (Ordinal Hr) (widen_ord Hmn (Ordinal Hr)) = ((gauss_one_step_restrict A (Ordinal Hr) Hmn), 
    (insub (Ordinal Hr).+1), (insub (Ordinal Hr).+1)). 
    rewrite -gauss_one_step_equiv => [//|//|//]. rewrite Hstep.
    have: r.+1 <= m by []. rewrite leq_eqVlt. move => /orP[/eqP Hrmeq | Hrmlt].
    + subst. move : Hmrn1. rewrite subSnn -addn1. have H01 : (1 = 0 + 1)%N by []. rewrite {2}H01 {H01}. 
      move => Hn'. have: n' == 0%N. rewrite -(eqn_add2r 1). by apply (introT eqP). move => {Hn'} /eqP Hn'. subst.
      rewrite /=. rewrite insubF /=. by rewrite gauss_all_steps_equation. by rewrite ltnn.
    + move: Hstep. rewrite !insubT. apply (ltn_leq_trans Hrmlt Hmn). move => Hr1n.
      have: (Sub (Ordinal Hr).+1 Hrmlt) = (Ordinal Hrmlt) by []. move ->.
      have: (Sub (Ordinal Hr).+1 Hr1n) = (widen_ord Hmn (Ordinal Hrmlt)). apply (elimT eqP).
      have: nat_of_ord (Sub (Ordinal Hr).+1 Hr1n) == r.+1 by [].
      have: nat_of_ord (widen_ord Hmn (Ordinal Hrmlt)) == r.+1 by []. by []. move ->.
      move => Hstep.
      have Hmrnalt: n' = (m - r.+1)%N by rewrite subnS -Hmrn1 -pred_Sn. 
      rewrite -IH.
      by rewrite /gauss_all_steps_restrict_end Hmrnalt. by [].
      have Hinv': gauss_invar A (Ordinal Hr) (widen_ord Hmn (Ordinal Hr)) by [].
      apply gauss_one_step_invar in Hinv'. rewrite Hstep in Hinv'. apply Hinv'.
      apply strong_inv_preserved. by []. apply Hinv.
Qed.

(*More specifically, we have [gauss_invar m m], which will allow us to prove that the result looks like [I_m, E] for
  some matrix E*)
Lemma gauss_all_steps_inv: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: nat) (Hr: r < m),
  gauss_invar A r r ->
  strong_inv A Hmn (Ordinal Hr) ->
  gauss_invar (gauss_all_steps_restrict_end A Hmn r) m m.
Proof.
  move => m n A Hmn r Hr Hinv Hstr. rewrite /gauss_all_steps_restrict_end.
  have /eqP Hrm: (r + (m-r) == m)%N. rewrite -addnC subnK. by []. by apply ltnW.
  have Hrmbound: r + (m - r) <= m. by rewrite Hrm.
  pose proof (gauss_all_steps_restrict_aux_inv Hrmbound Hinv Hstr) as Hinv'.
  by rewrite Hrm in Hinv'.
Qed.

(*Finally, for the C proofs, we will want a version which goes from row 0 to some row x < m (instead of the previous,
  which goes from r to m. We will define this (virtually identically, only the bounds for iota change) and prove that
  this is equivalent*)
Definition gauss_all_steps_restrict_beg {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: nat) :=
  gauss_all_steps_restrict_aux A Hmn 0 r.

Lemma gauss_all_steps_restrict_beg_unfold: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (r: nat) (Hr: r < m),
  gauss_all_steps_restrict_beg A Hmn (r.+1) = gauss_one_step_restrict (gauss_all_steps_restrict_beg A Hmn r) (Ordinal Hr) Hmn.
Proof.
  move => m n A Hmn r Hr. rewrite /gauss_all_steps_restrict_beg /gauss_all_steps_restrict_aux.
  have: (iota 0 r.+1) = rev (rev (iota 0 r.+1)) by rewrite revK. move ->. rewrite foldl_rev.
  have: (iota 0 r.+1) = rcons(iota 0 r) r. by rewrite -cats1 -addn1 iotaD. move ->. 
  by rewrite rev_rcons /= insubT -foldl_rev revK.
Qed.

Lemma gauss_all_steps_restrict_both_dirs: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n),
  gauss_all_steps_restrict_end A Hmn 0 = gauss_all_steps_restrict_beg A Hmn m.
Proof.
  move => m n A Hmn. by rewrite /gauss_all_steps_restrict_end /gauss_all_steps_restrict_beg subn0.
Qed.

(*We need to know that the invariants are preserved through this function*)
Lemma gauss_all_steps_restrict_beg_gauss: forall {m n } (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: nat) (Hm: 0 < m),
  strong_inv A Hmn (Ordinal Hm) ->
  r <= m ->
  gauss_invar (gauss_all_steps_restrict_beg A Hmn r) r r.
Proof.
  move => m n A Hmn r Hm Hstr Hrm. rewrite /gauss_all_steps_restrict_beg.
  have /eqP H0r: (0 + r == r)%N by rewrite add0n.
  have H0rbound: 0 + r <= m by rewrite H0r.
  pose proof (gauss_all_steps_restrict_aux_inv H0rbound (gauss_invar_init _) Hstr).
  by rewrite H0r in H.
Qed.

Lemma gauss_all_steps_restrict_beg_strong: forall {m n } (A: 'M[F]_(m, n)) (Hmn : m <= n) (r: nat) (Hm: 0 < m) 
  (Hr: r < m),
  strong_inv A Hmn (Ordinal Hm) ->
  strong_inv (gauss_all_steps_restrict_beg A Hmn r) Hmn (Ordinal Hr).
Proof.
  move => m n A Hmn r Hm Hr Hstr.
  rewrite /gauss_all_steps_restrict_beg.
  have H0rm : 0 + r < m by [].
  pose proof (@gauss_all_steps_restrict_aux_strong _ _ _ _ _ _ _ H0rm  (gauss_invar_init _) Hstr).
  rewrite strong_inv_dep. apply H. by have: (r == 0 + r)%N by [].
Qed. 

(*Similarly, we wrap this into a nice definition which we can then prove results about to use in the C code
  which oeprates on the result of gaussian elimination*)

(*In this case, we know all the leading coefficients are at position r (for row r). We provide a 
  generic upper bound because the last row is not needed*)
Definition mk_identity {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (b: nat) :=
  foldr (fun x acc => sc_mul acc (A x (widen_ord Hmn x))^-1 x) A (pmap insub (iota 0 b)).

Lemma mk_identity_val_in: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (b: nat) (i: 'I_m) (j: 'I_n),
  (forall (r': 'I_m), lead_coef A r' = Some (widen_ord Hmn r')) ->
  i < b ->
  mk_identity A Hmn b i j = (A i (widen_ord Hmn i))^-1 * A i j.
Proof.
  move => m n A Hmn b i j Hlc Hib. rewrite mx_row_transform.
  - by rewrite /sc_mul mxE eq_refl.
  - move => A' i' j' r' Hir'. rewrite /sc_mul mxE. by have ->: i' == r' = false by move : Hir'; by case : (i' == r').
  - move => A' B' r Hab Hnotin j'. by rewrite /sc_mul !mxE eq_refl Hab.
  - apply pmap_sub_uniq. apply iota_uniq.
  - by rewrite mem_pmap_sub /= mem_iota add0n.
Qed.

Lemma mk_identity_val_notin: forall {m n} (A: 'M[F]_(m, n)) (Hmn : m <= n) (b: nat) (i: 'I_m) (j: 'I_n),
  (forall (r': 'I_m), lead_coef A r' = Some (widen_ord Hmn r')) ->
  b <= i ->
  mk_identity A Hmn b i j = A i j.
Proof.
  move => m n A Hmn b i j Hlc Hbi. rewrite mx_row_transform_notin.
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
  - rewrite mk_identity_val_notin =>[|//|//]. 
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

(*The only complication is that we don't need to scalar multiply the last row*)
Definition gaussian_elim_restrict {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) :=
  mk_identity (gauss_all_steps_restrict_end A Hmn 0) Hmn (m.-1).



Lemma gaussian_elim_equiv:  forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (Hm: 0 < m),
  strong_inv A Hmn (Ordinal Hm) ->
  gaussian_elim_restrict A Hmn = gaussian_elim A.
Proof.
  move => m n A Hmn Hm Hstrong. rewrite /gaussian_elim_restrict /gaussian_elim.
  have Hinv: gauss_invar (gauss_all_steps_restrict_end A Hmn 0) m m
  by apply (gauss_all_steps_inv (gauss_invar_init A) Hstrong).
  rewrite mk_identity_equiv.
  - f_equal. rewrite gauss_all_steps_equiv =>[ | |//].
    have H0n: 0 < n by apply (ltn_leq_trans Hm Hmn). rewrite !insubT /=.
    have ->: (widen_ord Hmn (Ordinal Hm)) = (Ordinal H0n) by apply (elimT eqP). by [].
    apply gauss_invar_init.
  - by rewrite ltn_predL.
  - move => r'. by apply (gauss_invar_square_lc Hmn (leqnn m)).
  - move => Hm1. rewrite /gauss_all_steps_restrict_end. rewrite subn0.
    apply (@gauss_all_steps_restrict_aux_lc_1 m n A Hmn 0 m Hm) => [//||//]. apply gauss_invar_init.
Qed. 

(*Not sure if we actually need this now*)
Lemma gaussian_elim_restrict_row_equiv: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (Hm: 0 < m),
  strong_inv A Hmn (Ordinal Hm) ->
  row_equivalent A (gaussian_elim_restrict A Hmn).
Proof.
  move => m n A Hmn Hm Hstrong. rewrite gaussian_elim_equiv => [|//]. apply gaussian_elim_row_equiv.
Qed.

(*For any matrix satisfiying [gauss_invar m m], the left hand side is the identity matrix*)
Lemma gauss_invar_square_inverse: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n),
  gauss_invar A m m ->
  (forall (x: 'I_m) (y: 'I_n), y < m -> (all_lc_1 A) x y == (if nat_of_ord x == nat_of_ord y then 1 else 0)).
Proof.
  move => m n A Hmn Hinv x y Hym. case Hxy : (nat_of_ord x == nat_of_ord y).
  - have Hxm: x < m by eq_subst Hxy; rewrite Hxy. have: lead_coef (all_lc_1 A) x = Some (widen_ord Hmn x)
    by apply (gauss_invar_square_lc Hmn (leqnn m) (all_lc_1_gauss_invar Hinv)).
    move => Hlc. rewrite -all_lc_1_lcs in Hlc. apply all_lc_1_sets_lc in Hlc.
    have Hyw: widen_ord Hmn x = y by apply (elimT eqP). rewrite -Hyw. by apply (introT eqP).
  - rewrite -all_lc_1_zeroes. rewrite (gauss_invar_square_id Hmn (leqnn m) Hinv).
    by rewrite Hxy. by []. by [].
Qed.

(*And therefore, the same holds for [gaussian_elim_restrict] if the input matrix satisfies [strong_inv]*)
Lemma gauss_elim_restrict_inverse: forall {m n} (A: 'M[F]_(m, n)) (Hmn: m <= n) (Hm: 0 < m),
  strong_inv A Hmn (Ordinal Hm) ->
  (forall (x: 'I_m) (y: 'I_n), y < m -> 
    (gaussian_elim_restrict A Hmn) x y == (if nat_of_ord x == nat_of_ord y then 1 else 0)).
Proof.
  move => m n A Hmn Hm Hstr x y Hym. rewrite /gaussian_elim_restrict mk_identity_equiv.
  apply gauss_invar_square_inverse.
  by []. apply (@gauss_all_steps_inv m n A Hmn 0 Hm). apply gauss_invar_init. by []. by [].
  by rewrite ltn_predL.
  move => r. apply (gauss_invar_square_lc Hmn (leqnn m)). 
  by apply (gauss_all_steps_inv (gauss_invar_init A) Hstr). by []. 
  move => Hm1. rewrite /gauss_all_steps_restrict_end. rewrite subn0.
  apply (@gauss_all_steps_restrict_aux_lc_1 m n A Hmn 0 m Hm) => [//||//]. apply gauss_invar_init.
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

Lemma gauss_one_step_restrict_castmx: forall  m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N) 
  (A: 'M[F]_(m, n)) (x: 'I_m),
  castmx Heq (gauss_one_step_restrict A x Hmn) =
  gauss_one_step_restrict (castmx Heq A) (cast_ord Heq.1 x) (cast_leq Heq Hmn).
Proof.
  move => m n m' n' Heq Hmn A x. rewrite /gauss_one_step_restrict sub_all_rows_noif_castmx
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

Lemma gauss_all_steps_restrict_castmx: forall m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N) (A: 'M[F]_(m, n)) x y,
  castmx Heq (gauss_all_steps_restrict_aux A Hmn x y) =
  gauss_all_steps_restrict_aux (castmx Heq A) (cast_leq Heq Hmn) x y.
Proof.
  move => m n m' n' Heq Hmn A x y. apply foldl_castmx => x' A'.
  case Hx': (x' < m)%N.
  - rewrite !insubT. by rewrite -(fst Heq). move => Hxm'.
    rewrite gauss_one_step_restrict_castmx /=. f_equal. by apply ord_inj.
  - rewrite !insubF //. by rewrite -Heq.1.
Qed.

(*The final result we need*)
Lemma castmx_gaussian_restrict: forall m n m' n' (A: 'M[F]_(m, n)) (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N),
  castmx Heq (gaussian_elim_restrict A Hmn) = gaussian_elim_restrict (castmx Heq A) (cast_leq Heq Hmn).
Proof.
  move => m n m' n' A Heq Hmn. rewrite /gaussian_elim_restrict. rewrite -matrixP => x y.
  rewrite mk_identity_castmx. f_equal. f_equal. 2: by rewrite (fst Heq).
  rewrite /gauss_all_steps_restrict_end. rewrite gauss_all_steps_restrict_castmx. f_equal.
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
  strong_inv A Hmn x <-> strong_inv (castmx (Hmm, Hnn) A) (leq_subst Hmm Hnn Hmn) (eq_ord Hmm x).
Proof.
  move => m n m' n' A Hmm Hnn Hmn x. rewrite /strong_inv /=. split; move => Hstr r' Hxr'.
  - remember (eq_ord (esym Hmm) r') as r.  move: Hstr => /(_ r). rewrite Heqr /= => /(_ Hxr') => [[Hcol Hrow]].
    have ->: r' = eq_ord Hmm r by subst; apply ord_inj. rewrite /=.
    split; move => j Hjr;remember (eq_ord (esym Hmm) j) as j';  have ->:j = eq_ord Hmm j' by subst; apply ord_inj.
    + rewrite -submx_remove_col_castmx Heqr. apply Hcol. by subst.
    + rewrite -submx_add_row_castmx Heqr. apply Hrow. by subst.
  - remember (eq_ord Hmm r') as r.  move: Hstr => /(_ r). rewrite Heqr /= => /(_ Hxr') => [[Hcol Hrow]].
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
  strong_inv A Hmn r ->
  strong_inv (row_mx A B) Hmn' r.
Proof.
  move => m n A B Hmn Hmn' r. rewrite /strong_inv => Hstr r' Hr'. split.
  - move => j Hj. rewrite -submx_remove_col_rowmx. move : Hstr => /(_ r' Hr') => [[Hcol Hrow]].
    by apply Hcol.
  - move => j Hj. rewrite -submx_add_row_rowmx. move : Hstr => /(_ r' Hr') => [[Hcol Hrow]].
    by apply Hrow.
Qed.

(*Finally, [srong_inv] is actually a stronger condition than invertibility*)

Lemma lt_subst: forall (n m p: nat),
  (n < m)%N ->
  m = p ->
  (n < p)%N.
Proof.
  move => n m p Hn Hmp. by rewrite -Hmp.
Qed.

Lemma strong_inv_unitmx: forall {n} (A: 'M[F]_n) (H: (n <= n)%N) (r: 'I_n),
  strong_inv A H r ->
  A \in unitmx.
Proof.
  move => n A H r. rewrite /strong_inv.
  have: (0 <= n)%N by []. rewrite leq_eqVlt => /orP[/eqP H0n | Hn].
  -  move => Hstr. (*i guess the empty matrix is invertible?*)
     have->: A = (1%:M)%R. subst. apply matrix_zero_rows. apply unitmx1.
  - have Hr: (r <= (pred_ord Hn))%N by rewrite /= -ltn_pred. 
    move => /(_ (pred_ord Hn) Hr) => [[Hrow Hcol]].
    move : Hcol => /(_ (pred_ord Hn) (leqnn _)).
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
*)