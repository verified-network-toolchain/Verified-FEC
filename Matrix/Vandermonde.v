From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.poly.
Require Import LinIndep.
Require Import Gaussian. (*TODO: maybe move summation things to common file*)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section GenericVandermonde.

Variable F : fieldType.

Local Open Scope ring_scope.

(*Sometimes this is defined as the transpose of a vandermonde mx. In our case, we want each column to
  contain the powers of a given element*)
Definition vandermonde (m n: nat) (l: list F) : 'M[F]_(m, n) :=
  \matrix_(i < m, j < n) (nth 0 l j) ^+ i.

(*TODO: move*)
(*Not sure why this is not included, also I couldn't get {in l, P} to work*)
Lemma all_in: forall {A: eqType} (l: seq A) (p: pred A),
  all p l <-> forall x, x \in l -> p x.
Proof.
  move => A l. elim: l =>[p // | h t IH p /=].
  split. move => /andP[Hh Htl x]. rewrite in_cons => /orP[/eqP Hxh | Hxt].
  by subst. by apply IH.
  move => Hall. rewrite Hall. rewrite IH. move => x Hint. apply Hall. by rewrite in_cons Hint orbT.
  by rewrite in_cons eq_refl.
Qed.

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

End GenericVandermonde.

Require Import PolyField.
Require Import Poly.
Require Import Coq.ZArith.BinInt.
Require Import PolyMod.
Require Import PrimitiveFacts.
Require Import Lia.

Import WPoly.

Section PrimitiveVandermonde.

Local Open Scope ring_scope.

(*The specific Vandermonde matrix that we will actually use*)
Variable f: poly.

Variable Hpos: (deg f > 0)%Z.

(*Technically we don't need this one, but I'm not sure if there will be an issue if I prove it separately and then
  we have two different proofs*)
Variable Hirred: irreducible f.

Variable Hprim: primitive f.

Variable Hnotx: f <> x.

Lemma f_nonzero: f <> zero.
Proof.
  move => Hfz. have Hzpos: (deg zero > 0)%Z by rewrite -Hfz.
  have Hzneg: (deg zero < 0)%Z by rewrite deg_zero. lia.
Qed.

Definition F := qpoly_fieldType Hpos Hirred.

Definition qx : qpoly f := poly_to_qpoly f Hpos x.

Definition vandermonde_powers m n : 'M[F]_(m, n) := vandermonde m n (map (fun i => (qx ^+ i)) (iota 0 n)).

(*Alternate definition, useful for rewriting*)
Lemma vandermonde_powers_val: forall (m n: nat) (i : 'I_m) (j: 'I_n),
  vandermonde_powers m n i j = (qx ^+ (i * j)).
Proof.
  move => m n i j. rewrite /vandermonde_powers /vandermonde mxE.
  have Hjsz: j < size (iota 0 n) by rewrite size_iota.
  have->: [seq qx ^+ i0 | i0 <- iota 0 n]`_j = qx ^+ j. { move => Hf.
  rewrite (nth_map 0%nat) => [|//]. rewrite nth_iota. by rewrite add0n. by []. }
  by rewrite GRing.exprAC GRing.exprM.
Qed. 


(*Now we need to prove [strong_inv] for this matrix*)

(*Transform statement about x^n from ssreflect ring ops to polynomial functions*)
Lemma exp_monomial: forall (n: nat),
  (@GRing.exp F qx n) = poly_to_qpoly f Hpos (monomial n).
Proof.
  move => n. elim: n.
  - rewrite GRing.expr0. rewrite monomial_0. 
    have->: (GRing.one F) = q1 Hpos by []. rewrite /q1 /r1 /poly_to_qpoly. exist_eq.
    rewrite pmod_refl =>[//|//|]. have <-: (0%Z = deg one) by rewrite deg_one. lia.
  - move => n IH.
    rewrite GRing.exprS IH.
    have ->: (ssralg.GRing.mul (R:=ssralg.GRing.Field.ringType F)) = qmul Hpos by [].
    rewrite /poly_to_qpoly /qmul /r_mul /poly_mult_mod /=. exist_eq. by rewrite monomial_expand -pmod_mult_distr.
Qed.
  
(*First, we need to know that x^i != x^j if i != j and i, j < 2 ^ (deg f) -1. We proved something very similar in
  [PrimitiveFacts]*)
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
  move : Heq. have Hzero: (GRing.zero F = q0 Hpos) by []. 
  rewrite Hn_split {Hn_split} GRing.exprD -{2}(GRing.mulr1 (qx ^+ m)) -GRing.mulrDr GRing.mulf_eq0 =>
  /orP[Hm0 | Hnm0].
  - have {}Hm0 : (@GRing.exp F qx m) = 0 by apply (elimT eqP). move : Hm0.
    rewrite Hzero exp_monomial /poly_to_qpoly /q0 /r0 => Hpoly. case: Hpoly => [Hmzero].
    have Hdiv: f |~ (monomial m). rewrite divides_pmod_iff. by []. 
    left. by apply f_nonzero. exfalso.
    apply (irred_doesnt_divide_monomial f m Hpos Hirred Hnotx Hdiv).
  - have {}Hnm0: (@GRing.exp F qx (n - m)) + 1 = 0 by apply (elimT eqP). move: Hnm0. 
    rewrite exp_monomial Hzero.
    have ->: (GRing.one F = q1 Hpos) by []. 
    have ->: (GRing.add (V:=ssralg.GRing.Field.zmodType F)) = qadd Hpos by []. 
    rewrite /qadd /q1 /q0 /poly_to_qpoly /r_add /= /r0 => Hpoly; case: Hpoly => [Hmnpoly].
    move: Hmnpoly; rewrite /poly_add_mod. rewrite -(pmod_refl f Hpos one). rewrite -pmod_add_distr =>[Hmod |//].
    have Hdiv: ( f |~ nth_minus_one (n - m)). rewrite divides_pmod_iff. by [].
    by left; apply f_nonzero. move : Hprim => [Hdeg [Hir [Hn0 Hnodiv]]].
    apply Hnodiv in Hdiv. case: Hdiv => [Hmn0 | Hlarge].
    + have: (n - m == 0)%nat by apply (introT eqP). by rewrite subn_eq0 leqNgt Hnm.
    + have Hnup: (n >= (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat)%coq_nat.
      have: (n - m <= n)%coq_nat. apply (elimT leP).  by rewrite leq_subr. lia.
      have Hnlow: (n < (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat)%coq_nat by apply (elimT ltP). lia.
    + have <-: (0%Z = deg one) by rewrite deg_one. lia. }
   move => n m Hnm Hn Hm.
   pose proof (ltn_total n m) as Hmntotal. move: Hmntotal => /orP[/orP[Hlt | Heq] |Hgt].
   - by apply Hgen.
   - by rewrite Heq in Hnm.
   - rewrite eq_sym. by apply Hgen.
Qed.

(*We need the above in order to prove our lists are uniq for proving the variable vandermonde submatrices invertible*)
Lemma power_list_uniq: forall (n: nat),
  n < (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat ->
  uniq [seq (@GRing.exp F qx i) | i <- iota 0 n].
Proof.
  move => n Hn. rewrite map_inj_in_uniq. by rewrite iota_uniq.
  move => x y Hx Hy Hqxy.
  apply (elimT eqP). case Hxy: (x == y) =>[//|].
  have:  (@ GRing.exp F qx x) != qx ^+ y. apply powers_unequal. by rewrite Hxy.
  move : Hx. rewrite mem_iota add0n => /andP[H{H} Hx].
  by apply (ltn_trans Hx).
  move : Hy. rewrite mem_iota add0n => /andP[H{H} Hy].
  by apply (ltn_trans Hy). by rewrite Hqxy eq_refl.
Qed.

(*Now we deal with the matrices more directly*)

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

(*TODO: move*)
Lemma ltn_leq_total: forall n m,
  (n < m) || (m <= n).
Proof.
  move => m n.   
  pose proof (ltn_total m n). move : H => /orP[/orP[Hlt | Heq] | Hgt].
  + by rewrite Hlt.
  + by rewrite (leq_eqVlt n) eq_sym Heq orbT.
  + by rewrite (leq_eqVlt n) Hgt !orbT.
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
  (n < (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat) ->
  submx_remove_col (vandermonde_powers m n) Hmn r j \in unitmx.
Proof.
  move => m n Hmn r j Hjr Hnbound.
  rewrite vandermonde_remove_col_list. apply vandermonde_unitmx.
  - apply rem_nth_uniq. apply 0. apply take_uniq. by apply power_list_uniq.
  - have Hsz: size (take r.+1 [seq (@GRing.exp F qx i) | i <- iota 0 n]) = r.+1. {
    rewrite size_take size_map size_iota.
    have Hrm: r.+1 <= m by []. have: r.+1 <= n by apply (leq_trans Hrm Hmn).
    rewrite leq_eqVlt => /orP[/eqP Hr1n | Hr1n].
    + rewrite Hr1n. rewrite ltnn -Hr1n. apply pred_Sn.
    + rewrite Hr1n. apply pred_Sn. }
    rewrite rem_nth_size; rewrite Hsz. apply pred_Sn. by apply (ltn_trans Hjr).
Qed.

Lemma vandermonde_powers_add_row_list: forall m n (Hmn: m <= n) (r j:'I_m),
  (submx_add_row (@vandermonde_powers m n) Hmn r j)^T = 
    vandermonde (r.+1) (r.+1) ((map (fun i => (qx ^+ i)) (iota 0 r)) ++ (qx ^+ j :: nil)).
Proof.
  move => m n Hmn r j. rewrite /submx_remove_col /vandermonde -matrixP /trmx /eqrel => x y.
  rewrite !mxE /=.
  have Hxn: x < n. have Hxr: x < r.+1 by []. rewrite ltnS in Hxr.
    have Hrm: r < m by []. have Hxm: x < m by apply (leq_ltn_trans Hxr Hrm).
    by apply (ltn_leq_trans Hxm Hmn).
  have: y < r.+1 by []. rewrite ltnS leq_eqVlt => /orP[/eqP Hyr | Hyr].
  - rewrite Hyr ltnn. rewrite nth_cat.
    rewrite size_map size_iota ltnn subnn /=.
    rewrite (nth_map 0%nat). rewrite nth_iota. rewrite add0n. apply GRing.exprAC. by [].
    by rewrite size_iota.
  - rewrite Hyr /=. rewrite nth_cat size_map size_iota Hyr.
    rewrite !(nth_map 0%nat) /=. rewrite !nth_iota.
    rewrite !add0n. apply GRing.exprAC. by []. by []. by rewrite size_iota.
    by rewrite size_iota.
Qed.

Lemma vandermonde_add_row_unitmx: forall m n (Hmn: m <= n) (r j:'I_m),
  (r <= j) ->
  (n < (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat) ->
  submx_add_row (vandermonde_powers m n) Hmn r j \in unitmx.
Proof.
  move => m n Hmn r j Hrj Hn. rewrite -unitmx_tr vandermonde_powers_add_row_list.
  apply vandermonde_unitmx.
  - rewrite cats1 rcons_uniq.
    have->: (qx ^+ j \notin [seq (@GRing.exp F qx i) | i <- iota 0 r]). {
      case Hin: (qx ^+ j \in [seq qx ^+ i | i <- iota 0 r]) =>[|//]. 
      apply (elimT mapP) in Hin. move : Hin => [i Hi Heq].
      move : Hi; rewrite mem_iota add0n => /andP[H{H} Hir].
      have: (@GRing.exp F qx j != qx ^+ i). {
      have Hjbound: j < (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat. {
        have Hjm: j < m by []. have Hjn: j < n by apply (ltn_leq_trans Hjm Hmn).
        apply (ltn_trans Hjn Hn). }
      apply powers_unequal.
      + rewrite eq_sym. have: i < j by apply (ltn_leq_trans Hir Hrj). by rewrite ltn_neqAle => /andP[Hneq H{H}].
      + by [].
      + have Hij: i < j by apply (ltn_leq_trans Hir Hrj). apply (ltn_trans Hij Hjbound). }
      by rewrite Heq eq_refl. }
    rewrite /=. apply power_list_uniq.
    have Hrn: r < n. have Hrm: r < m. have Hjm: j < m by []. by apply (leq_ltn_trans Hrj Hjm).
    by apply (ltn_leq_trans Hrm Hmn). by apply (ltn_trans Hrn Hn).
  - by rewrite size_cat /= size_map size_iota addn1.
Qed.

(*Finally, the result we want: The Vandermonde matrix consisting of powers of the primitive element
  satisfied [strong_inv 0]*)
Lemma vandermonde_strong_inv: forall m n (Hmn: m <= n) (Hm: 0 < m),
  (n < (PeanoNat.Nat.pow 2 (Z.to_nat (deg f)) - 1)%coq_nat) ->
  strong_inv (vandermonde_powers m n) Hmn (Ordinal Hm).
Proof.
  move => m n Hmn Hm Hn. rewrite /strong_inv => r' H{H}.
  split; move => j Hrj.
  - by apply vandermonde_remove_col_unitmx.
  - by apply vandermonde_add_row_unitmx.
Qed.

End PrimitiveVandermonde.