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

Lemma pred_lt: forall n, 0 < n -> n.-1 < n.
Proof.
  move => n Hn. by rewrite ltn_predL.
Qed.

Definition pred_ord (n: nat) (Hn: 0 < n) : 'I_n := Ordinal (pred_lt Hn).

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

End PrimitiveVandermonde.