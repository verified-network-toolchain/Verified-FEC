(*Represent Matrices as 2D lists of elements in a field F, indexed by Z. This allows us to deal with all of the
  Ordinal and other dependent type proof obligations here, giving a nicer interface for the VST proofs that uses
  [Znth], [sublist], and Z, and lets us use lia for the resulting goals*)

Require Import VST.floyd.functional_base.

From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import Gaussian.


Lemma sublist_split_Zlength: forall {A} mid (l: list A),
  0 <= mid ->
  Zlength (sublist 0 mid l) + Zlength(sublist mid (Zlength l) l) = Zlength l.
Proof.
  move => A mid l Hmid.
  have [Hin | Hout]: mid <= Zlength l \/ mid > Zlength l by lia.
  - rewrite !Zlength_sublist; lia.
  - rewrite sublist_same_gen; try lia. rewrite sublist_nil_gen; try lia. list_solve.
Qed.

(*Convert bounded Z to ordinal*)
Lemma Z_nat_bound: forall m x (Hx: 0 <= x < m),
  (Z.to_nat x < Z.to_nat m)%N.
Proof.
  intros m x Hxm. have Hcoqnat: (Z.to_nat x < Z.to_nat m)%coq_nat by apply Z2Nat.inj_lt; lia.
  by apply (introT ltP).
Qed.

Lemma Z_ord_eq: forall {m} (r: Z) (x: 'I_(Z.to_nat m)) (Hr: 0 <= r < m),
  Z.of_nat x = r <-> x == Ordinal (Z_nat_bound Hr).
Proof.
  move => m r x Hr. split => [Hxr | Hord].
  - have Hord: nat_of_ord (Ordinal (Z_nat_bound Hr)) == Z.to_nat r by [].
    have: nat_of_ord (Ordinal (Z_nat_bound Hr)) == Z.to_nat (Z.of_nat x). by rewrite Hxr. by rewrite Nat2Z.id eq_sym.
  - have: x = Ordinal (Z_nat_bound Hr). by apply (elimT eqP). move ->.
    have Hordr: nat_of_ord (Ordinal (Z_nat_bound Hr)) == Z.to_nat r by [].
    have: Z.to_nat (Z.of_nat (Ordinal (Z_nat_bound Hr))) = Z.to_nat r. move : Hordr => /eqP Hordr.
    by rewrite Nat2Z.id. rewrite Nat2Z.id. move ->. by lia.
Qed.

Lemma Z_ord_bound: forall {m} (x : 'I_(Z.to_nat m)),
  0 <= m ->
  0 <= Z.of_nat x < m.
Proof.
  move => m x Hm. have HxmN: (x < Z.to_nat m)%N by [].
  have Hxm_nat : (x < Z.to_nat m)%coq_nat by apply (elimT ltP). by lia.
Qed.

Definition Z_to_ord {m} x (Hx: 0 <= x < m) : 'I_(Z.to_nat m) :=
  Ordinal (Z_nat_bound Hx).
  
Section ListMx.

Variable F : fieldType.

Local Open Scope ring_scope.

Instance inhabitant_F: Inhabitant F.
apply 0.
Defined.

Definition matrix_type := list (list F).

Definition wf_matrix (mx: matrix_type) (m n : Z) :=
  Zlength mx = m /\ 0 <= n /\ forall x, In x mx -> Zlength x = n.

(*get the (i,j)th entry of a matrix*)
Definition get_aux (mx: matrix_type) (i j : Z) :=
  let row := Znth i mx in
  Znth j row.

Definition matrix m n := {mx : matrix_type | wf_matrix mx m n}.

Lemma matrix_m_pos: forall m n (mx: matrix m n),
  0 <= m.
Proof.
  move => m n mx. case: mx => mx. rewrite /wf_matrix => [[Hm Hn]]. list_solve.
Qed.

Lemma matrix_n_pos: forall m n (mx: matrix m n),
  0 <= n.
Proof.
  move => m n mx. case: mx => mx. rewrite /wf_matrix => [[Hm [Hn Hin]]]. list_solve.
Qed.

Definition get {m n} (mx: matrix m n) (i j : Z) :=
  get_aux (proj1_sig mx) i j.

Definition matrix_to_mx {m n} (mx: matrix m n) : 'M[F]_(Z.to_nat m, Z.to_nat n) :=
  \matrix_(i < Z.to_nat m, j < Z.to_nat n) (get mx (Z.of_nat i) (Z.of_nat j)).

(*For the row operations, it will help to define "partial" versions that operate on a sublist, since
  we need need a loop invariant for the operation*)

Section ScMul.

(*Note: we include the conditional so that the result is always a valid matrix, even if r is invalid*)
Definition scalar_mul_row_partial_aux (mx: matrix_type) (r: Z) (k: F) (bound: Z) : matrix_type :=
  if (range_le_lt_dec 0 r (Zlength mx)) then
    let old_row := Znth r mx in
    let new_row := map (fun x => k * x) (sublist 0 bound old_row) ++ sublist bound (Zlength old_row) old_row in
    upd_Znth r mx new_row 
  else mx.

Definition scalar_mul_row_aux (mx: matrix_type) (r: Z) (k: F) : matrix_type :=
  scalar_mul_row_partial_aux mx r k (Zlength (Znth r mx)).

Lemma scalar_mul_row_aux_wf: forall mx m n r k bound,
  0 <= bound ->
  wf_matrix mx m n ->
  wf_matrix (scalar_mul_row_partial_aux mx r k bound) m n.
Proof.
  move => mx m n r k bound Hb. rewrite /wf_matrix /scalar_mul_row_partial_aux => [[Hm [Hn Hin]]].
  case: (range_le_lt_dec 0 r (Zlength mx)) => [Hr /= |//].
  split.  by list_solve. split. lia. move => x. rewrite In_Znth_iff => [[i [Hbound Hznth]]].
  have: 0 <= i < m. rewrite Zlength_solver.Zlength_upd_Znth in Hbound.
  by list_solve. move => {} Hbound.
  have [Hir | Hir]: i = r \/ i <> r by lia. subst. rewrite upd_Znth_same => [|//].
  rewrite Zlength_app Zlength_map (sublist_split_Zlength _ Hb). apply Hin. by apply Znth_In.
  subst; rewrite upd_Znth_diff; try lia. apply Hin. by apply Znth_In.
Qed.

Lemma scalar_mul_row_aux_spec: forall mx m n r k i j,
  wf_matrix mx m n ->
  (0 <= r < m) ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  get_aux (scalar_mul_row_aux mx r k) i j =
    if (Z.eq_dec i r) then k * (get_aux mx i j) else get_aux mx i j.
Proof.
  move => mx m n r h i j Hwf Hr. rewrite /scalar_mul_row_aux /get_aux /scalar_mul_row_partial_aux sublist_nil 
  cats0 sublist_same => [|//|//]. move : Hwf => [Hm [Hn Hin]].
  have: proj_sumbool (range_le_lt_dec 0 r (Zlength mx)). subst. by apply proj_sumbool_is_true. move ->.
  case :  (Z.eq_dec i r) => [Hir Hi Hj /= | Hir Hi Hj /=].
  subst.  rewrite upd_Znth_same; try lia. rewrite Znth_map. by [].
  rewrite Hin => [//|]. by apply Znth_In; lia. rewrite upd_Znth_diff => [//|||//]. all: lia.
Qed. 

(*Fold definition into dependent type*)
Definition scalar_mul_row {m n} (mx: matrix m n) (r: Z) (k: F) : matrix m n :=
  exist _ (scalar_mul_row_aux (proj1_sig mx) r k) 
    (scalar_mul_row_aux_wf r k (Zlength_nonneg (Znth r (proj1_sig mx))) (proj2_sig mx)).

(*Prove equivalent to [sc_mul]*)
Lemma scalar_mul_row_equiv: forall {m n} (mx: matrix m n) r k (Hr: 0 <= r < m),
  matrix_to_mx (scalar_mul_row mx r k) = sc_mul (matrix_to_mx mx) k (Z_to_ord Hr).
Proof.
  move => m n mx r k Hr. rewrite /matrix_to_mx /scalar_mul_row /sc_mul /get /Z_to_ord /= -matrixP /eqrel => [x y].
  rewrite !mxE. rewrite (scalar_mul_row_aux_spec k (proj2_sig mx)). 
  - case: (Z.eq_dec (Z.of_nat x) r) => [Hxr /= | Hxr /=].
    have: x == Ordinal (Z_nat_bound Hr) by rewrite -Z_ord_eq. by move ->.
    case Hxord : (x == Ordinal (Z_nat_bound Hr)). have: Z.of_nat x = r. rewrite (Z_ord_eq x Hr). by apply Hxord.
    move => Hxr'. contradiction. by [].
  - by [].
  - apply Z_ord_bound. by lia.
  - apply Z_ord_bound. apply (matrix_n_pos mx).
Qed.

End ScMul.

(*Version of [iota] for nonnegative integers - TODO move*)
Definition Ziota (x len : Z) :=
  map (fun y => Z.of_nat y) (iota (Z.to_nat x) (Z.to_nat len)).

Lemma size_length: forall {A : Type} (l: list A),
  size l = Datatypes.length l.
Proof.
  move => A l. elim: l => [//|h t IH /=].
  by rewrite IH.
Qed.

Lemma in_mem_In: forall (l: list nat) x,
  x \in l <-> In x l.
Proof.
  move => l x. elim: l => [//| h t IH /=].
  rewrite in_cons -IH eq_sym. split => [/orP[/eqP Hx | Ht]| [Hx | Hlt]]. by left. by right.
  subst. by rewrite eq_refl. by rewrite Hlt orbT.
Qed.

Lemma Zlength_iota: forall a b,
  Zlength (iota a b) = Z.of_nat b.
Proof.
  move => a b. by rewrite Zlength_correct -size_length size_iota.
Qed.

Lemma Zlength_Ziota: forall x len,
  (0<=x) ->
  (0<= len) ->
  Zlength (Ziota x len) = len.
Proof.
  move => x len Hx Hlen. rewrite /Ziota Zlength_map Zlength_iota. by lia.
Qed.

Lemma Zseq_In: forall x len z,
  (0 <= x) ->
  (0 <= len) ->
  In z (Ziota x len) <-> (x <= z < x + len).
Proof.
  move => x len z Hx Hlen. rewrite /Ziota in_map_iff. split => [[i [Hiz Hin]] | Hb].
  move : Hin; rewrite -in_mem_In mem_iota. move => /andP[Hxi Hixlen].
  have {} Hxi: (Z.to_nat x <= i)%coq_nat by apply (elimT leP).
  have {} Hixlen: (i < Z.to_nat x + Z.to_nat len)%coq_nat by apply (elimT ltP). subst.
  split. lia. rewrite Z2Nat.inj_lt; try lia. by rewrite Nat2Z.id Z2Nat.inj_add; try lia.
  exists (Z.to_nat z). split. rewrite Z2Nat.id; lia. rewrite -in_mem_In mem_iota.
  apply (introT andP). split. by apply (introT leP); lia. apply (introT ltP).
  move : Hb => [Hxz Hzxlen]. move: Hzxlen. rewrite Z2Nat.inj_lt; try lia. by rewrite Z2Nat.inj_add; try lia.
Qed. 

(*Function to make all columns one (repeated scalar multiplication)*)
Section AllColsOne.

Definition all_cols_one_partial {m n} (mx: matrix m n) (c: Z) (bound: Z) :=
  fold_right (fun x acc => scalar_mul_row acc x (get mx x c)^-1 ) mx (Ziota 0 bound).

Lemma all_cols_one_equiv: forall {m n} (mx: matrix m n) (c: Z) (Hc: 0 <= c < n),
  matrix_to_mx (all_cols_one_partial mx c m) = all_cols_one_noif (matrix_to_mx mx) (Z_to_ord Hc).
Proof.
  move => m n mx c Hc. rewrite /all_cols_one_partial /all_cols_one_noif /Ziota /ord_enum.
  have: (Z.to_nat 0) = 0%N by lia. move ->. (*Can't do induction on [iota 0 (Z.to_nat m)] because of dependent typse*)
  have: forall (l: seq nat),
    (forall n, n \in l -> (n < Z.to_nat m)%N) ->
    matrix_to_mx
  (fold_right (fun (x : Z) (acc : matrix m n) => scalar_mul_row acc x (get mx x c)^-1) mx
     [seq Z.of_nat y | y <- l]) =
  foldr
  (fun (x : 'I_(Z.to_nat m)) (acc : 'M_(Z.to_nat m, Z.to_nat n)) =>
   sc_mul acc (matrix_to_mx mx x (Z_to_ord Hc))^-1 x) (matrix_to_mx mx)
  (pmap insub l).
  - move => l. elim : l => [//| h t IH Hin].
    rewrite //=. have Hbound: (h < Z.to_nat m)%N. apply Hin. by rewrite in_cons eq_refl. rewrite insubT /=.
    rewrite -IH. have Hhm : 0 <= Z.of_nat h < m. split. lia. have {} Hbound : (h < Z.to_nat m)%coq_nat by apply (elimT ltP).
    lia. rewrite scalar_mul_row_equiv. f_equal. rewrite /matrix_to_mx mxE.
    have /eqP Hhb: h == Ordinal Hbound by []. rewrite -Hhb.
    have /eqP Hhc : Z.to_nat c == (Z_to_ord Hc) by []. rewrite -Hhc. rewrite Z2Nat.id. by []. lia.
    apply (elimT eqP). have: nat_of_ord (Z_to_ord Hhm) == h.
    have: nat_of_ord (Z_to_ord Hhm) == Z.to_nat (Z.of_nat h) by []. by rewrite (Nat2Z.id h).
    by []. move => n' Hinn'. apply Hin. by rewrite in_cons Hinn' orbT.
  - move ->. by []. move => x. by rewrite mem_iota.
Qed.

End AllColsOne.


End ListMx.
