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

Definition scalar_mul_row_partial_aux (mx: matrix_type) (r: Z) (k: F) (bound: Z) : matrix_type :=
  let old_row := Znth r mx in
  let new_row := map (fun x => k * x) (sublist 0 bound old_row) ++ sublist bound (Zlength old_row) old_row in
  upd_Znth r mx new_row.

Definition scalar_mul_row_aux (mx: matrix_type) (r: Z) (k: F) : matrix_type :=
  scalar_mul_row_partial_aux mx r k (Zlength (Znth r mx)).

Lemma scalar_mul_row_aux_wf: forall mx m n r k bound,
  0 <= bound ->
  0 <= r < m ->
  wf_matrix mx m n ->
  wf_matrix (scalar_mul_row_partial_aux mx r k bound) m n.
Proof.
  move => mx m n r k bound Hb Hr. rewrite /wf_matrix /scalar_mul_row_partial_aux. move => Hwf.
  split. by list_solve. split. lia. move => x. rewrite In_Znth_iff => [[i [Hbound Hznth]]].
  have: 0 <= i < m. rewrite Zlength_solver.Zlength_upd_Znth in Hbound.
  by list_solve. move : Hwf => [Hm [Hn Hin]] {} Hbound.
  have [Hir | Hir]: i = r \/ i <> r by lia. subst. rewrite upd_Znth_same => [|//].
  rewrite Zlength_app Zlength_map (sublist_split_Zlength _ Hb). apply Hin. by apply Znth_In.
  subst; rewrite upd_Znth_diff; try lia. apply Hin. by apply Znth_In.
Qed.

Lemma scalar_mul_row_aux_spec: forall mx m n r k i j,
  wf_matrix mx m n ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  (0 <= r < m) ->
  get_aux (scalar_mul_row_aux mx r k) i j =
    if (Z.eq_dec i r) then k * (get_aux mx i j) else get_aux mx i j.
Proof.
  move => mx m n r h i j Hwf. rewrite /scalar_mul_row_aux /get_aux /scalar_mul_row_partial_aux sublist_nil 
  cats0 sublist_same => [|//|//]. move : Hwf => [Hm [Hn Hin]].
  case :  (Z.eq_dec i r) => [Hir Hi Hj Hr /= | Hir Hi Hj Hr /=].
  subst.  rewrite upd_Znth_same; try lia. rewrite Znth_map. by [].
  rewrite Hin => [//|]. by apply Znth_In; lia. rewrite upd_Znth_diff => [//|||//]. all: lia.
Qed. 

(*Fold definition into dependent type*)
Definition scalar_mul_row {m n} (mx: matrix m n) (r: Z) (k: F) (Hr: 0 <= r < m) : matrix m n :=
  exist _ (scalar_mul_row_aux (proj1_sig mx) r k) 
    (scalar_mul_row_aux_wf k (Zlength_nonneg (Znth r (proj1_sig mx))) Hr (proj2_sig mx)).

(*Prove equivalent to [sc_mul]*)
Lemma scalar_mul_row_equiv: forall {m n} (mx: matrix m n) r k (Hr: 0 <= r < m),
  matrix_to_mx (scalar_mul_row mx k Hr) = sc_mul (matrix_to_mx mx) k (Z_to_ord Hr).
Proof.
  move => m n mx r k Hr. rewrite /matrix_to_mx /scalar_mul_row /sc_mul /get /Z_to_ord /= -matrixP /eqrel => [x y].
  rewrite !mxE. rewrite (scalar_mul_row_aux_spec k (proj2_sig mx)). 
  - case: (Z.eq_dec (Z.of_nat x) r) => [Hxr /= | Hxr /=].
    have: x == Ordinal (Z_nat_bound Hr) by rewrite -Z_ord_eq. by move ->.
    case Hxord : (x == Ordinal (Z_nat_bound Hr)). have: Z.of_nat x = r. rewrite (Z_ord_eq x Hr). by apply Hxord.
    move => Hxr'. contradiction. by [].
  - apply Z_ord_bound. by lia.
  - apply Z_ord_bound. apply (matrix_n_pos mx).
  - by [].
Qed.

End ScMul.

End ListMx.
