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
Require Import PropList.


Lemma sublist_split_Zlength: forall {A} mid (l: list A),
  0 <= mid ->
  Zlength (sublist 0 mid l) + Zlength(sublist mid (Zlength l) l) = Zlength l.
Proof.
  move => A mid l Hmid.
  have [Hin | Hout]: mid <= Zlength l \/ mid > Zlength l by lia.
  - rewrite !Zlength_sublist; lia.
  - rewrite sublist_same_gen; try lia. rewrite sublist_nil_gen; try lia. list_solve.
Qed.

Lemma sublist_same_Zlength: forall {A} mid (l1 l2: list A),
  0 <= mid ->
  Zlength l1 = Zlength l2 ->
  Zlength (sublist 0 mid l1) = Zlength (sublist 0 mid l2).
Proof.
  move => A mid l1 l2 Hmid Hlen. 
  have [Hin | Hout] : mid <= Zlength l1 \/ mid > Zlength l1 by lia.
  - rewrite !Zlength_sublist; lia.
  - rewrite !sublist_same_gen; lia.
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

Lemma le_Z_N: forall (m n: Z),
  m <= n ->
  (Z.to_nat m <= Z.to_nat n)%N.
Proof.
  move => m n Hmn. apply (introT leP). lia.
Qed.
  
Section ListMx.

Variable F : fieldType.

Local Open Scope ring_scope.

Instance inhabitant_F: Inhabitant F.
apply 0.
Defined.

Definition matrix := list (list F).

Definition wf_matrix (mx: matrix) (m n : Z) :=
  Zlength mx = m /\ 0 <= n /\ forall x, In x mx -> Zlength x = n.

(*get the (i,j)th entry of a matrix*)
Definition get (mx: matrix) (i j : Z) :=
  let row := Znth i mx in
  Znth j row.

Definition set (mx: matrix) (i j : Z) (k: F) :=
  let row := Znth i mx in
  let new_row := upd_Znth j row k in
  upd_Znth i mx new_row.

Lemma matrix_m_pos: forall {m n} (mx: matrix) (Hwf: wf_matrix mx m n),
  0 <= m.
Proof.
  move => m n mx. rewrite /wf_matrix => [[Hm Hn]]. list_solve.
Qed.

Lemma matrix_n_pos: forall {m n} (mx: matrix) (Hwf: wf_matrix mx m n),
  0 <= n.
Proof.
  move => m n mx. by rewrite /wf_matrix => [[Hm [Hn Hin]]].
Qed.

Definition matrix_to_mx m n (mx: matrix) : 'M[F]_(Z.to_nat m, Z.to_nat n) :=
  \matrix_(i < Z.to_nat m, j < Z.to_nat n) (get mx (Z.of_nat i) (Z.of_nat j)).

Section ScMul.

(*For the row operations, it will help to define "partial" versions that operate on a sublist, since
  we need need a loop invariant for the operation*)

Definition scalar_mul_row_partial (mx: matrix) (r: Z) (k: F) (bound: Z) : matrix :=
    let old_row := Znth r mx in
    let new_row := map (fun x => k * x) (sublist 0 bound old_row) ++ sublist bound (Zlength old_row) old_row in
    upd_Znth r mx new_row.

Definition scalar_mul_row (mx: matrix) (r: Z) (k: F) : matrix :=
  scalar_mul_row_partial mx r k (Zlength (Znth r mx)).

Lemma scalar_mul_row_partial_0: forall mx r k,
  scalar_mul_row_partial mx r k 0 = mx.
Proof.
  move => mx r k. rewrite /scalar_mul_row_partial sublist_nil /= sublist_same => [//|//|//].
  have [Hout | Hin]: ((0 > r \/ r >= Zlength mx) \/ 0 <= r < Zlength mx) by lia.
  - by apply upd_Znth_out_of_range.
  - apply Znth_eq_ext. list_solve. move => i len.
    have [Heq | Hneq]: (i = r \/ i <> r) by lia.
    + subst. by rewrite upd_Znth_same; try lia.
    + rewrite upd_Znth_diff => [//|//|//|//]. list_solve.
Qed.

Lemma scalar_mul_row_partial_wf: forall mx m n r k bound,
  0 <= bound ->
  0 <= r < m ->
  wf_matrix mx m n ->
  wf_matrix (scalar_mul_row_partial mx r k bound) m n.
Proof.
  move => mx m n r k bound Hb Hr. rewrite /wf_matrix /scalar_mul_row_partial => [[Hm [Hn Hin]]].
  split.  by list_solve. split. lia. move => x. rewrite In_Znth_iff => [[i [Hbound Hznth]]].
  have: 0 <= i < m. rewrite Zlength_solver.Zlength_upd_Znth in Hbound.
  by list_solve. move => {} Hbound.
  have [Hir | Hir]: i = r \/ i <> r by lia. subst. rewrite upd_Znth_same => [|//]. 
  rewrite Zlength_app Zlength_map (sublist_split_Zlength _ Hb). apply Hin. by apply Znth_In.
  subst; rewrite upd_Znth_diff; try lia. apply Hin. by apply Znth_In.
Qed.

Lemma scalar_mul_row_outside: forall m n mx r k b j,
  wf_matrix mx m n ->
  0 <= r < m ->
  0 <= b < n ->
  0 <= j < n ->
  b <= j ->
  get (scalar_mul_row_partial mx r k b) r j = get mx r j.
Proof.
  move => m n mx r k b j [Hlen [Hn Hin]] Hr Hb Hj Hbj. rewrite /scalar_mul_row_partial /get.
  rewrite upd_Znth_same; try lia.
  have Hsub: Zlength (sublist 0 b (Znth r mx)) = b. rewrite Zlength_sublist; try lia. rewrite Hin; try lia.
  apply Znth_In; lia. 
  rewrite Znth_app2; rewrite Zlength_map. rewrite Hsub.
  rewrite Znth_sublist; try list_solve. rewrite Hin. lia. apply Znth_In; lia.
  rewrite Hsub. lia.
Qed.

Lemma scalar_mul_row_spec: forall mx m n r k i j,
  wf_matrix mx m n ->
  (0 <= r < m) ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  get (scalar_mul_row mx r k) i j =
    if (Z.eq_dec i r) then k * (get mx i j) else get mx i j.
Proof.
  move => mx m n r h i j Hwf Hr. rewrite /scalar_mul_row /get /scalar_mul_row_partial sublist_nil 
  cats0 sublist_same => [|//|//]. move : Hwf => [Hm [Hn Hin]].
  case :  (Z.eq_dec i r) => [Hir Hi Hj /= | Hir Hi Hj /=].
  subst.  rewrite upd_Znth_same; try lia. rewrite Znth_map. by [].
  rewrite Hin => [//|]. by apply Znth_In; lia. rewrite upd_Znth_diff => [//|||//]. all: lia.
Qed. 

Lemma cat_app: forall {A: Type} (l1 l2 : list A),
  l1 ++ l2 = (l1 ++ l2)%list.
Proof.
  move => A l1 l2. elim : l1 => [// | h t IH /=].
  by rewrite IH.
Qed.

(*TODO: move*)
Lemma upd_Znth_twice: forall {A: Type} `{H: Inhabitant A} (l: list A) r x y,
  upd_Znth r (upd_Znth r l x) y = upd_Znth r l y.
Proof.
  move => A Hin l r x y. have [Hout | Hin']: ((0 > r \/ r >= Zlength l) \/ 0 <= r < Zlength l) by lia.
  - by rewrite !upd_Znth_out_of_range.
  - apply Znth_eq_ext. list_solve. move => i Hilen.
    have [Hir | Hir] : (i =r \/ i <> r) by lia.
    + subst. rewrite !upd_Znth_same; list_solve.
    + rewrite !upd_Znth_diff; list_solve.
Qed.

Lemma scalar_mul_row_plus_1_aux: forall mx r k b,
  0 <= r < Zlength mx ->
  0 <= b < Zlength (Znth r mx) ->
  scalar_mul_row_partial mx r k (b+1)%Z = set (scalar_mul_row_partial mx r k b) r b (k * (get mx r b)).
Proof.
  move => mx r k b hr Hb. rewrite /scalar_mul_row_partial /set.
  rewrite !sublist_last_1; try lia. rewrite upd_Znth_twice upd_Znth_same; try lia.
  rewrite upd_Znth_app2.
  - have ->: Zlength [seq k * x | x <- sublist 0 b (Znth r mx)] = b by rewrite Zlength_map; list_solve.
    have ->: ((b - b)%Z = 0%Z) by lia.
    rewrite (sublist_split b (b+1)%Z); try lia. rewrite sublist_len_1 => [|//].
    by rewrite upd_Znth0 map_cat -catA.
  - rewrite !Zlength_map. rewrite !Zlength_sublist; try lia. (*why doesn't lia do this?*)
    apply Z.lt_le_incl. apply Hb.
Qed. 

Lemma scalar_mul_row_plus_1: forall mx m n r k b,
  wf_matrix mx m n ->
  0 <= r < m ->
  0 <= b < n ->
  scalar_mul_row_partial mx r k (b+1)%Z = set (scalar_mul_row_partial mx r k b) r b (k * (get mx r b)).
Proof.
  move => mx m n r k b [Hlen [Hn Hin]] Hr Hb. apply scalar_mul_row_plus_1_aux. lia. rewrite Hin. by [].
  apply Znth_In. list_solve.
Qed.

(*Prove equivalent to [sc_mul]*)
Lemma scalar_mul_row_equiv: forall {m n} (mx: matrix) r k (Hr: 0 <= r < m),
  wf_matrix mx m n ->
  matrix_to_mx m n (scalar_mul_row mx r k) = sc_mul (matrix_to_mx m n mx) k (Z_to_ord Hr).
Proof.
  move => m n mx r k Hr Hwf. rewrite /matrix_to_mx /scalar_mul_row /sc_mul /Z_to_ord /= -matrixP /eqrel => [x y].
  rewrite !mxE. rewrite (scalar_mul_row_spec k Hwf). 
  - case: (Z.eq_dec (Z.of_nat x) r) => [Hxr /= | Hxr /=].
    have: x == Ordinal (Z_nat_bound Hr) by rewrite -Z_ord_eq. by move ->.
    case Hxord : (x == Ordinal (Z_nat_bound Hr)). have: Z.of_nat x = r. rewrite (Z_ord_eq x Hr). by apply Hxord.
    move => Hxr'. contradiction. by [].
  - by [].
  - apply Z_ord_bound. by lia.
  - apply Z_ord_bound. apply (matrix_n_pos Hwf).
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

Lemma Ziota_plus_1: forall (x len : Z),
  0 <= x ->
  0 <= len ->
  Ziota x (len + 1) = Ziota x len ++ [:: (x +len)%Z].
Proof.
  move => x len Hx Hlen. rewrite /Ziota.
  have ->: (Z.to_nat (len + 1) = Z.to_nat len + 1%nat)%nat by rewrite Z2Nat.inj_add; try lia.
  rewrite iotaD map_cat /=.
  f_equal. f_equal.
  have ->: ((Z.to_nat x + Z.to_nat len)%nat = Z.to_nat (x + len)%Z) by rewrite Z2Nat.inj_add; try lia.
  lia.
Qed.

(*Function to make all columns one (repeated scalar multiplication)*)
Section AllColsOne.

Definition all_cols_one_partial (mx: matrix) (c: Z) (bound: Z) :=
  fold_left (fun acc x => scalar_mul_row acc x (get mx x c)^-1 ) (Ziota 0 bound) mx.

Lemma all_cols_one_plus_1: forall mx c b,
  0 <= b ->
  all_cols_one_partial mx c (b+1) = scalar_mul_row (all_cols_one_partial mx c b) b (get mx b c)^-1.
Proof.
  move => mx c b Hb. rewrite /all_cols_one_partial Ziota_plus_1; try lia.
  by rewrite fold_left_app /=.
Qed.

Lemma all_cols_one_outside: forall m n mx c bound i j,
  wf_matrix mx m n ->
  0 <= bound <= i ->
  0 <= bound <= m ->
  0 <= i < m ->
  0 <= j < n ->
  get (all_cols_one_partial mx c bound) i j = get mx i j.
Proof.
  move => m n mx c bound i j Hwf Hbi Hbm Hi Hj. rewrite /all_cols_one_partial.
  have: ~In i (Ziota 0 bound) by rewrite Zseq_In; lia.
  have: forall x, In x (Ziota 0 bound) -> 0 <= x < bound by move => x; rewrite Zseq_In; lia.
  remember mx as mx' eqn : Hmx. rewrite {1}Hmx {Hmx}. move : mx' Hwf.  
  elim : (Ziota 0 bound) => [//|h t IH mx' Hwf Hallin Hnotin /=].
  have Hh: 0 <= h < m. have H: 0 <= h < bound by apply Hallin; left. lia.
  rewrite IH. rewrite (scalar_mul_row_spec _ Hwf) => [|//|//|//].
  - case: (Z.eq_dec i h) => [Hih /= | Hneq /=]. subst. exfalso. apply Hnotin. by left. by [].
  - rewrite /scalar_mul_row. apply scalar_mul_row_partial_wf => [|//|//]. move: Hwf => [Hlen [Hn Hin]].
    rewrite Hin. lia. apply Znth_In; lia. 
  - move => x Hinx. apply Hallin. by right.
  - move => Hint. apply Hnotin. by right.
Qed.

Lemma all_cols_one_equiv_partial: forall {m n} (mx: matrix) (c: Z) (Hc: 0 <= c < n) bound,
  0 <= bound <= m ->
  wf_matrix mx m n ->
  matrix_to_mx m n (all_cols_one_partial mx c bound) = all_cols_one_noif_gen (matrix_to_mx m n mx) (Z_to_ord Hc)
  (pmap insub (iota 0 (Z.to_nat bound))). 
Proof.
  move => m n mx c Hc b Hb Hwf. rewrite all_cols_one_noif_gen_foldl /all_cols_one_partial /all_cols_one_noif_l_gen /Ziota /ord_enum.
  have ->: (Z.to_nat 0) = 0%N by lia.
  have: forall n, n \in (iota 0 (Z.to_nat b)) -> (n < Z.to_nat b)%N. move => n'. by rewrite mem_iota.
  remember mx as mx' eqn : Hmx. have Hwf' : wf_matrix mx m n by rewrite -Hmx. 
  rewrite {2}Hmx. rewrite {3}Hmx. move: mx {Hmx} Hwf Hwf'.  
  elim: (iota 0 (Z.to_nat b)) => [//| h t IH mx Hwf Hwf' Hin].
  rewrite /=. have Hbound: (h < Z.to_nat b)%N. apply Hin. by rewrite in_cons eq_refl.
  have Hbm : (h < Z.to_nat m)%N. apply (ltn_leq_trans Hbound). apply (introT leP). lia. rewrite insubT /=.
  have Hhm : 0 <= Z.of_nat h < m. split. lia. have {} Hbound : (h < Z.to_nat m)%coq_nat by apply (elimT ltP).
  lia. rewrite IH.
  - rewrite scalar_mul_row_equiv. f_equal. rewrite /matrix_to_mx mxE.
    have /eqP Hhb: h == Ordinal Hbm by []. rewrite -Hhb.
    have /eqP Hhc : Z.to_nat c == (Z_to_ord Hc) by []. rewrite -Hhc. rewrite Z2Nat.id.
    + f_equal. apply (elimT eqP). have: nat_of_ord (Z_to_ord Hhm) = (Z.to_nat (Z.of_nat h)) by [].
      rewrite Nat2Z.id. move => Hzh. have: nat_of_ord (Z_to_ord Hhm) == nat_of_ord (Ordinal Hbound).
      by rewrite Hzh. by [].
    + lia.
    + by [].
  - by [].
  - apply scalar_mul_row_partial_wf. move : Hwf'; rewrite /wf_matrix => [[Hlen [H0n Hinlen]]].
    rewrite Hinlen. by []. apply Znth_In. lia. by []. by [].
  - move => n' Hinn'. apply Hin. by rewrite in_cons Hinn' orbT.
  - apply pmap_sub_uniq. apply iota_uniq.
Qed.

Lemma all_cols_one_list_equiv: forall {m n} (mx: matrix) (c: Z) (Hc: 0 <= c < n),
  wf_matrix mx m n ->
  matrix_to_mx m n (all_cols_one_partial mx c m) = all_cols_one_noif (matrix_to_mx m n mx) (Z_to_ord Hc).
Proof.
  move => m n mx c Hc Hwf. rewrite /all_cols_one_noif. apply all_cols_one_equiv_partial. split.
  apply (matrix_m_pos Hwf). lia. by [].
Qed.

Lemma all_cols_one_partial_wf: forall {m n} mx c bound,
  0 <= bound <= m ->
  wf_matrix mx m n ->
  wf_matrix (all_cols_one_partial mx c bound) m n.
Proof.
  move => m n mx c bound Hb. rewrite /all_cols_one_partial /Ziota.
  have ->: (Z.to_nat 0) = 0%N by lia.
  have: forall n, n \in (iota 0 (Z.to_nat bound)) -> (n < Z.to_nat bound)%N. move => n'. by rewrite mem_iota.
  remember mx as mx' eqn : Hmx. rewrite {1}Hmx {2}Hmx {Hmx}. move : mx.
  elim: (iota 0 (Z.to_nat bound)) => [//| h t IH mx Hin Hwf /=].
  - have Hbound: (h < Z.to_nat bound)%N. apply Hin. by rewrite in_cons eq_refl. 
    have Hhm : 0 <= Z.of_nat h < bound. split. lia. have {} Hbound : (h < Z.to_nat bound)%coq_nat by apply (elimT ltP).
    lia. apply IH.  move => n' Hinn'. apply Hin. by rewrite in_cons Hinn' orbT. apply scalar_mul_row_partial_wf.
    move : Hwf => [Hlen [Hn0 Hinlen]]. rewrite Hinlen =>[//|]. apply Znth_In. list_solve. lia. by [].
Qed. 

End AllColsOne.

(*Combine two lists with a pairwise binary operation - TODO: move probably*)
Fixpoint combineWith {X Y Z: Type} (l1 : list X) (l2: list Y) (f: X -> Y -> Z) : list Z :=
  match (l1, l2) with
  | (h1 :: t1, h2 :: t2) => f h1 h2 :: combineWith t1 t2 f
  | (_, _) => nil
  end.

Lemma combineWith_Zlength: forall {X Y Z} l1 l2 (f : X -> Y -> Z),
  Zlength l1 = Zlength l2 ->
  Zlength (combineWith l1 l2 f) = Zlength l1.
Proof.
  move => X Y Z l1. elim : l1 => [//| h t IH l2 f /=]. case : l2.
  - by move ->.
  - move => a l. rewrite !Zlength_cons =>[Hlen]. apply Z.succ_inj in Hlen. f_equal. by apply IH.
Qed. 

Lemma combine_Znth: forall {X Y Z} `{Inhabitant X} `{Inhabitant Y} `{Inhabitant Z} l1 l2 (f: X -> Y -> Z) z,
  Zlength l1 = Zlength l2 ->
  0 <= z < Zlength l1 ->
  Znth z (combineWith l1 l2 f) = f (Znth z l1) (Znth z l2).
Proof.
  move => X Y Z I1 I2 H3 l1. elim: l1 => [l2 f z|h t IH l2 f z]. list_solve.
  case : l2. list_solve. move => h' t' Hlen Hz. rewrite //=.
  have [Hz0 | Hzpos]: (z = 0)%Z \/ 0 < z by lia. subst. list_solve.
  rewrite !Znth_pos_cons; try by []. apply IH; list_solve.
Qed.

Lemma combine_app: forall {X Y Z} `{Inhabitant X} `{Inhabitant Y} `{Inhabitant Z} l1 l2 l3 l4 (f: X -> Y -> Z),
  Zlength l1 = Zlength l3 ->
  Zlength l2 = Zlength l4 ->
  combineWith (l1 ++ l2) (l3 ++ l4) f = (combineWith l1 l3 f) ++ (combineWith l2 l4 f).
Proof.
  move => X Y Z I1 I2 I3 l1 l2 l3 l4 f. move : l2 l3 l4. elim : l1 => [/= l2 l3 l4 H13 H24|h t IH l2 l3 l4 H13 H24 /=].
  - by have ->: l3 = nil by list_solve.
  - move : H13 IH. case : l3; move => h' t'.
    + list_solve.
    + move => Hht IH. have Htt': Zlength t = Zlength t' by list_solve.
      rewrite /=. by rewrite IH.
Qed. 

Section AddRow.

(*Once again, we only add the first [bound] indices, which will help in the VST proofs*)
Definition add_multiple_partial (mx: matrix) (r1 r2 : Z) (k : F) (bound: Z) : matrix :=
   let new_r2 := combineWith (sublist 0 bound (Znth r2 mx)) (sublist 0 bound (Znth r1 mx)) (fun x y => x + (k * y)) ++
    sublist bound (Zlength (Znth r2 mx)) (Znth r2 mx) in
  upd_Znth r2 mx new_r2.

Lemma add_multiple_partial_0: forall mx r1 r2 k,
  add_multiple_partial mx r1 r2 k 0 = mx.
Proof.
  move => mx r1 r2 k. rewrite /add_multiple_partial. rewrite sublist_nil /= sublist_same => [|//|//].
  have [Hout | Hin]: ((0 > r2 \/ r2 >= Zlength mx) \/ 0 <= r2 < Zlength mx) by lia.
  - by apply upd_Znth_out_of_range.
  - apply Znth_eq_ext. list_solve. move => i len.
    have [Heq | Hneq]: (i = r2 \/ i <> r2) by lia.
    + subst. by rewrite upd_Znth_same; try lia.
    + rewrite upd_Znth_diff => [//|//|//|//]. list_solve.
Qed.

Lemma add_multiple_partial_plus_1: forall m n mx r1 r2 k b,
  wf_matrix mx m n ->
  0 <= r1 < m ->
  0 <= r2 < m ->
  0 <= b < n ->
  add_multiple_partial mx r1 r2 k (b + 1) =
    set (add_multiple_partial mx r1 r2 k b) r2 b ((get mx r2 b) + (k * (get mx r1 b)))%R.
Proof.
  move => m n mx r1 r2 k b [Hlen [Hn Hin]] Hr1 Hr2 Hb.
  rewrite /add_multiple_partial /set.
  rewrite !sublist_last_1; try lia. rewrite upd_Znth_twice upd_Znth_same; try lia.
  have Hcomblen:
     Zlength (combineWith (sublist 0 b (Znth r2 mx)) (sublist 0 b (Znth r1 mx)) (fun x y : F => x + k * y)) = b.
  { rewrite combineWith_Zlength; rewrite !Zlength_sublist; try lia. all: rewrite Hin; try lia; apply Znth_In; lia. }
  rewrite upd_Znth_app2; rewrite Hcomblen.
  - have ->: ((b - b)%Z = 0%Z) by lia.
    rewrite (sublist_split b (b+1)%Z); try lia. rewrite sublist_len_1 => [|//].
    rewrite upd_Znth0. rewrite combine_app //=.
    by rewrite -catA. rewrite !Zlength_sublist; try lia. 
    all: rewrite Hin; try lia; apply Znth_In; lia.
  - pose proof (Zlength_nonneg (sublist b (Zlength (Znth r2 mx)) (Znth r2 mx))); lia.
  - rewrite Hin; try lia; apply Znth_In; lia.
  - rewrite Hin; try lia; apply Znth_In; lia.
Qed.

Lemma add_multiple_partial_outside: forall m n mx r1 r2 k b j,
  wf_matrix mx m n ->
  0 <= r1 < m ->
  0 <= r2 < m ->
  0 <= b < n ->
  0 <= j < n ->
  b <= j ->
  get (add_multiple_partial mx r1 r2 k b) r2 j = get mx r2 j.
Proof.
  move => m n mx r1 r2 k b j [Hlen [Hn Hin]] Hr1 Hr2 Hb Hj Hbj.
  rewrite /add_multiple_partial /get.
  rewrite upd_Znth_same; try lia.
  have Hcomlen: Zlength (combineWith (sublist 0 b (Znth r2 mx)) (sublist 0 b (Znth r1 mx)) (fun x y : F => x + k * y)) = b
   by rewrite combineWith_Zlength !Zlength_sublist; try lia; rewrite Hin; try lia; apply Znth_In; lia.
  rewrite Znth_app2; rewrite Hcomlen; try lia.
  rewrite Znth_sublist; try lia. list_solve. rewrite Hin; try lia; apply Znth_In; lia.
Qed.

Lemma add_multiple_partial_other_row: forall m n mx r1 r2 k b i j,
  wf_matrix mx m n ->
  0 <= r1 < m ->
  0 <= r2 < m ->
  0 <= b < n ->
  0 <= j < n ->
  0 <= i < m ->
  i <> r2 ->
  get (add_multiple_partial mx r1 r2 k b) i j = get mx i j.
Proof.
  move => m n mx r1 r2 k b i j [Hlen [Hn Hin]] Hr1 Hr2 Hb Hj Hi Hir2.
  rewrite /add_multiple_partial /get.
  rewrite upd_Znth_diff; try lia. reflexivity.
Qed. 
  

Definition add_multiple (mx: matrix) (r1 r2 : Z) (k: F) : matrix :=
  add_multiple_partial mx r1 r2 k (Zlength (Znth r1 mx)).

Lemma add_multiple_partial_wf: forall mx m n r1 r2 k bound,
  0 <= bound ->
  0 <= r1 < m ->
  0 <= r2 < m ->
  wf_matrix mx m n ->
  wf_matrix (add_multiple_partial mx r1 r2 k bound) m n.
Proof.
  move => mx m n r1 r2 k bound Hb Hr1 Hr2. rewrite /wf_matrix /add_multiple_partial /= => [[Hm [Hn Hin]]]. subst.
  split. list_solve. split =>[//| l]. rewrite In_Znth_iff =>[[i [Hlen Hznth]]].
  have {} Hlen: 0 <= i < Zlength mx by list_solve.
  have [Heq | Hneq]: i = r2 \/ i <> r2 by lia. subst.
  rewrite upd_Znth_same => [|//]. rewrite Zlength_app combineWith_Zlength. rewrite sublist_split_Zlength =>[|//].
  apply Hin. by apply Znth_In; lia. apply sublist_same_Zlength. lia. rewrite !Hin. by [].
  all: try(apply Znth_In; lia). rewrite -Hznth upd_Znth_diff; try lia. apply Hin. by (apply Znth_In; lia).
Qed.

Lemma add_multiple_spec: forall (mx: matrix) m n r1 r2 k i j,
  wf_matrix mx m n ->
  (0 <= r1 < m) ->
  (0 <= r2 < m) ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  get (add_multiple mx r1 r2 k) i j =
    if (Z.eq_dec i r2) then (get mx r2 j) + k * (get mx r1 j)
    else get mx i j.
Proof.
  move => mx m n r1 r2 k i j [Hm [Hn Hin]] Hr1 Hr2. rewrite /add_multiple /add_multiple_partial.
  have Hlen: Zlength (Znth r1 mx) = Zlength (Znth r2 mx). { rewrite !Hin =>[//||]. all: apply Znth_In; lia. }
  rewrite Hlen sublist_nil cats0 !sublist_same; try lia.
  case : (Z.eq_dec i r2) => [Hir2 Hi Hj /=| Hir Hi Hj /=].
  - subst. rewrite /get upd_Znth_same =>[|//]. rewrite combine_Znth =>[//|//|]. rewrite Hin =>[//|].
    by apply Znth_In; lia.
  - by subst; rewrite /get upd_Znth_diff =>[|//|//|//].
Qed.

(*Equivalence with [add_mul]*)
Lemma add_multiple_row_equiv: forall {m n} (mx: matrix) (r1 r2: Z) (k: F) (Hr1 : 0 <= r1 < m) (Hr2: 0 <= r2 < m),
  wf_matrix mx m n ->
  matrix_to_mx m n (add_multiple mx r1 r2 k) = add_mul (matrix_to_mx m n mx) k (Z_to_ord Hr1) (Z_to_ord Hr2).
Proof.
  move => m n mx r1 r2 k Hr1 Hr2 Hwf. rewrite /matrix_to_mx /add_mul /add_multiple -matrixP /= /eqrel =>[x y].
  rewrite !mxE (add_multiple_spec k Hwf); try lia.
  case : (Z.eq_dec (Z.of_nat x) r2) => [Hxr2 /= | Hxr2 /=].
  have ->: x == Z_to_ord Hr2 by rewrite -Z_ord_eq. by rewrite !Z2Nat.id; try lia.
  case Hxord : (x == Z_to_ord Hr2). have Hcont: Z.of_nat x = r2 by rewrite (Z_ord_eq x Hr2). by [].
  by []. apply Z_ord_bound; lia. apply Z_ord_bound. apply (matrix_n_pos Hwf).
Qed. 

End AddRow.

(*The last intermediate function is the analogue of [sub_all_rows]*)
Section SubRows.

Definition sub_all_rows_partial (mx: matrix) (r: Z) (bound: Z) :=
  fold_left (fun acc x => if Z.eq_dec x r then acc else add_multiple acc r x (- 1)) (Ziota 0 bound) mx.

Lemma sub_all_rows_plus_1: forall mx r b,
  0 <= b ->
  sub_all_rows_partial mx r (b+1) = if Z.eq_dec b r then (sub_all_rows_partial mx r b) else 
     add_multiple (sub_all_rows_partial mx r b) r b (- 1).
Proof.
  move => mx r b Hb. rewrite /sub_all_rows_partial Ziota_plus_1; try lia.
  case : (Z.eq_dec b r) => [Heq //= | Hneq //=].
  - subst. rewrite fold_left_app /=. by case : (Z.eq_dec r r).
  - rewrite fold_left_app /=.
    by case : (Z.eq_dec b r) => [Hbreq // | Hbrneq /=].
Qed. 

Lemma sub_all_rows_outside: forall m n mx r bound i j,
  wf_matrix mx m n ->
  0 <= r < m ->
  0 <= bound <= i ->
  0 <= bound <= m ->
  0 <= i < m ->
  0 <= j < n ->
  get (sub_all_rows_partial mx r bound) i j = get mx i j.
Proof.
  move => m n mx r bound i j Hwf Hr Hbi Hbm Hi Hj. rewrite /sub_all_rows_partial.
  have : ~In i (Ziota 0 bound) by rewrite Zseq_In; lia.
  have: forall x, In x (Ziota 0 bound) -> 0 <= x < bound by move => x; rewrite Zseq_In; lia.
  move : mx Hwf.
  elim : (Ziota 0 bound) => [//|h t IH mx' Hwf Hallin Hnotin /=].
  have Hh: 0 <= h < m. have H: 0 <= h < bound by apply Hallin; left. lia.
  case : (Z.eq_dec h r) => [Hhr /= | Hhr /=].
  - subst. apply IH => [//||]. move => x Hinx. apply Hallin. by right.
    move => Hint. apply Hnotin. by right.
  - rewrite IH. rewrite (add_multiple_spec _ Hwf) => [|//|//|//|//].
    case : (Z.eq_dec i h) => [Hih /= | Hih /=]. subst. exfalso. apply Hnotin. by left.
    by []. apply add_multiple_partial_wf; try lia; auto.
    move : Hwf => [Hlen [Hn Hin]]. rewrite Hin; try lia; apply Znth_In; lia.
    move => x' Hinx'. apply Hallin. by right. move => Hint. apply Hnotin. by right.
Qed.

Lemma sub_all_rows_equiv: forall {m n} (mx: matrix) (r: Z) (Hr: 0 <= r < m),
  wf_matrix mx m n ->
  matrix_to_mx m n (sub_all_rows_partial mx r m) = sub_all_rows_noif (matrix_to_mx m n mx) (Z_to_ord Hr).
Proof.
  move => m n mx r Hr. rewrite sub_all_rows_noif_foldl /sub_all_rows_partial /sub_all_rows_noif_l /Ziota /ord_enum.
  have ->: (Z.to_nat 0) = 0%N by lia.
  have: forall n, n \in (iota 0 (Z.to_nat m)) -> (n < Z.to_nat m)%N. move => n'. by rewrite mem_iota. move : mx.
  elim: (iota 0 (Z.to_nat m)) => [//| h t IH mx Hin Hwf].
  rewrite /=. have Hbound: (h < Z.to_nat m)%N. apply Hin. by rewrite in_cons eq_refl. rewrite insubT /=.
  have Hhm : 0 <= Z.of_nat h < m. split. lia. have Hbound' : (h < Z.to_nat m)%coq_nat by apply (elimT ltP).
  lia. 
  rewrite IH.
  - case : (Z.eq_dec (Z.of_nat h) r) => [Heq /= | Hneq /=].
    + have ->: Ordinal Hbound == Z_to_ord Hr by rewrite -Z_ord_eq. by [].
    + case Hord: (Ordinal Hbound == Z_to_ord Hr). have Heqr: Z.of_nat h = r
      by rewrite (Z_ord_eq (Ordinal Hbound) Hr). by [].
      rewrite add_multiple_row_equiv. f_equal. f_equal. apply (elimT eqP).
      have: nat_of_ord (Z_to_ord Hhm) = (Z.to_nat (Z.of_nat h)) by [].
      rewrite Nat2Z.id. move => Hzh. have: nat_of_ord (Z_to_ord Hhm) == nat_of_ord (Ordinal Hbound).
      by rewrite Hzh. by []. by [].
  - move => n' Hinn'. apply Hin. by rewrite in_cons Hinn' orbT.
  - case : (Z.eq_dec (Z.of_nat h) r) => [// | Hneq /=].
    apply add_multiple_partial_wf; try lia. move: Hwf => [Hlen [H0n Hinlen]].
    rewrite Hinlen. lia. apply Znth_In. lia. by [].
Qed.

Lemma sub_all_rows_partial_wf: forall {m n} mx r bound,
  0 <= bound <= m ->
  0 <= r < m ->
  wf_matrix mx m n ->
  wf_matrix (sub_all_rows_partial mx r bound) m n.
Proof.
  move => m n mx c bound Hb Hr. rewrite /sub_all_rows_partial /Ziota.
  have ->: (Z.to_nat 0) = 0%N by lia.
  have: forall n, n \in (iota 0 (Z.to_nat bound)) -> (n < Z.to_nat bound)%N. move => n'. by rewrite mem_iota.
  move : mx.
  elim: (iota 0 (Z.to_nat bound)) => [//| h t IH mx Hin Hwf /=].
  have Hbound: (h < Z.to_nat bound)%N. apply Hin. by rewrite in_cons eq_refl. 
  have Hhm : 0 <= Z.of_nat h < bound. split. lia. have {} Hbound : (h < Z.to_nat bound)%coq_nat by apply (elimT ltP).
  lia. apply IH. move => n' Hinn'. apply Hin. by rewrite in_cons Hinn' orbT.
  case : (Z.eq_dec (Z.of_nat h) c) => [// | Hneq /=].
  apply add_multiple_partial_wf; try lia. move: Hwf => [Hlen [H0n Hinlen]].
  rewrite Hinlen. lia. apply Znth_In. lia. by [].
Qed.

End SubRows.

Section AllSteps.

Definition gauss_all_steps_rows_partial (mx: matrix) m (bound : Z) :=
  fold_left (fun acc r => let A1 := (all_cols_one_partial acc r m) in sub_all_rows_partial A1 r m) (Ziota 0 bound) mx.

Lemma gauss_all_steps_rows_partial_plus_1: forall mx m b,
  0 <= b ->
  gauss_all_steps_rows_partial mx m (b+1) =
  sub_all_rows_partial (all_cols_one_partial (gauss_all_steps_rows_partial mx m b) b m) b m.
Proof.
  move => mx m n Hb. rewrite /gauss_all_steps_rows_partial Ziota_plus_1; try lia.
  by rewrite fold_left_app.
Qed. 

Lemma gauss_all_steps_rows_equiv: forall {m n} (mx: matrix) (Hmn : m <= n) r,
  wf_matrix mx m n ->
  0 <= r <= m ->
  matrix_to_mx m n (gauss_all_steps_rows_partial mx m r) = gauss_all_steps_restrict_beg (matrix_to_mx m n mx) (le_Z_N Hmn) (Z.to_nat r).
Proof.
  move => m n mx Hmn r Hwf Hrm. rewrite /gauss_all_steps_rows_partial /gauss_all_steps_restrict_beg /Ziota
  /gauss_all_steps_restrict_aux.
  have ->: (Z.to_nat 0) = 0%N by lia.
  have: forall n, n \in (iota 0 (Z.to_nat r)) -> (n < Z.to_nat r)%N. move => n'. by rewrite mem_iota. move : mx Hwf.
  elim: (iota 0 (Z.to_nat r)) => [//| h t IH mx Hwf Hin].
  rewrite /=. have Hhr: (h < Z.to_nat r)%N. apply Hin. by rewrite in_cons eq_refl.
  have Hhr': 0 <= Z.of_nat h < r. split. lia. 
  have Hbound' : (h < Z.to_nat r)%coq_nat by apply (elimT ltP). lia.
  have Hhm : (h < Z.to_nat m)%N. apply (ltn_leq_trans Hhr). apply (introT leP). lia.
  have Hhm' : (0 <= Z.of_nat h < m) by lia. 
  have Hwf_inter : wf_matrix (all_cols_one_partial mx (Z.of_nat h) m) m n.
  apply all_cols_one_partial_wf. lia. by [].
  rewrite insubT IH /gauss_one_step_restrict. f_equal. 
  rewrite sub_all_rows_equiv. rewrite all_cols_one_list_equiv. lia. move => Hhn. rewrite /=.
  have ->: (Z_to_ord Hhn) = (widen_ord (le_Z_N Hmn) (Ordinal Hhm)). apply (elimT eqP).
  have : nat_of_ord (Z_to_ord Hhn) == Z.to_nat (Z.of_nat h) by []. by rewrite Nat2Z.id.
  have ->: (Z_to_ord Hhm') = (Ordinal Hhm). apply (elimT eqP). 
  have: nat_of_ord (Z_to_ord Hhm') == Z.to_nat (Z.of_nat h) by []. by rewrite Nat2Z.id. by []. by [].
  by []. apply sub_all_rows_partial_wf. lia. lia. by [].
  move => n' Hnin. apply Hin. by rewrite in_cons Hnin orbT.
Qed.

Lemma gauss_all_steps_rows_partial_wf: forall {m n} (mx: matrix) bound,
  0 <= bound <= m ->
  wf_matrix mx m n ->
  wf_matrix (gauss_all_steps_rows_partial mx m bound) m n.
Proof.
  move => m n mx bound Hb. rewrite /gauss_all_steps_rows_partial /Ziota.
  have ->: (Z.to_nat 0) = 0%N by lia.
  have: forall n, n \in (iota 0 (Z.to_nat bound)) -> (n < Z.to_nat bound)%N. move => n'. by rewrite mem_iota.
  move : mx.
  elim: (iota 0 (Z.to_nat bound)) => [//| h t IH mx Hin Hwf /=].
  have Hbound: (h < Z.to_nat bound)%N. apply Hin. by rewrite in_cons eq_refl. 
  have Hhm : 0 <= Z.of_nat h < bound. split. lia. have {} Hbound : (h < Z.to_nat bound)%coq_nat by apply (elimT ltP).
  lia. apply IH. move => n' Hinn'. apply Hin. by rewrite in_cons Hinn' orbT.
  apply sub_all_rows_partial_wf; try lia. by apply all_cols_one_partial_wf; try lia.
Qed.

End AllSteps.

(*Finally, the last function makes all leading coefficients 1*)

Section LCOne.

Definition all_lc_one_rows_partial (mx: matrix) (bound : Z) :=
  fold_left (fun acc x => scalar_mul_row acc x (get mx x x)^-1) (Ziota 0 bound) mx.

Lemma all_lc_one_plus_one: forall mx b,
  0 <= b ->
  all_lc_one_rows_partial mx (b+1) = scalar_mul_row (all_lc_one_rows_partial mx b) b (get mx b b)^-1.
Proof.
  move => mx b Hb. rewrite /all_lc_one_rows_partial Ziota_plus_1; try lia.
  by rewrite fold_left_app /=.
Qed.

Lemma all_lc_one_outside: forall m n mx bound i j,
  wf_matrix mx m n ->
  0 <= bound <= i ->
  0 <= i < m ->
  0 <= j < n ->
  get (all_lc_one_rows_partial mx bound) i j = get mx i j.
Proof.
  move => m n mx b i j Hwf Hbi Hi Hj.
  rewrite /all_lc_one_rows_partial.
  have: ~In i (Ziota 0 b) by rewrite Zseq_In; lia.
  have: forall x, In x (Ziota 0 b) -> 0 <= x < b by move => x; rewrite Zseq_In; lia.
  remember mx as mx' eqn : Hmx. rewrite {1}Hmx {Hmx}. move : mx' Hwf.  
  elim : (Ziota 0 b) => [//|h t IH mx' Hwf Hallin Hnotin /=].
  have Hh: 0 <= h < m. have H: 0 <= h < b by apply Hallin; left. lia.
  rewrite IH. rewrite (scalar_mul_row_spec _ Hwf) => [|//|//|//].
  - case: (Z.eq_dec i h) => [Hih /= | Hneq /=]. subst. exfalso. apply Hnotin. by left. by [].
  - apply scalar_mul_row_partial_wf => [|//|//]. move: Hwf => [Hlen [Hn Hin]].
    rewrite Hin. lia. apply Znth_In; lia. 
  - move => x Hinx. apply Hallin. by right.
  - move => Hint. apply Hnotin. by right.
Qed.

(*There is a slight complication - we only go to m - 1 because the last row's leading coefficient is already 1. This
  optimization is present in the C code*)
Lemma all_lc_one_rows_equiv: forall {m n} (mx: matrix) (Hmn: m <= n),
  wf_matrix mx m n ->
  matrix_to_mx m n (all_lc_one_rows_partial mx (m-1)) = mk_identity (matrix_to_mx m n mx) (le_Z_N Hmn) (Z.to_nat m-1).
Proof.
  move => m n mx Hmn Hwf. rewrite mk_identity_foldl /all_lc_one_rows_partial /mk_identity_l /Ziota /ord_enum.
  have[H0m | H0m]: m = 0%Z \/ 0 < m. apply matrix_m_pos in Hwf. lia.
  - by subst. 
  - have Hm1: (Z.to_nat (m-1)) = (Z.to_nat m - 1)%coq_nat by lia.
    have HmN: Z.to_nat (m - 1) = (Z.to_nat m - 1)%N by []. rewrite {Hm1} -HmN {HmN}.
    have ->: (Z.to_nat 0) = 0%N by lia. remember mx as mx' eqn : Hmx. rewrite {2}Hmx {3}Hmx. 
    have Hwf' : wf_matrix mx m n by rewrite -Hmx. move : Hwf' Hwf.
    have: forall n, n \in (iota 0 (Z.to_nat (m-1))) -> (n < Z.to_nat (m-1))%N. move => n'. by rewrite mem_iota. 
    move : {Hmx} mx. elim : (iota 0 (Z.to_nat (m-1))) => [//|h t IH mx Hin Hwf Hwf'].
    rewrite /=.
    have Hm1: (Z.to_nat (m-1) < Z.to_nat m)%N. have Htemp: (Z.to_nat (m-1) < Z.to_nat m)%coq_nat by lia.
    by apply (introT ltP).
    have Hhm1: (h < Z.to_nat (m-1))%N. apply Hin. by rewrite in_cons eq_refl.
    have Hhm: (h < Z.to_nat m)%N by apply (ltn_trans Hhm1 Hm1).
    have Hhm': 0 <= Z.of_nat h < m. split. lia. have Hbound' : (h < Z.to_nat m)%coq_nat by apply (elimT ltP). lia.
    rewrite insubT IH /=; try by [].
    rewrite scalar_mul_row_equiv. rewrite {5}/matrix_to_mx mxE. f_equal. f_equal. apply (elimT eqP).
    have: nat_of_ord (Z_to_ord Hhm') == Z.to_nat (Z.of_nat h) by []. by rewrite Nat2Z.id. by [].
    move => n' Hnin. apply Hin. by rewrite in_cons Hnin orbT. apply scalar_mul_row_partial_wf; try lia.
    move : Hwf => [Hlen [H0n Hinlen]]. rewrite Hinlen =>[//|]. apply Znth_In; lia. by [].
Qed.

Lemma all_lc_one_rows_partial_wf: forall {m n} mx bound,
  0 <= bound <= m ->
  wf_matrix mx m n ->
  wf_matrix (all_lc_one_rows_partial mx bound) m n.
Proof.
  move => m n mx bound Hb Hwf. rewrite /all_lc_one_rows_partial /Ziota.
  have ->: (Z.to_nat 0) = 0%N by lia.
  have: forall n, n \in (iota 0 (Z.to_nat bound)) -> (n < Z.to_nat bound)%N. move => n'. by rewrite mem_iota.
  remember mx as mx' eqn : Hmx. move : Hwf. rewrite {3}Hmx {1}Hmx {Hmx}. move : mx.
  elim: (iota 0 (Z.to_nat bound)) => [//| h t IH mx Hwf Hin /=].
  have Hbound: (h < Z.to_nat bound)%N. apply Hin. by rewrite in_cons eq_refl. 
  have Hhm : 0 <= Z.of_nat h < bound. split. lia. have {} Hbound : (h < Z.to_nat bound)%coq_nat by apply (elimT ltP).
  lia. apply IH. apply scalar_mul_row_partial_wf; try lia.
  move : Hwf => [Hlen [Hn0 Hinlen]]. rewrite Hinlen =>[//|]. apply Znth_In. list_solve. by []. 
  move => n' Hinn'. apply Hin. by rewrite in_cons Hinn' orbT.
Qed. 

End LCOne.

Section GaussFull.

Definition gauss_restrict_rows (mx: matrix) m :=
  all_lc_one_rows_partial (gauss_all_steps_rows_partial mx m m) (m-1).


Lemma gauss_restrict_rows_equiv: forall {m n} (mx: matrix) (Hmn: m <= n),
  wf_matrix mx m n ->
  matrix_to_mx m n (gauss_restrict_rows mx m) = gaussian_elim_restrict (matrix_to_mx m n mx) (le_Z_N Hmn).
Proof.
  move => m n mx Hmn Hwf.
  have H0m: 0 <= m by apply (matrix_m_pos Hwf).
  rewrite /gauss_restrict_rows /gaussian_elim_restrict all_lc_one_rows_equiv.
  rewrite gauss_all_steps_rows_equiv. rewrite -gauss_all_steps_restrict_both_dirs.
  by rewrite subn1. by []. lia.
  apply gauss_all_steps_rows_partial_wf =>[|//]. lia.
Qed.

Lemma gauss_restrict_rows_wf: forall {m n} (mx: matrix),
  wf_matrix mx m n ->
  wf_matrix (gauss_restrict_rows mx m) m n.
Proof.
  move => m n mx Hwf. have H0m: 0 <= m by apply (matrix_m_pos Hwf).
  have [H0meq | H0mlt]:  (0%Z = m \/ 0 < m) by lia.
  - subst. by rewrite /gauss_restrict_rows /= /gauss_all_steps_rows_partial /= /all_lc_one_rows_partial /=.
  - apply all_lc_one_rows_partial_wf.
    lia. apply gauss_all_steps_rows_partial_wf. lia. by [].
Qed.

End GaussFull.
(*
Lemma Z_range_le_le_dec: forall x y z : Z,
  { x <= y <= z } + {~ (x <= y <= z)}.
Proof.
  move => x y z. case : (Z_le_lt_dec x y) => [Hxy | Hxy].
  - case : (Z_le_lt_dec y z) => [Hyz | Hyz]. left. lia. right. lia.
  - right. lia.
Qed.
*)
(*We need a way to specify that a list matrix m satisfies [strong_inv] without using dependent types*)
Definition strong_inv_list m n (mx: matrix) (r: Z) : Prop :=
  match (range_le_lt_dec 0 r m) with
  | left Hrm =>
      match (Z_le_lt_dec m n) with
      | left H => strong_inv (matrix_to_mx m n mx) (le_Z_N H) (Z_to_ord Hrm)
      | right _ => False
      end
  |right _ => False
  end.

Lemma strong_inv_list_unfold: forall m n mx r (Hrm : 0 <= r < m) (Hmn : m <= n),
  strong_inv_list m n mx r ->
  strong_inv (matrix_to_mx m n mx) (le_Z_N Hmn) (Z_to_ord Hrm).
Proof.
  move => m n mx r Hrm Hmn. rewrite /strong_inv_list. destruct (range_le_lt_dec 0 r m) => [|//]. (*case doesnt work*)
  destruct (Z_le_lt_dec m n) => [|//]. move => Hstr.
  have <-: (le_Z_N l) = (le_Z_N Hmn) by apply ProofIrrelevance.proof_irrelevance. 
  rewrite strong_inv_dep. apply Hstr. by have: Z.to_nat r == Z.to_nat r by [].
Qed.

(*Even though we already know that the reduced Gaussian elimination is equivalent to the full algorithm
  if [strong_inv 0] is satisfied, that is not enough, since the C code checks and fails if the invariant
  is violated. So we need to use some of the intermediate theories from Gaussian.v - in particular, if we 
  have finished up to row r, then the rth column contains all nonzero entries. Here, we show in several
  steps the analogous result for the list matrices in use in VST*)

Lemma gauss_all_steps_rows_partial_strong_inv: forall m n mx r,
  wf_matrix mx m n ->
  0 <= r < m ->
  strong_inv_list m n mx 0 ->
  strong_inv_list m n (gauss_all_steps_rows_partial mx m r) r.
Proof.
  move => m n mx r Hwf Hrm. rewrite /strong_inv_list.
  case : (range_le_lt_dec 0 0 m) => [H0m | //].
  case : (Z_le_lt_dec m n) => [Hmn | //].
  case : (range_le_lt_dec 0 r m) => [{}Hrm | //]; try lia.
  rewrite gauss_all_steps_rows_equiv => [|//|//].
  rewrite {1}/Z_to_ord => [Hstr].
  have Hrmnat : ((Z.to_nat r) < (Z.to_nat m))%N. apply (introT ltP). lia.
  pose proof (@gauss_all_steps_restrict_beg_strong _ _ _ _ _ _ _ Hrmnat Hstr).
  rewrite strong_inv_dep. apply H. rewrite /Z_to_ord. by have: (Z.to_nat r == Z.to_nat r) by [].
  lia.
Qed.

Lemma gauss_all_steps_rows_partial_gauss_inv: forall m n mx r,
  wf_matrix mx m n ->
  0 <= r < m ->
  strong_inv_list m n mx 0 ->
  gauss_invar (matrix_to_mx m n (gauss_all_steps_rows_partial mx m r)) (Z.to_nat r) (Z.to_nat r).
Proof.
  move => m n mx r Hwf Hrm. rewrite /strong_inv_list. case : (range_le_lt_dec 0 0 m) => [H0m |//].
  case : (Z_le_lt_dec m n) => [Hmn Hstr | //].
  rewrite gauss_all_steps_rows_equiv => [|//|//].
  have H0rm: (0 + Z.to_nat r <= Z.to_nat m)%N. rewrite add0n. apply (introT leP). lia.
  pose proof (gauss_all_steps_restrict_aux_inv H0rm (gauss_invar_init _ ) Hstr) as Hinv'.
  rewrite add0n in Hinv'. by []. lia.
Qed.

Lemma gauss_all_steps_rows_partial_zeroes: forall m n mx r (Hr: 0 <= r < m) (Hmn : m <= n),
  wf_matrix mx m n ->
  strong_inv_list m n mx 0 ->
  (forall (x: 'I_(Z.to_nat m)), (matrix_to_mx m n (gauss_all_steps_rows_partial mx m r)) x (widen_ord (le_Z_N Hmn)
   (Z_to_ord Hr)) != 0).
Proof.
  move => m n mx r Hr Hmn Hwf Hstr x.
  apply strong_inv_nonzero_cols. by apply gauss_all_steps_rows_partial_gauss_inv.
  pose proof (gauss_all_steps_rows_partial_strong_inv Hwf Hr Hstr) as Htemp.
  by apply strong_inv_list_unfold.
Qed.

Lemma gauss_all_steps_columns_partial_zeroes: forall m n mx r (Hr: 0 <= r < m) (Hmn : m <= n) c ,
  0 <= c <= m ->
  wf_matrix mx m n ->
  strong_inv_list m n mx 0 ->
  (forall (x: 'I_(Z.to_nat m)),
  (matrix_to_mx m n (all_cols_one_partial (gauss_all_steps_rows_partial mx m r) r c) x (widen_ord (le_Z_N Hmn)
   (Z_to_ord Hr))) != 0).
Proof.
  move => m n mx r Hr Hmn c Hc Hwf Hstr x. rewrite all_cols_one_equiv_partial. lia.
  move => Hrn.
  have Hord: Z_to_ord Hrn = widen_ord (le_Z_N Hmn) (Z_to_ord Hr). apply (elimT eqP). by
  have : Z.to_nat r == Z.to_nat r by []. rewrite Hord.
  have Hz: forall x0 : 'I_(Z.to_nat m),
    matrix_to_mx m n (gauss_all_steps_rows_partial mx m r) x0 (widen_ord (le_Z_N Hmn) (Z_to_ord Hr)) != 0.
  move => x'. by apply gauss_all_steps_rows_partial_zeroes.
  rewrite all_cols_one_noif_gen_zero. apply Hz. 2: apply Hz.
  apply pmap_sub_uniq. apply iota_uniq. by []. apply gauss_all_steps_rows_partial_wf. lia. by [].
Qed.

(*Finally, the result we need for the VST proof*)
Lemma gauss_all_steps_columns_partial_zeroes_list: forall m n mx r c,
  0 <= r < m ->
  0 <= c <= m ->
  m <= n ->
  wf_matrix mx m n ->
  strong_inv_list m n mx 0 ->
  (forall x, 0 <= x < m -> get (all_cols_one_partial (gauss_all_steps_rows_partial mx m r) r c) x r <> 0).
Proof.
  move => m n mx r c Hr Hc Hmn Hwf Hstr x Hx.
  pose proof (@gauss_all_steps_columns_partial_zeroes m n mx r Hr Hmn c Hc Hwf Hstr (Z_to_ord Hx)).
  move : H. rewrite /matrix_to_mx mxE.
  have ->: (Z.of_nat (Z_to_ord Hx)) = x.  have /eqP Hord: nat_of_ord (Z_to_ord Hx) == Z.to_nat x by []. rewrite Hord. lia.
  have ->: (Z.of_nat (widen_ord (le_Z_N Hmn) (Z_to_ord Hr))) = r. 
    have /eqP Hord: nat_of_ord (widen_ord (le_Z_N Hmn) (Z_to_ord Hr)) == Z.to_nat r by []. rewrite Hord. lia.
  move => Hneq. move => Hget. rewrite Hget in Hneq. by rewrite eq_refl in Hneq.
Qed. 

End ListMx.

Require Import Vandermonde.
Require Import Poly.
Require Import PolyMod.
Import WPoly.
Require Import PolyField.

(*Weight matrix definition*)
Section WeightMx.

Variable f : poly.
Variable Hpos : deg f > 0.
Variable Hirred : irreducible f.
Definition F := qpoly_fieldType Hpos Hirred.

Definition weight_mx_list (m n : Z) : matrix F :=
  prop_list (fun i => (prop_list (fun j => (poly_to_qpoly f Hpos (monomial (Z.to_nat (i * j))))) n)) m.

Lemma weight_matrix_wf: forall m n, 0 <= n -> 0 <= m -> wf_matrix (weight_mx_list m n) m n.
Proof.
  move => m n Hn Hm. rewrite /wf_matrix /weight_mx_list. repeat(split).
  - rewrite prop_list_length; lia.
  - by [].
  - move => x. rewrite In_Znth_iff. move => [i [Hilen Hith]].
    rewrite <- Hith. rewrite prop_list_Znth. rewrite prop_list_length; lia.
    rewrite prop_list_length in Hilen; lia.
Qed.

Lemma weight_mx_list_spec: forall m n, 
  0 <= m ->
  0 <= n ->
  matrix_to_mx m n (weight_mx_list m n) = vandermonde_powers Hpos Hirred (Z.to_nat m) (Z.to_nat n).
Proof.
  move => m n Hm Hn. rewrite -matrixP /eqrel. move => x y. rewrite mxE vandermonde_powers_val /get /weight_mx_list.
  rewrite !prop_list_Znth. rewrite exp_monomial =>[|//]. f_equal. f_equal. 
  have->: (x * y)%N = (x * y)%coq_nat by []. lia.
  split; try lia. have /ltP Hy: (y < Z.to_nat n)%N by []. lia.
  split; try lia. have /ltP Hx: (x < Z.to_nat m)%N by []. lia.
Qed. 
End WeightMx.