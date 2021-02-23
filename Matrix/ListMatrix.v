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
Require Import CommonSSR.

(*TODO: see if we need all of these*)

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
  Zlength mx = m /\ 0 <= n /\ Forall (fun x => Zlength x = n) mx.

(*get the (i,j)th entry of a matrix*)
Definition get (mx: matrix) (i j : Z) :=
  let row := Znth i mx in
  Znth j row.

Definition set (mx: matrix) (i j : Z) (k: F) :=
  let row := Znth i mx in
  let new_row := upd_Znth j row k in
  upd_Znth i mx new_row.

Lemma set_wf: forall m n mx i j k,
  wf_matrix mx m n ->
  wf_matrix (set mx i j k) m n.
Proof.
  move => m n mx i j k [Hlen [Hn Hin]].
  move : Hin; rewrite Forall_Znth /wf_matrix /set => Hin.
  split. list_solve. split. by []. rewrite Forall_Znth Zlength_upd_Znth => i' Hi'.
  have [Hii' | Hii']: i = i' \/ i <> i' by lia.
  - subst. rewrite upd_Znth_same; list_solve.
  - list_solve.
Qed. 

Lemma get_set: forall m n mx i j i' j' k,
  wf_matrix mx m n ->
  0 <= i < m ->
  0 <= i' < m ->
  0 <= j < n ->
  0 <= j' < n -> 
  get (set mx i' j' k) i j = if (Z.eqb i i') && (Z.eqb j j') then k else get mx i j.
Proof.
  move => m n mx i j i' j' k [Hlen [ Hn Hin]] Hi Hi' Hj Hj'. rewrite /get /set.
  move : Hin; rewrite Forall_Znth => Hin. 
  case Hii' : (Z.eqb i i'); move : Hii' => /Z.eqb_spec Hii' /=.
  - subst. rewrite upd_Znth_same; [| lia].
    case Hjj' : (Z.eqb j j'); move : Hjj' => /Z.eqb_spec Hjj' /=.
    + subst. rewrite upd_Znth_same. by []. rewrite Hin; lia.
    + by rewrite upd_Znth_diff; try rewrite Hin; try lia.
  - by rewrite upd_Znth_diff; try lia.
Qed.

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

Lemma matrix_ext_eq: forall m n mx1 mx2,
  wf_matrix mx1 m n ->
  wf_matrix mx2 m n ->
  (forall i j, 0 <= i < m -> 0 <= j < n -> get mx1 i j = get mx2 i j) -> 
  mx1 = mx2.
Proof.
  move => m n mx1 mx2 [Hm1 [Hn1 Hin1]] [Hm2 [Hn2 Hin2]] Hsame. apply Znth_eq_ext. lia.
  move => i Hi. move: Hin1 Hin2; rewrite !Forall_Znth => Hin1 Hin2.
  apply Znth_eq_ext. rewrite Hin1 =>[|//]. rewrite Hin2; lia.
  move => j Hj. rewrite Hin1 in Hj =>[|//]. apply Hsame; lia.
Qed.

(*Create a matrix by giving a function for the elements*)
Section GenMx.

Definition mk_matrix m n (f: Z -> Z -> F) : matrix :=
  prop_list (fun i => prop_list (fun j => f i j) n) m.

Lemma mk_matrix_wf: forall m n f,
  0 <= m ->
  0 <= n ->
  wf_matrix (mk_matrix m n f) m n.
Proof.
  move => m n f Hm Hn. rewrite /wf_matrix /mk_matrix prop_list_length =>[|//].
  repeat split; try lia. rewrite Forall_Znth prop_list_length =>[i Hi|//].
  rewrite prop_list_Znth; try lia. by rewrite prop_list_length.
Qed.

Lemma mk_matrix_get: forall m n f i j,
  0 <= i < m ->
  0 <= j < n ->
  get (mk_matrix m n f) i j = f i j.
Proof.
  move => m n f i j Hi Hj. rewrite /mk_matrix /get prop_list_Znth => [|//].
  by rewrite prop_list_Znth.
Qed.

Lemma mk_matrix_mx: forall m n f,
  0 <= m ->
  0 <= n ->
  matrix_to_mx m n (mk_matrix m n f) = \matrix_(i < Z.to_nat m, j < Z.to_nat n) (f (Z.of_nat i) (Z.of_nat j)).
Proof.
  move => m n f Hm Hn. rewrite /matrix_to_mx -matrixP /eqrel => x y.
  rewrite !mxE mk_matrix_get =>[//||].
  by apply Z_ord_bound.
  by apply Z_ord_bound.
Qed.

End GenMx.

(*So we don't have to repeat this every time. This is quite annoying with ssreflect for some reason*)
Ltac case_view E P H :=
  destruct E eqn : H; [ apply (elimT P) in H | apply (elimF P) in H].

Ltac case_eqb x y H :=
  case_view (x =? y) (Z.eqb_spec x y) H.

Ltac case_ltb x y H :=
  case_view (x <? y) (Z.ltb_spec0 x y) H.


Section ScMul.

(*For the row operations, it will help to define "partial" versions that operate on a sublist, since
  we need need a loop invariant for the operation*)

(*Really, this only makes sense if mx is a wf_matrix m n, but we want to avoid dependent types*)
Definition scalar_mul_row_partial m n (mx: matrix) (r: Z) (k: F) (bound: Z) :=
  mk_matrix m n (fun i j => if (Z.eqb i r) && (Z.ltb j bound) then k * (get mx i j) else (get mx i j)).

Definition scalar_mul_row m n mx r k :=
  scalar_mul_row_partial m n mx r k n.

Lemma scalar_mul_row_partial_0: forall m n mx r k,
  0 <= m ->
  0 <= n ->
  wf_matrix mx m n ->
  scalar_mul_row_partial m n mx r k 0 = mx.
Proof.
  move => m n mx r k Hm Hn Hwf. apply (@matrix_ext_eq m n). by apply mk_matrix_wf.
  by []. move => i j Hi  Hj. rewrite mk_matrix_get =>[|//|//].
  case_ltb j 0%Z Hlt.
  - lia.
  - by rewrite andbF.
Qed.

Lemma scalar_mul_row_partial_wf: forall mx m n r k bound,
  0 <= m ->
  0 <= n ->
  wf_matrix (scalar_mul_row_partial m n mx r k bound) m n.
Proof.
  move => mx m n r k b Hm Hn. by apply mk_matrix_wf.
Qed.

Lemma scalar_mul_row_outside: forall m n mx r k b j,
  wf_matrix mx m n ->
  0 <= r < m ->
  0 <= j < n ->
  b <= j ->
  get (scalar_mul_row_partial m n mx r k b) r j = get mx r j.
Proof.
  move => m n mx r k b j Hwf Hr Hj Hbj. rewrite mk_matrix_get =>[|//|//].
  case_eqb r r Hrr => [/= | //=].
  by case_ltb j b Hjb; try lia.
Qed.

Lemma scalar_mul_row_spec: forall mx m n r k i j,
  wf_matrix mx m n ->
  (0 <= i < m) ->
  (0 <= j < n) ->
  get (scalar_mul_row m n mx r k) i j =
    if (Z.eq_dec i r) then k * (get mx i j) else get mx i j.
Proof.
  move => mx m n r k i j Hwf Hi Hj. rewrite mk_matrix_get =>[|//|//].
  case_ltb j n Hjn; try lia.
  by case : (Z.eq_dec i r) => [Heq /= | Hneq /=]; case_eqb i r Hir.
Qed.

Lemma scalar_mul_row_plus_1: forall mx m n r k b,
  wf_matrix mx m n ->
  0 <= r < m ->
  0 <= b < n ->
  scalar_mul_row_partial m n mx r k (b+1)%Z = set (scalar_mul_row_partial m n mx r k b) r b (k * (get mx r b)).
Proof.
  move => mx m n r k b Hwf Hr Hb. apply (@matrix_ext_eq m n).
  - apply scalar_mul_row_partial_wf; lia.
  - apply set_wf. apply scalar_mul_row_partial_wf; lia.
  - move => i j Hi Hj. rewrite (@get_set m n); try by []. rewrite !mk_matrix_get; try by [].
    case_eqb i r Hir =>[/= | //]. subst.
    case_eqb j b Hjb.
    + subst. by case_ltb b (b+1)%Z Hbb1; try lia.
    + by case_ltb j b Hjblt; case_ltb j (b+1)%Z Hjb1; try lia.
    + apply scalar_mul_row_partial_wf; lia.
Qed.

Lemma scalar_mul_row_equiv: forall {m n} (mx: matrix) r k (Hr: 0 <= r < m),
  wf_matrix mx m n ->
  matrix_to_mx m n (scalar_mul_row m n mx r k) = sc_mul (matrix_to_mx m n mx) k (Z_to_ord Hr).
Proof.
  move => m n mx r k Hr Hwf. rewrite /sc_mul mk_matrix_mx.
  - rewrite -matrixP /eqrel => x y; rewrite !mxE /=.
    case_ltb (Z.of_nat y) n Hyn.
    + rewrite andbT. case_eqb (Z.of_nat x) r Hxr =>[/= | /=].
      * move : Hxr; rewrite (Z_ord_eq x Hr). by move ->.
      * case  Hxr' : (x == Z_to_ord Hr). by have hxr'': Z.of_nat x = r by  rewrite (Z_ord_eq x Hr).
        by [].
    + have Hn: 0 <= n by apply (matrix_n_pos Hwf). pose proof (Z_ord_bound y). lia.
  - apply (matrix_m_pos Hwf).
  - apply (matrix_n_pos Hwf).
Qed.

End ScMul.

(*Version of [iota] for nonnegative integers*)
Definition Ziota (x len : Z) :=
  map (fun y => Z.of_nat y) (iota (Z.to_nat x) (Z.to_nat len)).

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

Lemma Ziota_NoDup: forall x len,
  NoDup (Ziota x len).
Proof.
  move => x len. rewrite /Ziota. apply FinFun.Injective_map_NoDup.
  - rewrite /FinFun.Injective => x' y' Hxy. lia.
  - rewrite -uniq_NoDup. apply iota_uniq.
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

(*Generalized notion of repeated fold_left for row transformation (we have something similar in Gaussian for foldr*)

(*We need a function that a) only affects the row it is called on and b) preserves well-formedness*)
Definition fn_notin_conds m n (f: matrix -> Z -> matrix) :=
   (forall mx' i j r, wf_matrix mx' m n -> 0 <= i < m -> 0 <= j < n -> i <> r -> get mx' i j = get (f mx' r) i j)/\
  (forall mx' i, wf_matrix mx' m n -> wf_matrix (f mx' i) m n).
  

Lemma mx_foldl_notin: forall m n (mx: matrix) (f: matrix -> Z -> matrix) (l: list Z) i j,
  fn_notin_conds m n f ->
  0 <= i < m ->
  0 <= j < n ->
  ~In i l ->
  wf_matrix mx m n ->
  get (fold_left f l mx) i j = get mx i j.
Proof.
  move => m n mx f l i j [Hcond Hwfpres] Hi Hj. move : mx. elim : l => [//|h t IH /= mx Hin Hwf].
  rewrite IH. rewrite -Hcond; try by []. move => Heq. subst. apply Hin. by left.
  move => Hin'. apply Hin. by right. by apply Hwfpres.
Qed.

Definition fn_in_conds m n (f: matrix -> Z -> matrix) :=
  fn_notin_conds m n f /\
  (forall mx h i j, wf_matrix mx m n -> 0 <= i < m -> 0 <= j < n -> i <> h -> get (f (f mx h) i) i j = get (f mx i) i j).

Lemma mx_foldl_in: forall m n (mx: matrix) (f: matrix -> Z -> matrix) (l: list Z) i j,
  fn_in_conds m n f ->
  0 <= i < m ->
  0 <= j < n ->
  In i l ->
  NoDup l ->
  wf_matrix mx m n ->
  get (fold_left f l mx) i j = get (f mx i) i j.
Proof.
  move => m n mx f l i j [[Hcond Hwfpres] Htwice] Hi Hj. move : mx. elim : l => [//|h t IH /= mx Hin Hnodup Hwf].
  move: Hnodup; rewrite NoDup_cons_iff; move => [Hnotin  Hnodupt].
  case: Hin => [Hhi | Hin].
  - subst. rewrite (@mx_foldl_notin m n); try by []. by apply Hwfpres.
  - rewrite IH. apply Htwice; try by []. move => Heq. subst. by []. by []. by []. apply Hwfpres. by [].
Qed.

Lemma mx_foldl_wf: forall m n (mx: matrix) (f: matrix -> Z -> matrix) (l : list Z),
  (forall mx' i, wf_matrix mx' m n -> wf_matrix (f mx' i) m n) ->
  wf_matrix mx m n ->
  wf_matrix (fold_left f l mx) m n.
Proof.
  move => m n mx f l Hwfpres. move : mx. elim : l => [//|h t IH mx Hwf /=].
  apply IH. by apply Hwfpres.
Qed.

(*Now specialize this for functions operating on Ziota 0 b*)
Lemma foldl_ziota_get: forall m n (mx: matrix) (f: matrix -> Z -> matrix) (b: Z) i j,
  fn_in_conds m n f ->
  0 <= i < m ->
  0 <= j < n ->
  0 <= b ->
  wf_matrix mx m n ->
  get (fold_left f (Ziota 0 b) mx) i j = if (Z_lt_le_dec i b) then get (f mx i) i j else get mx i j.
Proof.
  move => m n mx f b i j Hconds Hi Hj Hb Hwf.
  case : (Z_lt_le_dec i b) => [Hin /= | Hout /=].
  - apply (mx_foldl_in Hconds); try by []. rewrite Zseq_In; lia. apply Ziota_NoDup.
  - apply (mx_foldl_notin (proj1 Hconds)); try by []. rewrite Zseq_In; lia.
Qed.

(*Convert any function of this form to a mathcomp matrix (so we only have to prove this once*)
Lemma foldl_ziota_to_mx: forall m n mx f b 
  (g: 'M[F]_(Z.to_nat m, Z.to_nat n) -> 'I_(Z.to_nat m) -> 'M[F]_(Z.to_nat m, Z.to_nat n)),
  (forall (r: Z) (Hr: 0 <= r < m) (mx: matrix), wf_matrix mx m n ->
      matrix_to_mx m n (f mx r) = g (matrix_to_mx m n mx) (Z_to_ord Hr)) ->
  fn_in_conds m n f ->
  0 <= b <= m ->
  wf_matrix mx m n ->
  matrix_to_mx m n (fold_left f (Ziota 0 b) mx) = foldl g (matrix_to_mx m n mx) (pmap insub (iota 0 (Z.to_nat b))).
Proof.
  move => m n mx f b g Hcompat Hconds Hb Hwf.
  rewrite /Ziota.   have ->: (Z.to_nat 0) = 0%N by lia.
  have: forall n, n \in (iota 0 (Z.to_nat b)) -> (n < Z.to_nat b)%N. { move => n'. by rewrite mem_iota. }
  move : mx Hwf.
  elim: (iota 0 (Z.to_nat b)) => [//| h t IH mx Hwf Hin /=].
  have Hh : (h < Z.to_nat m)%N. { apply /ltP. have: (h < Z.to_nat b)%coq_nat. apply /ltP. apply Hin.
   by rewrite in_cons eq_refl. lia. }
  rewrite insubT /=. rewrite IH /=.
  have Hhm: 0 <= Z.of_nat h < m. { apply (elimT ltP) in Hh. lia. }
  rewrite Hcompat /=. f_equal. f_equal.
  have Hord1: (nat_of_ord (Z_to_ord Hhm) = Z.to_nat (Z.of_nat h)) by []. rewrite Nat2Z.id in Hord1.
  have Hord2: (nat_of_ord (Ordinal Hh) = h) by []. by apply ord_inj. by [].
  by apply Hconds. move => n' Hn'. apply Hin. by rewrite in_cons Hn' orbT.
Qed.

(*Corollaries and useful general results*)
Lemma foldl_ziota_plus_one: forall (mx: matrix) (f: matrix -> Z -> matrix) (b: Z),
  0 <= b ->
  fold_left f (Ziota 0 (b+1)%Z) mx = f (fold_left f (Ziota 0 b) mx) b.
Proof.
  move => mx f b Hb. rewrite Ziota_plus_1; try lia.
  by rewrite fold_left_app /=.
Qed.
 
(*easy corollary of [foldl_ziota_get]*)
Lemma foldl_ziota_outside: forall m n mx f b i j,
  fn_in_conds m n f ->
  0 <= i < m ->
  0 <= j < n ->
  0 <= b <= i ->
  wf_matrix mx m n ->
  get (fold_left f (Ziota 0 b) mx) i j = get mx i j.
Proof.
  move => m n mx f b i j Hcond Hi Hj Hb Hwf.
  rewrite (foldl_ziota_get Hcond); try by []; try lia.
  by case : (Z_lt_le_dec i b) => [Hin | Hout /=]; try lia.
Qed.

(*Make all cols one (scalar multiplication)*)

Section AllColsOne.

Definition all_cols_one_partial m n (mx: matrix) (c: Z) (bound: Z) :=
  fold_left (fun acc x => scalar_mul_row m n acc x (get mx x c)^-1 ) (Ziota 0 bound) mx.

Lemma all_cols_one_fn_in_conds: forall m n mx c,
  wf_matrix mx m n ->
  fn_in_conds m n (fun acc x => scalar_mul_row m n acc x (get mx x c)^-1 ).
Proof.
  move => m n mx c Hwf. rewrite /fn_in_conds /fn_notin_conds. split; [ split |]. 
  - move => mx' i j r Hwf' Hi Hj Hir. rewrite scalar_mul_row_spec; try by [].
    by case : (Z.eq_dec i r) => [Heq | Hneq /=]; try lia.
  - move => mx' i Hwf'. apply scalar_mul_row_partial_wf. apply (matrix_m_pos Hwf).
    apply (matrix_n_pos Hwf).
  - move => mx' h i j Hwf' Hi Hj Hih.
    rewrite !scalar_mul_row_spec //=. 
    case: (Z.eq_dec i i) => [Htriv {Htriv} /= | Hbad]; try lia.
    by case: (Z.eq_dec i h) => [Hbad | Htriv /=]; try lia.
    apply scalar_mul_row_partial_wf. apply (matrix_m_pos Hwf). apply (matrix_n_pos Hwf).
Qed.

(*Now all the results are easy corollaries*)
Lemma all_cols_one_plus_1: forall m n mx c b,
  0 <= b ->
  all_cols_one_partial m n mx c (b+1) = scalar_mul_row m n (all_cols_one_partial m n mx c b) b (get mx b c)^-1.
Proof.
  move => m n mx c b Hb. by apply foldl_ziota_plus_one.
Qed.

Lemma all_cols_one_outside: forall m n mx c bound i j,
  wf_matrix mx m n ->
  0 <= bound <= i ->
  0 <= i < m ->
  0 <= j < n ->
  get (all_cols_one_partial m n mx c bound) i j = get mx i j.
Proof.
  move => m n mx c b i j Hwf Hb Hi Hj. 
  by apply (foldl_ziota_outside (all_cols_one_fn_in_conds c Hwf)).
Qed.

Lemma all_cols_one_equiv_partial: forall {m n} (mx: matrix) (c: Z) (Hc: 0 <= c < n) bound,
  0 <= bound <= m ->
  wf_matrix mx m n ->
  matrix_to_mx m n (all_cols_one_partial m n mx c bound) = all_cols_one_noif_gen (matrix_to_mx m n mx) (Z_to_ord Hc)
  (pmap insub (iota 0 (Z.to_nat bound))).
Proof.
  move => m n mx c Hc b Hb Hwf. rewrite all_cols_one_noif_gen_foldl /all_cols_one_noif_l_gen /Ziota /ord_enum.
  apply foldl_ziota_to_mx; try by [].
  - move => r Hr mx' Hwf'. rewrite scalar_mul_row_equiv //=. f_equal.
    by rewrite /matrix_to_mx mxE /= !Z2Nat.id; try lia.
  - by apply all_cols_one_fn_in_conds.
  - apply pmap_sub_uniq. apply iota_uniq.
Qed.

Lemma all_cols_one_list_equiv: forall {m n} (mx: matrix) (c: Z) (Hc: 0 <= c < n),
  wf_matrix mx m n ->
  matrix_to_mx m n (all_cols_one_partial m n mx c m) = all_cols_one_noif (matrix_to_mx m n mx) (Z_to_ord Hc).
Proof.
  move => m n mx c Hc Hwf. apply all_cols_one_equiv_partial. split; try lia.
  apply (matrix_m_pos Hwf). by [].
Qed.

Lemma all_cols_one_partial_wf: forall {m n} mx c bound,
  wf_matrix mx m n ->
  wf_matrix (all_cols_one_partial m n mx c bound) m n.
Proof.
  move => m n mx c b Hwf. apply mx_foldl_wf =>[|//]. by apply all_cols_one_fn_in_conds.
Qed.


(*Combine two lists with a pairwise binary operation (zipWith in Haskell) *)
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

(*TODO: start here*)

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

(** Matrix for Encoder*)
(*Here, the matrix may be partial - ie, not all rows are filled in. So we need to extend with zeroes*)
Definition extend_mx (l: list (list F)) (n : Z) : matrix :=
  map (fun x => x ++ list_repeat (Z.to_nat (n - Zlength x)) 0%R) l.

Lemma extend_mx_wf: forall m n l,
  0 <= n ->
  Zlength l = m ->
  (Forall (fun x => (Zlength x <= n)%Z)) l ->
  wf_matrix (extend_mx l n) m n.
Proof.
  move => m n l H0n Hlen. rewrite /wf_matrix Forall_forall => Hall. repeat split.
  - by rewrite /extend_mx Zlength_map.
  - by [].
  - move => x. rewrite /extend_mx in_map_iff => [[l' [Hl' Hin]]]. subst.
    move : Hall => /(_ l' Hin) => Hlen.
    rewrite Zlength_app Zlength_list_repeat. apply Zplus_minus. by apply Zle_minus_le_0.
Qed.

Lemma extend_mx_spec: forall n l i j,
  (Forall (fun x => (Zlength x <= n)%Z) l) ->
  0 <= i < (Zlength l) ->
  0 <= j < n ->
  get (extend_mx l n) i j = if (Z_lt_le_dec j (Zlength (Znth i l))) then Znth j (Znth i l) else 0%R.
Proof.
  move => n l i j Hall Hi Hj. rewrite /extend_mx /get.
  have Hznth: 0 <= Zlength (Znth i l) <= n. split. list_solve. move: Hall. 
    rewrite Forall_forall => /(_ (Znth i l)) Hlen. apply Hlen. apply Znth_In; lia.
  rewrite {Hall} Znth_map =>[|//].  
  case : (Z_lt_le_dec j (Zlength (Znth i l))) => [Hjlen /= | Hjlen /=].
  - by rewrite Znth_app1.
  - rewrite Znth_app2; try lia. list_solve.
Qed. 

(* We use the above to define matrix multiplication of ListMatrices, since we will be setting the entries
  manually. Using mathcomp summations in VST would be
  very annoying, so we define a specialized summation for our purposes and prove them equivalent*)

Definition dot_prod (mx1: matrix) (mx2: matrix) i j (bound : Z) : F :=
  foldl (fun acc k => acc + ((get mx1 i k) * (get mx2 k j))) 0 (Ziota 0 bound).

Lemma dot_prod_zero: forall mx1 mx2 i j,
  dot_prod mx1 mx2 i j 0%Z = 0.
Proof.
  by [].
Qed.

Lemma dot_prod_plus_1: forall mx1 mx2 i j bound,
  0 <= bound ->
  dot_prod mx1 mx2 i j (bound+1)%Z = (dot_prod mx1 mx2 i j bound) + (get mx1 i bound * get mx2 bound j).
Proof.
  move => mx1 mx2 i j b Hb. rewrite /dot_prod Ziota_plus_1; try lia. by rewrite foldl_cat.
Qed.

Lemma iota_plus_1: forall x y,
  iota x (y.+1) = iota x y ++ [ :: (x + y)%N].
Proof.
  move => x y. by rewrite -addn1 iotaD /=.
Qed.

(*Prove that this [dot_prod] expression is equivalent to the matrix multiplication sum in ssreflect*)
Lemma dot_prod_sum: forall m n p mx1 mx2 i j b (d: 'I_(Z.to_nat n)) (Hi: 0 <= i < m) (Hj : 0 <= j < p),
  0 <= b <= n ->
  wf_matrix mx1 m n ->
  wf_matrix mx2 n p ->
  dot_prod mx1 mx2 i j b = 
  \sum_(0 <= i0 < Z.to_nat b) 
    matrix_to_mx m n mx1 (Z_to_ord Hi) (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) i0) *
    matrix_to_mx n p mx2 (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) i0) (Z_to_ord Hj).
Proof.
  move => m n p mx1 mx2 i j b d Hi Hj Hb Hwf1 Hwf2. rewrite /dot_prod /Ziota. have: (0%nat <= Z.to_nat b)%coq_nat by lia.
  have: (Z.to_nat b <= Z.to_nat n)%coq_nat by lia. rewrite {Hb}.
  (*We will do induction on (Z.to_nat b)*)
  remember (Z.to_nat b) as c. rewrite {b Heqc}. elim: c => [Hub Hlb //= | c' IH Hub Hlb].
  - by rewrite big_mkord big_ord0.
  - have Hc0 : (0 <= c')%N. apply (introT leP). lia.
    rewrite iota_plus_1 map_cat foldl_cat /= big_nat_recr /= =>[|//].
    rewrite IH; try lia.
    rewrite /matrix_to_mx !mxE /=. f_equal. 
    have Hc': (0 <= c' < Z.to_nat n)%nat. rewrite Hc0 /=. apply (introT ltP). lia.
    have ->: (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) c') = 
      (nth d (Finite.enum (ordinal_finType (Z.to_nat n))) (Ordinal Hc')) by []. rewrite ordinal_enum //=.
    by rewrite !Z2Nat.id; try lia.
Qed.

(*Therefore, the full product is the same as multiplying matrices*)
Lemma dot_prod_mulmx: forall m n p mx1 mx2 i j (Hi: 0 <= i < m) (Hj : 0 <= j < p),
  wf_matrix mx1 m n ->
  wf_matrix mx2 n p ->
  dot_prod mx1 mx2 i j n = ((matrix_to_mx m n mx1) *m (matrix_to_mx n p mx2)) (Z_to_ord Hi) (Z_to_ord Hj).
Proof.
  move => m n p mx1 mx2 i j Hi Hj Hwf1 Hwf2. rewrite !mxE.
  have Hn0: 0 <= n by apply Hwf1.
  have: n = 0%Z \/ 0 < n by lia. move => [{}Hn0 | {} Hn0].
  - subst. rewrite /dot_prod /=. by rewrite big_ord0.
  - (*Now we have an instance of an 'I_n, which we need*)
    have Hnord: 0 <= 0 < n by lia.
    rewrite (big_nth (Z_to_ord Hnord)) /= /index_enum /= ordinal_enum_size /dot_prod.
    apply dot_prod_sum; try by []. lia.
Qed.

Lemma mulmx_dot_equiv: forall m n p mx1 mx2 mx3,
  wf_matrix mx1 m n ->
  wf_matrix mx2 n p ->
  wf_matrix mx3 m p ->
  (forall i j, 0 <= i < m -> 0 <= j < p -> get mx3 i j = dot_prod mx1 mx2 i j n) ->
  matrix_to_mx m p mx3 = (matrix_to_mx m n mx1) *m (matrix_to_mx n p mx2).
Proof.
  move => m n p mx1 mx2 mx3 Hwf1 Hwf2 Hwf3 Hall.
  rewrite -matrixP /eqrel => x y.
  rewrite mxE.
  have Hxm: 0 <= Z.of_nat x < m. split; try lia. have Hxm: (x < Z.to_nat m)%N by [].
    have {}Hxm : (x < Z.to_nat m)%coq_nat by apply (elimT ltP). lia.
  have Hyp: 0 <= Z.of_nat y < p. split; try lia. have Hyp: (y < Z.to_nat p)%N by [].
    have {}Hyp : (y < Z.to_nat p)%coq_nat by apply (elimT ltP). lia.
  rewrite Hall =>[|//|//].
  rewrite (dot_prod_mulmx Hxm Hyp Hwf1 Hwf2) /=. f_equal. 
  have /eqP Hx: nat_of_ord (Z_to_ord Hxm) == x.
    have: nat_of_ord (Z_to_ord Hxm) == (Z.to_nat (Z.of_nat x)) by []. by rewrite Nat2Z.id.
  apply ord_inj. by rewrite Hx.
  have /eqP Hy: nat_of_ord (Z_to_ord Hyp) == y.
    have: nat_of_ord (Z_to_ord Hyp) == (Z.to_nat (Z.of_nat y)) by []. by rewrite Nat2Z.id.
  apply ord_inj. by rewrite Hy.
Qed.

(*Finally, we give a definition with lists so we don't need to directly refer to any
 ssreflect functions in the VST proofs*)

Definition list_matrix_multiply m n p mx1 mx2 : matrix :=
  prop_list (fun (row : Z) => prop_list (fun col => dot_prod mx1 mx2 row col n) p) m.

Lemma list_matrix_multiply_wf: forall m n p mx1 mx2,
  0 <= m ->
  0 <= p ->
  wf_matrix (list_matrix_multiply m n p mx1 mx2) m p.
Proof.
  move => m n p mx1 mx2 Hm Hp. rewrite /wf_matrix. repeat split.
  rewrite /list_matrix_multiply. rewrite prop_list_length; lia. lia.
  move => l. rewrite /list_matrix_multiply In_Znth_iff => [[i [Hilen Hznth]]].
  subst. rewrite prop_list_Znth. rewrite prop_list_length; lia. rewrite prop_list_length in Hilen; lia.
Qed.

Lemma list_matrix_multiply_correct: forall m n p mx1 mx2 ,
  wf_matrix mx1 m n ->
  wf_matrix mx2 n p ->
  matrix_to_mx m p (list_matrix_multiply m n p mx1 mx2) = (matrix_to_mx m n mx1) *m (matrix_to_mx n p mx2).
Proof.
  move => m n p mx1 mx2 Hwf1 Hwf2.
  apply mulmx_dot_equiv =>[//|//||].
  apply list_matrix_multiply_wf. apply (matrix_m_pos Hwf1). apply (matrix_n_pos Hwf2).
  move => i j Hi Hj. rewrite /get /list_matrix_multiply. rewrite prop_list_Znth =>[|//].
  by rewrite prop_list_Znth.
Qed.

(** Submatrices*)

(*This is the submatrix we will need for the encoder - take the first a rows and last b columns of a matrix,
  reversed.*)

Definition submatrix (mx: matrix) a b :=
  sublist 0 a (map (fun x => rev (sublist ((Zlength x) - b) (Zlength x) x)) mx).

Lemma rev_rev: forall {A: Type} (l: list A),
  rev l = List.rev l.
Proof.
  move => A l. elim : l => [//|h t IH /=]. by rewrite rev_cons IH  -cats1.
Qed.

Lemma submatrix_wf: forall m n mx a b,
  wf_matrix mx m n ->
  0 <= a <= m ->
  0 <= b <= n ->
  wf_matrix (submatrix mx a b) a b.
Proof.
  move => m n mx a b [Hm1 [Hn1 Hin1]] Ha Hb.
  rewrite /wf_matrix /submatrix. repeat split.
  - rewrite Zlength_sublist; try lia. rewrite Zlength_map. lia.
  - lia.
  - move => x Hin. apply sublist_In in Hin. move: Hin. rewrite in_map_iff => [[x' [Hx' Hin]]].
    subst. rewrite rev_rev Zlength_rev Zlength_sublist; try lia. by rewrite Hin1; try lia. 
Qed.

Lemma submatrix_spec: forall m n mx a b i j,
  wf_matrix mx m n ->
  0 <= i < a ->
  0 <= j < b ->
  a <= m ->
  b <= n ->
  get (submatrix mx a b) i j = get mx i (n - j - 1).
Proof.
  move => m n mx a b i j [Hm [Hn Hin]] Hi Hj Ha Hb. rewrite /submatrix /get.
  rewrite Znth_sublist; try lia. rewrite Znth_map; try lia.
  have ->: (i+0)%Z = i by lia.
  have Hnth: Zlength (Znth i mx) = n. apply Hin. apply Znth_In; lia. rewrite Hnth.
  have Hsub: Zlength (sublist (n - b) n (Znth i mx)) = b by list_solve. 
  rewrite rev_rev Znth_rev; try lia. rewrite Hsub. rewrite Znth_sublist; try lia.
  f_equal. lia.
Qed.

(*A bit of complication because of the ordinals, i -> i and j -> n - j - 1*)
Lemma submatrix_to_mx: forall m n mx a b (Ha: a <= m) (Hb: b <= n),
  wf_matrix mx m n ->
  matrix_to_mx a b (submatrix mx a b) = mxsub
    (fun (x: 'I_(Z.to_nat a)) => widen_ord (le_Z_N Ha) x)
    (fun (x: 'I_(Z.to_nat b)) => (rev_ord (widen_ord (le_Z_N Hb) x)))
    (matrix_to_mx m n mx).
Proof.
  move => m n mx a b Ha Hb Hwf. rewrite -matrixP /eqrel => x y.
  rewrite /mxsub !mxE /=. rewrite (submatrix_spec Hwf); try lia.
  - f_equal. have Hyb: (y < Z.to_nat b)%N by []. apply (elimT ltP) in Hyb. 
    have->: (Z.to_nat n - y.+1)%N = (Z.to_nat n - y.+1)%coq_nat by []. lia.
  - have Hxa: (x < Z.to_nat a)%N by []. apply (elimT ltP) in Hxa. lia.
  - have Hyb: (y < Z.to_nat b)%N by []. apply (elimT ltP) in Hyb. lia.
Qed.

End ListMx.