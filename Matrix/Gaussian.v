From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Section Gauss.

Variable F : fieldType.

Local Open Scope ring_scope.

(*Preliminaries*)

Lemma ltn_total: forall (n1 n2: nat),
  (n1 < n2) || (n1 == n2) || (n2 < n1).
Proof.
  move => n1 n2. case: (orP (leq_total n1 n2)); rewrite leq_eqVlt.
  - move => le_n12; case (orP le_n12) => [Heq | Hlt].  rewrite Heq /=.
    by rewrite orbT orTb. by rewrite Hlt !orTb.
  - move => le_n21; case (orP le_n21) => [Heq | Hlt]. rewrite eq_sym Heq /=.
    by rewrite orbT orTb. by rewrite Hlt !orbT.
Qed. 

(*get elements of identity matrix*)
(*TODO:is there a better way to get the field F in there?*)
Lemma id_A : forall {n} (x y : 'I_n),
  (1%:M) x y = if x == y then 1 else (GRing.zero F).
Proof.
move => n x y; rewrite /scalar_mx mxE; by case : (x == y). 
Qed.

(*Working with enums of ordinals*)
Lemma ordinal_enum_size: forall n,
  size (Finite.enum (ordinal_finType n)) = n.
Proof.
  move => n. have: size ([seq val i | i <- enum 'I_n]) = n. rewrite val_enum_ord. by apply: size_iota.
  rewrite size_map. unfold enum. rewrite size_map //.
Qed.

Lemma ordinal_enum: forall {n: nat} (x: 'I_n) y,
  nth y (Finite.enum (ordinal_finType n)) x = x.
Proof.
  move => n x y. have nth_ord := (nth_ord_enum y x). unfold enum in nth_ord. move: nth_ord.
  rewrite (@nth_map _ y) //. by rewrite ordinal_enum_size.
Qed. 

(*Some closed form summations we will use*)
Lemma sum_if: forall {n} (x : 'I_n) (f1 : 'I_n -> F),
  \sum_(i < n) (if x == i then f1 i else 0) = f1 x.
Proof.
  move => n x f1. rewrite (big_nth x) /= /index_enum /=. rewrite ordinal_enum_size.
  have Hzero: forall i : nat, i < n -> i != x ->
  (if x == nth x (Finite.enum (ordinal_finType n)) i
    then f1 (nth x (Finite.enum (ordinal_finType n)) i)
    else 0) = 0. {  move => i Hin Hx. have: i == Ordinal Hin by []. move => /eqP Hi; rewrite Hi.
   rewrite ordinal_enum. have: (Ordinal Hin != x) by [].
   rewrite /negb. rewrite eq_sym. by case(x == Ordinal Hin). }
  rewrite (@big_cat_nat _ _ _ x) /= => [| // | ]. 2: by apply: ltnW.
  rewrite big_nat_cond big1.
  - rewrite big_ltn => [|//]. rewrite big_nat_cond big1.
    + by rewrite ordinal_enum eq_refl GRing.add0r GRing.addr0.
    + move => i /andP[/andP [Hxi Hin]]. move => H{H}. apply Hzero. by []. by rewrite gtn_eqF.
  - move => i /andP[/andP [Hxi Hin]]. move => H{H}. apply Hzero. have: x < n by []. move : Hin.
    apply ltn_trans. by rewrite ltn_eqF.
Qed.

Lemma sum_if_twice: forall {n} (r1 r2 : 'I_n) (f1 f2 : 'I_n -> F),
  r1 < r2 ->
  \sum_(i < n) (if i == r1 then f1 i else if i == r2 then f2 i else 0) = f1 r1 + f2 r2.
Proof.
move => n r1 r2 f1 f2 Hlt. rewrite (big_nth r1) /= /index_enum /= ordinal_enum_size.
  have Hzero: forall i : nat, i < n -> i != r1 -> i != r2 ->
  (if nth r1 (Finite.enum (ordinal_finType n)) i == r1
  then f1 (nth r1 (Finite.enum (ordinal_finType n)) i)
  else
  if nth r1 (Finite.enum (ordinal_finType n)) i == r2
  then f2 (nth r1 (Finite.enum (ordinal_finType n)) i)
  else 0) = 0. {
  move => i Hin Hir1 Hr2. have: i == Ordinal Hin by []. move => /eqP Hi. rewrite Hi. 
  rewrite ordinal_enum.
  have: (Ordinal Hin != r1) by []. have: (Ordinal Hin != r2) by []. rewrite /negb.  case(Ordinal Hin == r2).
  by []. by case (Ordinal Hin == r1). } 
  rewrite (@big_cat_nat _ _ _ r1) /=. 2 : by []. 2 : by [apply: ltnW].
  rewrite big_nat_cond big1. 
  - rewrite big_ltn. 2: by [].
    rewrite ordinal_enum eq_refl GRing.add0r (@big_cat_nat _ _ _ r2) /=. 2 : by []. 2 : by [apply: ltnW].
    rewrite big_nat_cond big1.
    + rewrite big_ltn. 2: by []. rewrite ordinal_enum.
      have: (r2 == r1 = false) by apply gtn_eqF. move => Hneq; rewrite Hneq {Hneq}.
      rewrite eq_refl GRing.add0r big_nat_cond big1. by rewrite GRing.addr0.
      move => i /andP[/andP [H0i Hix]]. move =>H {H}. 
      apply: Hzero. by []. rewrite gtn_eqF. by []. move : Hlt H0i. apply ltn_trans. by rewrite gtn_eqF.
    + move => i /andP[/andP [H0i Hix]]. move =>H {H}. apply: Hzero. have: r2 < n by []. move : Hix.
      apply ltn_trans. by rewrite gtn_eqF. by rewrite ltn_eqF.
  - move => i /andP[/andP [H0i Hix]]. move =>H {H}. apply: Hzero. have: r1 < n by []. move : Hix.
    apply ltn_trans. by rewrite ltn_eqF. rewrite ltn_eqF //. move : Hix Hlt. apply ltn_trans.
Qed.

(** Elementary Row Operations*)

(*Swapping rows is already defined by mathcomp - it is xrow*)

(*scalar multiply row r in matrix A by scalar c*)
Definition sc_mul {m n} (A : 'M[F]_(m, n)) (c: F) (r: 'I_m) : 'M[F]_(m, n) :=
  \matrix_(i < m, j < n) if i == r then c * (A i j) else A i j. 

(*elementary matrix for scalar multiplication*)
Definition sc_mul_mx (n: nat) (c: F) r : 'M[F]_(n, n) := @sc_mul n n (1%:M) c r.

(*scalar multiplication is same as mutliplying by sc_mul_mx on left*)
Lemma sc_mulE: forall {m n : nat} (A: 'M[F]_(m, n)) (c: F) (r: 'I_m),
  sc_mul A c r = (sc_mul_mx c r) *m A.
Proof.
move => m n A c r; rewrite /sc_mul_mx /sc_mul. rewrite -matrixP /eqrel => x y. rewrite !mxE /=. erewrite eq_big_seq.
2 : { move => z. rewrite mxE id_A //. }
rewrite /=. case : (eq_op x r). 
  - erewrite eq_big_seq. 2 : { move => z Inz. rewrite -GRing.mulrA //. }
    rewrite (@eq_big_seq _ _ _ _ _ _ (fun z => c * ((if x == z then A z y else 0)))).
    rewrite -big_distrr. by rewrite sum_if. rewrite //= /eqfun. move => x' Xin.
    case(x == x'). by rewrite GRing.mul1r. by rewrite GRing.mul0r.
  - rewrite (@eq_big_seq _ _ _ _ _ _ (fun z => ((if x == z then A z y else 0)))).
    by rewrite sum_if. rewrite /eqfun //= => x' Xin. case (x == x').
    by rewrite GRing.mul1r. by rewrite GRing.mul0r.
Qed.

(*inverse for scalar sc_mul_mx*)
Lemma sc_mul_mx_inv: forall {m : nat} (c: F) (r: 'I_m),
  c != 0 ->
  (sc_mul_mx c r) *m (sc_mul_mx c^-1 r) = 1%:M.
Proof.
  move => m c r Hc. rewrite -sc_mulE. rewrite !/sc_mul_mx /sc_mul.
  rewrite -matrixP /eqrel => x y. rewrite !mxE. destruct (x == r) eqn : Hxr. rewrite !Hxr.
  rewrite GRing.mulrA. rewrite GRing.divff. by rewrite GRing.mul1r. by [].
  by rewrite Hxr.
Qed.

(*sc_mul_mx is invertible*)
Lemma sc_mul_mx_unitmx: forall {m : nat} (c: F) (r: 'I_m),
  c != 0 ->
  (sc_mul_mx c r) \in unitmx.
Proof.
  move => m c r Hc. apply: (proj1 (mulmx1_unit (@sc_mul_mx_inv m c r  Hc))).
Qed. 

(*Add multiple of one row to another - r2 := r2 + c * r1*)
Definition add_mul {m n} (A : 'M[F]_(m, n)) (c: F) (r1 r2: 'I_m) : 'M[F]_(m, n) :=
  \matrix_(i < m, j < n) if i == r2 then (A r2 j) + (c * (A r1 j)) else A i j. 

(*elementary matrix for adding multiples*)
Definition add_mul_mx (n: nat) (c: F) r1 r2 : 'M[F]_(n,n) := 
  \matrix_(i < n, j < n) if i == r2 then 
                            if j == r1 then c else if j == r2 then 1 else 0
                         else if i == j then 1 else 0.


(*adding multiple is the same as multiplying by [add_mul_mx] matrix on left *)
Lemma add_mulE: forall {m n : nat} (A: 'M[F]_(m, n)) (c: F) (r1 r2: 'I_m),
  r1 != r2 ->
  add_mul A c r1 r2 = (add_mul_mx c r1 r2) *m A.
Proof.
move => m n A c r1 r2 Hr12; rewrite /add_mul_mx /add_mul. rewrite -matrixP /eqrel => x y. rewrite !mxE /=.
erewrite eq_big_seq. 2 : { move => z. rewrite mxE //. } rewrite //=.
case : (eq_op x r2). 
  - rewrite (@eq_big_seq _ _ _ _ _ _ (fun z => ((if z == r1 then c * A z y else if z == r2 then A z y else 0)))).
    case (orP (ltn_total r1 r2)) => [Hleq | Hgt].
    + case (orP Hleq) => [Hlt | Heq]. rewrite sum_if_twice //. by rewrite GRing.addrC.
      have: (nat_of_ord r1 != nat_of_ord r2) by [].
      rewrite /negb. by rewrite Heq.
    + rewrite (@eq_big_seq _ _ _ _ _ _ (fun z => ((if z == r2 then A z y else if z == r1 then c * A z y else 0)))).
      rewrite sum_if_twice //. move => z Hz. destruct (z == r1) eqn : Hzr1. destruct (z == r2) eqn : Hzr2.
      have: r1 == r2. move : Hzr1; rewrite eq_sym. move => Hzr1. by rewrite (eq_op_trans Hzr1 Hzr2).
      move => Heq. move : Hr12. by rewrite Heq. by []. by [].
    + move => z Hz. destruct (z == r1) eqn : Hzeq. have: z == r1 by [].
      by move ->. have: z == r1 = false by []. move ->. destruct (z == r2) eqn : Hzr2.
      have: z == r2 by []. move ->. by apply GRing.mul1r.
      have: z == r2 = false by []. move ->. by apply GRing.mul0r.
  - rewrite (@eq_big_seq _ _ _ _ _ _ (fun z => (if x == z then A z y else 0))). by rewrite sum_if.
    move => z Hz. destruct (x == z) eqn : Heqz. have: x == z by []. move ->. by apply GRing.mul1r.
    have: x == z = false by []. move ->. by apply GRing.mul0r.
Qed.

(*surprisingly annoying to prove because the types of equality don't line up always (between ordinals and nats)*)
Lemma add_mul_mx_inv: forall {m : nat} (c: F) (r1 r2: 'I_m),
  r1 != r2 ->
  (add_mul_mx c r1 r2) *m (add_mul_mx (- c) r1 r2) = 1%:M.
Proof.
  move => m c r1 r2 Hr12.  rewrite -add_mulE //. rewrite !/add_mul_mx /add_mul.
  rewrite -matrixP /eqrel => x y. rewrite !mxE. rewrite eq_refl. have: r1 == r2 = false. move : Hr12. rewrite /negb.
  by case (r1 == r2). move ->. destruct (x == r2) eqn : Hxr2.
  have: x == r2 by []. move ->. rewrite eq_sym. destruct (r1 == y) eqn : Hyr1. 
  have: r1 == y by []. move ->. rewrite GRing.mulr1 GRing.addNr. pose proof (eqP Hxr2).
  pose proof (eqP Hyr1). rewrite H. rewrite -H0. rewrite eq_sym.
  have: (r1 == r2 = false). move : Hr12. rewrite /negb. by case(r1 == r2). by move ->.
  have: r1 == y = false by []. move ->.
  destruct (y == r2) eqn : Hyr2. have: y == r2 by []. move ->. pose proof (eqP Hxr2). pose proof (eqP Hyr2).
  by rewrite H H0 eq_refl GRing.mulr0 GRing.addr0. have: (y == r2 = false) by [].  move ->.
  pose proof (eqP Hxr2). by rewrite H eq_sym Hyr2 GRing.mulr0 GRing.addr0.
  have: (x == r2 = false) by []. move->. destruct (x == y) eqn : Hxy. pose proof (eqP Hxy). rewrite H.
  by rewrite eq_refl. have: x == y = false by []. by move ->.
Qed.

(*add_mul_mx is invertible*)
Lemma add_mul_mx_unitmx: forall {m : nat} (c: F) (r1 r2: 'I_m),
  r1 != r2 ->
  (add_mul_mx c r1 r2) \in unitmx.
Proof.
  move => m c r1 r2 Hr12. apply: (proj1 (mulmx1_unit (@add_mul_mx_inv m c r1 r2 Hr12))).
Qed.

(** Row equivalence *)

Inductive ero : forall (m n : nat), 'M[F]_(m, n) -> 'M[F]_(m, n) -> Prop :=
  | ero_swap: forall {m n} r1 r2 (A : 'M[F]_(m,n)),
      ero A (xrow r1 r2 A)
  | ero_sc_mul: forall {m n} r c (A : 'M[F]_(m,n)),
      c != 0 ->
      ero A (sc_mul A c r)
  | ero_add_mul: forall {m n} r1 r2 c (A : 'M[F]_(m,n)),
      r1 != r2 ->
      ero A (add_mul A c r1 r2).

Lemma ero_mul_unit: forall {m n} (A B : 'M[F]_(m, n)),
  ero A B ->
  exists E, (E \in unitmx) && (B == E *m A).
Proof.
  move => m n A B Hero. elim: Hero; move => m' n' r1.
  - move => r2 A'. exists (tperm_mx r1 r2). by rewrite {1}/tperm_mx unitmx_perm xrowE eq_refl.
  - move => c A' Hc. exists (sc_mul_mx c r1). by rewrite sc_mulE eq_refl sc_mul_mx_unitmx.
  - move => r2 c A' Hr. exists (add_mul_mx c r1 r2). rewrite add_mulE. by rewrite eq_refl add_mul_mx_unitmx. by [].
Qed.

Inductive row_equivalent: forall m n, 'M[F]_(m, n) -> 'M[F]_(m, n) -> Prop :=
  | row_equiv_refl: forall {m n} (A: 'M[F]_(m,n)),
     row_equivalent A A
  | row_equiv_ero: forall {m n} (A B C: 'M[F]_(m,n)),
     ero A B ->
     row_equivalent B C ->
     row_equivalent A C.

Lemma row_equivalent_trans: forall {m n} (A B C : 'M[F]_(m, n)),
  row_equivalent A B ->
  row_equivalent B C ->
  row_equivalent A C.
Proof.
  move => m n A B C Hre. move : C. elim: Hre; clear m n A B.
  - by [].
  - move => m n A B C Hero Hre IH D Hd. apply (@row_equiv_ero _ _ A B D). by []. by apply: IH.
Qed. 

(*If A and B are row equivalent, then A = EB for some invertible matrix E*) 
Lemma row_equivalent_mul_unit: forall {m n} (A B : 'M[F]_(m, n)),
  row_equivalent A B ->
  exists E, (E \in unitmx) && (B == E *m A).
Proof.
  move => m n A B Hre. elim: Hre; clear m n A B; move => m n A.
  - exists (1%:M). by rewrite unitmx1 mul1mx eq_refl.
  - move => B C Hero Hre IH. destruct IH as [E IH]. apply ero_mul_unit in Hero. destruct Hero as [E' Hero]. 
    exists (E *m E'). move : Hero IH => /andP[He' /eqP Hb] /andP[He /eqP Hc]. rewrite unitmx_mul.
    subst. by rewrite mulmxA eq_refl He He'. 
Qed.

(*If A and B are row equivalent, then A is invertible iff B is*)
Lemma row_equivalent_unitmx_iff: forall {n} (A B : 'M[F]_(n, n)),
  row_equivalent A B ->
  (A \in unitmx) = (B \in unitmx).
Proof.
  move => n A B Hre. apply row_equivalent_mul_unit in Hre. destruct Hre as [E Hre].
  move : Hre => /andP[Hunit /eqP Hb]. by rewrite Hb unitmx_mul Hunit. 
Qed. 

(** Gaussian Elimination*)

(*First, we define the leading coefficient of a row (ie, the first nonzero element) - will be n if row is all zeroes*)
Definition lead_coef {m n} (A: 'M[F]_(m, n)) (row: 'I_m) : nat :=
  find (fun x => A row x != 0) (ord_enum n).

Definition ord_iota {n: nat} (a b : nat) : seq 'I_n := pmap insub (iota a b).

Lemma ord_iota_val: forall {n} (a b : nat), (a + b < n) -> map val (@ord_iota n a b) = iota a b.
Proof.
move => n a b Hle.
rewrite pmap_filter; last exact: insubK.
apply/all_filterP; apply/allP => i. rewrite mem_iota isSome_insub. move => /andP[H{H} Hin]. move: Hin Hle.
apply: ltn_trans.
Qed.

(*Find the first nonzero entry in column col, starting from index r*)
Definition fst_nonzero {m n} (A: 'M[F]_(m, n)) (col: 'I_n) (r: 'I_m) : nat :=
  find (fun x => A x col != 0) (ord_iota r (m - r)).

(*Fold a function over the rows of a matrix that are contained in a list.
  If this function only affects a single row and depends only on the entries in that row and possibly
  rows that are not in the list, then we can describe the (i, j)th component just with the function itself.
  This allows us to prove things about the multiple intermediate steps in gaussian elimination at once*)

(*Two helper lemmas*)
Lemma mx_row_transform_notin: forall {m n} (A: 'M[F]_(m,n)) (f: 'I_m -> 'M[F]_(m,n) -> 'M[F]_(m,n)) (l: seq 'I_m),
  (forall (A: 'M[F]_(m,n)) i j r, i != r ->  A i j = (f r A) i j) ->
  forall r j, r \notin l ->
  (foldr f A l) r j = A r j.
Proof.
  move => m n A f l Hfcond. elim: l => [//| h t IH].
  move => r j. rewrite in_cons negb_or => /andP[Hhr Hnotint] //=. rewrite -Hfcond. by apply: IH. by []. 
Qed. 

Lemma row_function_equiv: forall {m n} (A: 'M[F]_(m,n)) (l : seq 'I_m) (r : 'I_m) (f: 'I_m -> 'M[F]_(m,n) -> 'M[F]_(m,n)),
  (forall (A : 'M_(m, n)) (i : ordinal_eqType m) (j : 'I_n) r,
         i != r -> A i j = f r A i j) -> (*f only changes entries in r*)
  (forall (A B : 'M[F]_(m,n)) r, (forall j, A r j = B r j) -> (forall r' j, r' \notin l -> A r' j = B r' j) ->
    f r A = f r B) -> (*f depends only on values in row r and rows not in the list*) 
  r \notin l ->
  forall j, (f r (foldr f A l)) r j = (f r A) r j.
Proof.
  move => m n A l r f Hres Hinp Hinr' j. f_equal. apply: Hinp. move => j'. by apply mx_row_transform_notin.
  clear Hinr' r j. elim: l => [//| h t IH].
  move => r j. rewrite in_cons negb_or => /andP[Hhr Hnotint] //=. rewrite -Hres. apply IH. all: by [].
Qed.

(*How we can describe the entries of the resulting list (all other entries are handled by [mx_row_transform_notin]*)
Lemma mx_row_transform: forall {m n} (A: 'M[F]_(m,n)) (f: 'I_m -> 'M[F]_(m,n) -> 'M[F]_(m,n)) (l: seq 'I_m),
  (forall (A: 'M[F]_(m,n)) i j r, i != r ->  A i j = (f r A) i j) ->
  (forall (A B : 'M[F]_(m,n)) r, (forall j, A r j = B r j) -> (forall r' j, r' \notin l -> A r' j = B r' j) ->
    f r A = f r B) ->
  uniq l ->
  forall r j, r \in l ->
  (foldr f A l) r j = (f r A) r j.
Proof.
  move => m n A f l Hfout. elim: l => [//| h t IH]. rewrite //= => Hfin /andP[Hnotin Huniq] r j.
  rewrite //= in_cons. move /orP => [/eqP Hhr | Hinr]. subst. apply (row_function_equiv).
  apply: Hfout. move => A' B r' H1 H2. apply: Hfin. apply: H1. move => r'' j'' Hnotin'. apply: H2.
  move : Hnotin'. rewrite in_cons negb_or => /andP[Heq Hnin]. by []. by [].
  rewrite -Hfout. apply: IH; rewrite //. move => A' B' r' H1 H2. apply: Hfin; rewrite //.
  move => r'' j''. rewrite in_cons negb_or => /andP[Heq Hnin]. by apply: H2.
  destruct (r == h) eqn : Heq. move : Heq => /eqP Heq. subst. move : Hinr Hnotin. move ->. by []. by [].
Qed.

(*This resulting matrix is row equivalent if f is*)
Lemma mx_row_transform_equiv: forall {m n} (A: 'M[F]_(m,n)) (f: 'I_m -> 'M[F]_(m,n) -> 'M[F]_(m,n)) (l: seq 'I_m),
  (forall (A: 'M[F]_(m, n)) (r : 'I_m), row_equivalent A (f r A)) ->
  row_equivalent A (foldr f A l).
Proof.
  move => m n A f l Hre. elim: l => [//=| h t IH].
  apply: row_equiv_refl. rewrite //=. apply (row_equivalent_trans IH). apply Hre.
Qed. 

(*Now we can define the gaussian elimination functions*)

(*make all entries in column c 1 or zero*)






End Gauss.