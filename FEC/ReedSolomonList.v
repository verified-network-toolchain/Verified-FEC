Require Import VST.floyd.functional_base.

From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import Vandermonde.
Require Import Common.
Require Import ListMatrix.
Require Import ReedSolomon.
Require Import VandermondeList.
Require Import Gaussian.
Require Import CommonSSR.


Section Encoder.

(* The ListMatrix version of the encoder*)
Definition encode_list_mx (h k c : Z) (packets : list (list Z)) : matrix (Common.F) :=
  list_matrix_multiply h k c (submatrix (fec_n - 1) weight_mx h k) 
      (extend_mx k c (int_to_poly_mx packets)).

(*Lift the above into ssreflect matrices and operations*)
Lemma encoder_spec : forall (h k c : Z) (packets: list (list Z)) (Hh: h <= fec_max_h) (Hk: k <= fec_n - 1),
  0 <= h ->
  0 <= k ->
  0 <= c ->
  Zlength packets = k ->
  Forall (fun x => Zlength x <= c) packets ->
  matrix_to_mx h c (encode_list_mx h k c packets) = encoder (le_Z_N Hh) (le_Z_N Hk)
    (matrix_to_mx fec_max_h (fec_n - 1) weight_mx) 
    (matrix_to_mx k c (extend_mx k c (int_to_poly_mx packets))).
Proof.
  move => h k c packets Hh Hk Hn0 Hk0 Hc0 Hlen Hin. rewrite /encode_list_mx /encoder.
  have Hwf: wf_matrix weight_mx fec_max_h (fec_n - 1). apply weight_mx_wf. 
  rewrite list_matrix_multiply_correct.
  by rewrite (@submatrix_to_mx _ (fec_max_h) (fec_n - 1) _ _ _ Hh Hk).
  by apply submatrix_wf.
  by apply extend_mx_wf. 
Qed.

End Encoder.

Section Decoder.

(*Intermediate functions*)

(*First, get the lost packets*)
Definition find_lost (stats: list Z) (c: Z) : list Z :=
  fold_left (fun acc x => if Z.eq_dec (Znth x stats) 1%Z then acc ++ [:: x] else acc) (Ziota 0 c) nil.

(*the first part of the found array*)
Definition find_found (stats: list Z) (c: Z) : list Z :=
  fold_left (fun acc x => if Z.eq_dec (Znth x stats) 1%Z then acc else acc ++ [:: x]) (Ziota 0 c) nil.

Instance Inhabitant_option: forall {A: Type}, Inhabitant (option A).
intros A. apply None.
Defined.

(*Parities are represented as a list (option (list Z)), representing whether the parity packet is there
  or not. We will translate this into Vundef or Vptr as needed*)
Definition find_parities (par: list (option (list Z))) (c: Z) (max_n : Z) : (list Z * list Z) :=
  fold_left (fun (acc: seq Z * seq Z) (x : Z) => let (rows, found) := acc in  match (Znth x par) with
                                       | None => (rows, found)
                                       | _ => (rows ++ [:: x], found ++ [:: max_n - 1 - x])
                                        end) (Ziota 0 c) (nil, nil).

(*The ListMatrix version of [submx_rows_cols] TODO maybe move*)
Definition submx_rows_cols_list (mx: matrix F) m n (rows: list Z) (cols: list Z) : matrix F :=
  mk_matrix m n (fun x y => get mx (Znth x rows) (Znth y cols)) .

(*TODO: definition move*)
Lemma submx_rows_cols_list_wf: forall mx m n rows cols,
  0 <= m ->
  0 <= n ->
  wf_matrix (submx_rows_cols_list mx m n rows cols) m n.
Proof.
  move => mx m n rows cols. by apply mk_matrix_wf.
Qed.

Check submx_rows_cols.

Lemma ord_zero_proof n (H: 0 < n) : (0 < Z.to_nat n)%N.
Proof.
  apply /ltP. lia.
Qed.

Definition ord_zero n (H: 0 < n) : 'I_(Z.to_nat n) :=
  Ordinal (ord_zero_proof H).

(*Need to transform a list of Z into a list of 'I_m*)
Definition Z_ord_list (l: list Z) (n: Z) : seq 'I_(Z.to_nat n) :=
  pmap insub (map Z.to_nat l).

(*See what we need - will be something like this - maybe for Znth instead*)
Lemma Z_ord_list_spec: forall (l: seq Z) n,
  0 <= n ->
  Forall (fun x => 0 <= x < n) l ->
  map (fun i => Z.of_nat (nat_of_ord i)) (Z_ord_list l n) = l.
Proof.
  move => l n Hn. elim : l => [//| /= h t IH Hall].
  rewrite /Z_ord_list /=. have Hhn: 0 <= h < n. move: Hall; rewrite Forall_forall =>/(_ h) Hh.
  apply Hh. by left.
  rewrite insubT.  apply /ltP. lia.
  move => Hh. rewrite /= IH. by rewrite Z2Nat.id; try lia. by inversion Hall.
Qed.
(*
(*TODO: move*)
Lemma map_map: forall {A B: Type} (f: A -> B) (l: list A),
  map f l = List.map f l.
Proof. by [].
Qed.*)

Lemma nth_nth: forall {A: Type} (d: A) (l: seq A) (n: nat),
  nth d l n = List.nth n l d.
Proof.
  move => A d l. elim : l => [//= n | //= h t IH n].
  - by case : n.
  - case: n. by []. move => n. by rewrite /= IH.
Qed.

Lemma Z_ord_list_Znth: forall (l: seq Z) n i (Hn: 0 < n),
  0 <= i ->
  Forall (fun x => 0 <= x < n) l ->
  Znth i l = Z.of_nat (nth (ord_zero Hn) (Z_ord_list l n) (Z.to_nat i)).
Proof.
  move => l n i Hn Hi Hall. rewrite -{1}(@Z_ord_list_spec l n) //. 2: lia.
  rewrite /Znth. case : (zlt i 0); try lia. move =>H{H}.
  rewrite nth_nth.
  have <-: Z.of_nat (ord_zero Hn) = Inhabitant_Z by []. by rewrite map_nth.
Qed.

Lemma submx_rows_cols_list_equiv: forall mx m n m' n' rows cols (Hm: 0 < m) (Hn: 0 < n),
  0 <= m' ->
  0 <= n' ->
  Forall (fun x => 0 <= x < m) rows ->
  Forall (fun x => 0 <= x < n) cols ->
  matrix_to_mx m' n' (submx_rows_cols_list mx m' n' rows cols) = 
    submx_rows_cols (Z.to_nat m') (Z.to_nat n') (matrix_to_mx m n mx)
       (Z_ord_list rows m) (Z_ord_list cols n) (ord_zero Hm) (ord_zero Hn).
Proof.
  move => mx m n m' n' rows cols Hm Hn Hm' Hn' Hrows Hcols. apply mk_matrix_mx =>[//|//| x y Hx Hy].
  rewrite !mxE. f_equal.
  - rewrite (Z_ord_list_Znth Hm) =>[//| |//]. lia.
  - rewrite (Z_ord_list_Znth Hn) => [//||//]. lia.
Qed. 

(*Concatenate two matrices*)
Definition row_mx_list (left: matrix F) (right: matrix F) m n1 n2 : matrix F :=
  mk_matrix m (n1 + n2) (fun x y => if Z_lt_ge_dec y n1 then get left x y else get right x (y - n1)).

Lemma row_mx_list_wf: forall left right m n1 n2,
  0 <= m ->
  0 <= n1 ->
  0 <= n2 ->
  wf_matrix (row_mx_list left right m n1 n2) m (n1 + n2).
Proof.
  move => l r m n1 n2 Hm Hn1 H2. apply mk_matrix_wf; lia.
Qed.

(*Need a cast bc it cannot unify Z.to_nat n + Z.to_nat m with Z.to_nat (n + m)*)
Lemma row_mx_list_spec: forall left right m n1 n2 (Hn1: 0 <= n1) (Hn2: 0 <= n2),
  0 <= m ->
  matrix_to_mx m (n1 + n2) (row_mx_list left right m n1 n2) =
    castmx (Logic.eq_refl _, Logic.eq_sym (Z2Nat.inj_add n1 n2 Hn1 Hn2))
    (row_mx (matrix_to_mx m n1 left) (matrix_to_mx m n2 right)).
Proof.
  move => l r m n1 n2 Hn1 Hn2 Hm. rewrite -matrixP => x y.
  rewrite castmxE !mxE /= mk_matrix_get.
  - case: (Z_lt_ge_dec (Z.of_nat y) n1) =>[ Hy /=|Hy  /=].
    + pose proof (splitP (cast_ord (esym (Logic.eq_sym (Z2Nat.inj_add n1 n2 Hn1 Hn2))) y)).
      case : X =>[j /= Hyj | k /= Hyk]. by rewrite Hyj cast_ord_id mxE.
      rewrite Hyk in Hy. move: Hy. rewrite Nat2Z.inj_add Z2Nat.id; lia. (*Why can't lia do this automatically?*)
    + pose proof (splitP (cast_ord (esym (Logic.eq_sym (Z2Nat.inj_add n1 n2 Hn1 Hn2))) y)).
      case : X =>[j /= Hyj | k /= Hyk]. 
      * have: (j < Z.to_nat n1)%N by []. rewrite -Hyj => /ltP Hyn1. lia.
      * rewrite cast_ord_id mxE Hyk. f_equal. rewrite Nat2Z.inj_add. lia. (*again, why do I need to rewrite?*)
  - by apply Z_ord_bound.
  - apply Z_ord_bound. lia.
Qed.

(*The identity matrix*)
Definition id_list (n: Z) := mk_matrix n n (fun x y => if Z.eq_dec x y then (GRing.one F) else (GRing.zero F)).

Lemma id_list_wf: forall n,
  0 <= n ->
  wf_matrix (id_list n) n n.
Proof.
  move => n Hn. by apply mk_matrix_wf.
Qed.

Lemma id_list_spec: forall n,
  0 <= n ->
  matrix_to_mx n n (id_list n) = (1%:M)%R.
Proof.
  move => n Hn. rewrite -matrixP => x y.
  rewrite id_A mxE mk_matrix_get.
  - case : (Z.eq_dec (Z.of_nat x) (Z.of_nat y)) => [Hxy /= | Hxy /=].
    + have->: x == y. apply /eqP. apply ord_inj. lia. by [].
    + have->:x == y = false. apply /eqP. move => C. rewrite C in Hxy. lia. by [].
  - by apply Z_ord_bound.
  - by apply Z_ord_bound.
Qed.

(*We want to invert a matrix by concatenating it with the identity, then running gaussian elimination. We define
  each part separately to make the VST proof cleaner*)
Definition concat_mx_id (mx: matrix F) n :=
  row_mx_list mx (id_list n) n n n.

(*NOTE: (delete later) - dont need to worry about reversal here, everything will be
  wrapped in [rev_mx_val] or whatever - only place to worry about is with portion of weight mx, since
  that is actually reversed*)

(*Get the right submatrix of an n x (n + n) matrix*)
Definition right_submx n (mx: matrix F) :=
  mk_matrix n n (fun x y => get mx x (n + y)).

Lemma right_submx_wf: forall n mx,
  0 <= n ->
  wf_matrix (right_submx n mx) n n.
Proof.
  move => n mx Hn. by apply mk_matrix_wf.
Qed.

(*We again need a cast to unify (Z.to_nat (n + n)) and Z.to_nat n + Z.to_nat n*)
Lemma right_submx_spec: forall n mx (Hn: 0 <= n),
  matrix_to_mx n n (right_submx n mx) = 
  rsubmx (castmx (Logic.eq_refl _, (Z2Nat.inj_add n n Hn Hn)) (matrix_to_mx n (n + n) mx)).
Proof.
  move => n mx Hn. rewrite -matrixP => x y.
  rewrite !mxE castmxE mxE /= mk_matrix_get. f_equal; try lia. rewrite Nat2Z.inj_add; lia.
  by apply Z_ord_bound. by apply Z_ord_bound.
Qed.

Definition find_invmx_list (mx: matrix F) n :=
  right_submx n (gauss_restrict_rows n (n + n) (concat_mx_id mx n)).

Check strong_inv_list.

Check castmx.

Lemma cast_eq: forall m n m' n' (A: 'M[F]_(m, n)) (B: 'M[F]_(m', n')) (Heq: (m = m') * (n = n')),
  (forall (x: 'I_m) (y: 'I_n), A x y = B (cast_ord (fst Heq) x) (cast_ord (snd Heq) y)) ->
  castmx Heq A = B.
Proof.
  move => m n m' n' A B Heq Hab. rewrite -matrixP => x y.
  rewrite castmxE Hab /=. f_equal; by apply ord_inj.
Qed.

(*TODO: move to Gaussian*)

(*Lots of annoying stuff due to casting - is there an easier way to bring it all through?*)
Print gaussian_elim_restrict.
Print gauss_all_steps_restrict_end.
Print gauss_all_steps_restrict_aux.
Print gauss_one_step_restrict.
Print all_cols_one_noif_gen.


Check mx_row_transform.

Check foldr.

Check pmap.

Print ord_enum.

Definition cast_seq n n' (H: n = n') (s: seq 'I_n)  : seq 'I_n' :=
  map (cast_ord H) s.

Lemma foldr_castmx: forall m n m' n' (A: 'M[F]_(m, n)) (Heq: (m = m') * (n = n')) 
  (f: 'I_m -> 'M[F]_(m, n) -> 'M[F]_(m, n)) (g: 'I_m' -> 'M[F]_(m', n') -> 'M[F]_(m', n')) (l: seq 'I_m),
  (forall (x: 'I_m) (A: 'M[F]_(m, n)), castmx Heq (f x A) = g (cast_ord (fst Heq) x) (castmx Heq A)) ->
  castmx Heq (foldr f A l) = foldr g (castmx Heq A) (cast_seq (fst Heq) l).
Proof.
  move => m n m' n' A Heq f g l Hfg. elim : l => [//= | h t IH /=].
  by rewrite Hfg IH.
Qed.

(*Probably can abstract this as functor or monad or something*)
Definition cast_option n n' (H: n = n')  (o: option 'I_n) : option 'I_n' :=
  match o with
  | None => None
  | Some x => Some ((cast_ord H) x)
  end.

Lemma cast_option_none: forall n n' (H: n = n') (o: option 'I_n),
  (cast_option H o == None) = (o == None).
Proof.
  move => n n' H o. by case : o.
Qed.

Lemma cast_option_some: forall n n' (H: n = n') (o: option 'I_n) c,
  cast_option H o = Some c ->
  exists d, o = Some d /\ (cast_ord H) d = c.
Proof.
  move => n n' H o c. case : o =>[d //= Hsome | //=]. exists d. case: Hsome. by move ->.
Qed.

(*Working with casts is very annoying*)
Lemma lead_coef_cast: forall m n m' n' (H: (m = m') * (n = n')) (A: 'M[F]_(m, n)) (r: 'I_m),
  lead_coef A r = cast_option (esym (snd H)) (lead_coef (castmx H A) (cast_ord (fst H) r)).
Proof.
  move => m n m' n' H A r.
  case Hlc: (lead_coef A r) =>[c /= | //=].
  - move: Hlc. rewrite lead_coef_some_iff => [[Hrc Hbefore]].
    symmetry. case Hlc : (lead_coef (castmx H A) (cast_ord H.1 r)) => [d /= | //=].
    + move : Hlc. rewrite lead_coef_some_iff => [[Hrd Hbef]].
      move : Hrd; rewrite castmxE /= => Hrd.
      case (orP (ltn_total c  (cast_ord (esym (snd H)) d))).
      * move => /orP[Hlt | Heq].
        -- have: A r c == 0%R. apply /eqP.  move: Hbef => /(_ (cast_ord (snd H) c)).
           rewrite castmxE !cast_ordK => Hzero. by apply Hzero.
            move : Hrc; by case : (A r c == 0%R).
        -- apply (elimT eqP) in Heq. f_equal. by apply ord_inj.
      * move => Hdc. have:  A (cast_ord (esym H.1) (cast_ord H.1 r)) (cast_ord (esym H.2) d) == 0%R.
        apply /eqP. move : Hbefore => /(_ _ Hdc). by rewrite !cast_ordK.
        move: Hrd. by case : (A (cast_ord (esym H.1) (cast_ord H.1 r)) (cast_ord (esym H.2) d) == 0%R).
    + move: Hlc. rewrite lead_coef_none_iff => /(_ (cast_ord (snd H) c)). rewrite castmxE !cast_ordK => Hrc'. move: Hrc.
      by rewrite Hrc' eq_refl.
  - move: Hlc. rewrite lead_coef_none_iff => [Hall]. symmetry. apply /eqP. rewrite cast_option_none. apply /eqP.
    rewrite lead_coef_none_iff. move => x. rewrite castmxE !cast_ordK. apply Hall.
Qed.

Check gauss_all_steps_equation.
(*
(*Could do in general but more annoying bc of Function*)
Print gauss_all_steps_restrict_aux.
Lemma gauss_all_steps_restrict_cast

Lemma gauss_all_steps_cast: forall m n m' n' (Heq: (m = m') * (n = n')) (A: 'M[F]_(m, n)) (r: option 'I_m)
  (c: option 'I_n),
  castmx Heq (gauss_all_steps A r c) = (gauss_all_steps (castmx Heq A) (cast_option (fst Heq) r) (cast_option (snd Heq) c)).
Proof.
  move => m n m' n' Heq A r c. apply gauss_all_steps_ind.
  - move => A' r' c' r'' Hr c'' Hc A'' or rc Hg IH. subst. rewrite IH /=. rewrite (gauss_all_steps_equation (castmx Heq A')) /=.
    


 rewrite /=.


 Search gauss_all_steps. 


(castmx Heq (gauss_all_steps A (insub 0%N) (insub 0%N))) = (gauss_all_steps (castmx Heq A) (insub 0%N) (insub 0%N))
*)

Lemma cast_leq: forall m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N),
  (m' <= n')%N.
Proof.
  move => m n m' n' [Hm Hn]. by rewrite Hm Hn.
Qed.

Check mk_identity.

Lemma cast_seq_pmap: forall n n' (H: n = n') (l: list nat),
  cast_seq H (pmap insub l) = pmap insub l.
Proof.
  move => n n' H l. elim : l => [//= | h t Ih /=].
  case Hh: (h < n)%N.
  - rewrite !insubT /=. by rewrite -H. move => Hn'. rewrite Ih /=. f_equal.
    by apply ord_inj.
  - by rewrite !insubF // -H.
Qed.  

Lemma cast_ord_enum: forall n n' (H: n = n'),
  cast_seq H (ord_enum n) = ord_enum n'.
Proof.
  move => n n' H. rewrite /ord_enum. by rewrite cast_seq_pmap H.
Qed.

Lemma cast_ord_switch: forall n n' (H: n = n') x y,
  (cast_ord (esym H) x == y) = (x == cast_ord H y).
Proof.
  move => n n' H x y.
  case Hx : (x == cast_ord H y).
  - apply /eqP. apply (elimT eqP) in Hx. rewrite Hx. apply cast_ordK.
  - apply /eqP. apply (elimF eqP) in Hx. move => C. move: Hx. by rewrite -C cast_ordKV.
Qed.

Lemma sc_mul_castmx: forall m n m' n' (Heq: (m = m') * (n = n')) (A: 'M[F]_(m, n)) c (r: 'I_m),
  castmx Heq (sc_mul A c r) = sc_mul (castmx Heq A) c (cast_ord (fst Heq) r).
Proof.
  move => m n m' n' Heq A c r. rewrite -matrixP => x y.
  by rewrite castmxE !mxE cast_ord_switch !castmxE.
Qed.

Lemma mk_identity_castmx: forall m n m' n' (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N) (A: 'M[F]_(m, n)) x,
  castmx Heq (mk_identity A Hmn x) = mk_identity (castmx Heq A) (cast_leq Heq Hmn) x.
Proof.
  move => m n m' n' Heq Hmn A x. rewrite /mk_identity -(cast_seq_pmap (fst Heq)).
  apply foldr_castmx. move => x' A'. rewrite sc_mul_castmx. f_equal.
  rewrite castmxE /= !cast_ordK. f_equal. f_equal. by apply ord_inj.
Qed.
Check gauss_one_step_restrict.

Check sub_all_rows_noif.

Check add_mul.

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
  case Hx: (x' == x).
  - apply (elimT eqP) in Hx. by have->: cast_ord Heq.1 x' == cast_ord Heq.1 x by rewrite Hx.
  - apply (elimF eqP) in Hx. have->: cast_ord Heq.1 x' == cast_ord Heq.1 x = false.
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


Lemma castmx_gaussian_restrict: forall m n m' n' (A: 'M[F]_(m, n)) (Heq: (m = m') * (n = n')) (Hmn: (m <= n)%N),
  castmx Heq (gaussian_elim_restrict A Hmn) = gaussian_elim_restrict (castmx Heq A) (cast_leq Heq Hmn).
Proof.
  move => m n m' n' A Heq Hmn. rewrite /gaussian_elim_restrict. rewrite -matrixP => x y.
  rewrite mk_identity_castmx. f_equal. f_equal. 2: by rewrite (fst Heq).
  rewrite /gauss_all_steps_restrict_end. rewrite gauss_all_steps_restrict_castmx. f_equal.
  by rewrite Heq.1.
Qed.

Print strong_inv.
(*
Lemma submx_remove_col_castmx: forall m n m' n' (Heq: (m = m') * (n = n')) (A: 'M[F]_(m, n)) (Hmn: (m <= n)%N) r j,
  submx_remove_col (castmx Heq A) (cast_leq Heq Hmn) r j = 
  submx_remove_col A Hmn (cast_ord (esym Heq.1) r) j.
Proof.
  move => m n m' n' Heq A Hmn r j. rewrite /submx_remove_col. rewrite -matrixP => x y.
  rewrite !mxE castmxE /=. f_equal. by apply ord_inj.
  case Hyj: (y < j)%N; by apply ord_inj.
Qed.

Lemma submx_add_row_castmx: forall m n m' n' (Heq: (m = m') * (n = n')) (A: 'M[F]_(m, n)) (Hmn: (m <= n)%N) r j,
  submx_add_row (castmx Heq A) (cast_leq Heq Hmn) r j =
  submx_add_row A Hmn (cast_ord (esym Heq.1) r) (cast_ord (esym Heq.1) j).
Proof.
  move => m n m' n' Heq A Hmn r j. rewrite /submx_add_row. rewrite -matrixP => x y.
  rewrite !mxE castmxE /=. f_equal. case Hxr : (x < r)%N; by apply ord_inj. by apply ord_inj.
Qed.

Lemma strong_inv_castmx: forall m n m' n' (Heq: (m = m') * (n = n')) (A: 'M[F]_(m, n)) (Hmn: (m <= n)%N) (r: 'I_m),
  strong_inv A Hmn r ->
  strong_inv (castmx Heq A) (cast_leq Heq Hmn) (cast_ord Heq.1 r).
Proof.
  move => m n m' n' Heq A Hmn r. rewrite /strong_inv => Hstr r' Hr'. split.
  - move => j Hj. rewrite submx_remove_col_castmx.
    have Hr: (r <= cast_ord (esym Heq.1) r')%N by [].
    move: Hstr => /(_ (cast_ord (esym Heq.1) r') Hr) => [[Hsub  Hcol]].
    by apply Hsub.
  - move => j Hj. rewrite submx_add_row_castmx.
    have Hr: ((r <= cast_ord (esym Heq.1) r')%N ) by [].
    move: Hstr => /(_ (cast_ord (esym Heq.1) r') Hr) => [[Hsub Hrow]].
    by apply Hrow.
Qed.
*)

Print strong_inv.

Search (?x <= ?x + ?y)%N.

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

Lemma mulmx_castmx: forall n n' (H: n = n') (A B: 'M[F]_n),
  castmx (H, H) (A *m B)%R = ((castmx (H, H) A) *m (castmx (H, H) B))%R.
Proof.
  move => n n' H A B. rewrite -matrixP => x y.
  rewrite castmxE !mxE. have Hn: (n <= n')%N by rewrite H leqnn.
  rewrite (big_nth x) (big_nth (cast_ord (esym H) x)) /=.
  rewrite !index_ord_enum !size_ord_enum.
  rewrite (big_nat_widen _ _ _ _ _ Hn) big_nat_cond (big_nat_cond _ _ _ _ (fun x => true)).
  apply eq_big.
  - move => i. by rewrite /= H andb_diag andbT.
  - rewrite /=. move => i /andP[Hi' Hi].
    rewrite !castmxE /=. 
    have Hii: i = nat_of_ord (Ordinal Hi) by []. 
    have Hii': i = nat_of_ord (Ordinal Hi') by []. 
    have->: (nth x (ord_enum n') i) = (nth x (ord_enum n') (Ordinal Hi')) by f_equal.
    have->: (nth (cast_ord (esym H) x) (ord_enum n) i) = (nth (cast_ord (esym H) x) (ord_enum n) (Ordinal Hi)) by f_equal.
    rewrite !nth_ord_enum. by f_equal; f_equal; apply ord_inj.
Qed.

Lemma id_castmx: forall n n' (H: n = n'),
  castmx (R:=F) (H, H) (1%:M)%R = (1%:M)%R.
Proof.
  move => n n' H. rewrite -matrixP => x y.
  by rewrite castmxE !id_A cast_ord_switch cast_ordKV.
Qed.

Lemma unitmx_castmx: forall n n' (H: n = n') (A: 'M[F]_n),
  ((castmx (H, H) A) \in unitmx) = (A \in unitmx).
Proof.
  move => n n' H A. case Hun: (A \in unitmx).
  - have Hmul: (A *m (invmx A))%R = (1%:M)%R by apply mulmxV.
    have: castmx (H, H) (A *m invmx A)%R = castmx (H, H) (1%:M)%R by rewrite Hmul.
    rewrite mulmx_castmx id_castmx => Hcast. apply mulmx1_unit in Hcast. apply Hcast.
  - case Hcastun: (castmx (H, H) A \in unitmx) => [|//].
    have Hmul: ((castmx (H, H) A) *m (invmx (castmx (H, H) A)))%R = (1%:M)%R by apply mulmxV.
    have: castmx (esym H, esym H) (castmx (H, H) A *m invmx (castmx (H, H) A))%R =
          castmx (esym H, esym H) (1%:M)%R by rewrite Hmul.
    rewrite mulmx_castmx castmxK id_castmx => Ha.
    apply mulmx1_unit in Ha. case : Ha => [Ha  Hc]. by rewrite Ha in Hun.
Qed.

Lemma lt_subst: forall (n m p: nat),
  (n < m)%N ->
  m = p ->
  (n < p)%N.
Proof.
  move => n m p Hn Hmp. by rewrite -Hmp.
Qed.

(*TODO: move this too*)
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



(*The result we want: [find_invmx_list] computes the inverse. This is quite complicated to prove
  because of all the casting*)
Lemma find_invmx_list_spec: forall mx n,
  strong_inv_list n n mx 0 -> 
  matrix_to_mx n n (find_invmx_list mx n) = invmx (matrix_to_mx n n mx).
Proof.
  move => mx n. rewrite /strong_inv_list. case : (range_le_lt_dec 0 0 n) => [H0n /= | //].
  case : (Z_le_lt_dec n n) => [/= Htriv Hstr|//]. rewrite -gaussian_finds_invmx.
  - rewrite /find_invmx_list. have Hn: 0 <= n by lia. rewrite right_submx_spec /=.
    rewrite /find_invmx gauss_restrict_rows_equiv. lia. move => Hnn. 2: by apply row_mx_list_wf.
    rewrite castmx_gaussian_restrict gaussian_elim_equiv.
    + f_equal. f_equal. rewrite row_mx_list_spec; try lia. rewrite id_list_spec; try lia.
      rewrite -matrixP => x y. rewrite !castmxE /=. f_equal. by apply ord_inj. by apply ord_inj.
    + apply /ltP. lia.
    + move => Hn'. rewrite row_mx_list_spec; try lia. rewrite id_list_spec; try lia. rewrite castmxKV.
      apply (@strong_inv_row_mx _ _ (matrix_to_mx n n mx) 1%:M (le_Z_N Htriv)
              (cast_leq (erefl (Z.to_nat n), Z2Nat.inj_add n n Hn Hn) (le_Z_N Hnn))).
      by have ->: (Ordinal Hn') = Z_to_ord H0n by apply ord_inj.
  - by apply strong_inv_unitmx in Hstr.
Qed.

