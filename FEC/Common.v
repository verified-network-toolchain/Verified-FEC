Require Import VST.floyd.proofauto.

(*
Require Export Poly.
Require Export IntPoly.
Require Import ConcretePolys.
Require Export PropList.
Require Export PolyMod.
Require Export PrimitiveFacts.
Require Export PolyField.*)
Require Import ByteField.
Require Export ListMatrix.
Require Import ZSeq.
Require Import ByteFacts (*for xor only*).

Set Bullet Behavior "Strict Subproofs".

(*TODO: is this the right place?*)
(*Need because "forward" gives some weird defaults for Znth*)
Lemma Znth_default: forall {A: Type} (H2 H1: Inhabitant A) (l: list A) (i: Z),
  0 <= i < Zlength l ->
  @Znth _ H1 i l = @Znth _ H2 i l.
Proof.
  intros A Hin1 Hin2 l i Hi. unfold Znth. destruct (zlt i 0); try lia.
  apply nth_indep. rewrite <-ZtoNat_Zlength. lia.
Qed.

(*TODO: maybe put this in [ByteFacts] and remove import*)
Lemma byte_xor_size: forall b1 b2,
  0 <= Z.lxor (Byte.unsigned b1) (Byte.unsigned b2) <= Byte.max_unsigned.
Proof.
  intros b1 b2. split.
  - apply Z.lxor_nonneg; rep_lia.
  - pose proof (@Byte_unsigned_nonneg b1) as Hb1.
    pose proof (@Byte_unsigned_nonneg b2) as Hb2.
    pose proof (Z.log2_lxor (Byte.unsigned b1) (Byte.unsigned b2) Hb1 Hb2) as Hlog.
    assert (Hxorlog: Z.log2 (Z.lxor (Byte.unsigned b1) (Byte.unsigned b2)) <= 7). {
      apply (Z.le_trans _ _ _ Hlog). apply Z.max_lub; apply byte_log2_range. }
    assert (Hxorlt: Z.log2 (Z.lxor (Byte.unsigned b1) (Byte.unsigned b2)) < 8) by lia.
    replace 8 with (Z.log2 Byte.modulus) in Hxorlt by reflexivity. 
    apply Z.log2_lt_cancel in Hxorlt. rep_lia.
Qed.

Lemma byte_xor_fold: forall b1 b2,
  (Z.lxor (Byte.unsigned b1) (Byte.unsigned b2)) = Byte.unsigned  (Byte.xor b1 b2).
Proof.
  intros b1 b2. unfold Byte.xor. rewrite Byte.unsigned_repr; [ reflexivity | apply byte_xor_size].
Qed.

(** Facts about Integer Representations and Bounds*)
(*
(*Probably helpful more generally*)
Lemma unsigned_repr: forall z,
  0 <= z < Int.modulus -> Int.unsigned (Int.repr z) = z.
Proof.
  intros.
  pose proof (Int.eqm_unsigned_repr z).
  apply Int.eqm_sym in H0.
  unfold Int.eqm in H0. eapply Zbits.eqmod_small_eq. apply H0. all: rep_lia. 
Qed.

Lemma zbits_small: forall i,
  0 <= i < 256 ->
  Zbits.Zzero_ext 8 i = i.
Proof.
  intros i Hi. rewrite Zbits.Zzero_ext_mod; [|rep_lia]. replace (two_p 8) with (256) by reflexivity.
  rewrite Zmod_small; lia.
Qed.

Lemma Z_expand_bounds: forall a b c d n,
  a <= b ->
  c <= d ->
  b <= n <= c ->
  a <= n <= d.
Proof.
  intros. lia.
Qed.

Lemma Zmod_mod: forall (z1 z2 : Z),
  0 <= z1 ->
  0%Z < z2 ->
  Z.to_nat (z1 mod z2) = ((Z.to_nat z1) mod (Z.to_nat z2))%nat.
Proof.
  intros z1 z2 Hz1 Hz2. replace z1 with (Z.of_nat (Z.to_nat z1)) at 1 by lia.
  replace z2 with (Z.of_nat (Z.to_nat z2)) at 1 by lia.
  rewrite <- mod_Zmod. lia. lia.
Qed. 

Lemma Int_eq_reflect: forall (a b : int),
  reflect (a = b) (Int.eq a b).
Proof.
  intros. destruct (Int.eq a b) eqn : Heq. apply ReflectT. apply Int.same_if_eq; auto.
  apply ReflectF. apply int_eq_false_e; auto.
Qed.
*)

(*TODO: see where to put these, in specs or not

(** Facts about [FEC_N and modulus] *)

Definition fec_n : Z := proj1_sig (opaque_constant 256).
Definition fec_n_eq : fec_n = 256%Z := proj2_sig (opaque_constant _).

Definition modulus : Z := proj1_sig (opaque_constant 285).
Definition modulus_eq : modulus = 285%Z := proj2_sig (opaque_constant _).

Definition fec_max_h : Z := proj1_sig (opaque_constant 128).
Definition fec_max_h_eq : fec_max_h = 128%Z := proj2_sig (opaque_constant _).

Definition fec_max_cols : Z := proj1_sig (opaque_constant 16000).
Definition fec_max_cols_eq: fec_max_cols = 16000%Z := proj2_sig(opaque_constant _).

Hint Rewrite fec_n_eq : rep_lia.
Hint Rewrite fec_max_h_eq : rep_lia.
Hint Rewrite modulus_eq : rep_lia.
Hint Rewrite fec_max_cols_eq : rep_lia.

Definition mod_poly : poly := proj1_sig (opaque_constant (poly_of_int modulus)).
Definition mod_poly_eq : mod_poly = poly_of_int modulus := proj2_sig (opaque_constant _).

(*not used in VST proofs - we only need to know that it is irreducible, primitive, and has degree 8*)
Lemma modulus_poly: mod_poly = p256.
Proof.
  rewrite mod_poly_eq. rewrite modulus_eq. reflexivity.
Qed.

Lemma mod_poly_deg_log: deg mod_poly = Z.log2 (fec_n).
Proof.
  rewrite modulus_poly. replace (deg p256) with 8 by reflexivity. rewrite fec_n_eq.
  reflexivity. 
Qed.

Lemma mod_poly_deg_eq: deg mod_poly = 8.
Proof.
  rewrite modulus_poly. reflexivity.
Qed.

Lemma mod_poly_deg_pos: deg mod_poly > 0.
Proof.
  rewrite mod_poly_deg_eq; lia.
Qed.

Lemma mod_poly_not_x: mod_poly <> x.
Proof.
  rewrite modulus_poly. intro C; inversion C. 
Qed.

Lemma mod_poly_primitive: primitive mod_poly.
Proof.
  rewrite modulus_poly. apply p256_primitive. 
Qed.

Instance mod_poly_PosPoly : PosPoly mod_poly := {
  Hpos := mod_poly_deg_pos;}.

Instance mod_poly_PrimPoly : PrimPoly mod_poly := {
  Hprim := mod_poly_primitive;
  Hnotx := mod_poly_not_x}.

(*Other results about degrees of mod_poly and other polynomials*)

(*A very important lemma for bounds of polys represented by ints*)
Lemma polys_deg_bounded: forall z,
  0 <= z < fec_n ->
  deg (poly_of_int z) < deg mod_poly.
Proof.
  intros. destruct (Z.eq_dec 0 z).
  - subst. assert (poly_of_int 0 = zero) by (rewrite poly_of_int_zero; lia). rewrite H0.
    assert (deg zero < 0) by (rewrite deg_zero; reflexivity).
    rewrite mod_poly_deg_eq; lia.
  - rewrite poly_of_int_deg by lia. rewrite mod_poly_deg_eq.
    assert (z <= Z.pred(2 ^ 8)) by rep_lia.
    apply Z.log2_le_mono in H0.
    rewrite Z.log2_pred_pow2 in H0; lia.
Qed.

(*Also important: The verse of this*)
Lemma modulus_poly_bound: forall p,
  deg p < deg mod_poly ->
  0 <= poly_to_int p < fec_n.
Proof.
  intros. pose proof (poly_to_int_bounded p).
  rewrite mod_poly_deg_eq in H.
  assert (2 ^ (deg p + 1) <= fec_n). { replace fec_n with (2 ^8) by rep_lia.  
  apply Z.pow_le_mono_r; lia. } lia.
Qed. 

Lemma field_size_fec_n: Z.of_nat (field_size mod_poly) = fec_n - 1.
Proof.
  unfold field_size. rewrite mod_poly_deg_eq. rewrite fec_n_eq. reflexivity.
Qed. 

Lemma modulus_poly_monomial: forall n,
  0 < poly_to_int ((monomial n) %~ mod_poly).
Proof.
  intros. apply poly_to_int_monomial_irred.
  eapply f_irred. apply mod_poly_PrimPoly. apply Hnotx. apply Hpos.
Qed.

Lemma monomial_mod_nonzero: forall (n: nat),
  monomial n %~ mod_poly <> zero.
Proof.
  intros n Hz. pose proof modulus_poly_monomial n. rewrite <- poly_to_int_zero_iff in Hz. lia.
Qed.

Lemma poly_add_mod_bound: forall (p1 p2: poly),
  deg p1 < deg mod_poly ->
  deg p2 < deg mod_poly ->
  poly_add_mod mod_poly p1 p2 = p1 +~ p2.
Proof.
  intros. unfold poly_add_mod. rewrite pmod_refl. reflexivity.
  apply mod_poly_PosPoly. pose proof (poly_add_deg_max p1 p2). lia.
Qed.

(** Definition of lookup tables *)

(* i -> x^i % f in fec_2_index*)
Definition power_to_index_contents (bound : Z) :=
  (map Vint (map Int.repr (prop_list (fun z => 
      poly_to_int ( (monomial (Z.to_nat z)) %~ mod_poly)) bound))).

(*p -> i such that x^i % f = p in fec_2_power. This is the coq function [find_power]*)
Definition index_to_power_contents :=
  (map Vint (map Int.repr (prop_list
  (fun z => find_power mod_poly (poly_of_int z)) fec_n))).

Definition inverse_contents bound :=
    (map Vint (map Int.repr (prop_list (fun z => 
      poly_to_int (poly_inv mod_poly (poly_of_int z))) bound))).

Hint Rewrite Zlength_map : list_solve_rewrite. 

(*Use this here, so we don't define it in [FECTactics]*)
Ltac solve_prop_length :=
  repeat lazymatch goal with
  | [ |- context[ (power_to_index_contents ?b)]] => unfold power_to_index_contents
  | [ |- context [ index_to_power_contents]] => unfold index_to_power_contents
  | [ |- context [ (inverse_contents ?b) ]] => unfold inverse_contents
  | [ |- context [ Zlength (map ?f ?l) ]] => rewrite !Zlength_map
  | [ |- context [ Zlength (prop_list ?f ?z) ]] => rewrite prop_list_length
  | [ |- _ ] => list_solve
  end; try rep_lia; auto.

Lemma power_to_index_contents_plus_1: forall bound,
  0 <= bound ->
  power_to_index_contents (bound + 1) = power_to_index_contents bound ++ 
  (Vint (Int.repr (poly_to_int (monomial (Z.to_nat bound) %~ mod_poly)))) :: nil.
Proof.
  unfold power_to_index_contents. intros. rewrite prop_list_plus_1. rewrite? map_app.
  reflexivity. assumption.
Qed.

Lemma power_to_index_contents_length: forall bound,
  0 <= bound ->
  Zlength (power_to_index_contents bound) = bound.
Proof.
  intros. solve_prop_length.
Qed.

Lemma power_to_index_contents_Znth: forall bound i,
  0 <= i < bound ->
  Znth i (power_to_index_contents bound) = Vint (Int.repr (poly_to_int ((monomial (Z.to_nat i)) %~ mod_poly))).
Proof.
  intros. unfold power_to_index_contents. rewrite? Znth_map; try solve_prop_length.
  rewrite prop_list_Znth. reflexivity. lia.
Qed. 

Lemma index_to_power_contents_length: Zlength (index_to_power_contents) = fec_n.
Proof.
  solve_prop_length.
Qed.

Lemma index_to_power_contents_Znth: forall i,
  0 <= i < fec_n ->
  Znth i index_to_power_contents = Vint (Int.repr (find_power mod_poly (poly_of_int i))).
Proof.
  intros. unfold index_to_power_contents. rewrite? Znth_map; try solve_prop_length.
  rewrite prop_list_Znth. reflexivity. lia.
Qed.

Lemma inverse_contents_length: forall bound,
  0 <= bound ->
  Zlength (inverse_contents bound) = bound.
Proof.
  intros. solve_prop_length.
Qed.

Lemma inverse_contents_Znth: forall bound i,
  0 <= i < bound ->
  Znth i (inverse_contents bound) = Vint (Int.repr (poly_to_int (poly_inv mod_poly (poly_of_int i)))).
Proof.
  intros. unfold inverse_contents. rewrite? Znth_map; try solve_prop_length.
  rewrite prop_list_Znth. reflexivity. lia.
Qed.
*)

(** Field and Matrix Representations*)
(*
Definition B := byte_fieldType. @qpoly_fieldType mod_poly mod_poly_PosPoly mod_poly_PrimPoly.*)

(*

Instance F_inhab : Inhabitant (ssralg.GRing.Field.sort F) := inhabitant_F F.*)

(*Matrices are represented in the C code in two different ways: as a 2D array with reversed rows
  and as a single pointer, pointing to a location in memory of
  size m * n, such that the reversed rows appear one after another. We need to flatten a matrix
  into a single list to represent this in Coq*)

(*
(*We need this or else implict arguments are a nightmare*)
Definition f_to_poly (x: ssralg.GRing.Field.sort F) : poly := proj1_sig x.*)

(*Map a function over a 2D list, reversing each inner list*)
Definition map_2d_rev {A B: Type} (f: A -> B) (l: list (list A)) : list (list B) :=
  map (fun l' => rev (map f l')) l.

(*Do the same but without reversing*)
Definition map_2d {A B : Type} (f: A -> B) (l: list (list A)) : list (list B) :=
  map (fun l' => map f l') l.

(*[Znth] and [Zlength] for 2D maps*)

Lemma map_2d_Znth: forall {A B : Type} `{Inhabitant A} `{Inhabitant B} (f : A -> B) (l: list (list A)) i j,
  0 <= i < Zlength l ->
  0 <= j < Zlength (Znth i l) ->
  Znth j (Znth i (map_2d f l)) = f (Znth j (Znth i l)).
Proof.
  intros A B Hinh1 Hinh2 f l i j Hi Hj.
  unfold map_2d. rewrite !Znth_map by lia. reflexivity.
Qed.

Lemma map_2d_Zlength1: forall {A B : Type} (f : A -> B) (l: list (list A)),
  Zlength (map_2d f l) = Zlength l.
Proof.
  intros. unfold map_2d. list_solve.
Qed.

Lemma map_2d_Zlength2:  forall {A B : Type} (f : A -> B) (l: list (list A)) i,
  Zlength (Znth i (map_2d f l)) = Zlength (Znth i l).
Proof.
  intros A B f l i. assert (Hi: (0 <= i < Zlength l \/ ~ (0 <= i < Zlength l))) by lia. destruct Hi as [Hi | Hi].
  - unfold map_2d. rewrite Znth_map by auto. list_solve.
  - rewrite !Znth_outofbounds; [reflexivity | lia|]. rewrite map_2d_Zlength1. lia. 
Qed.

Lemma map_2d_app: forall {A B : Type} (f : A -> B) (l1 l2: list (list A)),
  map_2d f (l1 ++ l2) = map_2d f l1 ++ map_2d f l2.
Proof.
  intros. unfold map_2d. apply map_app.
Qed.

(*The same lemmas for [map_2d_rev]*)

Lemma map_2d_rev_Znth: forall {A B : Type} `{Inhabitant A} `{Inhabitant B} (f : A -> B) (l: list (list A)) i j,
  0 <= i < Zlength l ->
  0 <= j < Zlength (Znth i l) ->
  Znth j (Znth i (map_2d_rev f l)) = f (Znth ((Zlength (Znth i l)) - j - 1) (Znth i l)).
Proof.
  intros A B Hinh1 Hinh2 f l i j Hi Hj.
  unfold map_2d_rev. rewrite !Znth_map by lia. rewrite Znth_rev by list_solve. rewrite Zlength_map.
  rewrite Znth_map by list_solve. reflexivity.
Qed.

Lemma map_2d_rev_Zlength1: forall {A B : Type} (f : A -> B) (l: list (list A)),
  Zlength (map_2d_rev f l) = Zlength l.
Proof.
  intros. unfold map_2d_rev. list_solve.
Qed.

Lemma map_2d_rev_Zlength2:  forall {A B : Type} (f : A -> B) (l: list (list A)) i,
  Zlength (Znth i (map_2d_rev f l)) = Zlength (Znth i l).
Proof.
  intros A B f l i. assert (Hi: (0 <= i < Zlength l \/ ~ (0 <= i < Zlength l))) by lia. destruct Hi as [Hi | Hi].
  - unfold map_2d_rev. rewrite Znth_map by auto. rewrite Zlength_rev. list_solve.
  - rewrite !Znth_outofbounds; [reflexivity | lia|]. rewrite map_2d_rev_Zlength1. lia.
Qed.


Lemma map_2d_rev_app: forall {A B : Type} (f : A -> B) (l1 l2: list (list A)),
  map_2d_rev f (l1 ++ l2) = map_2d_rev f l1 ++ map_2d_rev f l2.
Proof.
  intros. unfold map_2d_rev. apply map_app.
Qed.

Definition bytemx := lmatrix byte_fieldType.

(*Now we define several transformation functions in terms of these functions*)
(*
Definition rev_mx : bmx -> bmx :=
  map_2d_rev id.
*)(*

Definition rev_mx : matrix F -> list (list Z) := 
  map_2d_rev (fun q => poly_to_int (f_to_poly q)).

Definition norev_mx : matrix F -> list (list Z) :=
  map_2d (fun q => poly_to_int (f_to_poly q)).*)

Definition flatten_mx (mx: bytemx): list byte :=
  concat (map_2d_rev id mx).

Definition mx_val: bytemx -> list (list val) :=
  map_2d Vubyte.

Definition rev_mx_val: bytemx -> list (list val) :=
  map_2d_rev Vubyte.
(*

Definition map_int_val_2d : list (list Z) -> list (list val) :=
  map_2d (fun x => Vint (Int.repr x)).

Definition rev_mx_val (mx: matrix F) : list (list val) :=
  map_int_val_2d (rev_mx mx).
*)

(*Add up all lengths of inner lists - matrices not necessarily well-formed*)
Definition whole_Zlength {A: Type} (l: list (list A)) :=
  fold_right (fun x acc => Zlength x + acc) 0%Z l.

Lemma concat_Zlength: forall {A: Type} (l: list (list A)),
  Zlength (concat l) = whole_Zlength l.
Proof.
  intros. induction l; simpl; list_solve.
Qed.

Lemma whole_Zlength_app: forall {A: Type} (l1 l2 : list (list A)),
  whole_Zlength (l1 ++ l2) = whole_Zlength l1 + whole_Zlength l2.
Proof.
  intros. induction l1; simpl; lia.
Qed.

Lemma whole_Zlength_upd_Znth: forall {A: Type} (l: list (list A)) i (l': list A),
  Zlength l' = Zlength (Znth i l) ->
  whole_Zlength (upd_Znth i l l') = whole_Zlength l.
Proof.
  intros A l i l' Hlen.
  assert ((0 > i \/ i >= Zlength l) \/ (0 <= i < Zlength l)) by lia. destruct H as [Hout | Hin].
  - rewrite upd_Znth_out_of_range; auto.
  - rewrite upd_Znth_unfold; auto. rewrite !whole_Zlength_app. simpl.
    assert (l = (sublist 0 i l) ++ (Znth i l :: sublist (i+1) (Zlength l) l)). { 
    rewrite <- (sublist_same 0 (Zlength l)) at 1 by reflexivity.
    rewrite (sublist_split 0 i) by lia.
    rewrite (sublist_split i (i+1)) by lia.  rewrite sublist_len_1 by lia. auto. }
    rewrite H at 4. rewrite !whole_Zlength_app. simpl. rewrite Hlen. lia.
Qed. 

Lemma whole_Zlength_nonneg: forall {A: Type} (l: list (list A)),
  0 <= whole_Zlength l.
Proof.
  intros. induction l; simpl; list_solve.
Qed.

Lemma whole_Zlength_map2d_rev: forall {A B: Type} (f: A -> B) (l: list (list A)),
  whole_Zlength (map_2d_rev f l) = whole_Zlength l.
Proof.
  intros. induction l; simpl; auto. rewrite Zlength_rev. list_solve.
Qed.

Lemma whole_Zlength_wf_matrix: forall (mx: bytemx) m n,
  wf_lmatrix mx m n ->
  whole_Zlength mx = m * n.
Proof.
  intros mx m n Hwf. destruct Hwf as [Hlen [Hn Hin]]. generalize dependent m.
  induction mx; intros m Hlen.
  - list_solve.
  - simpl in *. inversion Hin; subst. rewrite Zlength_cons. rewrite IHmx with(m:=Zlength mx); auto.
    nia.
Qed.

Lemma whole_Zlength_sublist: forall (mx: bytemx) m n lo hi,
  wf_lmatrix mx m n ->
  0 <= lo <= hi ->
  hi <= Zlength mx -> 
  whole_Zlength (sublist lo hi mx) = (hi - lo) * n.
Proof.
  intros mx m n lo hi Hwf Hlo Hi. apply whole_Zlength_wf_matrix.
  destruct Hwf as [Hlen [Hn Hin]].
  unfold wf_lmatrix. split. list_solve. split. assumption.
  rewrite Forall_forall in *. intros.  apply Hin. eapply sublist_In. apply H.
Qed.

(*The real result that we want: allows us to convert from the indexing used in the C code to
  our matrix functions*)
Lemma flatten_mx_Znth: forall {m n} (mx: bytemx) i j,
  wf_lmatrix mx m n ->
  0 <= i < m ->
  0 <= j < n ->
  Znth (i * n + n - 1 - j) (flatten_mx mx) = (get mx i j).
Proof.
  intros m n mx i j Hwf Him Hjn. unfold get. unfold flatten_mx.
  assert (Hwf' := Hwf).
  destruct Hwf as [Hlen [Hn Hin]]. 
  assert (Hsplit : mx = sublist 0 i mx ++ sublist i (Zlength mx) mx). rewrite <- sublist_split; try lia.
  rewrite sublist_same; reflexivity. rewrite Hsplit at 1. rewrite map_2d_rev_app. rewrite concat_app.
  assert (Hconlen: Zlength (concat (map_2d_rev id (sublist 0 i mx))) = i * n). {
    rewrite concat_Zlength. simpl. rewrite whole_Zlength_map2d_rev. rewrite (whole_Zlength_sublist _ m n); try lia.
    assumption. }
  rewrite Znth_app2 by lia. rewrite Hconlen. replace (i * n + n - 1 - j - i * n) with (n - 1 - j) by rep_lia.
  rewrite (sublist_split _ (i+1) _) by lia. rewrite sublist_len_1 by lia. simpl.
  assert (Hrevlen: Zlength (rev (map id (Znth i mx))) = n). {
    rewrite Zlength_rev. rewrite Zlength_map. rewrite Forall_Znth in Hin. apply Hin; lia. } simpl in *.
  rewrite Znth_app1 by lia. rewrite Zlength_rev in Hrevlen. rewrite Znth_rev by lia.
  rewrite Zlength_map. rewrite Zlength_map in Hrevlen. rewrite Znth_map by lia.
  rewrite Hrevlen. simpl. f_equal. lia.
Qed. 

(*Matrix accesses are within bounds*)
Lemma matrix_bounds_within: forall m n i j,
  0 <= i < m ->
  0 <= j < n ->
  0 <= (i * n) + n - 1 - j < m * n.
Proof.
  intros m n i j Him Hjn. nia.
Qed.

(*We want the opposite direction: for some 0 <= z < m * n, we want i and j which are the indices in the matrix*)
Definition find_indices (n z: Z) :=
  (Z.div z n, z mod n).

Lemma find_indices_correct: forall m n z,
  0 < n ->
  0 <= z < m * n ->
  0 <= z / n < m /\
  0 <= (n - 1 - (z mod n)) < n /\
  z = (z / n) * n + n - 1 - (n - 1 - (z mod n)).
Proof.
  intros m n z Hn Hz. split. pose proof (Z.mul_div_le z _ Hn).
  assert (n * (z / n) < n * m) by lia.
  rewrite <- Z.mul_lt_mono_pos_l in H0. split. apply Z.div_pos; lia. assumption. assumption.
  split. pose proof (Z.mod_pos_bound z n Hn). split; lia.
  rewrite Zmod_eq; lia.
Qed.

(*TODO: move probably*)
Lemma upd_Znth_rev: forall {A: Type} (l: list A) (i: Z) (x: A),
  upd_Znth i (rev l) x = rev (upd_Znth (Zlength l - i - 1) l x).
Proof.
  intros. assert (Inhabitant A). apply x. apply Znth_eq_ext. rewrite Zlength_rev. rewrite !Zlength_upd_Znth.
  apply Zlength_rev. intros j Hj. rewrite Zlength_upd_Znth in Hj. rewrite Zlength_rev in Hj.
  rewrite Znth_rev; rewrite Zlength_upd_Znth; try lia.
  assert (i = j \/ i <> j) by lia. destruct H as [Heq | Hneq].
  - subst. rewrite !upd_Znth_same; try lia. reflexivity. rewrite Zlength_rev. auto.
  - rewrite Znth_upd_Znth_diff by lia. rewrite Znth_rev by auto.
    rewrite Znth_upd_Znth_diff by lia. reflexivity.
Qed.

(*The analogue of [flatten_mx_Znth] for updating an entry in the matrix*)
Lemma flatten_mx_set: forall {m n} (mx: bytemx) i j q,
  wf_lmatrix mx m n ->
  0 <=i < m ->
  0 <= j < n ->
  upd_Znth (i * n + n - 1 - j) (flatten_mx mx) q  = flatten_mx (set mx i j q).
Proof.
  intros m n mx i j q Hwf Hi Hj. (*easier to use [Znth_eq_ext] than similar proof as get*)
  apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth. unfold set. unfold flatten_mx. rewrite !concat_Zlength. 
    rewrite !whole_Zlength_map2d_rev. 
    rewrite whole_Zlength_upd_Znth. reflexivity. list_solve.
  - intros i' Hilen'.
    rewrite Zlength_upd_Znth in Hilen'. unfold flatten_mx in *.
    assert (Hconlen: Zlength (concat (map_2d_rev id mx)) = m * n). {
      rewrite concat_Zlength. rewrite whole_Zlength_map2d_rev.
      apply (whole_Zlength_wf_matrix _ _ _ Hwf). }
    assert (Hwf' : wf_lmatrix (set mx i j q) m n). {
      unfold set. destruct Hwf as [Hlen [Hn Hin]]. unfold wf_lmatrix. split.
      list_solve. split; auto. rewrite Forall_Znth in *.
      intros z Hzlen. assert (z = i \/ z <> i) by lia. destruct H; subst. rewrite upd_Znth_same; try lia.
      rewrite Zlength_upd_Znth. apply Hin. lia.
      rewrite upd_Znth_diff; try lia; [| list_solve]. apply Hin. list_solve. } simpl in *.
    assert (i' <> (i * n + n - 1 - j) \/ i' = (i * n + n - 1 - j)) by lia. destruct H as [Hneq | Heq].
    + rewrite upd_Znth_diff; try lia; try nia. unfold set. simpl in *. rewrite Hconlen in Hilen'.
      assert (H0n : 0 < n) by lia.
      pose proof (find_indices_correct _ _ _ H0n Hilen') as [Hx [Hy Hi']].
      rewrite Hi'. pose proof (@flatten_mx_Znth m n). unfold flatten_mx in H.
      rewrite !H; try lia; unfold set in Hwf'; auto. unfold get.
      assert (( (i' / n) = i) \/ ((i' / n) <> i)) by lia. destruct H0.
      * subst. rewrite upd_Znth_same. list_solve. destruct Hwf as [Hlen [Hn Hin]]. lia.
      * destruct Hwf as [Hlen [Hn Hin]]. rewrite upd_Znth_diff by lia. reflexivity.
    + rewrite Heq. rewrite upd_Znth_same by lia. pose proof  (@flatten_mx_Znth m n); unfold flatten_mx in H; 
      rewrite H by (try lia; auto); clear H. unfold get. unfold set. destruct Hwf as [Hlen [Hn Hin]].
      repeat(rewrite upd_Znth_same; try lia). reflexivity. rewrite Forall_Znth in Hin. rewrite Hin; lia.
Qed.

(*

(** Going from list (list Z) -> matrix F*)
(* The reverse of the transformation in [Common] - to go from a matrix of ints (bounded correctly) to a matrix of qpolys.
  This is essentially "interpreting the input as elements of a finite field"*)
Definition int_to_poly_mx : list (list Z) -> matrix F :=
  map_2d (fun x => exist (fun x => deg x < deg mod_poly) (poly_of_int x %~ mod_poly) (pmod_lt_deg _ _)).

Lemma int_to_poly_mx_spec: forall (l: list (list Z)),
  Forall2D (fun z => 0 <= z <= Byte.max_unsigned) l ->
  forall i j,
  proj1_sig (Znth j (Znth i (int_to_poly_mx l))) = poly_of_int (Znth j (Znth i l)).
Proof.
  intros l Hall i j. unfold int_to_poly_mx.
  assert (Hi: (0 <= i < Zlength l \/ ~ (0 <= i < Zlength l))) by lia. destruct Hi as [Hi | Hi].
  -  assert (Hj: (0 <= j < Zlength (Znth i l) \/ ~ (0 <= j < Zlength (Znth i l)))) by lia. destruct Hj as [Hj | Hj].
    + rewrite map_2d_Znth by lia. simpl. rewrite pmod_refl. reflexivity. apply mod_poly_PosPoly.
      apply polys_deg_bounded. rewrite Forall2D_Znth in Hall. destruct (Hall i j); auto. rep_lia.
    + rewrite Znth_outofbounds. simpl. rewrite Znth_outofbounds.
      symmetry. rewrite poly_of_int_zero. unfold Inhabitant_Z. lia. lia.
      rewrite map_2d_Zlength2; lia.
  - rewrite !(Znth_outofbounds i). unfold Inhabitant_list. rewrite !Znth_nil. simpl. unfold default.
    unfold Inhabitant_Z. symmetry. rewrite poly_of_int_zero. lia. lia. rewrite map_2d_Zlength1; lia.
Qed.*)

(*Length and Znth lemmas - so that we don't have to unfold definitions*)

(*TODO: see what we need*)
(*
Lemma int_to_poly_mx_length1: forall l,
  Zlength (int_to_poly_mx l) = Zlength l.
Proof.
  intros. apply map_2d_Zlength1.
Qed.

Lemma int_to_poly_mx_length2: forall l i,
  Zlength (Znth i (int_to_poly_mx l)) = Zlength (Znth i l).
Proof.
  intros. apply map_2d_Zlength2.
Qed.

Lemma rev_mx_length1: forall l,
  Zlength (rev_mx l) = Zlength l.
Proof.
  intros. apply map_2d_rev_Zlength1.
Qed.

Lemma rev_mx_length2: forall l i,
  Zlength (Znth i (rev_mx l)) = Zlength (Znth i l).
Proof.
  intros. apply map_2d_rev_Zlength2.
Qed.

Lemma map_int_val_2d_length1: forall l,
  Zlength (map_int_val_2d l) = Zlength l.
Proof.
  intros. apply map_2d_Zlength1.
Qed.

Lemma map_int_val_2d_length2: forall l i,
  Zlength (Znth i (map_int_val_2d l)) = Zlength (Znth i l).
Proof.
  intros. apply map_2d_Zlength2.
Qed.*)

Lemma mx_val_length1: forall l,
  Zlength (mx_val l) = Zlength l.
Proof.
  intros. apply map_2d_Zlength1.
Qed.

Lemma mx_val_length2: forall l i,
  Zlength (Znth i (mx_val l)) = Zlength (Znth i l).
Proof.
  intros. apply map_2d_Zlength2.
Qed.

Lemma rev_mx_val_length1: forall l,
  Zlength (rev_mx_val l) = Zlength l.
Proof.
  intros. apply map_2d_rev_Zlength1.
Qed.

Lemma rev_mx_val_length2: forall l i,
  Zlength (Znth i (rev_mx_val l)) = Zlength (Znth i l).
Proof.
  intros. apply map_2d_rev_Zlength2.
Qed.

(*

Lemma norev_mx_length1: forall l, Zlength (norev_mx l) = Zlength l.
Proof.
  unfold norev_mx. apply map_2d_Zlength1.
Qed.

Lemma norev_mx_length2: forall l i,
  Zlength (Znth i (norev_mx l)) = Zlength (Znth i l).
Proof.
  unfold norev_mx. apply map_2d_Zlength2.
Qed.
*)
(*
Lemma rev_mx_Znth: forall l i j,
  0 <= i < Zlength l ->
  0 <= j <  Zlength (Znth i l) ->
  Znth j (Znth i (rev_mx l)) = poly_to_int (f_to_poly (Znth (Zlength (Znth i l) - j - 1) (Znth i l))).
Proof.
  intros. unfold rev_mx. rewrite map_2d_rev_Znth; auto.
Qed.

Lemma map_int_val_2d_Znth: forall l i j,
   0 <= i < Zlength l ->
   0 <= j < Zlength (Znth i l) ->
   Znth j (Znth i (map_int_val_2d l)) = Vint (Int.repr (Znth j (Znth i l))).
Proof.
  intros. unfold map_int_val_2d. rewrite map_2d_Znth; auto.
Qed.*)

Lemma rev_mx_val_Znth: forall l i j,
  0 <= i < Zlength l ->
  0 <= j < Zlength (Znth i l) ->
  Znth j (Znth i (rev_mx_val l)) =  Vubyte ((Znth (Zlength (Znth i l) - j - 1) (Znth i l))). 
Proof.
  intros. unfold rev_mx_val. apply map_2d_rev_Znth; assumption. 
Qed.

Lemma mx_val_Znth: forall l i j,
  0 <= i < Zlength l ->
  0 <= j < Zlength (Znth i l) ->
  Znth j (Znth i (mx_val l)) =  Vubyte (Znth j (Znth i l)).
Proof.
  intros. apply map_2d_Znth; assumption.
Qed.

Lemma mx_val_upd_Znth: forall l i j b,
  0 <= i < Zlength l ->
  upd_Znth i (mx_val l) (upd_Znth j (Znth i (mx_val l)) (Vubyte b)) =
    mx_val (set l i j b).
Proof.
  intros l i j b Hi. unfold set.  unfold mx_val. unfold map_2d.
  rewrite <- !upd_Znth_map. f_equal. f_equal. rewrite Znth_map by assumption. reflexivity.
Qed.

Lemma concat_rev_mx: forall mx,
  concat (rev_mx_val mx) = map Vubyte (flatten_mx mx).
Proof.
  intros mx. unfold flatten_mx. rewrite concat_map. unfold rev_mx_val.
  f_equal. unfold map_2d_rev. rewrite !map_map. apply map_ext.
  intros b. rewrite map_rev. rewrite map_id. reflexivity.
Qed. 

Lemma rev_mx_val_wf: forall mx m n,
  wf_lmatrix mx m n ->
  Zlength (rev_mx_val mx) = m /\ Forall (fun l => Zlength l = n) (rev_mx_val mx).
Proof.
  intros mx m n [Hlen [_ Hall]]. split.
  rewrite rev_mx_val_length1. apply Hlen. revert Hall.
  rewrite !Forall_Znth. rewrite rev_mx_val_length1. rewrite !Hlen. intros Hall i Hi.
  rewrite rev_mx_val_length2. apply Hall; assumption.
Qed.
  
(*Move between [map_2d] and [map_2d_rev]. This holds in general, but we only prove it
  for byte lists because we have useful abbreviations such as "get" and "wf_lmatrix"*)
Lemma map_2d_rev_equiv: forall {A} `{Inhabitant A} m n (mx1 mx2: bytemx) (f: byte -> A) ,
  wf_lmatrix mx1 m n ->
  wf_lmatrix mx2 m n ->
  (forall i j, 0 <= i < m -> 0 <= j < n -> get mx1 i j = get mx2 i (n - j - 1)) ->
  map_2d f mx1 = map_2d_rev f mx2.
Proof.
  intros A Hinhab m n mx1 mx2 f [Hlen1 [_ Hinlen1]] [Hlen2 [_ Hinlen2]] Hall. simpl in *. apply Znth_eq_ext;
  rewrite map_2d_Zlength1; rewrite Hlen1.
  - rewrite map_2d_rev_Zlength1. lia.
  - intros i Hi. revert Hinlen1 Hinlen2. rewrite !Forall_Znth. rewrite Hlen1. rewrite Hlen2. intros Hin1 Hin2.
    specialize (Hin1 _ Hi). specialize (Hin2 _ Hi).
    apply Znth_eq_ext; rewrite map_2d_Zlength2; rewrite Hin1.
    + rewrite map_2d_rev_Zlength2. lia.
    + intros j Hj. rewrite map_2d_Znth by lia. rewrite map_2d_rev_Znth by lia.
      unfold get in Hall. rewrite Hall by lia. f_equal. f_equal. lia.
Qed.

Require Import ZSeq.

Lemma mx_val_zseq: forall x y b,
  mx_val (zseq x (zseq y b)) = zseq x (zseq y (Vubyte b)).
Proof.
  intros x y b. unfold mx_val. unfold map_2d. rewrite !zseq_map. reflexivity.
Qed. 

(*

Lemma norev_mx_Znth: forall l i j,
  0 <= i < Zlength l ->
  0 <= j <  Zlength (Znth i l) ->
  Znth j (Znth i (norev_mx l)) = poly_to_int (f_to_poly (Znth j (Znth i l))).
Proof.
  intros. unfold norev_mx. rewrite map_2d_Znth; auto.
Qed.

Lemma Znth_inhab_eq: forall {A: Type} (H1: Inhabitant A) (H2: Inhabitant A) (i: Z) (l: list A),
  0 <= i < Zlength l ->
  @Znth _ H1 i l = @Znth _ H2 i l.
Proof.
  intros. unfold Znth. destruct (zlt i 0). lia. apply nth_indep. rewrite <- ZtoNat_Zlength. lia.
Qed. 
*)
(*TODO: see what we need*)
(*
Ltac simpl_map2d :=
  simpl; repeat match goal with
  | [ |- context [ Zlength (rev_mx ?l) ]] => rewrite rev_mx_length1
  | [ |- context [ Zlength (Znth ?i (rev_mx ?l)) ]] => rewrite rev_mx_length2
  | [ |- context [ Zlength (map_int_val_2d ?l) ]] => rewrite map_int_val_2d_length1
  | [ |- context [ Zlength (Znth ?i (map_int_val_2d ?l)) ]] => rewrite map_int_val_2d_length2
  | [ |- context [ Zlength (rev_mx_val ?l) ]] => rewrite rev_mx_val_length1
  | [ |- context [ Zlength (Znth ?i (rev_mx_val ?l)) ]] => rewrite rev_mx_val_length2
  | [ |- context [ Zlength (int_to_poly_mx ?l) ]] => rewrite int_to_poly_mx_length1
  | [ |- context [ Zlength (norev_mx ?l) ]] => rewrite norev_mx_length1
  | [ |- context [ Zlength (Znth ?i (norev_mx ?l)) ]] => rewrite norev_mx_length2
  | [ |- context [ Zlength (Znth ?i (int_to_poly_mx ?l)) ]] => rewrite int_to_poly_mx_length2
  | [ |- context [ Znth ?j (Znth ?i (rev_mx ?l)) ]] => 
        rewrite rev_mx_Znth; [ | auto; try lia; try list_solve  | auto; try lia; try list_solve ]
  | [ |- context [ Znth ?j (Znth ?i (norev_mx ?l)) ]] => 
        rewrite norev_mx_Znth; [ | auto; try lia; try list_solve  | auto; try lia; try list_solve ]
  | [ |- context [ Znth ?j (Znth ?i (map_int_val_2d ?l)) ]] => 
        rewrite map_int_val_2d_Znth; [ | auto; try lia; try list_solve  | auto; try lia; try list_solve ]
  | [ |- context [ Znth ?j (Znth ?i (rev_mx_val ?l)) ]] => 
      (*Because implicit arguments get screwed up - TODO: do we need for other cases?*)
      rewrite (Znth_inhab_eq _ Inhabitant_list i (rev_mx_val l)) ; 
      [ rewrite rev_mx_val_Znth; try rep_lia | try rep_lia; simpl_map2d; try rep_lia; list_solve]
  end.
*)
