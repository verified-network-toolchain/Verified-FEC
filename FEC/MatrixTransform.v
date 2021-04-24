(* Transform a matrix by mapping over it or flattening it*)
Require Import VST.floyd.proofauto.

Require Import ByteField.
Require Export ListMatrix.
Require Import ZSeq.

Set Bullet Behavior "Strict Subproofs".

(*Need because "forward" gives some weird defaults for Znth*)
Lemma Znth_default: forall {A: Type} (H2 H1: Inhabitant A) (l: list A) (i: Z),
  0 <= i < Zlength l ->
  @Znth _ H1 i l = @Znth _ H2 i l.
Proof.
  intros A Hin1 Hin2 l i Hi. unfold Znth. destruct (zlt i 0); try lia.
  apply nth_indep. rewrite <-ZtoNat_Zlength. lia.
Qed.

(** Map over 2D List*)

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

(*Now we define several transformation functions in terms of these functions*)

Definition flatten_mx (mx: bytemx): list byte :=
  concat (map_2d_rev id mx).

Definition mx_val: bytemx -> list (list val) :=
  map_2d Vubyte.

Definition rev_mx_val: bytemx -> list (list val) :=
  map_2d_rev Vubyte.

(** Working with [flatten_mx]*)
(*We want to flatten a matrix into a single list. We need to know - if we get or update
  an entry in the flattened matrix, what does that correspond to in the real matrix?*)

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

(** Working with [mx_val] and [rev_mx_val]*)

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
  
Require Import ZSeq.

Lemma mx_val_zseq: forall x y b,
  mx_val (zseq x (zseq y b)) = zseq x (zseq y (Vubyte b)).
Proof.
  intros x y b. unfold mx_val. unfold map_2d. rewrite !zseq_map. reflexivity.
Qed. 
