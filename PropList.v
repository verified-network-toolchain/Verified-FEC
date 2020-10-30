Require Import VST.floyd.functional_base.
Require Import Helper.

(*This gives us a way to specify lists/arrays by saying that "forall i, a[i] = f(i)"*)
Definition prop_list {A: Type} (f: Z -> A) (bound: Z) :=
  map f (map (Z.of_nat) (seq 0 (Z.to_nat bound))).

Lemma prop_list_length: forall {A} (f: Z -> A) bound,
  0 <= bound ->
  Zlength (prop_list f bound) = bound.
Proof.
  intros. unfold prop_list. rewrite? Zlength_map. 
  rewrite Zlength_seq. lia.
Qed.

Lemma prop_list_Znth: forall {A} `{Inhabitant A} (f: Z -> A) bound i,
  0 <= i < bound ->
  Znth i (prop_list f bound) = f i.
Proof.
  intros. unfold prop_list. rewrite Znth_map.
  rewrite Znth_map. rewrite Znth_seq. simpl. f_equal. lia. lia.
  rewrite Zlength_seq. lia. rewrite Zlength_map. rewrite Zlength_seq. lia.
Qed.

Lemma prop_list_0: forall {A: Type} (f: Z -> A),
  prop_list f 0 = nil.
Proof.
  intros. unfold prop_list. simpl. reflexivity.
Qed.

Lemma prop_list_plus_1: forall {A : Type} (f: Z -> A) (z: Z),
  0 <= z ->
  prop_list f (z+1) = prop_list f z ++ (f z) :: nil.
Proof.
  intros. unfold prop_list. replace (Z.to_nat (z+1)) with (Z.to_nat z + 1)%nat by lia.
  rewrite seq_app. simpl. rewrite map_app. simpl. rewrite map_app. simpl. 
  f_equal. f_equal. f_equal. lia.
Qed.