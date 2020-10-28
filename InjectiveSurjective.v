Require Import Coq.Logic.FinFun.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
(*Injective and Surjective Functions f : A -> B *)
Section InjectiveFacts.

Variable A: Type.
Variable B : Type.
Variable f : A -> B.
Variable lA : list A.
Variable lB : list B.
Variable HAfull : Listing lA.
Variable HBfull : Listing lB.

(*may add more later - of course this is really an iff  but this is all we need so far*)

Lemma injective_surjective: length lA >= length lB ->
  Injective f -> Surjective f.
Proof.
  intros. unfold Listing in HAfull. destruct HAfull.
  remember (map f lA) as l'.
  assert (NoDup l'). rewrite Heql'. apply Injective_map_NoDup. assumption. assumption.
  assert (length lA = length l'). rewrite Heql'. rewrite map_length. reflexivity.
  assert (Permutation l' lB). apply NoDup_Permutation_bis; try assumption.
  lia. unfold incl. intros. apply HBfull. 
  unfold Surjective. intros.
  assert (In y l'). eapply Permutation_in. apply Permutation_sym. apply H5.
  apply HBfull. rewrite Heql' in H6. rewrite in_map_iff in H6.
  destruct H6. exists x. apply H6.
Qed.

End InjectiveFacts.