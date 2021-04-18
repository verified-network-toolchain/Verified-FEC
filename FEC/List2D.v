Require Import VST.floyd.proofauto.
(*A generic notion of [Forall] for 2D lists. We give 3 equivalent definitions, but the 2nd will likely be
  the most useful for VST proofs*)

Definition Forall2D {A: Type} (P: A -> Prop) (l: list (list A)) : Prop :=
  forall l' x, In l' l -> In x l' -> P x.

Lemma Forall2D_Znth: forall {A: Type} `{Inhabitant A} (P: A -> Prop) (l : list (list A)),
  Forall2D P l <-> forall i j, 0 <= i < Zlength l -> 0 <= j < Zlength (Znth i l) -> P (Znth j (Znth i l)).
Proof.
  intros A Inh P l. unfold Forall2D. split.
  - intros Hin i j Hi Hj.
    apply (Hin (Znth i l)). apply Znth_In; lia. apply Znth_In; lia.
  - intros Hin l' x Hinx' Hinx.
    rewrite In_Znth_iff in Hinx. destruct Hinx as [ j [Hj Hjnth]]. subst. 
    rewrite In_Znth_iff in Hinx'. destruct Hinx' as [i [Hi Hinth]]. subst.
    apply Hin; auto.
Qed.

Lemma Forall2D_Forall : forall {A: Type} (P: A -> Prop) (l : list (list A)),
  Forall2D P l <-> Forall (fun l' => Forall (fun z => P z) l') l.
Proof.
  intros A P l. unfold Forall2D. rewrite Forall_forall. split; intros Hall l'.
  - intros Hin. rewrite Forall_forall. intros x Hinx. apply (Hall l'); auto.
  - intros x Hinl' Hinx. apply Hall in Hinl'. rewrite Forall_forall in Hinl'. apply Hinl'; auto.
Qed.