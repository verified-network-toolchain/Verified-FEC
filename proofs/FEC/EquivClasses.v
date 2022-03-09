Require Import compcert.lib.Coqlib.
Require Import Coq.Lists.List.
Require Import Lia.

Local Open Scope nat_scope.

Definition partition {A: Type} (f: A -> bool) (l: list A) : list A * list A :=
  ((List.filter f l), (List.filter (fun x => negb (f x)) l)).

Lemma partition_eq: forall {A: Type} (f: A -> bool) l,
  partition f l = List.partition f l.
Proof.
  intros. unfold partition. induction l; intros; simpl in *.
  - reflexivity.
  - destruct (f a); simpl; destruct (List.partition f l); inversion IHl; subst; reflexivity.
Qed.

Lemma partition_fst_spec: forall {A: Type} (f: A -> bool) (l: list A) (x: A),
  In x l ->
  (In x (fst (partition f l)) <-> f x = true).
Proof.
  intros. unfold partition. simpl. rewrite filter_In. intuition.
Qed.

Lemma partition_snd_spec: forall {A: Type} (f: A -> bool) (l: list A) (x: A),
  In x l ->
  (In x (snd (partition f l)) <-> negb(f x) = true).
Proof.
  intros. unfold partition. simpl. rewrite filter_In. intuition.
Qed.

Lemma partition_length: forall {A: Type} (f: A -> bool) (l: list A),
  (length (fst (partition f l)) + length (snd (partition f l))) = length l.
Proof.
  intros. rewrite !partition_eq.
  destruct (List.partition f l) as [l1 l2] eqn : Hpart.
  apply partition_length in Hpart. simpl. auto.
Qed. 

From Equations Require Import Equations.

Section EquivClass.

Context {A B: Type} (f: A -> B) (Heq: forall (b1 b2: B), {b1=b2} + {b1<>b2}).

(*Equations does not play well with "let" expressions*)
Equations equiv_classes (l: list A)  : list (list A) by wf (length l) lt :=
  equiv_classes nil := nil;
  equiv_classes (x :: _)  := 
     (fst (partition (fun y => proj_sumbool (Heq (f x) (f y))) l)) :: 
          equiv_classes (snd (partition (fun y => proj_sumbool (Heq (f x) (f y))) l)).
Next Obligation.
  assert (length (filter (fun x0 : A => negb (proj_sumbool (Heq (f x) (f x0)))) l) <= length l). {
    pose proof (partition_length (fun x0 : A => negb (proj_sumbool (Heq (f x) (f x0)))) l). 
    simpl in H. lia. }
  lia.
Defined.

(*TODO: see what lemmas we need *)
End EquivClass.