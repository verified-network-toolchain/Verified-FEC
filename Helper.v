Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import VST.floyd.functional_base.
(** Contains definitions and lemmas that are useful more generally *)

Ltac solve_neq := intro C; inversion C.

Definition null {A} (l: list A) :=
  match l with
  | nil => true
  | _ => false
  end.

Lemma in_tl_in_list: forall {A: Type } (x: A) l,
  In x (tl l) ->  
  In x l.
Proof.
  intros. unfold tl in H. destruct l. assumption. right. assumption.
Qed.

(* function (from Haskell) to remove all values from end of list that satisfy a predicate. *)
Definition dropWhileEnd {A} (p: A -> bool)(l: list A)  : list A :=
  fold_right (fun x acc => if (null acc) && (p x) then nil else x :: acc) nil l.

Lemma dropWhileEnd_nil: forall {A} p (l: list A),
  dropWhileEnd p l = nil <-> forall x, In x l -> p x = true.
Proof.
  intros. induction l; split; intros.
  - inversion H0.
  - reflexivity.
  - simpl in H. destruct (null (dropWhileEnd p l)) eqn : N. simpl in H. destruct (p a) eqn : P.
    + destruct H0. subst. assumption. apply IHl. destruct (dropWhileEnd p l). reflexivity. inversion N. assumption.
    + inversion H.
    + simpl in H. inversion H.
  - simpl. destruct ((dropWhileEnd p l)) eqn : D. simpl. assert (p a = true). apply H. left. reflexivity.
    rewrite H0. reflexivity. assert (a0 :: l0 = nil). apply IHl. intros. apply H. right. assumption.
    inversion H0.
Qed. 

Lemma dropWhileEnd_spec: forall {A} p (l: list A) (y: A) res,
  dropWhileEnd p l = res <->
  (exists l1, l = res ++ l1 /\ forall x, In x l1 -> p x = true) /\
  (res <> nil -> p (last res y) = false).
Proof.
  intros. split; intros; subst. induction l; simpl; split.
  - exists nil. auto.
  - intros. contradiction.
  - destruct IHl. destruct (dropWhileEnd p l) eqn : L.
    + simpl. destruct (p a) eqn : P.
      * exists (a :: l). simpl. split. reflexivity. intros. destruct H1. subst. assumption.
        destruct H. destruct H. simpl in H; subst. apply H2. assumption.
      * exists l. simpl. split. reflexivity. destruct H. destruct H. simpl in H; subst. apply H1.
    + simpl. destruct H as [l1]. destruct H. subst. exists l1. split. reflexivity. apply H1.
  - destruct IHl. destruct (dropWhileEnd p l) eqn : L; simpl.
    + destruct (p a) eqn : P.
      * intros. contradiction.
      * intros. simpl. assumption.
    + intros. simpl in H0. apply H0. intro. inversion H2.
  - destruct H. destruct H as [l1]. destruct H. rewrite H. unfold dropWhileEnd. rewrite fold_right_app.
    assert ((fold_right (fun (x : A) (acc : list A) => if null acc && p x then nil else x :: acc) nil l1) =
    dropWhileEnd p l1). unfold dropWhileEnd. reflexivity. rewrite H2; clear H2.
    assert (dropWhileEnd p l1 = nil). apply dropWhileEnd_nil. apply H1. rewrite H2.
    assert (fold_right (fun (x : A) (acc : list A) => if null acc && p x then nil else x :: acc) nil res
    = dropWhileEnd p res) by reflexivity. rewrite H3; clear H3.
    clear H2. clear H1. clear H. induction res.
    + reflexivity.
    + simpl. destruct (dropWhileEnd p res) eqn : D.
      * simpl. destruct (p a) eqn : P. simpl in H0. destruct res.
        rewrite H0 in P. inversion P. intro. inversion H.
        assert (nil = a0 :: res). apply IHres. intros. apply H0. intro. inversion H1. inversion H.
        destruct res. reflexivity. rewrite IHres. reflexivity. intros. simpl. simpl in H0. apply H0.
        intro. inversion H1.
      * simpl. destruct res. simpl in IHres. rewrite IHres. reflexivity. intros. contradiction.
        rewrite IHres. reflexivity. intros. simpl. simpl in H0. apply H0. intro. inversion H1; simpl in IHres.
Qed.

Lemma Znth_nil: forall {A} `{d: Inhabitant A} z,
  Znth z (@nil A) = d.
Proof.
  intros. assert (z < 0 \/ z >= 0) by lia. destruct H.
  - rewrite Znth_underflow; try lia. reflexivity.
  - rewrite Znth_overflow. reflexivity. list_solve.
Qed.

Lemma Znth_last: forall {A} `{Inhabitant A} (l: list A) x,
  l <> nil ->
  Znth (Zlength l - 1) l = last l x.
Proof.
  intros A H l. induction l; intros.
  - contradiction.
  - destruct l.
    + simpl. list_solve.
    + simpl in IHl. simpl. rewrite <- IHl. list_solve. intro C; inversion C. 
Qed.

Lemma last_nonempty: forall {A} (l1: list A) l2 (x: A),
  l2 <> nil ->
  last (l1 ++ l2) x = last l2 x.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. destruct ((l1 ++ l2)) eqn : L. 
    destruct l1. destruct l2. contradiction. inversion L. inversion L. apply IHl1.
Qed.

Lemma last_in: forall {A} (l1: list A) (x: A),
  l1 <> nil ->
  In (last l1 x) l1.
Proof.
  intros. induction l1.
  - contradiction.
  - destruct l1. simpl. left. reflexivity. right. simpl in *. apply IHl1. intro C; inversion C. 
Qed.  


Lemma Znth_seq: forall start len z,
  0 <= z < Z.of_nat len ->
  Znth z (seq start len) = Z.to_nat (Z.of_nat start + z).
Proof.
  intros. rewrite <- nth_Znth. rewrite seq_nth. lia. lia. 
  rewrite Zlength_correct. rewrite seq_length. lia.
Qed. 

Lemma Zlength_seq: forall start len,
  Zlength (seq start len) = Z.of_nat len.
Proof.
  intros. rewrite Zlength_correct. rewrite seq_length. reflexivity.
Qed. 

(*If we have a list of A and a proof that each element in the list satisfies P x, then we can create a list
  of {x : A | P x}*)
Definition exist_list {A : Type} (P: A -> Prop) (l: list A) :
  (forall x, In x l -> P x) ->
  list ({ x : A | P x}) .
Proof.
  intros. induction l.
  - apply nil.
  - apply cons. apply (exist _ a). apply H. left. reflexivity.
    apply IHl. intuition.
Defined.

(*Properties of [exist_list]*)
Lemma exist_list_length: forall {A: Type} (P: A -> Prop) (l: list A) (H: forall x, In x l -> P x),
  length (exist_list P l H) = length l.
Proof.
  induction l.
  - simpl. intros. reflexivity.
  - simpl. intros. rewrite IHl. reflexivity.
Qed.

Lemma exist_list_in: forall {A} (P : A -> Prop) l (H: forall x, In x l -> P x) x,
  In x (exist_list P l H) <-> In (proj1_sig x) l.
Proof.
  intros; induction l; simpl.
  - reflexivity.
  - split; intros.
    + destruct H0. subst. simpl. left. reflexivity.
      right. eapply IHl. apply H0.
    + destruct H0. left. subst. destruct x.
      apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat. reflexivity.
      right. apply IHl. apply H0.
Qed.

Lemma exist_list_NoDup: forall {A} (P: A -> Prop) l (H: forall x, In x l -> P x),
  NoDup (exist_list P l H) <-> NoDup l.
Proof.
  intros. induction l; simpl.
  - split; constructor.
  - split; intros. inversion H0. constructor. subst. intro. apply H3.
    rewrite exist_list_in. simpl. assumption. eapply IHl. apply H4.
    inversion H0; subst. constructor. intro. apply H3. rewrite exist_list_in in H1.
    simpl in H1. assumption. apply IHl. assumption.
Qed. 

Lemma NoDup_app: forall {A: Type} (l1 l2:list A),
  NoDup l1 ->
  NoDup l2 ->
  (forall x, In x l1 -> ~In x l2) ->
  NoDup (l1 ++ l2).
Proof.
  intros A l1; induction l1; intros.
  - simpl. assumption.
  - simpl. inversion H; subst. constructor. intro.
    apply in_app_or in H2. destruct H2. contradiction. apply (H1 a). left. reflexivity. assumption.
    apply IHl1. assumption. assumption. intros. apply H1. right. assumption.
Qed.

(* Likewise, we can turn a {x : A | P x} list into a list A by just unwrapping the types *)
Definition dep_list_to_list {A: Type} (P: A -> Prop) (l: list {x : A | P x}) : list A :=
  fold_right (fun x acc => (@proj1_sig A P x) :: acc) nil l.

(* Function to find the first element in a list satisfying a predicate*)
Definition find_default {A: Type} (l: list A) (x: A) (P: A -> A -> bool) (default : A) : A :=
  fold_right (fun hd acc => if (P x hd) then hd else acc) default l.

Lemma find_default_in: forall {A: Type} (l: list A) x P default,
  (forall a b, P a b = true -> b <> default) ->
  (exists y, In y l /\ P x y = true) <-> P x (find_default l x P default) = true.
Proof.
  intros. induction l; split; intros.
  - destruct H0. inversion H0. inversion H1.
  - simpl in H0. apply H in H0. contradiction.
  - simpl. destruct (P x a) eqn : E. assumption.
    simpl in H0. destruct H0 as [y]. destruct H0.
    destruct H0. subst. rewrite E in H1. inversion H1. 
    apply IHl. exists y; auto.
  - simpl in H0. destruct (P x a) eqn : E.
    exists a. intuition. apply IHl in H0. destruct H0 as [y]. exists y. intuition.
Qed.
