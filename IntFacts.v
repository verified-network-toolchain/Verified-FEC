Require Import VST.floyd.functional_base.
(** Lemmas about integers that are useful in other proofs *)


Lemma div2_0_iff: forall z,
  Z.div2 z = 0%Z <-> z = 0%Z \/ z = 1%Z.
Proof.
  intros. split; intros.
  - assert (z < 0 \/ z = 0%Z \/ z = 1 %Z \/ z > 1%Z) by lia. destruct H0.
    rewrite <- Z.div2_neg in H0. lia.
    destruct H0. left. assumption.
    destruct H0. right. assumption.
    destruct (Zeven_odd_dec z).
    + apply Zeven_div2 in z0. lia.
    + apply Zodd_div2 in z0. lia.
  - destruct H. subst. reflexivity. subst. reflexivity.
Qed.

Lemma log2_div2: forall z,
  1 < z ->
  1 + Z.log2 (Z.div2 z) = Z.log2 z.
Proof.
  intros. rewrite Z.div2_spec. rewrite Z.log2_shiftr.
  assert (Z.log2 z >= 1). pose proof (Z.log2_nonneg z).
  assert (Z.log2 z = 0%Z \/ Z.log2 z > 0) by lia. destruct H1.
  rewrite Z.log2_null in H1. lia. lia. lia. lia.
Qed. 

Lemma evens_even: forall z,
  Z.even (2 * z) = true.
Proof.
  intros. rewrite Z.even_mul. rewrite orb_true_iff. left.
  apply Z.even_2. 
Qed.

Lemma odds_odd: forall z,
  Z.odd (1 + 2 * z) = true.
Proof.
  intros. replace (1 + 2 * z) with (Z.succ (2 * z)) by lia. 
  rewrite Z.odd_succ. apply evens_even.
Qed.

Lemma div2_even: forall z,
  Z.div2 (2 * z) = z.
Proof.
  intros. 
  pose proof (evens_even z). rewrite Zeven_bool_iff in H.
  apply Zeven_div2 in H. lia.
Qed.

Lemma div2_odd: forall z,
  Z.div2 (1 + 2 * z) = z.
Proof.
  intros. rewrite Z.div2_spec. apply Z.bits_inj. unfold Z.eqf. intros.
  assert (n< 0 \/ 0 <= n) by lia. destruct H.
  rewrite Z.testbit_neg_r. rewrite Z.testbit_neg_r. reflexivity. all: try assumption.
  rewrite Z.shiftr_spec; try assumption.
  replace (n +1) with (Z.succ n) by lia. rewrite Z.add_comm.
  rewrite Z.testbit_odd_succ. reflexivity. assumption.
Qed.