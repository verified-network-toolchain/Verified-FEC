Require Import VST.floyd.functional_base.
Require Import compcert.common.Memdata. (*for [int_of_bytes] and [bytes_of_int]*)
Require Import ByteFacts.
Set Bullet Behavior "Strict Subproofs".

(** 4 and 16-bit integers *)

Module Wordsize_4 <: WORDSIZE.
Definition wordsize : nat := 4.
Lemma wordsize_not_zero : wordsize <> 0%nat.
Proof. 
  unfold wordsize. auto.
Qed.
End Wordsize_4.
Module Nibble := (Make Wordsize_4).
Notation nibble := Nibble.int.

Module Wordsize_16 <: WORDSIZE.
Definition wordsize : nat := 16.
Lemma wordsize_not_zero: wordsize <> 0%nat.
Proof.
  unfold wordsize. auto.
Qed.
End Wordsize_16.
Module Short := (Make Wordsize_16).
Notation short := Short.int.

(*Combine nibbles into a byte (n1, followed by n2, in bits)*)
Definition nibbles_to_Z (n1 n2: nibble) : Z :=
  Z.lor (Nibble.unsigned n1) (Z.shiftl (Nibble.unsigned n2) 4).

Lemma Z_testbit_false_le: forall (x y : Z),
  0 <= x -> 0 < y ->
  (forall i, i >= y -> Z.testbit x i = false) ->
  x < 2 ^ y.
Proof.
  intros x y Hx Hy Hbits. assert (x > 0 \/ x <= 0) as [Hpos | Hneg] by lia. 2: lia.
  apply Z.log2_lt_pow2; try lia.
  rewrite <- (Z.log2_pow2 y) by lia. apply (testbit_lt (m:=y)); try lia.
  replace 2 with (2^1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia.
  intros n Hn. apply Hbits. lia. apply Z.pow2_bits_true. lia.
Qed.

(*Need generic lemma about Z.lor bound*)
Lemma Z_lor_bound: forall (z1 z2 i: Z),
  0 < i ->
  0 <= z1 < 2 ^ i ->
  0 <= z2 < 2 ^ i ->
  0 <= Z.lor z1 z2 < 2 ^ i.
Proof.
  intros z1 z2 i Hi Hz1 Hz2.
  split.
  - apply Z.lor_nonneg. split; lia.
  - assert (z1 = 0 \/ 0 < z1) as [Hz1' | Hz1'] by lia.
    + subst. rewrite Z.lor_0_l. lia.
    + assert (z2 = 0 \/ 0 < z2) as [Hz2' |Hz2'] by lia.
      * subst. rewrite Z.lor_0_r. lia.
      * apply Z_testbit_false_le; try lia. apply Z.lor_nonneg. split; lia.
        intros j Hj. rewrite Z.lor_spec. 
        rewrite !Z.bits_above_log2; try lia; apply Z.log2_lt_pow2; try lia; eapply Z.lt_le_trans.
        apply (proj2 Hz2). apply Z.pow_le_mono_r; lia. apply (proj2 Hz1). apply Z.pow_le_mono_r; lia.
Qed.

Lemma nibbles_to_Z_bound: forall n1 n2,
  -1 < (nibbles_to_Z n1 n2) < Byte.modulus.
Proof.
  intros. unfold nibbles_to_Z.
  assert (0 <= Z.lor (Nibble.unsigned n1) (Z.shiftl (Nibble.unsigned n2) 4) < 2 ^ 8). {
    assert (Nibble.modulus = 16) by reflexivity.
    apply Z_lor_bound. lia. pose proof (Nibble.unsigned_range n1).
    assert (Nibble.modulus = 16) by reflexivity. lia.
    pose proof (Nibble.unsigned_range n2).
    split. apply Z.shiftl_nonneg. lia.
    rewrite Z.shiftl_mul_pow2 by lia. replace (2^8) with (2^4 * 2^4) by reflexivity.
    apply Zmult_lt_compat_r; lia. }
  replace (Byte.modulus) with 256 by reflexivity. lia.
Qed.

(*Utility lemmas: should move or something*)

(*Byte version in ByteFacts.v*)

(*NOTE: from VST.floyd.client_lemmas [unsigned_eq_eq] - but don't want to import all VST here*)
Lemma int_unsigned_inj: forall (i1 i2: int),
  Int.unsigned i1 = Int.unsigned i2 -> i1 = i2.
Proof.
  intros i1 i2 Hi.
  rewrite <- (Int.repr_unsigned i1), <- (Int.repr_unsigned i2).
  rewrite Hi. reflexivity.
Qed.

Lemma short_unsigned_inj: forall (i j: short), Short.unsigned i = Short.unsigned j -> i = j.
Proof.
  intros.
  rewrite <- (Short.repr_unsigned i), <- (Short.repr_unsigned j).
  rewrite H.
  reflexivity.
Qed.

(** Endianness *)
Section Endian.

(* We must convert between host and network byte order, thus we cannot assume the same endianness*)
Inductive Endian :=
  | BigEndian
  | LittleEndian.

Definition decode_int_endian (E: Endian) (l: list byte) : Z :=
  int_of_bytes (if E then rev l else l).

Definition encode_int_endian (E: Endian) (n: nat) (z: Z) : list byte :=
  let l := bytes_of_int n z in
  if E then rev l else l.

(* Since this machine is little-endian*)

Lemma decode_int_le: forall l,
  decode_int_endian LittleEndian l = decode_int l.
Proof.
  intros. reflexivity.
Qed. 

Lemma encode_int_le: forall n z,
  encode_int_endian LittleEndian n z = encode_int n z.
Proof.
  intros. reflexivity.
Qed.

(*Want to convert between endian values*)

(*Take n bytes of integer Z and reverse them*)
Definition reverse_endian_aux n (z : Z) : Z :=
  int_of_bytes (rev (bytes_of_int n z)).

Lemma byte_of_int_zero: forall n x,
  In x (bytes_of_int n 0)-> x = Byte.zero.
Proof.
  intros. induction n; simpl in *; destruct H; subst; auto.
Qed.

Lemma bytes_of_int_of_bytes: forall n l,
  (n = length l)%nat ->
  bytes_of_int n (int_of_bytes l) = l.
Proof.
  intros. revert n H. induction l; intros; simpl.
  - simpl in H. subst. reflexivity.
  - simpl in H. destruct n; simpl.
    + lia.
    + unfold Z.div. rewrite Zaux.Zdiv_eucl_unique, Z_div_plus by lia.
      rewrite Zdiv_small by rep_lia. rewrite Z.add_0_l.
      replace (Byte.repr (Byte.unsigned a + int_of_bytes l * 256)) with a.
      * rewrite IHl. reflexivity. lia.
      * apply byte_unsigned_inj. rewrite Byte.unsigned_repr_eq, Zplus_mod.
        rewrite (Zmod_small (Byte.unsigned a)) by rep_lia.
        rewrite Z_mod_mult,Z.add_0_r, <- Byte.unsigned_repr_eq, Byte.unsigned_repr; rep_lia.
Qed.

(*The most general lemma for reversing endianness*)
Lemma reverse_endian_aux_idem: forall n z,
  reverse_endian_aux n (reverse_endian_aux n z) = z mod two_p (Z.of_nat n * 8).
Proof.
  intros. unfold reverse_endian_aux.
  remember (bytes_of_int n z) as l.
  remember (int_of_bytes (rev l)) as j.
  assert (bytes_of_int n j = rev l). { rewrite Heqj, bytes_of_int_of_bytes.
    reflexivity. rewrite Heql. rewrite rev_length. rewrite length_bytes_of_int.
    reflexivity. }
  rewrite H. rewrite rev_involutive. rewrite Heql.
  apply int_of_bytes_of_int.
Qed.

(*If n is large enough, this is the identity*)
Lemma reverse_endian_aux_idem_id: forall n z,
  0 <= z < two_p (Z.of_nat n * 8) ->
  reverse_endian_aux n (reverse_endian_aux n z) = z.
Proof.
  intros. rewrite reverse_endian_aux_idem. rewrite Zmod_small by rep_lia. reflexivity.
Qed.

(*Versions specialized to shorts and ints - first we need bounds*)

Lemma reverse_endian_aux_bound: forall n z,
  0 <= reverse_endian_aux n z < two_p (Z.of_nat n * 8).
Proof.
  intros. unfold reverse_endian_aux. pose proof (int_of_bytes_range (rev (bytes_of_int n z))).
  rewrite rev_length in H. rewrite length_bytes_of_int in H. apply H.
Qed.

(* Reverse endianness of a machine-length int *)

Lemma reverse_endian_int_bound: forall z,
  -1 < reverse_endian_aux 4 z < Int.modulus.
Proof.
  intros. pose proof (reverse_endian_aux_bound 4 z). simpl in H.
  assert (two_power_pos 32 = Int.modulus) by reflexivity. lia.
Qed.

Definition reverse_endian_int (i: int) : int :=
  Int.mkint _ (reverse_endian_int_bound (Int.unsigned i)).



Lemma reverse_endian_int_idempotent: forall (i: int),
  reverse_endian_int (reverse_endian_int i) = i.
Proof.
  intros. apply int_unsigned_inj. unfold Int.unsigned at 1. simpl.
  apply reverse_endian_aux_idem_id. simpl. 
  replace (two_power_pos 32) with Int.modulus by reflexivity.
  apply Int.unsigned_range.
Qed.

(* Reverse endianness of a machine-length short *)

Lemma reverse_endian_short_bound: forall z,
  -1 < reverse_endian_aux 2 z < Short.modulus.
Proof.
  intros. pose proof (reverse_endian_aux_bound 2 z). simpl in H.
  assert (two_power_pos 16 = Short.modulus) by reflexivity. lia.
Qed.

Definition reverse_endian_short (s: short) : short :=
  Short.mkint _ (reverse_endian_short_bound (Short.unsigned s)).

Lemma reverse_endian_short_idempotent: forall (s: short),
  reverse_endian_short (reverse_endian_short s) = s.
Proof.
  intros. apply short_unsigned_inj. unfold Short.unsigned at 1. simpl.
  apply reverse_endian_aux_idem_id. simpl. 
  replace (two_power_pos 16) with Short.modulus by reflexivity.
  apply Short.unsigned_range.
Qed.

End Endian.

(** Convert primitive types to bytes *)
Section Convert.

Variable E: Endian.

Definition nibbles_to_byte (n1 n2: nibble) : byte :=
  Byte.mkint _ (nibbles_to_Z_bound n1 n2).

Definition short_to_bytes (s: short) : list byte :=
  encode_int_endian E 2 (Short.unsigned s).

Definition int_to_bytes (i: int) : list byte :=
  encode_int_endian E 4 (Int.unsigned i).

End Convert.

(** Represent data as bytes*)

(* This provides a shorthand to take machine-length types and represent as a list of bytes
  TODO; eventually this will be used to write short data_at representations*)

Export ListNotations.

Inductive MemBytes : Type :=
  | NibbleMem (n1: nibble) (n2: nibble)
  | ByteMem (b: byte)
  | ShortMem (s: short) (e: Endian) 
  | IntMem (i: int) (e: Endian).

Definition MemBytes_to_bytes (m: MemBytes) : list byte :=
  match m with
  | NibbleMem n1 n2 => [nibbles_to_byte n1 n2]
  | ByteMem b => [b]
  | ShortMem s e => short_to_bytes e s
  | IntMem i e => int_to_bytes e i
  end.

Definition MemBytes_to_byte_list (l: list MemBytes) : list byte :=
  List.flat_map MemBytes_to_bytes l.

(** Convert bytes to primitive types *)

(* Gives: lower 4 bits, higher 4 bits*)
Definition byte_to_nibbles (b: byte) : nibble * nibble :=
  (Nibble.repr (Z.land 15 (Byte.unsigned b)), Nibble.repr (Z.shiftr (Byte.unsigned b) 4)).

Lemma byte_simpl: forall (i: Z) (Hi: -1 < i < Byte.modulus),
  Byte.intval {| Byte.intval := i; Byte.intrange := Hi |} = i.
Proof.
  intros. reflexivity.
Qed.

(*This is much harder to prove than it seems
  TODO: is there an easier way?*)
Lemma byte_to_nibbles_inv: forall b,
  let (n1, n2) := byte_to_nibbles b in
  nibbles_to_byte n1 n2 = b.
Proof.
  intros b. unfold byte_to_nibbles. unfold nibbles_to_byte. apply byte_unsigned_inj.
  rewrite byte_simpl. unfold nibbles_to_Z.
  rewrite !Nibble.unsigned_repr.
  - apply Z.bits_inj_iff. unfold Z.eqf. intros n.
    assert (H15n: (Z.testbit 15 n = true) <-> 0 <= n < 4). {
      split; intros.
      - assert (0 <= n < 4 \/ n < 0 \/ n >= 4) as [Hin |[ Hlo | Hhi]] by lia.
        + lia.
        + rewrite Z.testbit_neg_r in H by lia. inversion H.
        + rewrite Z.bits_above_log2 in H; try lia. 
          replace (Z.log2 15) with 3 by reflexivity. lia.
      - assert (n= 0 \/ n = 1 \/ n = 2 \/ n = 3) as [H1 | [H2 | [H3 | H4]]] by lia; subst; reflexivity. } 
    rewrite Z.lor_spec,Z.land_spec.
    assert (n < 0 \/ 0 <= n < 4 \/ 4 <= n) as [Hout |[Hfst | Hsnd]] by lia.
    + assert (Z.testbit 15 n = false). { destruct (Z.testbit 15 n) eqn : Ht; auto. lia. }
      rewrite H,andb_false_l,orb_false_l.
      rewrite !Z.testbit_neg_r; lia.
    + rewrite Z.shiftl_spec by lia.
      replace (Z.testbit 15 n) with true. 2 : { symmetry; apply H15n; lia. }
      simpl.
      assert (Z.testbit (Z.shiftr (Byte.unsigned b) 4) (n - 4) = false). {
        rewrite Z.testbit_neg_r; auto. lia. } rewrite H. rewrite orb_false_r. reflexivity.
    + assert (Z.testbit 15 n = false). { destruct (Z.testbit 15 n) eqn : Ht; auto. lia. }
      rewrite H,andb_false_l,orb_false_l.
      rewrite Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia.
      f_equal. lia.
  - split.
    + apply Z.shiftr_nonneg. pose proof (Byte.unsigned_range b); lia.
    + rewrite Z.shiftr_div_pow2 by lia. replace (Nibble.max_unsigned) with 15 by reflexivity.
      pose proof (Byte.unsigned_range b). replace (Byte.modulus) with 256 in H by reflexivity.
      eapply Z.le_trans. apply Z.div_le_mono. lia. assert (Byte.unsigned b <= 255) by lia. apply H0.
      replace (2^4) with 16 by reflexivity. 
      replace (255 /16) with 15 by reflexivity. lia.
  - split. 
    + rewrite Z.land_nonneg. left. lia.
    + replace (Nibble.max_unsigned) with 15 by reflexivity. apply Zbits.Ztestbit_le. lia.
      intros i Hi. rewrite Z.land_spec, andb_true_iff. intros [Hi1 Hi2].
      apply Hi1.
Qed.
