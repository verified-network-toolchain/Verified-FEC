Require Import Endian.
Require Import VST.floyd.functional_base.
From RecordUpdate Require Import RecordSet. (*for updating records easily*)
Import RecordSetNotations.
Set Bullet Behavior "Strict Subproofs".

(** IP and UDP Packets *)

(** IP *)

(*TODO: I believe that everything > 1 byte is in network byte order. Can I find a source for this?
  It is very poorly documented*)

Record ip_fields :=
  mk_ip { ip_hl : nibble; ip_v : nibble; ip_tos : byte; ip_len : short; ip_id : short; ip_off : short;
    ip_ttl: byte; ip_p: byte; ip_sum : short; ip_src : int; ip_dst: int; ip_options: list byte}.

#[export]Instance eta_ip_fields: Settable _ := 
  settable! mk_ip <ip_hl; ip_v; ip_tos; ip_len; ip_id; ip_off; ip_ttl; ip_p; ip_sum; ip_src; ip_dst; ip_options>.

Definition ip_list (f: ip_fields) :=
  let e:= BigEndian in
  [NibbleMem (ip_hl f) (ip_v f); ByteMem (ip_tos f); ShortMem (ip_len f) e; ShortMem (ip_id f) e;
    ShortMem (ip_off f) e; ByteMem (ip_ttl f); ByteMem (ip_p f); ShortMem (ip_sum f) e;
    IntMem (ip_src f) e; IntMem (ip_dst f) e].

Definition ip_bytes (f: ip_fields) :=
  MemBytes_to_byte_list (ip_list f) ++ (ip_options f).

(*TODO: do we need any other validity conditions?*)
Definition valid_ip_bytes (f: ip_fields) (contents: list byte) : bool :=
  Z.eq_dec (Nibble.unsigned (ip_hl f) * 4) (Zlength (ip_bytes f)) &&
  Z.eq_dec (Short.unsigned (ip_len f)) (Zlength (ip_bytes f ++ contents)).

(*Fixed parts of IP packet take up 20 bytes*) 

(*Suppose we are given the header along with the packet contents. We want to reconstruct the fields and
  define a validity predicate*)

(*Get header fields from a list of bytes representing the header*)
Definition bytes_to_ip_header (header: list byte) : option (ip_fields) :=
  match header with
  | ip_hlv :: ip_tos :: ip_len1 :: ip_len2 :: ip_id1 :: ip_id2 :: ip_off1 :: ip_off2 ::
    ip_tll :: ip_p :: ip_sum1 :: ip_sum2 :: ip_src1 :: ip_src2 :: ip_src3 :: ip_src4 ::
    ip_dst1 :: ip_dst2 :: ip_dst3 :: ip_dst4 :: rest =>
      let E := BigEndian in
      let (ip_hl, ip_v) := byte_to_nibbles ip_hlv in
        Some (mk_ip ip_hl ip_v ip_tos (bytes_to_short E ip_len1 ip_len2) (bytes_to_short E ip_id1 ip_id2)
        (bytes_to_short E ip_off1 ip_off2) ip_tll ip_p (bytes_to_short E ip_sum1 ip_sum2)
        (bytes_to_int E ip_src1 ip_src2 ip_src3 ip_src4)
        (bytes_to_int E ip_dst1 ip_dst2 ip_dst3 ip_dst4) rest)
  | _ => None
  end.

Definition packet_to_ip_fields (packet: list byte) : option (ip_fields * list byte) :=
  match (bytes_to_ip_header packet) with
  | Some i => 
    let realOptions := sublist 20 (4 * Nibble.unsigned (ip_hl i)) packet in
    let contents := sublist (4 * Nibble.unsigned (ip_hl i)) (Short.unsigned (ip_len i)) packet in
    Some (i <| ip_options := realOptions |>, contents)
  | None => None
  end.

(*Given the header and contents, we want to define a validity predicate*)
Definition valid_ip_packet (header: list byte) (contents: list byte) : bool :=
  match (bytes_to_ip_header header) with
  | Some i => Z.eq_dec (4 * Nibble.unsigned (ip_hl i)) (Zlength header) &&  
              Z.eq_dec (Short.unsigned (ip_len i)) (Zlength (header ++ contents))
  | None => false
  end.

(*Get header and contents from a packet*)
Definition recover_ip_packet (pack: list byte) : (list byte * list byte) :=
  match (packet_to_ip_fields pack) with
  | None => (nil, nil)
  | Some (i, con) => (ip_bytes i, con)
  end.

(*Now, we need to prove the correctness, in the following way: suppose we have a valid
  header and packet contents. Then, if we have header ++ contents ++ extra bytes, we can
  recover the original header and contents. For IP packets, this is challenging because
  of the variable sized header. We need some intermediate lemmas first*)

(*Reason about ip_fields without options*)
Definition ip_wo_options (i: ip_fields) : ip_fields :=
  i <| ip_options := nil |>.

Lemma ip_wo_options_eq_spec: forall (i1 i2: ip_fields),
  ip_wo_options i1 = ip_wo_options i2 ->
  ip_options i1 = ip_options i2 ->
  i1 = i2.
Proof.
  intros i1 i2. unfold ip_wo_options. intros Hwo Hopt.
  destruct i1; destruct i2. simpl in *.
  inversion Hwo; subst. reflexivity.
Qed.

(*Solve goals with false=true -> H, False -> H, or _ :: _ = nil -> H*)
Ltac solve_con:=
  solve[ let H := fresh in
  intros H; inversion H].

(*Unfolding these is not needed and blows up terms*)
Opaque bytes_to_short.
Opaque bytes_to_int.
Opaque byte_to_nibbles.

(*A key point: the IP header is the same if we extend the packet except for possibly the options*)
Lemma bytes_to_header_ext: forall header ip l,
  bytes_to_ip_header header = Some ip ->
  bytes_to_ip_header (header ++ l) = Some (ip <| ip_options := sublist 20 (Zlength (header ++ l)) (header ++ l) |>).
Proof.
  intros header ip l. unfold bytes_to_ip_header. do 20 (destruct header; [solve_con |]). intros Heq. simpl.
  destruct (byte_to_nibbles i) as [iphl ipv] eqn : Hi. inversion Heq; subst; clear Heq. f_equal.
  apply ip_wo_options_eq_spec.
  - reflexivity.
  - simpl. list_solve.
Qed.

Opaque nibbles_to_byte.
Opaque short_to_bytes.
Opaque int_to_bytes.

(*Second important lemma: 
 Here, we need the lemmas about (ex) [bytes_to_int] and [int_to_bytes] proved in Endian.v*)
Lemma bytes_to_ip_header_bytes: forall header ip,
  bytes_to_ip_header header = Some ip <-> ip_bytes ip = header.
Proof.
  intros header ip. unfold ip_bytes. simpl. rewrite app_nil_r.
  unfold bytes_to_ip_header; split.
  - do 20 (destruct header; [solve_con |]). 
    destruct (byte_to_nibbles i) as [iphl ipv] eqn : Hi. intro Hip; inversion Hip; subst; clear Hip; simpl.
    f_equal. pose proof (byte_to_nibbles_inv i). rewrite Hi in H. assumption.
    f_equal.
    rewrite !bytes_to_short_inv, !bytes_to_int_inv. reflexivity.
  - intros Hhead. rewrite <- Hhead; clear Hhead. destruct ip; simpl.
    (*simplify all the [short_to_bytes] and [int_to_byte]*)
    repeat match goal with
    | [ |- context [short_to_bytes ?e ?x ]] => 
      let H := fresh in
      let l := fresh in
      pose proof (short_to_bytes_inv e x) as H;
      remember (short_to_bytes e x) as l;
      repeat (let i := fresh "i" in destruct l as [|i l]; try(solve[inversion H]))
    | [ |- context [ int_to_bytes ?e ?x ]] =>
      let H := fresh in
      let l := fresh in
      pose proof (int_to_bytes_inv e x) as H;
      remember (int_to_bytes e x) as l;
      repeat (let i := fresh "i" in destruct l as [|i l]; try(solve[inversion H]))
    end.
    simpl. rewrite nibbles_to_byte_inv. f_equal. congruence.
Qed.

(*Other smaller lemmas*)
Lemma ip_header_length: forall header ip,
  bytes_to_ip_header header = Some ip ->
  Zlength header >= 20.
Proof.
  intros header ip. unfold bytes_to_ip_header. do 20 (destruct header; [solve_con |]). list_solve.
Qed.

(*Then, we can get the options list in the following way:*)
Lemma ip_options_sublist: forall header ip,
  bytes_to_ip_header header = Some ip ->
  ip_options ip = sublist 20 (Zlength header) header.
Proof.
  intros header ip. unfold bytes_to_ip_header.
  do 20 (destruct header; [solve_con |]). intros.
  replace (ip_options ip) with header by (inversion H; reflexivity). list_solve.
Qed.

(*TODO: move, may be useful more generally*)
Ltac simpl_sumbool :=
  repeat match goal with
  | [ H: proj_sumbool ?x = true |- _ ] => destruct x; [ clear H | solve[inversion H]]
  | [ H: proj_sumbool ?x = false |- _] => destruct x; [solve[inversion H]|clear H]
  end.

(*Correctness theorem*)
Lemma recover_ip_packet_correct: forall (header contents extra: list byte),
  valid_ip_packet header contents = true ->
  recover_ip_packet (header ++ contents ++ extra) = (header, contents).
Proof.
  intros ? ? ?. unfold valid_ip_packet. destruct (bytes_to_ip_header header) as [ip |] eqn : Hhead.
  2 : intro C; inversion C.
  intros Hlens. apply andb_prop in Hlens. destruct Hlens as [Hlen1 Hlen2].
  simpl_sumbool.
  unfold recover_ip_packet. unfold packet_to_ip_fields.
  pose proof (bytes_to_header_ext _ _ (contents ++ extra) Hhead) as Happ.
  remember (ip <| ip_options :=
          sublist 20 (Zlength (header ++ contents ++ extra)) (header ++ contents ++ extra) |>) as ip' eqn : Heq.
  rewrite Happ.
  assert (Hhleq: ip_hl ip = ip_hl ip') by
       (destruct ip; destruct ip'; subst; inversion Heq; reflexivity).
 f_equal.
  - rewrite <- bytes_to_ip_header_bytes. rewrite Hhead. f_equal.
    apply ip_wo_options_eq_spec.
    + rewrite Heq. reflexivity.
    + rewrite <- Hhleq, e0. simpl. rewrite sublist_app1; try lia.
      apply ip_options_sublist. assumption. apply ip_header_length in Hhead; list_solve.
  - assert (Hleneq: ip_len ip = ip_len ip') by  (destruct ip; destruct ip'; inversion Heq; reflexivity).
    rewrite <- Hhleq, e0, <- Hleneq, e. list_solve.
Qed. 

(** UDP Packets *)

Record udp_fields :=
  mk_udp { udp_source: short; udp_dest: short; udp_len: short; udp_check: short }.

#[export]Instance eta_udp_fields: Settable _ := 
  settable! mk_udp <udp_source; udp_dest; udp_len; udp_check>.

Definition udp_list (u: udp_fields) :=
  let e:= BigEndian in
  [ShortMem (udp_source u) e; ShortMem (udp_dest u) e; ShortMem (udp_len u) e; ShortMem (udp_check u) e].

Definition udp_bytes (u: udp_fields) :=
  MemBytes_to_byte_list (udp_list u).

(*TODO: any other validity conditions?*)
Definition valid_udp_bytes (u: udp_fields) (contents: list byte) : bool :=
  Z.eq_dec (Short.unsigned (udp_len u)) (Zlength (udp_bytes u ++ contents)).

(*UDP packets are easier - header is fixed size of 8 bytes*)

Definition bytes_to_udp_header (header: list byte) : option udp_fields :=
  match header with
  | src1 :: src2 :: dst1 :: dst2 :: len1 :: len2 :: check1 :: check2 :: nil =>
    let E := BigEndian in
    Some (mk_udp (bytes_to_short E src1 src2) (bytes_to_short E dst1 dst2) (bytes_to_short E len1 len2)
      (bytes_to_short E check1 check2))
  | _ => None
  end.

Definition packet_to_udp_fields (packet: list byte) : option (udp_fields * list byte) :=
  match (bytes_to_udp_header (sublist 0 8 packet)) with
  | Some u => 
    let contents := sublist 8 (Short.unsigned (udp_len u)) packet in 
    Some(u, contents)
  | None => None
  end.

(*Given the header and contents, we want to define a validity predicate*)
Definition valid_udp_packet (header: list byte) (contents: list byte) : bool :=
  match (bytes_to_udp_header header) with
  | Some u => Z.eq_dec (Short.unsigned (udp_len u)) (Zlength (header ++ contents))
  | None => false
  end.

(*Get header and contents from a packet*)
Definition recover_udp_packet (pack: list byte) : (list byte * list byte) :=
  match (packet_to_udp_fields pack) with
  | None => (nil, nil)
  | Some (u, con) => (udp_bytes u, con)
  end.

(*The correctness theorem is much, much easier this time because of the fixed header size*)
Lemma recover_udp_packet_correct: forall (header contents extra: list byte),
  valid_udp_packet header contents = true ->
  recover_udp_packet (header ++ contents ++ extra) = (header, contents).
Proof.
  intros ? ? ?. unfold valid_udp_packet, recover_udp_packet, bytes_to_udp_header.
  do 8 (destruct header; [solve_con|]). destruct header; [|solve_con]. simpl. intro Hlen.
  simpl_sumbool. 
  replace (Zlength (i :: i0 :: i1 :: i2 :: i3 :: i4 :: i5 :: i6 :: contents)) with
  (8 + Zlength contents) in e by list_solve. rewrite e.
  f_equal.
  - unfold udp_bytes. simpl. rewrite !bytes_to_short_inv. reflexivity.
  - rewrite !sublist_S_cons by lia.
    rewrite sublist0_app1 by list_solve.
    rewrite sublist_same by lia. reflexivity.
Qed.


(** IP/UDP Packets *)

(*An IP/UDP packet has an IP header, followed by a UDP header. We compose the above to get
  the final functions and predicates we need*)

Definition valid_packet (header: list byte) (contents: list byte) : bool :=
  Z_le_lt_dec 8 (Zlength header) && 
  let ip_header := sublist 0 (Zlength header - 8) header in
  let udp_header := sublist (Zlength header - 8) (Zlength header) header in
  valid_ip_packet ip_header (udp_header ++ contents) &&
  valid_udp_packet udp_header contents.

Definition recover_packet (pack: list byte) : (list byte * list byte) :=
  let (ip_head, rest) := recover_ip_packet pack in
  let (udp_head, contents) := recover_udp_packet rest in
  (ip_head ++ udp_head, contents).

(*Now, the main theorem we need:*)
Theorem recover_packet_correct: forall (header contents extra: list byte),
  valid_packet header contents = true ->
  recover_packet (header ++ contents ++ extra) = (header, contents).
Proof.
  intros ? ? ?. unfold valid_packet, recover_packet. intros Hvalid.
  apply andb_prop in Hvalid. destruct Hvalid as [Hlen Hvalid].
  apply andb_prop in Hvalid. destruct Hvalid as [Hip Hudp].
  destruct (Z_le_lt_dec 8 (Zlength header)); try solve[inversion Hlen]. clear Hlen.
  rewrite  <- (sublist_same 0 (Zlength header) header) by reflexivity.
  rewrite (sublist_split 0 (Zlength header - 8) (Zlength header)); try lia.
  rewrite <- app_assoc, (app_assoc _ contents), recover_ip_packet_correct by assumption.
  rewrite <- (app_nil_r (_ ++ contents)), <- app_assoc, recover_udp_packet_correct; auto.
Qed.

(*Separately, we want to take a valid packet and modify the contents, changing the appropriate
  header fields to ensure that the resulting packet is still well-formed*)

Definition copy_fix_header (header: list byte) (contents : list byte) : list byte :=
  match (bytes_to_ip_header (sublist 0 (Zlength header - 8) header)), 
    (bytes_to_udp_header (sublist (Zlength header - 8) (Zlength header) header))  with
  | Some i, Some u => 
    let new_ip_len := Zlength (ip_bytes i ++ udp_bytes u ++ contents) in
    let new_udp_len := Zlength (udp_bytes u ++ contents) in
    ip_bytes (i <| ip_len := Short.repr new_ip_len |>) ++ udp_bytes (u <| udp_len := Short.repr new_udp_len |>) 
  | _, _ => nil
  end.

Lemma ip_bytes_Zlength: forall (i: ip_fields),
  Zlength (ip_bytes i) = 20 + Zlength (ip_options i).
Proof.
  intros i. destruct i. unfold ip_bytes. list_solve.
Qed. 

(*An easy corollary*)
Lemma ip_bytes_len_eq: forall (i1 i2: ip_fields),
  Zlength (ip_options i1) = Zlength (ip_options i2) ->
  Zlength (ip_bytes i1) = Zlength (ip_bytes i2).
Proof.
  intros i1 i2 Hi. rewrite !ip_bytes_Zlength. lia.
Qed.

(*It helps to have this for UDP too*)
Lemma bytes_to_udp_header_bytes: forall header u,
  bytes_to_udp_header header = Some u <-> udp_bytes u = header.
Proof.
  intros header u. unfold udp_bytes. simpl. rewrite app_nil_r.
  unfold bytes_to_udp_header; split.
  - do 8 (destruct header; [solve_con |]). destruct header; [|solve_con].
    intros Hu. inversion Hu; subst; clear Hu. simpl.
    rewrite !bytes_to_short_inv. reflexivity.
  - intros Hhead. rewrite <- Hhead; clear Hhead. destruct u; simpl.
    (*simplify all the [short_to_bytes] and [int_to_byte]*)
    repeat match goal with
    | [ |- context [short_to_bytes ?e ?x ]] => 
      let H := fresh in
      let l := fresh in
      pose proof (short_to_bytes_inv e x) as H;
      remember (short_to_bytes e x) as l;
      repeat (let i := fresh "i" in destruct l as [|i l]; try(solve[inversion H]))
    end.
    simpl. f_equal. congruence.
Qed.

(*TODO: where to put the boundedness assumptions?*)
Lemma copy_fix_header_valid: forall (header con1 con2: list byte),
  Zlength header + Zlength con2 <= Short.max_unsigned ->
  valid_packet header con1 = true ->
  valid_packet (copy_fix_header header con2) con2 = true.
Proof.
  intros h c1 c2 Hlenb. unfold valid_packet. intros Hvalid.
  apply andb_prop in Hvalid. destruct Hvalid as [Hlen Hvalid].
  apply andb_prop in Hvalid. destruct Hvalid as [Hip Hudp].
  destruct (Z_le_lt_dec 8 (Zlength h)); try solve[inversion Hlen]. clear Hlen.
  unfold valid_ip_packet in Hip.
  unfold valid_udp_packet in Hudp.
  repeat match goal with | [ H: (match ?x with | Some o => ?z | None => ?y end) = ?b |- _ ] => let H1 := fresh in
    destruct x eqn : H1; try solve[inversion H]
  end.
  assert (Hi': Zlength (ip_bytes (i <| ip_len := Short.repr (Zlength (ip_bytes i ++ udp_bytes u ++ c2)) |>)) 
    = Zlength (ip_bytes i)). { apply ip_bytes_len_eq. reflexivity. }
  assert (Hilen: Zlength (ip_bytes i) = Zlength h - 8). { rewrite bytes_to_ip_header_bytes in H0.
    rewrite H0. list_solve. }
  assert (Hu': Zlength (udp_bytes (u <| udp_len := Short.repr (Zlength (udp_bytes u ++ c2)) |>)) = 8). {
    destruct u; reflexivity. }
  assert (Hlen: Zlength (copy_fix_header h c2) = Zlength h). {
    unfold copy_fix_header. rewrite H, H0, Zlength_app, Hi', Hilen, Hu'. lia. }
  rewrite Hlen. clear Hlen.
  unfold copy_fix_header. rewrite H, H0. apply andb_true_intro. split.
    destruct (Z_le_lt_dec 8 (Zlength h)); auto; lia.
  apply andb_true_intro. split.
  - rewrite sublist_app1 by list_solve.
    rewrite sublist_app2 by list_solve. rewrite Hi',Hilen.
    rewrite !sublist_same by list_solve.
    unfold valid_ip_packet.
    assert (Hsome:  bytes_to_ip_header
    (ip_bytes (i <| ip_len := Short.repr (Zlength (ip_bytes i ++ udp_bytes u ++ c2)) |>)) = Some
      (i <| ip_len := Short.repr (Zlength (ip_bytes i ++ udp_bytes u ++ c2)) |>)). {
      rewrite bytes_to_ip_header_bytes. reflexivity. }
    rewrite Hsome. rewrite (Zlength_app _ (ip_bytes (i <| ip_len := _ |>))), Hi', 
      (Zlength_app _ (udp_bytes _)), Hu', Hilen.
    apply andb_true_intro. split.
    + apply andb_prop in Hip. destruct Hip as [Hhl _]. simpl_sumbool.
      replace (ip_hl (i <| ip_len := Short.repr (Zlength (ip_bytes i ++ udp_bytes u ++ c2)) |>)) with
        (ip_hl i) by reflexivity. rewrite e0, Zlength_sublist by lia. apply proj_sumbool_is_true. lia.
    + rewrite !Zlength_app, Hilen. replace (Zlength (udp_bytes u)) with 8 by (destruct u; reflexivity).
      replace (Zlength h - 8 + (8 + Zlength c2)) with (Zlength h + Zlength c2) by lia.
      simpl ip_len. rewrite Short.unsigned_repr by list_solve. apply proj_sumbool_is_true. reflexivity.
  - (*UDP packet is easier*)
    rewrite sublist_app2 by list_solve.
    rewrite Hi', Hilen,sublist_same by lia.
    unfold valid_udp_packet.
    assert (Hsome: bytes_to_udp_header (udp_bytes (u <| udp_len := Short.repr (Zlength (udp_bytes u ++ c2)) |>)) =
      Some (u <| udp_len := Short.repr (Zlength (udp_bytes u ++ c2)) |>)). {
      rewrite bytes_to_udp_header_bytes. reflexivity. } rewrite Hsome. clear Hsome.
    rewrite (Zlength_app _ (udp_bytes (u <| udp_len := _ |>))), Hu', !Zlength_app.
    replace (Zlength (udp_bytes u)) with 8 by (destruct u; reflexivity).
    remember (8 + Zlength c2) as m. simpl udp_len. rewrite Short.unsigned_repr.
    apply proj_sumbool_is_true. reflexivity. subst; list_solve.
Qed.