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
Definition bytes_to_header_fields (header: list byte) : option (ip_fields) :=
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
  match (bytes_to_header_fields packet) with
  | Some i => 
    let realOptions := sublist 20 (4 * Nibble.unsigned (ip_hl i)) packet in
    let contents := sublist (4 * Nibble.unsigned (ip_hl i)) (Short.unsigned (ip_len i)) packet in
    Some (i <| ip_options := realOptions |>, contents)
  | None => None
  end.

(*Given the header and contents, we want to define a validity predicate*)
Definition valid_packet (header: list byte) (contents: list byte) : bool :=
  match (bytes_to_header_fields header) with
  | Some i => Z.eq_dec (4 * Nibble.unsigned (ip_hl i)) (Zlength header) &&  
              Z.eq_dec (Short.unsigned (ip_len i)) (Zlength (header ++ contents))
  | None => false
  end.

(*Get header and contents from a packet*)
Definition recover_packet (pack: list byte) : (list byte * list byte) :=
  match (packet_to_ip_fields pack) with
  | None => (nil, nil)
  | Some (i, con) => (ip_bytes i, con)
  end.

Ltac solve_con:=
  solve[ let H := fresh in
  intros H; inversion H].

(*The main theorem we need*)

(*KEY! what we want: bytes_to_header_fields header = Some ip <-> ip_bytes ip = header
(maybe, not as sure although this may help me prove the next lemma)

  WANT: bytes_to_header_fields header = Some ip ->
  bytes_to_header_fields header ++ l = Some ip' ->
  (forall fields other than contents, ip.f = ip'.f)

then we reason as follows (to show that recover_packet gives (header, contents)
  want to show that ip_bytes ip' = header - USE ABOVE LEMMA and equality from above
  and then contents, reason about sublist and length

THESE TWO LEMMAS ARE WHAT WE NEED

Lemma recover_packet_correct: forall (header contents : list byte) (extra: list byte),
  valid_packet header contents = true ->
  recover_packet (header ++ contents ++ extra) = (header, contents).
Proof.
*)

(** UDP *)

Record udp_fields :=
  mk_udp { source: short; dest: short; len: short; check: short }.

Definition udp_list (u: udp_fields) :=
  let e:= BigEndian in
  [ShortMem (source u) e; ShortMem (dest u) e; ShortMem (len u) e; ShortMem (check u) e].

Definition udp_bytes (u: udp_fields) :=
  MemBytes_to_byte_list (udp_list u).

(*TODO: any other validity conditions?*)
Definition valid_udp_bytes (u: udp_fields) (contents: list byte) :=
  Short.unsigned (len u) = Zlength (udp_bytes u ++ contents).

(** IP/UDP Packets*)

Definition ip_udp_bytes (i: ip_fields) (ip_options: list byte) (u: udp_fields) (data: list byte) : list byte :=
  ip_bytes i ip_options ++ udp_bytes u ++ data.

Definition valid_ip_udp_bytes (i: ip_fields) (ip_options: list byte) (u: udp_fields) (data: list byte) : Prop :=
  valid_ip_bytes i ip_options (udp_bytes u ++ data) /\
  valid_udp_bytes u data.

