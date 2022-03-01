Require Import Endian.
Require Import VST.floyd.functional_base.

(** IP and UDP Packets *)

(** IP *)

(*TODO: I believe that everything > 1 byte is in network byte order. Can I find a source for this?
  It is very poorly documented*)

Record ip_fields :=
  mk_ip { ip_hl : nibble; ip_v : nibble; ip_tos : byte; ip_len : short; ip_id : short; ip_off : short;
    ip_ttl: byte; ip_p: byte; ip_sum : short; ip_src : int; ip_dst: int; ip_options: list byte}.

Definition ip_list (f: ip_fields) :=
  let e:= BigEndian in
  [NibbleMem (ip_hl f) (ip_v f); ByteMem (ip_tos f); ShortMem (ip_len f) e; ShortMem (ip_id f) e;
    ShortMem (ip_off f) e; ByteMem (ip_ttl f); ByteMem (ip_p f); ShortMem (ip_sum f) e;
    IntMem (ip_src f) e; IntMem (ip_dst f) e].

Definition ip_bytes (f: ip_fields) :=
  MemBytes_to_byte_list (ip_list f) ++ (ip_options f).

(*TODO: do we need any other validity conditions?*)
Definition valid_ip_bytes (f: ip_fields) (contents: list byte) : Prop :=
  Nibble.unsigned (ip_hl f) * 4 = Zlength (ip_bytes f) /\
  Short.unsigned (ip_len f) = Zlength (ip_bytes f ++ contents).

(* Now we need to go to the other way: header bytes -> ip_fields*)
(*TODO:*)
Definition packet_to_ip_fields (packet: list byte) : option ip_fields :=
  match packet with
  | ip_hlv :: ip_tos :: ip_len1 :: ip_len2 :: ip_id1 :: ip_id2 :: ip_off1 :: ip_off2 ::
    ip_tll :: ip_p :: ip_sum1 :: ip_sum2 :: ip_src1 :: ip_src2 :: ip_src3 :: ip_src4 ::
    ip_dst1 :: ip_dst2 :: ip_dst3 :: id_dst4 :: rest =>
      mk_ip 



  | _ => None
    
  | _ => None
  end.
  | nil => None
  | 




Definition valid_ip_bytes (f: ip_fields) (options: list byte) (contents: list byte) : Prop :=
  Nibble.unsigned (ip_hl f) * 4 = Zlength (ip_bytes f options) /\
  Short.unsigned (ip_len f) = Zlength (ip_bytes f options ++ contents).

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

