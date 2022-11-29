From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.10".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "fecCommon.c".
  Definition normalized := true.
End Info.

Definition _RETURN : ident := $"RETURN".
Definition __2163 : ident := $"_2163".
Definition __2164 : ident := $"_2164".
Definition __2165 : ident := $"_2165".
Definition __IO_FILE : ident := $"_IO_FILE".
Definition __IO_backup_base : ident := $"_IO_backup_base".
Definition __IO_buf_base : ident := $"_IO_buf_base".
Definition __IO_buf_end : ident := $"_IO_buf_end".
Definition __IO_codecvt : ident := $"_IO_codecvt".
Definition __IO_marker : ident := $"_IO_marker".
Definition __IO_read_base : ident := $"_IO_read_base".
Definition __IO_read_end : ident := $"_IO_read_end".
Definition __IO_read_ptr : ident := $"_IO_read_ptr".
Definition __IO_save_base : ident := $"_IO_save_base".
Definition __IO_save_end : ident := $"_IO_save_end".
Definition __IO_wide_data : ident := $"_IO_wide_data".
Definition __IO_write_base : ident := $"_IO_write_base".
Definition __IO_write_end : ident := $"_IO_write_end".
Definition __IO_write_ptr : ident := $"_IO_write_ptr".
Definition ___assert_fail : ident := $"__assert_fail".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___func__ : ident := $"__func__".
Definition ___func____1 : ident := $"__func____1".
Definition ___func____2 : ident := $"__func____2".
Definition ___func____3 : ident := $"__func____3".
Definition ___func____4 : ident := $"__func____4".
Definition ___func____5 : ident := $"__func____5".
Definition ___pad5 : ident := $"__pad5".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_10 : ident := $"__stringlit_10".
Definition ___stringlit_11 : ident := $"__stringlit_11".
Definition ___stringlit_12 : ident := $"__stringlit_12".
Definition ___stringlit_13 : ident := $"__stringlit_13".
Definition ___stringlit_14 : ident := $"__stringlit_14".
Definition ___stringlit_15 : ident := $"__stringlit_15".
Definition ___stringlit_16 : ident := $"__stringlit_16".
Definition ___stringlit_17 : ident := $"__stringlit_17".
Definition ___stringlit_18 : ident := $"__stringlit_18".
Definition ___stringlit_19 : ident := $"__stringlit_19".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_20 : ident := $"__stringlit_20".
Definition ___stringlit_21 : ident := $"__stringlit_21".
Definition ___stringlit_22 : ident := $"__stringlit_22".
Definition ___stringlit_23 : ident := $"__stringlit_23".
Definition ___stringlit_24 : ident := $"__stringlit_24".
Definition ___stringlit_25 : ident := $"__stringlit_25".
Definition ___stringlit_26 : ident := $"__stringlit_26".
Definition ___stringlit_27 : ident := $"__stringlit_27".
Definition ___stringlit_28 : ident := $"__stringlit_28".
Definition ___stringlit_29 : ident := $"__stringlit_29".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_30 : ident := $"__stringlit_30".
Definition ___stringlit_31 : ident := $"__stringlit_31".
Definition ___stringlit_32 : ident := $"__stringlit_32".
Definition ___stringlit_33 : ident := $"__stringlit_33".
Definition ___stringlit_34 : ident := $"__stringlit_34".
Definition ___stringlit_35 : ident := $"__stringlit_35".
Definition ___stringlit_36 : ident := $"__stringlit_36".
Definition ___stringlit_37 : ident := $"__stringlit_37".
Definition ___stringlit_38 : ident := $"__stringlit_38".
Definition ___stringlit_39 : ident := $"__stringlit_39".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_40 : ident := $"__stringlit_40".
Definition ___stringlit_41 : ident := $"__stringlit_41".
Definition ___stringlit_42 : ident := $"__stringlit_42".
Definition ___stringlit_43 : ident := $"__stringlit_43".
Definition ___stringlit_44 : ident := $"__stringlit_44".
Definition ___stringlit_45 : ident := $"__stringlit_45".
Definition ___stringlit_46 : ident := $"__stringlit_46".
Definition ___stringlit_47 : ident := $"__stringlit_47".
Definition ___stringlit_48 : ident := $"__stringlit_48".
Definition ___stringlit_49 : ident := $"__stringlit_49".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_50 : ident := $"__stringlit_50".
Definition ___stringlit_51 : ident := $"__stringlit_51".
Definition ___stringlit_52 : ident := $"__stringlit_52".
Definition ___stringlit_53 : ident := $"__stringlit_53".
Definition ___stringlit_54 : ident := $"__stringlit_54".
Definition ___stringlit_55 : ident := $"__stringlit_55".
Definition ___stringlit_56 : ident := $"__stringlit_56".
Definition ___stringlit_57 : ident := $"__stringlit_57".
Definition ___stringlit_58 : ident := $"__stringlit_58".
Definition ___stringlit_59 : ident := $"__stringlit_59".
Definition ___stringlit_6 : ident := $"__stringlit_6".
Definition ___stringlit_60 : ident := $"__stringlit_60".
Definition ___stringlit_61 : ident := $"__stringlit_61".
Definition ___stringlit_62 : ident := $"__stringlit_62".
Definition ___stringlit_63 : ident := $"__stringlit_63".
Definition ___stringlit_64 : ident := $"__stringlit_64".
Definition ___stringlit_65 : ident := $"__stringlit_65".
Definition ___stringlit_66 : ident := $"__stringlit_66".
Definition ___stringlit_7 : ident := $"__stringlit_7".
Definition ___stringlit_8 : ident := $"__stringlit_8".
Definition ___stringlit_9 : ident := $"__stringlit_9".
Definition __chain : ident := $"_chain".
Definition __codecvt : ident := $"_codecvt".
Definition __cur_column : ident := $"_cur_column".
Definition __fileno : ident := $"_fileno".
Definition __flags : ident := $"_flags".
Definition __flags2 : ident := $"_flags2".
Definition __freeres_buf : ident := $"_freeres_buf".
Definition __freeres_list : ident := $"_freeres_list".
Definition __lock : ident := $"_lock".
Definition __markers : ident := $"_markers".
Definition __mode : ident := $"_mode".
Definition __offset : ident := $"_offset".
Definition __old_offset : ident := $"_old_offset".
Definition __shortbuf : ident := $"_shortbuf".
Definition __unused2 : ident := $"_unused2".
Definition __vtable_offset : ident := $"_vtable_offset".
Definition __wide_data : ident := $"_wide_data".
Definition _a : ident := $"a".
Definition _actuatorIndex : ident := $"actuatorIndex".
Definition _actuatorParams : ident := $"actuatorParams".
Definition _b : ident := $"b".
Definition _blackFecActuator : ident := $"blackFecActuator".
Definition _blackFecActuator_addPacketToBlock : ident := $"blackFecActuator_addPacketToBlock".
Definition _blackFecActuator_init : ident := $"blackFecActuator_init".
Definition _blackFecActuator_initBlockWithPacket : ident := $"blackFecActuator_initBlockWithPacket".
Definition _blackFecActuator_regenerateMissingPackets : ident := $"blackFecActuator_regenerateMissingPackets".
Definition _blackFecActuator_removeHeaders : ident := $"blackFecActuator_removeHeaders".
Definition _blackFecActuator_unDeduce : ident := $"blackFecActuator_unDeduce".
Definition _blockIndex : ident := $"blockIndex".
Definition _blockListHead : ident := $"blockListHead".
Definition _blockListTail : ident := $"blockListTail".
Definition _blockSeq : ident := $"blockSeq".
Definition _block_seq : ident := $"block_seq".
Definition _bpacketptrs : ident := $"bpacketptrs".
Definition _bpacketsizes : ident := $"bpacketsizes".
Definition _bpstat : ident := $"bpstat".
Definition _buf : ident := $"buf".
Definition _buf__1 : ident := $"buf__1".
Definition _buf__2 : ident := $"buf__2".
Definition _bufptr : ident := $"bufptr".
Definition _c : ident := $"c".
Definition _calloc : ident := $"calloc".
Definition _check : ident := $"check".
Definition _comp : ident := $"comp".
Definition _compId : ident := $"compId".
Definition _complete : ident := $"complete".
Definition _composition : ident := $"composition".
Definition _currTime : ident := $"currTime".
Definition _currblock : ident := $"currblock".
Definition _data : ident := $"data".
Definition _data_lost_row : ident := $"data_lost_row".
Definition _deducehdr : ident := $"deducehdr".
Definition _deducehdr_logAll : ident := $"deducehdr_logAll".
Definition _deducehdrsize : ident := $"deducehdrsize".
Definition _deduceparamsizeWithPad : ident := $"deduceparamsizeWithPad".
Definition _deduceparamsizeWithoutPad : ident := $"deduceparamsizeWithoutPad".
Definition _description : ident := $"description".
Definition _dest : ident := $"dest".
Definition _destination : ident := $"destination".
Definition _dhdr : ident := $"dhdr".
Definition _dstaddr : ident := $"dstaddr".
Definition _dstport : ident := $"dstport".
Definition _err : ident := $"err".
Definition _f : ident := $"f".
Definition _fecBlock : ident := $"fecBlock".
Definition _fecBlockHead : ident := $"fecBlockHead".
Definition _fecBlockTail : ident := $"fecBlockTail".
Definition _fecBlock_free : ident := $"fecBlock_free".
Definition _fecBlock_log : ident := $"fecBlock_log".
Definition _fecBlock_new : ident := $"fecBlock_new".
Definition _fecCommon_maskHeader : ident := $"fecCommon_maskHeader".
Definition _fecPacketCount : ident := $"fecPacketCount".
Definition _fecParams : ident := $"fecParams".
Definition _fec_2_index : ident := $"fec_2_index".
Definition _fec_2_power : ident := $"fec_2_power".
Definition _fec_blk_decode : ident := $"fec_blk_decode".
Definition _fec_blk_encode : ident := $"fec_blk_encode".
Definition _fec_display_tables : ident := $"fec_display_tables".
Definition _fec_find_mod : ident := $"fec_find_mod".
Definition _fec_generate_math_tables : ident := $"fec_generate_math_tables".
Definition _fec_generate_weights : ident := $"fec_generate_weights".
Definition _fec_gf_mult : ident := $"fec_gf_mult".
Definition _fec_h : ident := $"fec_h".
Definition _fec_invefec : ident := $"fec_invefec".
Definition _fec_k : ident := $"fec_k".
Definition _fec_matrix_display : ident := $"fec_matrix_display".
Definition _fec_matrix_transform : ident := $"fec_matrix_transform".
Definition _fec_n : ident := $"fec_n".
Definition _fec_seq : ident := $"fec_seq".
Definition _fec_weights : ident := $"fec_weights".
Definition _fecblock : ident := $"fecblock".
Definition _fecblocknext : ident := $"fecblocknext".
Definition _fecparams : ident := $"fecparams".
Definition _fflush : ident := $"fflush".
Definition _flow : ident := $"flow".
Definition _flowSeq : ident := $"flowSeq".
Definition _flowTuple : ident := $"flowTuple".
Definition _flowTuple_log : ident := $"flowTuple_log".
Definition _flow_seq : ident := $"flow_seq".
Definition _flowhash : ident := $"flowhash".
Definition _flowid : ident := $"flowid".
Definition _flowtuple : ident := $"flowtuple".
Definition _found : ident := $"found".
Definition _fprintf : ident := $"fprintf".
Definition _free : ident := $"free".
Definition _h : ident := $"h".
Definition _htons : ident := $"htons".
Definition _i : ident := $"i".
Definition _i_max : ident := $"i_max".
Definition _in_addr : ident := $"in_addr".
Definition _inv : ident := $"inv".
Definition _ip : ident := $"ip".
Definition _ip_dst : ident := $"ip_dst".
Definition _ip_hl : ident := $"ip_hl".
Definition _ip_id : ident := $"ip_id".
Definition _ip_len : ident := $"ip_len".
Definition _ip_off : ident := $"ip_off".
Definition _ip_p : ident := $"ip_p".
Definition _ip_src : ident := $"ip_src".
Definition _ip_sum : ident := $"ip_sum".
Definition _ip_tos : ident := $"ip_tos".
Definition _ip_ttl : ident := $"ip_ttl".
Definition _ip_v : ident := $"ip_v".
Definition _iphdrsize : ident := $"iphdrsize".
Definition _ipheader : ident := $"ipheader".
Definition _iphl : ident := $"iphl".
Definition _iplen : ident := $"iplen".
Definition _ipversion : ident := $"ipversion".
Definition _isParity : ident := $"isParity".
Definition _isUsefulLevel : ident := $"isUsefulLevel".
Definition _j : ident := $"j".
Definition _j_max : ident := $"j_max".
Definition _k : ident := $"k".
Definition _len : ident := $"len".
Definition _length : ident := $"length".
Definition _lost : ident := $"lost".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _maxn : ident := $"maxn".
Definition _maxpacketsize : ident := $"maxpacketsize".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _mod : ident := $"mod".
Definition _modulus : ident := $"modulus".
Definition _n : ident := $"n".
Definition _nbufptr : ident := $"nbufptr".
Definition _newBuffer : ident := $"newBuffer".
Definition _newFlow : ident := $"newFlow".
Definition _newblock : ident := $"newblock".
Definition _newipheader : ident := $"newipheader".
Definition _newlength : ident := $"newlength".
Definition _newpacket : ident := $"newpacket".
Definition _newpinfo : ident := $"newpinfo".
Definition _next : ident := $"next".
Definition _nfPacketId : ident := $"nfPacketId".
Definition _nfq_q_handle : ident := $"nfq_q_handle".
Definition _no_deducehdr : ident := $"no_deducehdr".
Definition _ntohl : ident := $"ntohl".
Definition _ntohs : ident := $"ntohs".
Definition _number : ident := $"number".
Definition _oldblock : ident := $"oldblock".
Definition _origDstIpAddr : ident := $"origDstIpAddr".
Definition _origIpProtocol : ident := $"origIpProtocol".
Definition _origLength : ident := $"origLength".
Definition _origSrcIpAddr : ident := $"origSrcIpAddr".
Definition _origin : ident := $"origin".
Definition _outstring : ident := $"outstring".
Definition _p : ident := $"p".
Definition _packetCount : ident := $"packetCount".
Definition _packetdata : ident := $"packetdata".
Definition _packetinfo : ident := $"packetinfo".
Definition _packetinfo_copyNoData : ident := $"packetinfo_copyNoData".
Definition _packetinfo_copyWithData : ident := $"packetinfo_copyWithData".
Definition _packetinfo_free : ident := $"packetinfo_free".
Definition _packetinfo_getAParam : ident := $"packetinfo_getAParam".
Definition _packetinfo_get_deducehdrFromPacket : ident := $"packetinfo_get_deducehdrFromPacket".
Definition _packetptrs : ident := $"packetptrs".
Definition _packets : ident := $"packets".
Definition _packetsizes : ident := $"packetsizes".
Definition _paramSize : ident := $"paramSize".
Definition _pbeg : ident := $"pbeg".
Definition _pdata : ident := $"pdata".
Definition _pend : ident := $"pend".
Definition _pflow : ident := $"pflow".
Definition _pindex : ident := $"pindex".
Definition _pinfo : ident := $"pinfo".
Definition _plen : ident := $"plen".
Definition _plist : ident := $"plist".
Definition _plisttail : ident := $"plisttail".
Definition _pparity : ident := $"pparity".
Definition _prev : ident := $"prev".
Definition _printf : ident := $"printf".
Definition _privateHexDump : ident := $"privateHexDump".
Definition _protocol : ident := $"protocol".
Definition _pstat : ident := $"pstat".
Definition _q : ident := $"q".
Definition _qh : ident := $"qh".
Definition _queue : ident := $"queue".
Definition _r : ident := $"r".
Definition _remaindersize : ident := $"remaindersize".
Definition _reserved : ident := $"reserved".
Definition _returnlist : ident := $"returnlist".
Definition _row : ident := $"row".
Definition _rse_code : ident := $"rse_code".
Definition _rse_code_print : ident := $"rse_code_print".
Definition _rse_init : ident := $"rse_init".
Definition _s : ident := $"s".
Definition _s_addr : ident := $"s_addr".
Definition _shim : ident := $"shim".
Definition _size : ident := $"size".
Definition _source : ident := $"source".
Definition _srcaddr : ident := $"srcaddr".
Definition _srcport : ident := $"srcport".
Definition _stderr : ident := $"stderr".
Definition _t : ident := $"t".
Definition _temp : ident := $"temp".
Definition _tempBuffer : ident := $"tempBuffer".
Definition _tempLength : ident := $"tempLength".
Definition _timeout : ident := $"timeout".
Definition _trace : ident := $"trace".
Definition _tuple : ident := $"tuple".
Definition _tuplestr_buff : ident := $"tuplestr_buff".
Definition _u : ident := $"u".
Definition _udph : ident := $"udph".
Definition _udphdr : ident := $"udphdr".
Definition _udphdrsize : ident := $"udphdrsize".
Definition _udplen : ident := $"udplen".
Definition _uh_dport : ident := $"uh_dport".
Definition _uh_sport : ident := $"uh_sport".
Definition _uh_sum : ident := $"uh_sum".
Definition _uh_ulen : ident := $"uh_ulen".
Definition _util_getCurrentTime : ident := $"util_getCurrentTime".
Definition _v : ident := $"v".
Definition _w : ident := $"w".
Definition _weight : ident := $"weight".
Definition _x : ident := $"x".
Definition _xh : ident := $"xh".
Definition _xk : ident := $"xk".
Definition _xr : ident := $"xr".
Definition _y : ident := $"y".
Definition _z : ident := $"z".
Definition _zc_blackFec : ident := $"zc_blackFec".
Definition _zc_blackFec__1 : ident := $"zc_blackFec__1".
Definition _zlog : ident := $"zlog".
Definition _zlog_category_s : ident := $"zlog_category_s".

Definition f_fecCommon_maskHeader := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ipheader, (tptr (Tstruct _ip noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
        (Tstruct _ip noattr)) _ip_sum tushort)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
          (Tstruct _ip noattr)) _ip_ttl tuchar)
      (Econst_int (Int.repr 0) tint))
    (Sreturn None)))
|}.

Definition composites : list composite_definition :=
(Composite _in_addr Struct (Member_plain _s_addr tuint :: nil) noattr ::
 Composite _ip Struct
   (Member_bitfield _ip_hl I32 Unsigned noattr 4 false ::
    Member_bitfield _ip_v I32 Unsigned noattr 4 false ::
    Member_plain _ip_tos tuchar :: Member_plain _ip_len tushort ::
    Member_plain _ip_id tushort :: Member_plain _ip_off tushort ::
    Member_plain _ip_ttl tuchar :: Member_plain _ip_p tuchar ::
    Member_plain _ip_sum tushort ::
    Member_plain _ip_src (Tstruct _in_addr noattr) ::
    Member_plain _ip_dst (Tstruct _in_addr noattr) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_fecCommon_maskHeader, Gfun(Internal f_fecCommon_maskHeader)) :: nil).

Definition public_idents : list ident :=
(_fecCommon_maskHeader :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


