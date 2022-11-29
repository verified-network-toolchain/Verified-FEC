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
  Definition source_file := "redFecActuator.c".
  Definition normalized := true.
End Info.

Definition _RETURN : ident := $"RETURN".
Definition __12672 : ident := $"_12672".
Definition __12673 : ident := $"_12673".
Definition __12674 : ident := $"_12674".
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
Definition _base_pinfo : ident := $"base_pinfo".
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
Definition _buf__3 : ident := $"buf__3".
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
Definition _htonl : ident := $"htonl".
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
Definition _maxlength : ident := $"maxlength".
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
Definition _new_pinfo : ident := $"new_pinfo".
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
Definition _packetinfo_addAParam : ident := $"packetinfo_addAParam".
Definition _packetinfo_copyNoData : ident := $"packetinfo_copyNoData".
Definition _packetinfo_copyWithData : ident := $"packetinfo_copyWithData".
Definition _packetinfo_free : ident := $"packetinfo_free".
Definition _packetinfo_getAParam : ident := $"packetinfo_getAParam".
Definition _packetinfo_get_deducehdrFromPacket : ident := $"packetinfo_get_deducehdrFromPacket".
Definition _packetinfo_log : ident := $"packetinfo_log".
Definition _packetptrs : ident := $"packetptrs".
Definition _packets : ident := $"packets".
Definition _packetsizes : ident := $"packetsizes".
Definition _paramSize : ident := $"paramSize".
Definition _paritySeq : ident := $"paritySeq".
Definition _pbeg : ident := $"pbeg".
Definition _pcopy : ident := $"pcopy".
Definition _pdata : ident := $"pdata".
Definition _pend : ident := $"pend".
Definition _pflow : ident := $"pflow".
Definition _pindex : ident := $"pindex".
Definition _pinfo : ident := $"pinfo".
Definition _pinfolist : ident := $"pinfolist".
Definition _pinfotail : ident := $"pinfotail".
Definition _plen : ident := $"plen".
Definition _plist : ident := $"plist".
Definition _plisttail : ident := $"plisttail".
Definition _pnext : ident := $"pnext".
Definition _pparity : ident := $"pparity".
Definition _prepend_pinfo : ident := $"prepend_pinfo".
Definition _prev : ident := $"prev".
Definition _printf : ident := $"printf".
Definition _privateHexDump : ident := $"privateHexDump".
Definition _protocol : ident := $"protocol".
Definition _pstat : ident := $"pstat".
Definition _q : ident := $"q".
Definition _qh : ident := $"qh".
Definition _queue : ident := $"queue".
Definition _r : ident := $"r".
Definition _redFecActuator : ident := $"redFecActuator".
Definition _redFecActuator_generateParity : ident := $"redFecActuator_generateParity".
Definition _redFecActuator_init : ident := $"redFecActuator_init".
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
Definition _zc_redFec : ident := $"zc_redFec".
Definition _zlog : ident := $"zlog".
Definition _zlog_category_s : ident := $"zlog_category_s".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'100 : ident := 227%positive.
Definition _t'101 : ident := 228%positive.
Definition _t'102 : ident := 229%positive.
Definition _t'103 : ident := 230%positive.
Definition _t'104 : ident := 231%positive.
Definition _t'105 : ident := 232%positive.
Definition _t'106 : ident := 233%positive.
Definition _t'107 : ident := 234%positive.
Definition _t'108 : ident := 235%positive.
Definition _t'109 : ident := 236%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'110 : ident := 237%positive.
Definition _t'111 : ident := 238%positive.
Definition _t'112 : ident := 239%positive.
Definition _t'113 : ident := 240%positive.
Definition _t'114 : ident := 241%positive.
Definition _t'115 : ident := 242%positive.
Definition _t'116 : ident := 243%positive.
Definition _t'117 : ident := 244%positive.
Definition _t'118 : ident := 245%positive.
Definition _t'119 : ident := 246%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'120 : ident := 247%positive.
Definition _t'121 : ident := 248%positive.
Definition _t'122 : ident := 249%positive.
Definition _t'123 : ident := 250%positive.
Definition _t'124 : ident := 251%positive.
Definition _t'125 : ident := 252%positive.
Definition _t'126 : ident := 253%positive.
Definition _t'127 : ident := 254%positive.
Definition _t'128 : ident := 255%positive.
Definition _t'129 : ident := 256%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'130 : ident := 257%positive.
Definition _t'131 : ident := 258%positive.
Definition _t'132 : ident := 259%positive.
Definition _t'133 : ident := 260%positive.
Definition _t'134 : ident := 261%positive.
Definition _t'135 : ident := 262%positive.
Definition _t'136 : ident := 263%positive.
Definition _t'137 : ident := 264%positive.
Definition _t'138 : ident := 265%positive.
Definition _t'139 : ident := 266%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'140 : ident := 267%positive.
Definition _t'141 : ident := 268%positive.
Definition _t'142 : ident := 269%positive.
Definition _t'143 : ident := 270%positive.
Definition _t'144 : ident := 271%positive.
Definition _t'145 : ident := 272%positive.
Definition _t'146 : ident := 273%positive.
Definition _t'147 : ident := 274%positive.
Definition _t'148 : ident := 275%positive.
Definition _t'149 : ident := 276%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'150 : ident := 277%positive.
Definition _t'151 : ident := 278%positive.
Definition _t'152 : ident := 279%positive.
Definition _t'153 : ident := 280%positive.
Definition _t'154 : ident := 281%positive.
Definition _t'155 : ident := 282%positive.
Definition _t'156 : ident := 283%positive.
Definition _t'157 : ident := 284%positive.
Definition _t'158 : ident := 285%positive.
Definition _t'159 : ident := 286%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'160 : ident := 287%positive.
Definition _t'161 : ident := 288%positive.
Definition _t'162 : ident := 289%positive.
Definition _t'163 : ident := 290%positive.
Definition _t'164 : ident := 291%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'33 : ident := 160%positive.
Definition _t'34 : ident := 161%positive.
Definition _t'35 : ident := 162%positive.
Definition _t'36 : ident := 163%positive.
Definition _t'37 : ident := 164%positive.
Definition _t'38 : ident := 165%positive.
Definition _t'39 : ident := 166%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'40 : ident := 167%positive.
Definition _t'41 : ident := 168%positive.
Definition _t'42 : ident := 169%positive.
Definition _t'43 : ident := 170%positive.
Definition _t'44 : ident := 171%positive.
Definition _t'45 : ident := 172%positive.
Definition _t'46 : ident := 173%positive.
Definition _t'47 : ident := 174%positive.
Definition _t'48 : ident := 175%positive.
Definition _t'49 : ident := 176%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'50 : ident := 177%positive.
Definition _t'51 : ident := 178%positive.
Definition _t'52 : ident := 179%positive.
Definition _t'53 : ident := 180%positive.
Definition _t'54 : ident := 181%positive.
Definition _t'55 : ident := 182%positive.
Definition _t'56 : ident := 183%positive.
Definition _t'57 : ident := 184%positive.
Definition _t'58 : ident := 185%positive.
Definition _t'59 : ident := 186%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'60 : ident := 187%positive.
Definition _t'61 : ident := 188%positive.
Definition _t'62 : ident := 189%positive.
Definition _t'63 : ident := 190%positive.
Definition _t'64 : ident := 191%positive.
Definition _t'65 : ident := 192%positive.
Definition _t'66 : ident := 193%positive.
Definition _t'67 : ident := 194%positive.
Definition _t'68 : ident := 195%positive.
Definition _t'69 : ident := 196%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'70 : ident := 197%positive.
Definition _t'71 : ident := 198%positive.
Definition _t'72 : ident := 199%positive.
Definition _t'73 : ident := 200%positive.
Definition _t'74 : ident := 201%positive.
Definition _t'75 : ident := 202%positive.
Definition _t'76 : ident := 203%positive.
Definition _t'77 : ident := 204%positive.
Definition _t'78 : ident := 205%positive.
Definition _t'79 : ident := 206%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'80 : ident := 207%positive.
Definition _t'81 : ident := 208%positive.
Definition _t'82 : ident := 209%positive.
Definition _t'83 : ident := 210%positive.
Definition _t'84 : ident := 211%positive.
Definition _t'85 : ident := 212%positive.
Definition _t'86 : ident := 213%positive.
Definition _t'87 : ident := 214%positive.
Definition _t'88 : ident := 215%positive.
Definition _t'89 : ident := 216%positive.
Definition _t'9 : ident := 136%positive.
Definition _t'90 : ident := 217%positive.
Definition _t'91 : ident := 218%positive.
Definition _t'92 : ident := 219%positive.
Definition _t'93 : ident := 220%positive.
Definition _t'94 : ident := 221%positive.
Definition _t'95 : ident := 222%positive.
Definition _t'96 : ident := 223%positive.
Definition _t'97 : ident := 224%positive.
Definition _t'98 : ident := 225%positive.
Definition _t'99 : ident := 226%positive.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 3);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_28 := {|
  gvar_info := (tarray tschar 61);
  gvar_init := (Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_20 := {|
  gvar_info := (tarray tschar 25);
  gvar_init := (Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_10 := {|
  gvar_info := (tarray tschar 70);
  gvar_init := (Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_34 := {|
  gvar_info := (tarray tschar 23);
  gvar_init := (Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_19 := {|
  gvar_info := (tarray tschar 26);
  gvar_init := (Init_int8 (Int.repr 42) :: Init_int8 (Int.repr 42) ::
                Init_int8 (Int.repr 42) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_15 := {|
  gvar_info := (tarray tschar 42);
  gvar_init := (Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 38);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_33 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_21 := {|
  gvar_info := (tarray tschar 60);
  gvar_init := (Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_27 := {|
  gvar_info := (tarray tschar 54);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_31 := {|
  gvar_info := (tarray tschar 41);
  gvar_init := (Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 47);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_14 := {|
  gvar_info := (tarray tschar 28);
  gvar_init := (Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_22 := {|
  gvar_info := (tarray tschar 57);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 38);
  gvar_init := (Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 33);
  gvar_init := (Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_25 := {|
  gvar_info := (tarray tschar 52);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_29 := {|
  gvar_info := (tarray tschar 52);
  gvar_init := (Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_11 := {|
  gvar_info := (tarray tschar 38);
  gvar_init := (Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_13 := {|
  gvar_info := (tarray tschar 68);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 91) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 93) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_35 := {|
  gvar_info := (tarray tschar 56);
  gvar_init := (Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_36 := {|
  gvar_info := (tarray tschar 23);
  gvar_init := (Init_int8 (Int.repr 42) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 42) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_18 := {|
  gvar_info := (tarray tschar 58);
  gvar_init := (Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_30 := {|
  gvar_info := (tarray tschar 56);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_9 := {|
  gvar_info := (tarray tschar 71);
  gvar_init := (Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_17 := {|
  gvar_info := (tarray tschar 28);
  gvar_init := (Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_23 := {|
  gvar_info := (tarray tschar 62);
  gvar_init := (Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_24 := {|
  gvar_info := (tarray tschar 32);
  gvar_init := (Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_26 := {|
  gvar_info := (tarray tschar 61);
  gvar_init := (Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_12 := {|
  gvar_info := (tarray tschar 63);
  gvar_init := (Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_32 := {|
  gvar_info := (tarray tschar 23);
  gvar_init := (Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_37 := {|
  gvar_info := (tarray tschar 25);
  gvar_init := (Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_16 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_zc_redFec := {|
  gvar_info := (tptr (Tstruct _zlog_category_s noattr));
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_redFecActuator_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None (Evar _rse_init (Tfunction Tnil tvoid cc_default)) nil)
  (Sreturn None))
|}.

Definition v___func__ := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_redFecActuator_generateParity := {|
  fn_return := (tptr (Tstruct _packetinfo noattr));
  fn_callconv := cc_default;
  fn_params := ((_f, (tptr (Tstruct _flow noattr))) ::
                (_pinfo, (tptr (Tstruct _packetinfo noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_maxn, tint) ::
               (_pinfolist, (tptr (Tstruct _packetinfo noattr))) ::
               (_pinfotail, (tptr (Tstruct _packetinfo noattr))) ::
               (_pindex, tint) ::
               (_p, (tptr (Tstruct _packetinfo noattr))) ::
               (_pnext, (tptr (Tstruct _packetinfo noattr))) ::
               (_base_pinfo, (tptr (Tstruct _packetinfo noattr))) ::
               (_maxlength, tuint) ::
               (_ipheader, (tptr (Tstruct _ip noattr))) :: (_iphl, tint) ::
               (_bufptr, (tptr tuchar)) :: (_paritySeq, tint) ::
               (_buf, (tptr tschar)) :: (_buf__1, (tptr tschar)) ::
               (_buf__2, (tptr tschar)) ::
               (_udph, (tptr (Tstruct _udphdr noattr))) ::
               (_new_pinfo, (tptr (Tstruct _packetinfo noattr))) ::
               (_buf__3, (tptr tschar)) :: (_t'22, tint) ::
               (_t'21, (tptr tschar)) :: (_t'20, tushort) ::
               (_t'19, tushort) :: (_t'18, tushort) :: (_t'17, tushort) ::
               (_t'16, (tptr tvoid)) ::
               (_t'15, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'14, tint) :: (_t'13, (tptr tschar)) :: (_t'12, tuint) ::
               (_t'11, tuint) :: (_t'10, (tptr tvoid)) :: (_t'9, tint) ::
               (_t'8, (tptr tschar)) :: (_t'7, (tptr tvoid)) ::
               (_t'6, tint) :: (_t'5, (tptr tschar)) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'164, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'163, (tptr tint)) :: (_t'162, tuchar) ::
               (_t'161, (tptr (tptr tuchar))) :: (_t'160, (tptr tint)) ::
               (_t'159, (tptr tschar)) ::
               (_t'158, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'157, tuchar) :: (_t'156, tuint) ::
               (_t'155, (tptr (tptr tuchar))) :: (_t'154, tuint) ::
               (_t'153, (tptr tuchar)) :: (_t'152, (tptr tuchar)) ::
               (_t'151, (tptr (tptr tuchar))) :: (_t'150, tuint) ::
               (_t'149, (tptr tint)) :: (_t'148, (tptr tuchar)) ::
               (_t'147, (tptr (tptr tuchar))) :: (_t'146, tuint) ::
               (_t'145, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'144, tint) :: (_t'143, (tptr tint)) :: (_t'142, tint) ::
               (_t'141, (tptr tint)) :: (_t'140, (tptr tuchar)) ::
               (_t'139, (tptr (tptr tuchar))) ::
               (_t'138, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'137, tuchar) ::
               (_t'136, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'135, tuchar) :: (_t'134, tuint) ::
               (_t'133, (tptr (tptr tuchar))) :: (_t'132, tuint) ::
               (_t'131, (tptr tuchar)) :: (_t'130, (tptr tuchar)) ::
               (_t'129, (tptr (tptr tuchar))) :: (_t'128, tuint) ::
               (_t'127, (tptr tint)) :: (_t'126, (tptr tuchar)) ::
               (_t'125, (tptr (tptr tuchar))) :: (_t'124, tuint) ::
               (_t'123, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'122, tint) :: (_t'121, (tptr tint)) :: (_t'120, tint) ::
               (_t'119, (tptr tint)) :: (_t'118, (tptr tuchar)) ::
               (_t'117, (tptr (tptr tuchar))) ::
               (_t'116, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'115, tuchar) :: (_t'114, (tptr (tptr tuchar))) ::
               (_t'113, (tptr tint)) :: (_t'112, (tptr tschar)) ::
               (_t'111, (tptr tint)) :: (_t'110, (tptr (tptr tuchar))) ::
               (_t'109, tuchar) :: (_t'108, tuchar) ::
               (_t'107, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'106, (tptr tschar)) :: (_t'105, (tptr tint)) ::
               (_t'104, (tptr (tptr tuchar))) :: (_t'103, tuchar) ::
               (_t'102, tuchar) :: (_t'101, tuchar) :: (_t'100, tuint) ::
               (_t'99, (tptr tuchar)) :: (_t'98, (tptr (tptr tuchar))) ::
               (_t'97, (tptr tuchar)) :: (_t'96, (tptr (tptr tuchar))) ::
               (_t'95, tschar) :: (_t'94, (tptr tschar)) :: (_t'93, tint) ::
               (_t'92, (tptr tint)) ::
               (_t'91, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'90, tuint) :: (_t'89, (tptr tuchar)) ::
               (_t'88, (tptr (tptr tuchar))) :: (_t'87, (tptr tuchar)) ::
               (_t'86, (tptr (tptr tuchar))) :: (_t'85, tschar) ::
               (_t'84, (tptr tschar)) :: (_t'83, tint) ::
               (_t'82, (tptr tint)) ::
               (_t'81, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'80, tuchar) ::
               (_t'79, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'78, tint) :: (_t'77, (tptr tint)) :: (_t'76, tint) ::
               (_t'75, (tptr tint)) :: (_t'74, (tptr tuchar)) ::
               (_t'73, (tptr (tptr tuchar))) ::
               (_t'72, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'71, tuchar) :: (_t'70, (tptr tuchar)) ::
               (_t'69, (tptr (tptr tuchar))) ::
               (_t'68, (tptr (tptr tuchar))) :: (_t'67, (tptr tuchar)) ::
               (_t'66, (tptr (tptr tuchar))) :: (_t'65, tint) ::
               (_t'64, (tptr (Tstruct _flow noattr))) ::
               (_t'63, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'62, tuchar) :: (_t'61, (tptr tuchar)) :: (_t'60, tint) ::
               (_t'59, tuint) :: (_t'58, (tptr tuchar)) :: (_t'57, tuint) ::
               (_t'56, tushort) ::
               (_t'55, (tptr (Tstruct _flowTuple noattr))) ::
               (_t'54, tushort) ::
               (_t'53, (tptr (Tstruct _flowTuple noattr))) ::
               (_t'52, tint) :: (_t'51, (tptr tint)) :: (_t'50, tint) ::
               (_t'49, (tptr tint)) :: (_t'48, tint) ::
               (_t'47, (tptr tint)) ::
               (_t'46, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'45, tint) :: (_t'44, (tptr tint)) ::
               (_t'43, (tptr tuchar)) :: (_t'42, (tptr (tptr tuchar))) ::
               (_t'41, (tptr tuchar)) :: (_t'40, (tptr (tptr tuchar))) ::
               (_t'39, (tptr (tptr tuchar))) :: (_t'38, (tptr tint)) ::
               (_t'37, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'36, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'35, tuint) :: (_t'34, tuint) :: (_t'33, (tptr tuchar)) ::
               (_t'32, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'31, (tptr (Tstruct _flow noattr))) ::
               (_t'30, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'29, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'28, tint) :: (_t'27, tint) :: (_t'26, tuint) ::
               (_t'25, (tptr (Tstruct _flow noattr))) ::
               (_t'24, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'23, (tptr (Tstruct _zlog_category_s noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _maxn (Econst_int (Int.repr 256) tint))
  (Ssequence
    (Sset _pinfolist (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
    (Ssequence
      (Sset _pinfotail (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'164
            (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
          (Scall None
            (Evar _zlog (Tfunction
                          (Tcons (tptr (Tstruct _zlog_category_s noattr))
                            (Tcons (tptr tschar)
                              (Tcons tulong
                                (Tcons (tptr tschar)
                                  (Tcons tulong
                                    (Tcons tlong
                                      (Tcons tint (Tcons (tptr tschar) Tnil))))))))
                          tvoid
                          {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
            ((Etempvar _t'164 (tptr (Tstruct _zlog_category_s noattr))) ::
             (Ebinop Oadd (Evar ___stringlit_2 (tarray tschar 17))
               (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
             (Ebinop Osub (Esizeof (tarray tschar 17) tulong)
               (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                 (Econst_int (Int.repr 3) tint) tint) tulong) ::
             (Evar ___func__ (tarray tschar 30)) ::
             (Ebinop Osub (Esizeof (tarray tschar 30) tulong)
               (Econst_int (Int.repr 1) tint) tulong) ::
             (Econst_int (Int.repr 116) tint) ::
             (Econst_int (Int.repr 20) tint) ::
             (Evar ___stringlit_1 (tarray tschar 38)) ::
             (Etempvar _f (tptr (Tstruct _flow noattr))) ::
             (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) :: nil)))
        (Ssequence
          (Sifthenelse (Ebinop One
                         (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Sassign
              (Efield
                (Ederef (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                  (Tstruct _packetinfo noattr)) _next
                (tptr (Tstruct _packetinfo noattr)))
              (Econst_int (Int.repr 0) tint))
            Sskip)
          (Ssequence
            (Ssequence
              (Sset _t'163
                (Efield
                  (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                    (Tstruct _flow noattr)) _packetsizes (tptr tint)))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'163 (tptr tint))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'1)
                      (Evar _calloc (Tfunction
                                      (Tcons tulong (Tcons tulong Tnil))
                                      (tptr tvoid) cc_default))
                      ((Esizeof (tptr tuchar) tulong) ::
                       (Etempvar _maxn tint) :: nil))
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                          (Tstruct _flow noattr)) _packetptrs
                        (tptr (tptr tuchar)))
                      (Ecast (Etempvar _t'1 (tptr tvoid))
                        (tptr (tptr tuchar)))))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'2)
                        (Evar _calloc (Tfunction
                                        (Tcons tulong (Tcons tulong Tnil))
                                        (tptr tvoid) cc_default))
                        ((Esizeof tint tulong) :: (Etempvar _maxn tint) ::
                         nil))
                      (Sassign
                        (Efield
                          (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                            (Tstruct _flow noattr)) _packetsizes (tptr tint))
                        (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tint))))
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _calloc (Tfunction
                                        (Tcons tulong (Tcons tulong Tnil))
                                        (tptr tvoid) cc_default))
                        ((Esizeof tschar tulong) :: (Etempvar _maxn tint) ::
                         nil))
                      (Sassign
                        (Efield
                          (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                            (Tstruct _flow noattr)) _pstat (tptr tschar))
                        (Ecast (Etempvar _t'3 (tptr tvoid)) (tptr tschar))))))
                Sskip))
            (Ssequence
              (Ssequence
                (Sset _t'162
                  (Efield
                    (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                      (Tstruct _flow noattr)) _fec_n tuchar))
                (Sifthenelse (Ebinop Ole (Etempvar _t'162 tuchar)
                               (Etempvar _maxn tint) tint)
                  Sskip
                  (Scall None
                    (Evar ___assert_fail (Tfunction
                                           (Tcons (tptr tschar)
                                             (Tcons (tptr tschar)
                                               (Tcons tuint
                                                 (Tcons (tptr tschar) Tnil))))
                                           tvoid cc_default))
                    ((Evar ___stringlit_3 (tarray tschar 17)) ::
                     (Evar ___stringlit_2 (tarray tschar 17)) ::
                     (Econst_int (Int.repr 132) tint) ::
                     (Evar ___func__ (tarray tschar 30)) :: nil))))
              (Ssequence
                (Ssequence
                  (Sset _t'161
                    (Efield
                      (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                        (Tstruct _flow noattr)) _packetptrs
                      (tptr (tptr tuchar))))
                  (Scall None
                    (Evar _memset (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons tint (Tcons tulong Tnil)))
                                    (tptr tvoid) cc_default))
                    ((Etempvar _t'161 (tptr (tptr tuchar))) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Ebinop Omul (Etempvar _maxn tint)
                       (Esizeof (tptr tuchar) tulong) tulong) :: nil)))
                (Ssequence
                  (Ssequence
                    (Sset _t'160
                      (Efield
                        (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                          (Tstruct _flow noattr)) _packetsizes (tptr tint)))
                    (Scall None
                      (Evar _memset (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons tint (Tcons tulong Tnil)))
                                      (tptr tvoid) cc_default))
                      ((Etempvar _t'160 (tptr tint)) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Ebinop Omul (Etempvar _maxn tint)
                         (Esizeof tint tulong) tulong) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'159
                        (Efield
                          (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                            (Tstruct _flow noattr)) _pstat (tptr tschar)))
                      (Scall None
                        (Evar _memset (Tfunction
                                        (Tcons (tptr tvoid)
                                          (Tcons tint (Tcons tulong Tnil)))
                                        (tptr tvoid) cc_default))
                        ((Etempvar _t'159 (tptr tschar)) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Etempvar _maxn tint) :: nil)))
                    (Ssequence
                      (Sset _pindex (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sset _maxlength (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Ssequence
                            (Sset _t'157
                              (Efield
                                (Ederef
                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                  (Tstruct _flow noattr)) _fec_k tuchar))
                            (Sifthenelse (Ebinop Oeq (Etempvar _t'157 tuchar)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)
                              (Sset _paritySeq
                                (Efield
                                  (Ederef
                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                    (Tstruct _packetinfo noattr)) _flow_seq
                                  tuint))
                              (Ssequence
                                (Sset _t'158
                                  (Efield
                                    (Ederef
                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                      (Tstruct _flow noattr)) _fecBlockHead
                                    (tptr (Tstruct _packetinfo noattr))))
                                (Sset _paritySeq
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'158 (tptr (Tstruct _packetinfo noattr)))
                                      (Tstruct _packetinfo noattr)) _flow_seq
                                    tuint)))))
                          (Ssequence
                            (Ssequence
                              (Sset _p
                                (Efield
                                  (Ederef
                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                    (Tstruct _flow noattr)) _fecBlockHead
                                  (tptr (Tstruct _packetinfo noattr))))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop One
                                                 (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                 (Ecast
                                                   (Econst_int (Int.repr 0) tint)
                                                   (tptr tvoid)) tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                          (Tstruct _packetinfo noattr))
                                        _blockIndex tint)
                                      (Etempvar _pindex tint))
                                    (Ssequence
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                            (Tstruct _packetinfo noattr))
                                          _isParity tint)
                                        (Econst_int (Int.repr 0) tint))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'156
                                              (Efield
                                                (Ederef
                                                  (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                  (Tstruct _packetinfo noattr))
                                                _length tuint))
                                            (Scall (Some _t'4)
                                              (Evar _calloc (Tfunction
                                                              (Tcons tulong
                                                                (Tcons tulong
                                                                  Tnil))
                                                              (tptr tvoid)
                                                              cc_default))
                                              ((Etempvar _t'156 tuint) ::
                                               (Esizeof tuchar tulong) ::
                                               nil)))
                                          (Ssequence
                                            (Sset _t'155
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _packetptrs
                                                (tptr (tptr tuchar))))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _t'155 (tptr (tptr tuchar)))
                                                  (Etempvar _pindex tint)
                                                  (tptr (tptr tuchar)))
                                                (tptr tuchar))
                                              (Etempvar _t'4 (tptr tvoid)))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'151
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _packetptrs
                                                (tptr (tptr tuchar))))
                                            (Ssequence
                                              (Sset _t'152
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _t'151 (tptr (tptr tuchar)))
                                                    (Etempvar _pindex tint)
                                                    (tptr (tptr tuchar)))
                                                  (tptr tuchar)))
                                              (Ssequence
                                                (Sset _t'153
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                      (Tstruct _packetinfo noattr))
                                                    _packetdata
                                                    (tptr tuchar)))
                                                (Ssequence
                                                  (Sset _t'154
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                        (Tstruct _packetinfo noattr))
                                                      _length tuint))
                                                  (Scall None
                                                    (Evar _memcpy (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                    ((Etempvar _t'152 (tptr tuchar)) ::
                                                     (Etempvar _t'153 (tptr tuchar)) ::
                                                     (Etempvar _t'154 tuint) ::
                                                     nil))))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'149
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                    (Tstruct _flow noattr))
                                                  _packetsizes (tptr tint)))
                                              (Ssequence
                                                (Sset _t'150
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                      (Tstruct _packetinfo noattr))
                                                    _length tuint))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _t'149 (tptr tint))
                                                      (Etempvar _pindex tint)
                                                      (tptr tint)) tint)
                                                  (Etempvar _t'150 tuint))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'147
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                      (Tstruct _flow noattr))
                                                    _packetptrs
                                                    (tptr (tptr tuchar))))
                                                (Ssequence
                                                  (Sset _t'148
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _t'147 (tptr (tptr tuchar)))
                                                        (Etempvar _pindex tint)
                                                        (tptr (tptr tuchar)))
                                                      (tptr tuchar)))
                                                  (Scall None
                                                    (Evar _fecCommon_maskHeader 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _ip noattr))
                                                        Tnil) tvoid
                                                      cc_default))
                                                    ((Ecast
                                                       (Etempvar _t'148 (tptr tuchar))
                                                       (tptr (Tstruct _ip noattr))) ::
                                                     nil))))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'146
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                        (Tstruct _packetinfo noattr))
                                                      _length tuint))
                                                  (Sifthenelse (Ebinop Ogt
                                                                 (Etempvar _t'146 tuint)
                                                                 (Etempvar _maxlength tuint)
                                                                 tint)
                                                    (Sset _maxlength
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                          (Tstruct _packetinfo noattr))
                                                        _length tuint))
                                                    Sskip))
                                                (Ssequence
                                                  (Sloop
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'145
                                                          (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                        (Scall (Some _t'6)
                                                          (Evar _isUsefulLevel 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _zlog_category_s noattr))
                                                              (Tcons tint
                                                                Tnil)) tint
                                                            cc_default))
                                                          ((Etempvar _t'145 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                           (Econst_int (Int.repr 20) tint) ::
                                                           nil)))
                                                      (Sifthenelse (Etempvar _t'6 tint)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'139
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                  _packetptrs
                                                                  (tptr (tptr tuchar))))
                                                              (Ssequence
                                                                (Sset _t'140
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'139 (tptr (tptr tuchar)))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                (Ssequence
                                                                  (Sset _t'141
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetsizes
                                                                    (tptr tint)))
                                                                  (Ssequence
                                                                    (Sset _t'142
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'141 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'143
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetsizes
                                                                    (tptr tint)))
                                                                    (Ssequence
                                                                    (Sset _t'144
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'143 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                    (Scall (Some _t'5)
                                                                    (Evar _privateHexDump 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil)))
                                                                    (tptr tschar)
                                                                    {|cc_vararg:=(Some 3); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'140 (tptr tuchar)) ::
                                                                    (Etempvar _t'142 tint) ::
                                                                    (Evar ___stringlit_4 (tarray tschar 38)) ::
                                                                    (Etempvar _t'144 tint) ::
                                                                    (Etempvar _pindex tint) ::
                                                                    nil))))))))
                                                            (Sset _buf
                                                              (Etempvar _t'5 (tptr tschar))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'138
                                                                (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                              (Scall None
                                                                (Evar _zlog 
                                                                (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                  tvoid
                                                                  {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                ((Etempvar _t'138 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                 (Ebinop Oadd
                                                                   (Evar ___stringlit_2 (tarray tschar 17))
                                                                   (Econst_int (Int.repr 3) tint)
                                                                   (tptr tschar)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 17) tulong)
                                                                   (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                   tulong) ::
                                                                 (Evar ___func__ (tarray tschar 30)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 30) tulong)
                                                                   (Econst_int (Int.repr 1) tint)
                                                                   tulong) ::
                                                                 (Econst_int (Int.repr 177) tint) ::
                                                                 (Econst_int (Int.repr 20) tint) ::
                                                                 (Evar ___stringlit_5 (tarray tschar 3)) ::
                                                                 (Etempvar _buf (tptr tschar)) ::
                                                                 nil)))
                                                            (Scall None
                                                              (Evar _free 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr tvoid)
                                                                  Tnil) tvoid
                                                                cc_default))
                                                              ((Etempvar _buf (tptr tschar)) ::
                                                               nil))))
                                                        Sskip))
                                                    Sbreak)
                                                  (Sset _pindex
                                                    (Ebinop Oadd
                                                      (Etempvar _pindex tint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tint)))))))))))
                                (Sset _p
                                  (Efield
                                    (Ederef
                                      (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                      (Tstruct _packetinfo noattr)) _next
                                    (tptr (Tstruct _packetinfo noattr))))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'136
                                  (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                (Ssequence
                                  (Sset _t'137
                                    (Efield
                                      (Ederef
                                        (Etempvar _f (tptr (Tstruct _flow noattr)))
                                        (Tstruct _flow noattr)) _fec_k
                                      tuchar))
                                  (Scall None
                                    (Evar _zlog (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                    (Tcons (tptr tschar)
                                                      (Tcons tulong
                                                        (Tcons (tptr tschar)
                                                          (Tcons tulong
                                                            (Tcons tlong
                                                              (Tcons tint
                                                                (Tcons
                                                                  (tptr tschar)
                                                                  Tnil))))))))
                                                  tvoid
                                                  {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                    ((Etempvar _t'136 (tptr (Tstruct _zlog_category_s noattr))) ::
                                     (Ebinop Oadd
                                       (Evar ___stringlit_2 (tarray tschar 17))
                                       (Econst_int (Int.repr 3) tint)
                                       (tptr tschar)) ::
                                     (Ebinop Osub
                                       (Esizeof (tarray tschar 17) tulong)
                                       (Ebinop Oadd
                                         (Econst_int (Int.repr 1) tint)
                                         (Econst_int (Int.repr 3) tint) tint)
                                       tulong) ::
                                     (Evar ___func__ (tarray tschar 30)) ::
                                     (Ebinop Osub
                                       (Esizeof (tarray tschar 30) tulong)
                                       (Econst_int (Int.repr 1) tint) tulong) ::
                                     (Econst_int (Int.repr 181) tint) ::
                                     (Econst_int (Int.repr 20) tint) ::
                                     (Evar ___stringlit_6 (tarray tschar 33)) ::
                                     (Etempvar _pindex tint) ::
                                     (Etempvar _t'137 tuchar) :: nil))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'135
                                    (Efield
                                      (Ederef
                                        (Etempvar _f (tptr (Tstruct _flow noattr)))
                                        (Tstruct _flow noattr)) _fec_k
                                      tuchar))
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _pindex tint)
                                                 (Etempvar _t'135 tuchar)
                                                 tint)
                                    Sskip
                                    (Scall None
                                      (Evar ___assert_fail (Tfunction
                                                             (Tcons
                                                               (tptr tschar)
                                                               (Tcons
                                                                 (tptr tschar)
                                                                 (Tcons tuint
                                                                   (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))
                                                             tvoid
                                                             cc_default))
                                      ((Evar ___stringlit_7 (tarray tschar 18)) ::
                                       (Evar ___stringlit_2 (tarray tschar 17)) ::
                                       (Econst_int (Int.repr 183) tint) ::
                                       (Evar ___func__ (tarray tschar 30)) ::
                                       nil))))
                                (Ssequence
                                  (Sifthenelse (Ebinop One
                                                 (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                 (Ecast
                                                   (Econst_int (Int.repr 0) tint)
                                                   (tptr tvoid)) tint)
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'134
                                            (Efield
                                              (Ederef
                                                (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                (Tstruct _packetinfo noattr))
                                              _length tuint))
                                          (Scall (Some _t'7)
                                            (Evar _calloc (Tfunction
                                                            (Tcons tulong
                                                              (Tcons tulong
                                                                Tnil))
                                                            (tptr tvoid)
                                                            cc_default))
                                            ((Etempvar _t'134 tuint) ::
                                             (Esizeof tuchar tulong) :: nil)))
                                        (Ssequence
                                          (Sset _t'133
                                            (Efield
                                              (Ederef
                                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                (Tstruct _flow noattr))
                                              _packetptrs
                                              (tptr (tptr tuchar))))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'133 (tptr (tptr tuchar)))
                                                (Etempvar _pindex tint)
                                                (tptr (tptr tuchar)))
                                              (tptr tuchar))
                                            (Etempvar _t'7 (tptr tvoid)))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'129
                                            (Efield
                                              (Ederef
                                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                (Tstruct _flow noattr))
                                              _packetptrs
                                              (tptr (tptr tuchar))))
                                          (Ssequence
                                            (Sset _t'130
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _t'129 (tptr (tptr tuchar)))
                                                  (Etempvar _pindex tint)
                                                  (tptr (tptr tuchar)))
                                                (tptr tuchar)))
                                            (Ssequence
                                              (Sset _t'131
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                    (Tstruct _packetinfo noattr))
                                                  _packetdata (tptr tuchar)))
                                              (Ssequence
                                                (Sset _t'132
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                      (Tstruct _packetinfo noattr))
                                                    _length tuint))
                                                (Scall None
                                                  (Evar _memcpy (Tfunction
                                                                  (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                  (tptr tvoid)
                                                                  cc_default))
                                                  ((Etempvar _t'130 (tptr tuchar)) ::
                                                   (Etempvar _t'131 (tptr tuchar)) ::
                                                   (Etempvar _t'132 tuint) ::
                                                   nil))))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'127
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _packetsizes (tptr tint)))
                                            (Ssequence
                                              (Sset _t'128
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                    (Tstruct _packetinfo noattr))
                                                  _length tuint))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _t'127 (tptr tint))
                                                    (Etempvar _pindex tint)
                                                    (tptr tint)) tint)
                                                (Etempvar _t'128 tuint))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'125
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                    (Tstruct _flow noattr))
                                                  _packetptrs
                                                  (tptr (tptr tuchar))))
                                              (Ssequence
                                                (Sset _t'126
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _t'125 (tptr (tptr tuchar)))
                                                      (Etempvar _pindex tint)
                                                      (tptr (tptr tuchar)))
                                                    (tptr tuchar)))
                                                (Scall None
                                                  (Evar _fecCommon_maskHeader 
                                                  (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _ip noattr))
                                                      Tnil) tvoid cc_default))
                                                  ((Ecast
                                                     (Etempvar _t'126 (tptr tuchar))
                                                     (tptr (Tstruct _ip noattr))) ::
                                                   nil))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'124
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                      (Tstruct _packetinfo noattr))
                                                    _length tuint))
                                                (Sifthenelse (Ebinop Ogt
                                                               (Etempvar _t'124 tuint)
                                                               (Etempvar _maxlength tuint)
                                                               tint)
                                                  (Sset _maxlength
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                        (Tstruct _packetinfo noattr))
                                                      _length tuint))
                                                  Sskip))
                                              (Ssequence
                                                (Sloop
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'123
                                                        (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                      (Scall (Some _t'9)
                                                        (Evar _isUsefulLevel 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _zlog_category_s noattr))
                                                            (Tcons tint Tnil))
                                                          tint cc_default))
                                                        ((Etempvar _t'123 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                         (Econst_int (Int.repr 20) tint) ::
                                                         nil)))
                                                    (Sifthenelse (Etempvar _t'9 tint)
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'117
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                  (Tstruct _flow noattr))
                                                                _packetptrs
                                                                (tptr (tptr tuchar))))
                                                            (Ssequence
                                                              (Sset _t'118
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'117 (tptr (tptr tuchar)))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr (tptr tuchar)))
                                                                  (tptr tuchar)))
                                                              (Ssequence
                                                                (Sset _t'119
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetsizes
                                                                    (tptr tint)))
                                                                (Ssequence
                                                                  (Sset _t'120
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'119 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                  (Ssequence
                                                                    (Sset _t'121
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetsizes
                                                                    (tptr tint)))
                                                                    (Ssequence
                                                                    (Sset _t'122
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'121 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                    (Scall (Some _t'8)
                                                                    (Evar _privateHexDump 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil)))
                                                                    (tptr tschar)
                                                                    {|cc_vararg:=(Some 3); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'118 (tptr tuchar)) ::
                                                                    (Etempvar _t'120 tint) ::
                                                                    (Evar ___stringlit_4 (tarray tschar 38)) ::
                                                                    (Etempvar _t'122 tint) ::
                                                                    (Etempvar _pindex tint) ::
                                                                    nil))))))))
                                                          (Sset _buf__1
                                                            (Etempvar _t'8 (tptr tschar))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'116
                                                              (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                            (Scall None
                                                              (Evar _zlog 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _zlog_category_s noattr))
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                tvoid
                                                                {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                              ((Etempvar _t'116 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                               (Ebinop Oadd
                                                                 (Evar ___stringlit_2 (tarray tschar 17))
                                                                 (Econst_int (Int.repr 3) tint)
                                                                 (tptr tschar)) ::
                                                               (Ebinop Osub
                                                                 (Esizeof (tarray tschar 17) tulong)
                                                                 (Ebinop Oadd
                                                                   (Econst_int (Int.repr 1) tint)
                                                                   (Econst_int (Int.repr 3) tint)
                                                                   tint)
                                                                 tulong) ::
                                                               (Evar ___func__ (tarray tschar 30)) ::
                                                               (Ebinop Osub
                                                                 (Esizeof (tarray tschar 30) tulong)
                                                                 (Econst_int (Int.repr 1) tint)
                                                                 tulong) ::
                                                               (Econst_int (Int.repr 196) tint) ::
                                                               (Econst_int (Int.repr 20) tint) ::
                                                               (Evar ___stringlit_5 (tarray tschar 3)) ::
                                                               (Etempvar _buf__1 (tptr tschar)) ::
                                                               nil)))
                                                          (Scall None
                                                            (Evar _free 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr tvoid)
                                                                Tnil) tvoid
                                                              cc_default))
                                                            ((Etempvar _buf__1 (tptr tschar)) ::
                                                             nil))))
                                                      Sskip))
                                                  Sbreak)
                                                (Sset _pindex
                                                  (Ebinop Oadd
                                                    (Etempvar _pindex tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint))))))))
                                    Sskip)
                                  (Ssequence
                                    (Ssequence
                                      (Sset _pindex
                                        (Efield
                                          (Ederef
                                            (Etempvar _f (tptr (Tstruct _flow noattr)))
                                            (Tstruct _flow noattr)) _fec_k
                                          tuchar))
                                      (Sloop
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'115
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _fec_n tuchar))
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _pindex tint)
                                                           (Etempvar _t'115 tuchar)
                                                           tint)
                                              Sskip
                                              Sbreak))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'10)
                                                (Evar _calloc (Tfunction
                                                                (Tcons tulong
                                                                  (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                (tptr tvoid)
                                                                cc_default))
                                                ((Etempvar _maxlength tuint) ::
                                                 (Esizeof tuchar tulong) ::
                                                 nil))
                                              (Ssequence
                                                (Sset _t'114
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                      (Tstruct _flow noattr))
                                                    _packetptrs
                                                    (tptr (tptr tuchar))))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _t'114 (tptr (tptr tuchar)))
                                                      (Etempvar _pindex tint)
                                                      (tptr (tptr tuchar)))
                                                    (tptr tuchar))
                                                  (Etempvar _t'10 (tptr tvoid)))))
                                            (Ssequence
                                              (Sset _t'113
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                    (Tstruct _flow noattr))
                                                  _packetsizes (tptr tint)))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _t'113 (tptr tint))
                                                    (Etempvar _pindex tint)
                                                    (tptr tint)) tint)
                                                (Etempvar _maxlength tuint)))))
                                        (Sset _pindex
                                          (Ebinop Oadd
                                            (Etempvar _pindex tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'107
                                          (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                        (Ssequence
                                          (Sset _t'108
                                            (Efield
                                              (Ederef
                                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                (Tstruct _flow noattr))
                                              _fec_k tuchar))
                                          (Ssequence
                                            (Sset _t'109
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _fec_h tuchar))
                                            (Ssequence
                                              (Sset _t'110
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                    (Tstruct _flow noattr))
                                                  _packetptrs
                                                  (tptr (tptr tuchar))))
                                              (Ssequence
                                                (Sset _t'111
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                      (Tstruct _flow noattr))
                                                    _packetsizes (tptr tint)))
                                                (Ssequence
                                                  (Sset _t'112
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                        (Tstruct _flow noattr))
                                                      _pstat (tptr tschar)))
                                                  (Scall None
                                                    (Evar _zlog (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                  tvoid
                                                                  {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                    ((Etempvar _t'107 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                     (Ebinop Oadd
                                                       (Evar ___stringlit_2 (tarray tschar 17))
                                                       (Econst_int (Int.repr 3) tint)
                                                       (tptr tschar)) ::
                                                     (Ebinop Osub
                                                       (Esizeof (tarray tschar 17) tulong)
                                                       (Ebinop Oadd
                                                         (Econst_int (Int.repr 1) tint)
                                                         (Econst_int (Int.repr 3) tint)
                                                         tint) tulong) ::
                                                     (Evar ___func__ (tarray tschar 30)) ::
                                                     (Ebinop Osub
                                                       (Esizeof (tarray tschar 30) tulong)
                                                       (Econst_int (Int.repr 1) tint)
                                                       tulong) ::
                                                     (Econst_int (Int.repr 210) tint) ::
                                                     (Econst_int (Int.repr 20) tint) ::
                                                     (Evar ___stringlit_8 (tarray tschar 47)) ::
                                                     (Etempvar _t'108 tuchar) ::
                                                     (Etempvar _t'109 tuchar) ::
                                                     (Etempvar _maxlength tuint) ::
                                                     (Etempvar _t'110 (tptr (tptr tuchar))) ::
                                                     (Etempvar _t'111 (tptr tint)) ::
                                                     (Etempvar _t'112 (tptr tschar)) ::
                                                     nil))))))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'102
                                            (Efield
                                              (Ederef
                                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                (Tstruct _flow noattr))
                                              _fec_k tuchar))
                                          (Ssequence
                                            (Sset _t'103
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _fec_h tuchar))
                                            (Ssequence
                                              (Sset _t'104
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                    (Tstruct _flow noattr))
                                                  _packetptrs
                                                  (tptr (tptr tuchar))))
                                              (Ssequence
                                                (Sset _t'105
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                      (Tstruct _flow noattr))
                                                    _packetsizes (tptr tint)))
                                                (Ssequence
                                                  (Sset _t'106
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                        (Tstruct _flow noattr))
                                                      _pstat (tptr tschar)))
                                                  (Scall None
                                                    (Evar _rse_code (Tfunction
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr (tptr tuchar))
                                                                    (Tcons
                                                                    (tptr tint)
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))
                                                                    tint
                                                                    cc_default))
                                                    ((Etempvar _t'102 tuchar) ::
                                                     (Etempvar _t'103 tuchar) ::
                                                     (Etempvar _maxlength tuint) ::
                                                     (Etempvar _t'104 (tptr (tptr tuchar))) ::
                                                     (Etempvar _t'105 (tptr tint)) ::
                                                     (Etempvar _t'106 (tptr tschar)) ::
                                                     nil)))))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _pindex
                                              (Econst_int (Int.repr 0) tint))
                                            (Sloop
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'101
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                        (Tstruct _flow noattr))
                                                      _fec_n tuchar))
                                                  (Sifthenelse (Ebinop Olt
                                                                 (Etempvar _pindex tint)
                                                                 (Etempvar _t'101 tuchar)
                                                                 tint)
                                                    Sskip
                                                    Sbreak))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'80
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                          (Tstruct _flow noattr))
                                                        _fec_k tuchar))
                                                    (Sifthenelse (Ebinop Olt
                                                                   (Etempvar _pindex tint)
                                                                   (Etempvar _t'80 tuchar)
                                                                   tint)
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'96
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                (Tstruct _flow noattr))
                                                              _packetptrs
                                                              (tptr (tptr tuchar))))
                                                          (Ssequence
                                                            (Sset _t'97
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'96 (tptr (tptr tuchar)))
                                                                  (Etempvar _pindex tint)
                                                                  (tptr (tptr tuchar)))
                                                                (tptr tuchar)))
                                                            (Sifthenelse 
                                                              (Ebinop One
                                                                (Etempvar _t'97 (tptr tuchar))
                                                                (Ecast
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  (tptr tvoid))
                                                                tint)
                                                              (Ssequence
                                                                (Sset _t'98
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetptrs
                                                                    (tptr (tptr tuchar))))
                                                                (Ssequence
                                                                  (Sset _t'99
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'98 (tptr (tptr tuchar)))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                  (Ssequence
                                                                    (Sset _t'100
                                                                    (Ederef
                                                                    (Ecast
                                                                    (Etempvar _t'99 (tptr tuchar))
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _t'11
                                                                    (Ecast
                                                                    (Etempvar _t'100 tuint)
                                                                    tuint)))))
                                                              (Sset _t'11
                                                                (Ecast
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tuint)))))
                                                        (Ssequence
                                                          (Sset _t'91
                                                            (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                          (Ssequence
                                                            (Sset _t'92
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                  (Tstruct _flow noattr))
                                                                _packetsizes
                                                                (tptr tint)))
                                                            (Ssequence
                                                              (Sset _t'93
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'92 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                  tint))
                                                              (Ssequence
                                                                (Sset _t'94
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _pstat
                                                                    (tptr tschar)))
                                                                (Ssequence
                                                                  (Sset _t'95
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'94 (tptr tschar))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tschar))
                                                                    tschar))
                                                                  (Scall None
                                                                    (Evar _zlog 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'91 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_2 (tarray tschar 17))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func__ (tarray tschar 30)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 30) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 218) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_10 (tarray tschar 70)) ::
                                                                    (Etempvar _paritySeq tint) ::
                                                                    (Etempvar _pindex tint) ::
                                                                    (Etempvar _t'93 tint) ::
                                                                    (Etempvar _t'95 tschar) ::
                                                                    (Etempvar _t'11 tuint) ::
                                                                    nil))))))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'86
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                (Tstruct _flow noattr))
                                                              _packetptrs
                                                              (tptr (tptr tuchar))))
                                                          (Ssequence
                                                            (Sset _t'87
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'86 (tptr (tptr tuchar)))
                                                                  (Etempvar _pindex tint)
                                                                  (tptr (tptr tuchar)))
                                                                (tptr tuchar)))
                                                            (Sifthenelse 
                                                              (Ebinop One
                                                                (Etempvar _t'87 (tptr tuchar))
                                                                (Ecast
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  (tptr tvoid))
                                                                tint)
                                                              (Ssequence
                                                                (Sset _t'88
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetptrs
                                                                    (tptr (tptr tuchar))))
                                                                (Ssequence
                                                                  (Sset _t'89
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'88 (tptr (tptr tuchar)))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                  (Ssequence
                                                                    (Sset _t'90
                                                                    (Ederef
                                                                    (Ecast
                                                                    (Etempvar _t'89 (tptr tuchar))
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _t'12
                                                                    (Ecast
                                                                    (Etempvar _t'90 tuint)
                                                                    tuint)))))
                                                              (Sset _t'12
                                                                (Ecast
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tuint)))))
                                                        (Ssequence
                                                          (Sset _t'81
                                                            (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                          (Ssequence
                                                            (Sset _t'82
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                  (Tstruct _flow noattr))
                                                                _packetsizes
                                                                (tptr tint)))
                                                            (Ssequence
                                                              (Sset _t'83
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'82 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                  tint))
                                                              (Ssequence
                                                                (Sset _t'84
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _pstat
                                                                    (tptr tschar)))
                                                                (Ssequence
                                                                  (Sset _t'85
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'84 (tptr tschar))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tschar))
                                                                    tschar))
                                                                  (Scall None
                                                                    (Evar _zlog 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'81 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_2 (tarray tschar 17))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func__ (tarray tschar 30)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 30) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 226) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_9 (tarray tschar 71)) ::
                                                                    (Etempvar _paritySeq tint) ::
                                                                    (Etempvar _pindex tint) ::
                                                                    (Etempvar _t'83 tint) ::
                                                                    (Etempvar _t'85 tschar) ::
                                                                    (Etempvar _t'12 tuint) ::
                                                                    nil))))))))))
                                                  (Sloop
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'79
                                                          (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                        (Scall (Some _t'14)
                                                          (Evar _isUsefulLevel 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _zlog_category_s noattr))
                                                              (Tcons tint
                                                                Tnil)) tint
                                                            cc_default))
                                                          ((Etempvar _t'79 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                           (Econst_int (Int.repr 20) tint) ::
                                                           nil)))
                                                      (Sifthenelse (Etempvar _t'14 tint)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'73
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                  _packetptrs
                                                                  (tptr (tptr tuchar))))
                                                              (Ssequence
                                                                (Sset _t'74
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'73 (tptr (tptr tuchar)))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                (Ssequence
                                                                  (Sset _t'75
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetsizes
                                                                    (tptr tint)))
                                                                  (Ssequence
                                                                    (Sset _t'76
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'75 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'77
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetsizes
                                                                    (tptr tint)))
                                                                    (Ssequence
                                                                    (Sset _t'78
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'77 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                    (Scall (Some _t'13)
                                                                    (Evar _privateHexDump 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil)))
                                                                    (tptr tschar)
                                                                    {|cc_vararg:=(Some 3); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'74 (tptr tuchar)) ::
                                                                    (Etempvar _t'76 tint) ::
                                                                    (Evar ___stringlit_11 (tarray tschar 38)) ::
                                                                    (Etempvar _t'78 tint) ::
                                                                    (Etempvar _pindex tint) ::
                                                                    nil))))))))
                                                            (Sset _buf__2
                                                              (Etempvar _t'13 (tptr tschar))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'72
                                                                (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                              (Scall None
                                                                (Evar _zlog 
                                                                (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                  tvoid
                                                                  {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                ((Etempvar _t'72 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                 (Ebinop Oadd
                                                                   (Evar ___stringlit_2 (tarray tschar 17))
                                                                   (Econst_int (Int.repr 3) tint)
                                                                   (tptr tschar)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 17) tulong)
                                                                   (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                   tulong) ::
                                                                 (Evar ___func__ (tarray tschar 30)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 30) tulong)
                                                                   (Econst_int (Int.repr 1) tint)
                                                                   tulong) ::
                                                                 (Econst_int (Int.repr 233) tint) ::
                                                                 (Econst_int (Int.repr 20) tint) ::
                                                                 (Evar ___stringlit_5 (tarray tschar 3)) ::
                                                                 (Etempvar _buf__2 (tptr tschar)) ::
                                                                 nil)))
                                                            (Scall None
                                                              (Evar _free 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr tvoid)
                                                                  Tnil) tvoid
                                                                cc_default))
                                                              ((Etempvar _buf__2 (tptr tschar)) ::
                                                               nil))))
                                                        Sskip))
                                                    Sbreak)))
                                              (Sset _pindex
                                                (Ebinop Oadd
                                                  (Etempvar _pindex tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _pindex
                                                (Econst_int (Int.repr 0) tint))
                                              (Sloop
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'71
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                          (Tstruct _flow noattr))
                                                        _fec_k tuchar))
                                                    (Sifthenelse (Ebinop Olt
                                                                   (Etempvar _pindex tint)
                                                                   (Etempvar _t'71 tuchar)
                                                                   tint)
                                                      Sskip
                                                      Sbreak))
                                                  (Ssequence
                                                    (Sset _t'66
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                          (Tstruct _flow noattr))
                                                        _packetptrs
                                                        (tptr (tptr tuchar))))
                                                    (Ssequence
                                                      (Sset _t'67
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _t'66 (tptr (tptr tuchar)))
                                                            (Etempvar _pindex tint)
                                                            (tptr (tptr tuchar)))
                                                          (tptr tuchar)))
                                                      (Sifthenelse (Ebinop One
                                                                    (Etempvar _t'67 (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'69
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                  (Tstruct _flow noattr))
                                                                _packetptrs
                                                                (tptr (tptr tuchar))))
                                                            (Ssequence
                                                              (Sset _t'70
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'69 (tptr (tptr tuchar)))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr (tptr tuchar)))
                                                                  (tptr tuchar)))
                                                              (Scall None
                                                                (Evar _free 
                                                                (Tfunction
                                                                  (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                                                ((Etempvar _t'70 (tptr tuchar)) ::
                                                                 nil))))
                                                          (Ssequence
                                                            (Sset _t'68
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                  (Tstruct _flow noattr))
                                                                _packetptrs
                                                                (tptr (tptr tuchar))))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'68 (tptr (tptr tuchar)))
                                                                  (Etempvar _pindex tint)
                                                                  (tptr (tptr tuchar)))
                                                                (tptr tuchar))
                                                              (Econst_int (Int.repr 0) tint))))
                                                        Sskip))))
                                                (Sset _pindex
                                                  (Ebinop Oadd
                                                    (Etempvar _pindex tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint))))
                                            (Ssequence
                                              (Sifthenelse (Ebinop One
                                                             (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                             (Ecast
                                                               (Econst_int (Int.repr 0) tint)
                                                               (tptr tvoid))
                                                             tint)
                                                (Sset _base_pinfo
                                                  (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
                                                (Sset _base_pinfo
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                      (Tstruct _flow noattr))
                                                    _fecBlockTail
                                                    (tptr (Tstruct _packetinfo noattr)))))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'63
                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                  (Ssequence
                                                    (Sset _t'64
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _base_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                          (Tstruct _packetinfo noattr))
                                                        _pflow
                                                        (tptr (Tstruct _flow noattr))))
                                                    (Ssequence
                                                      (Sset _t'65
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _base_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                            (Tstruct _packetinfo noattr))
                                                          _blockIndex tint))
                                                      (Scall None
                                                        (Evar _zlog (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                        ((Etempvar _t'63 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                         (Ebinop Oadd
                                                           (Evar ___stringlit_2 (tarray tschar 17))
                                                           (Econst_int (Int.repr 3) tint)
                                                           (tptr tschar)) ::
                                                         (Ebinop Osub
                                                           (Esizeof (tarray tschar 17) tulong)
                                                           (Ebinop Oadd
                                                             (Econst_int (Int.repr 1) tint)
                                                             (Econst_int (Int.repr 3) tint)
                                                             tint) tulong) ::
                                                         (Evar ___func__ (tarray tschar 30)) ::
                                                         (Ebinop Osub
                                                           (Esizeof (tarray tschar 30) tulong)
                                                           (Econst_int (Int.repr 1) tint)
                                                           tulong) ::
                                                         (Econst_int (Int.repr 253) tint) ::
                                                         (Econst_int (Int.repr 20) tint) ::
                                                         (Evar ___stringlit_12 (tarray tschar 63)) ::
                                                         (Etempvar _base_pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                         (Etempvar _t'64 (tptr (Tstruct _flow noattr))) ::
                                                         (Etempvar _t'65 tint) ::
                                                         nil)))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _pindex
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                          (Tstruct _flow noattr))
                                                        _fec_k tuchar))
                                                    (Sloop
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'62
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                (Tstruct _flow noattr))
                                                              _fec_n tuchar))
                                                          (Sifthenelse 
                                                            (Ebinop Olt
                                                              (Etempvar _pindex tint)
                                                              (Etempvar _t'62 tuchar)
                                                              tint)
                                                            Sskip
                                                            Sbreak))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Scall (Some _t'15)
                                                              (Evar _packetinfo_copyWithData 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _packetinfo noattr))
                                                                  Tnil)
                                                                (tptr (Tstruct _packetinfo noattr))
                                                                cc_default))
                                                              ((Etempvar _base_pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                               nil))
                                                            (Sset _new_pinfo
                                                              (Etempvar _t'15 (tptr (Tstruct _packetinfo noattr)))))
                                                          (Ssequence
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                  (Tstruct _packetinfo noattr))
                                                                _flow_seq
                                                                tuint)
                                                              (Etempvar _paritySeq tint))
                                                            (Ssequence
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                  _blockIndex
                                                                  tint)
                                                                (Etempvar _pindex tint))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _isParity
                                                                    tint)
                                                                  (Econst_int (Int.repr 1) tint))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'61
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _packetdata
                                                                    (tptr tuchar)))
                                                                    (Sset _ipheader
                                                                    (Ecast
                                                                    (Etempvar _t'61 (tptr tuchar))
                                                                    (tptr (Tstruct _ip noattr)))))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'60
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                                                                    (Tstruct _ip noattr))
                                                                    _ip_hl
                                                                    tint))
                                                                    (Sset _iphl
                                                                    (Ebinop Oshl
                                                                    (Etempvar _t'60 tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _length
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Etempvar _maxlength tuint)
                                                                    (Etempvar _iphl tint)
                                                                    tuint)
                                                                    (Esizeof (Tstruct _udphdr noattr) tulong)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'59
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Scall (Some _t'16)
                                                                    (Evar _calloc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Etempvar _t'59 tuint) ::
                                                                    (Esizeof tuchar tulong) ::
                                                                    nil)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _packetdata
                                                                    (tptr tuchar))
                                                                    (Ecast
                                                                    (Etempvar _t'16 (tptr tvoid))
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _bufptr
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _packetdata
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _memcpy 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Etempvar _bufptr (tptr tuchar)) ::
                                                                    (Ecast
                                                                    (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                                                                    (tptr tvoid)) ::
                                                                    (Etempvar _iphl tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _free 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _ipheader (tptr (Tstruct _ip noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'58
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _packetdata
                                                                    (tptr tuchar)))
                                                                    (Sset _ipheader
                                                                    (Ecast
                                                                    (Etempvar _t'58 (tptr tuchar))
                                                                    (tptr (Tstruct _ip noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'57
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Scall (Some _t'17)
                                                                    (Evar _htons 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tushort
                                                                    Tnil)
                                                                    tushort
                                                                    cc_default))
                                                                    ((Etempvar _t'57 tuint) ::
                                                                    nil)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                                                                    (Tstruct _ip noattr))
                                                                    _ip_len
                                                                    tushort)
                                                                    (Etempvar _t'17 tushort)))
                                                                    (Ssequence
                                                                    (Sset _bufptr
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bufptr (tptr tuchar))
                                                                    (Etempvar _iphl tint)
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _udph
                                                                    (Ecast
                                                                    (Etempvar _bufptr (tptr tuchar))
                                                                    (tptr (Tstruct _udphdr noattr))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'55
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _base_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _tuple
                                                                    (tptr (Tstruct _flowTuple noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'56
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'55 (tptr (Tstruct _flowTuple noattr)))
                                                                    (Tstruct _flowTuple noattr))
                                                                    _srcport
                                                                    tushort))
                                                                    (Scall (Some _t'18)
                                                                    (Evar _htons 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tushort
                                                                    Tnil)
                                                                    tushort
                                                                    cc_default))
                                                                    ((Etempvar _t'56 tushort) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _udph (tptr (Tstruct _udphdr noattr)))
                                                                    (Tstruct _udphdr noattr))
                                                                    18727075383868559167%positive
                                                                    (Tunion __12672 noattr))
                                                                    18727075383868559167%positive
                                                                    (Tstruct __12673 noattr))
                                                                    _uh_sport
                                                                    tushort)
                                                                    (Etempvar _t'18 tushort)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'53
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _base_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _tuple
                                                                    (tptr (Tstruct _flowTuple noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'54
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'53 (tptr (Tstruct _flowTuple noattr)))
                                                                    (Tstruct _flowTuple noattr))
                                                                    _dstport
                                                                    tushort))
                                                                    (Scall (Some _t'19)
                                                                    (Evar _htons 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tushort
                                                                    Tnil)
                                                                    tushort
                                                                    cc_default))
                                                                    ((Etempvar _t'54 tushort) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _udph (tptr (Tstruct _udphdr noattr)))
                                                                    (Tstruct _udphdr noattr))
                                                                    18727075383868559167%positive
                                                                    (Tunion __12672 noattr))
                                                                    18727075383868559167%positive
                                                                    (Tstruct __12673 noattr))
                                                                    _uh_dport
                                                                    tushort)
                                                                    (Etempvar _t'19 tushort)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'51
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetsizes
                                                                    (tptr tint)))
                                                                    (Ssequence
                                                                    (Sset _t'52
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'51 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                    (Scall (Some _t'20)
                                                                    (Evar _htons 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tushort
                                                                    Tnil)
                                                                    tushort
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Etempvar _t'52 tint)
                                                                    (Esizeof (Tstruct _udphdr noattr) tulong)
                                                                    tulong) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _udph (tptr (Tstruct _udphdr noattr)))
                                                                    (Tstruct _udphdr noattr))
                                                                    18727075383868559167%positive
                                                                    (Tunion __12672 noattr))
                                                                    19015305760020270911%positive
                                                                    (Tstruct __12674 noattr))
                                                                    _len
                                                                    tushort)
                                                                    (Etempvar _t'20 tushort)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _udph (tptr (Tstruct _udphdr noattr)))
                                                                    (Tstruct _udphdr noattr))
                                                                    18727075383868559167%positive
                                                                    (Tunion __12672 noattr))
                                                                    19015305760020270911%positive
                                                                    (Tstruct __12674 noattr))
                                                                    _check
                                                                    tushort)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'49
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetsizes
                                                                    (tptr tint)))
                                                                    (Ssequence
                                                                    (Sset _t'50
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'49 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _remaindersize
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'50 tint)
                                                                    (Esizeof (Tstruct _udphdr noattr) tulong)
                                                                    tulong))))
                                                                    (Ssequence
                                                                    (Sset _bufptr
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bufptr (tptr tuchar))
                                                                    (Esizeof (Tstruct _udphdr noattr) tulong)
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'46
                                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'47
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetsizes
                                                                    (tptr tint)))
                                                                    (Ssequence
                                                                    (Sset _t'48
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'47 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                    (Scall None
                                                                    (Evar _zlog 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'46 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_2 (tarray tschar 17))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func__ (tarray tschar 30)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 30) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 310) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_13 (tarray tschar 68)) ::
                                                                    (Etempvar _t'48 tint) ::
                                                                    (Etempvar _pindex tint) ::
                                                                    (Etempvar _maxlength tuint) ::
                                                                    nil)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'42
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetptrs
                                                                    (tptr (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'43
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'42 (tptr (tptr tuchar)))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'44
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetsizes
                                                                    (tptr tint)))
                                                                    (Ssequence
                                                                    (Sset _t'45
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'44 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                    (Scall None
                                                                    (Evar _memcpy 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Etempvar _bufptr (tptr tuchar)) ::
                                                                    (Etempvar _t'43 (tptr tuchar)) ::
                                                                    (Etempvar _t'45 tint) ::
                                                                    nil))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'40
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetptrs
                                                                    (tptr (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'41
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'40 (tptr (tptr tuchar)))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                    (Scall None
                                                                    (Evar _free 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'41 (tptr tuchar)) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'39
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetptrs
                                                                    (tptr (tptr tuchar))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'39 (tptr (tptr tuchar)))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar))
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'38
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _packetsizes
                                                                    (tptr tint)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'38 (tptr tint))
                                                                    (Etempvar _pindex tint)
                                                                    (tptr tint))
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'37
                                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall None
                                                                    (Evar _zlog 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'37 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_2 (tarray tschar 17))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func__ (tarray tschar 30)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 30) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 318) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_14 (tarray tschar 28)) ::
                                                                    (Etempvar _pindex tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'36
                                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall (Some _t'22)
                                                                    (Evar _isUsefulLevel 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tint
                                                                    cc_default))
                                                                    ((Etempvar _t'36 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Econst_int (Int.repr 10) tint) ::
                                                                    nil)))
                                                                    (Sifthenelse (Etempvar _t'22 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'33
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _packetdata
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'34
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'35
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Scall (Some _t'21)
                                                                    (Evar _privateHexDump 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil)))
                                                                    (tptr tschar)
                                                                    {|cc_vararg:=(Some 3); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'33 (tptr tuchar)) ::
                                                                    (Etempvar _t'34 tuint) ::
                                                                    (Evar ___stringlit_15 (tarray tschar 42)) ::
                                                                    (Etempvar _t'35 tuint) ::
                                                                    (Etempvar _pindex tint) ::
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                                    nil)))))
                                                                    (Sset _buf__3
                                                                    (Etempvar _t'21 (tptr tschar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'32
                                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall None
                                                                    (Evar _zlog 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'32 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_2 (tarray tschar 17))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func__ (tarray tschar 30)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 30) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 319) tint) ::
                                                                    (Econst_int (Int.repr 10) tint) ::
                                                                    (Evar ___stringlit_5 (tarray tschar 3)) ::
                                                                    (Etempvar _buf__3 (tptr tschar)) ::
                                                                    nil)))
                                                                    (Scall None
                                                                    (Evar _free 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _buf__3 (tptr tschar)) ::
                                                                    nil))))
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _pinfotail (tptr (Tstruct _packetinfo noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sset _pinfolist
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _pinfotail (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _next
                                                                    (tptr (Tstruct _packetinfo noattr)))
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))))
                                                                    (Ssequence
                                                                    (Sset _pinfotail
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'30
                                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'31
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _new_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _pflow
                                                                    (tptr (Tstruct _flow noattr))))
                                                                    (Scall None
                                                                    (Evar _zlog 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'30 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_2 (tarray tschar 17))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func__ (tarray tschar 30)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 30) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 328) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_16 (tarray tschar 22)) ::
                                                                    (Etempvar _t'31 (tptr (Tstruct _flow noattr))) ::
                                                                    nil)))))))))))))))))))))))))))))))))))
                                                      (Sset _pindex
                                                        (Ebinop Oadd
                                                          (Etempvar _pindex tint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tint))))
                                                  (Ssequence
                                                    (Sset _pnext
                                                      (Ecast
                                                        (Econst_int (Int.repr 0) tint)
                                                        (tptr (Tstruct _packetinfo noattr))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _p
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                              (Tstruct _flow noattr))
                                                            _fecBlockHead
                                                            (tptr (Tstruct _packetinfo noattr))))
                                                        (Sloop
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop One
                                                                (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                (Ecast
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  (tptr tvoid))
                                                                tint)
                                                              Sskip
                                                              Sbreak)
                                                            (Ssequence
                                                              (Sset _pnext
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                  _next
                                                                  (tptr (Tstruct _packetinfo noattr))))
                                                              (Scall None
                                                                (Evar _packetinfo_free 
                                                                (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                                                ((Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                                 nil))))
                                                          (Sset _p
                                                            (Etempvar _pnext (tptr (Tstruct _packetinfo noattr))))))
                                                      (Ssequence
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                              (Tstruct _flow noattr))
                                                            _fecBlockHead
                                                            (tptr (Tstruct _packetinfo noattr)))
                                                          (Econst_int (Int.repr 0) tint))
                                                        (Ssequence
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                (Tstruct _flow noattr))
                                                              _fecBlockTail
                                                              (tptr (Tstruct _packetinfo noattr)))
                                                            (Econst_int (Int.repr 0) tint))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'29
                                                                (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                              (Scall None
                                                                (Evar _zlog 
                                                                (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                  tvoid
                                                                  {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                ((Etempvar _t'29 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                 (Ebinop Oadd
                                                                   (Evar ___stringlit_2 (tarray tschar 17))
                                                                   (Econst_int (Int.repr 3) tint)
                                                                   (tptr tschar)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 17) tulong)
                                                                   (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                   tulong) ::
                                                                 (Evar ___func__ (tarray tschar 30)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 30) tulong)
                                                                   (Econst_int (Int.repr 1) tint)
                                                                   tulong) ::
                                                                 (Econst_int (Int.repr 342) tint) ::
                                                                 (Econst_int (Int.repr 20) tint) ::
                                                                 (Evar ___stringlit_17 (tarray tschar 28)) ::
                                                                 nil)))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _p
                                                                  (Etempvar _pinfolist (tptr (Tstruct _packetinfo noattr))))
                                                                (Sloop
                                                                  (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'24
                                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'25
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _pflow
                                                                    (tptr (Tstruct _flow noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'26
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _flow_seq
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'27
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _blockIndex
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'28
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _isParity
                                                                    tint))
                                                                    (Scall None
                                                                    (Evar _zlog 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'24 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_2 (tarray tschar 17))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func__ (tarray tschar 30)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 30) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 344) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_18 (tarray tschar 58)) ::
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                                    (Etempvar _t'25 (tptr (Tstruct _flow noattr))) ::
                                                                    (Etempvar _t'26 tuint) ::
                                                                    (Etempvar _t'27 tint) ::
                                                                    (Etempvar _t'28 tint) ::
                                                                    nil)))))))
                                                                    (Ssequence
                                                                    (Sset _t'23
                                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall None
                                                                    (Evar _packetinfo_log 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'23 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                                    nil)))))
                                                                  (Sset _p
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _next
                                                                    (tptr (Tstruct _packetinfo noattr))))))
                                                              (Sreturn (Some (Etempvar _pinfolist (tptr (Tstruct _packetinfo noattr))))))))))))))))))))))))))))))))))))
|}.

Definition v___func____1 := {|
  gvar_info := (tarray tschar 15);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_redFecActuator := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_pinfo, (tptr (Tstruct _packetinfo noattr))) ::
                (_pbeg, (tptr (tptr (Tstruct _packetinfo noattr)))) ::
                (_pend, (tptr (tptr (Tstruct _packetinfo noattr)))) :: nil);
  fn_vars := ((_fecparams, (Tstruct _fecParams noattr)) :: nil);
  fn_temps := ((_f, (tptr (Tstruct _flow noattr))) ::
               (_prepend_pinfo, (tptr (Tstruct _packetinfo noattr))) ::
               (_pcopy, (tptr (Tstruct _packetinfo noattr))) ::
               (_p, (tptr (Tstruct _packetinfo noattr))) ::
               (_plisttail, (tptr (Tstruct _packetinfo noattr))) ::
               (_k, tint) :: (_h, tint) :: (_buf, (tptr tschar)) ::
               (_t'9, (tptr (Tstruct _deducehdr noattr))) :: (_t'8, tint) ::
               (_t'7, (tptr tschar)) :: (_t'6, tuint) :: (_t'5, tint) ::
               (_t'4, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'3, (tptr (Tstruct _packetinfo noattr))) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'100, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'99, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'98, tint) :: (_t'97, tint) :: (_t'96, tuint) ::
               (_t'95, (tptr (Tstruct _flow noattr))) ::
               (_t'94, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'93, (tptr (Tstruct _composition noattr))) ::
               (_t'92, (tptr (Tstruct _composition noattr))) ::
               (_t'91, tuint) ::
               (_t'90, (tptr (Tstruct _composition noattr))) ::
               (_t'89, tuchar) ::
               (_t'88, (tptr (Tstruct _composition noattr))) ::
               (_t'87, tuchar) :: (_t'86, tuchar) ::
               (_t'85, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'84, tuchar) :: (_t'83, tuchar) ::
               (_t'82, (tptr (Tstruct _composition noattr))) ::
               (_t'81, tuchar) :: (_t'80, tuchar) ::
               (_t'79, (tptr (Tstruct _composition noattr))) ::
               (_t'78, tuchar) :: (_t'77, tuchar) ::
               (_t'76, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'75, tint) :: (_t'74, tuchar) :: (_t'73, tuchar) ::
               (_t'72, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'71, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'70, tint) :: (_t'69, tint) :: (_t'68, tuint) ::
               (_t'67, (tptr (Tstruct _flow noattr))) ::
               (_t'66, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'65, tint) :: (_t'64, tint) ::
               (_t'63, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'62, tint) :: (_t'61, tint) ::
               (_t'60, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'59, tint) ::
               (_t'58, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'57, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'56, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'55, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'54, tint) :: (_t'53, tint) :: (_t'52, tuint) ::
               (_t'51, (tptr (Tstruct _flow noattr))) ::
               (_t'50, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'49, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'48, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'47, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'46, tint) :: (_t'45, tint) :: (_t'44, tuint) ::
               (_t'43, (tptr (Tstruct _flow noattr))) ::
               (_t'42, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'41, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'40, tint) :: (_t'39, tint) :: (_t'38, tuint) ::
               (_t'37, (tptr (Tstruct _flow noattr))) ::
               (_t'36, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'35, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'34, tint) :: (_t'33, tint) :: (_t'32, tuint) ::
               (_t'31, (tptr (Tstruct _flow noattr))) ::
               (_t'30, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'29, tint) :: (_t'28, tint) :: (_t'27, tint) ::
               (_t'26, tuint) :: (_t'25, tuchar) :: (_t'24, tuchar) ::
               (_t'23, tuchar) ::
               (_t'22, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'21, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'20, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'19, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'18, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'17, tuint) :: (_t'16, tuint) :: (_t'15, (tptr tuchar)) ::
               (_t'14, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'13, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'12, tuint) ::
               (_t'11, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'10, (tptr (Tstruct _packetinfo noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _plisttail
    (Ecast (Econst_int (Int.repr 0) tint)
      (tptr (Tstruct _packetinfo noattr))))
  (Ssequence
    (Sset _f
      (Efield
        (Ederef (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
          (Tstruct _packetinfo noattr)) _pflow (tptr (Tstruct _flow noattr))))
    (Ssequence
      (Ssequence
        (Sset _t'100
          (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
        (Scall None
          (Evar _zlog (Tfunction
                        (Tcons (tptr (Tstruct _zlog_category_s noattr))
                          (Tcons (tptr tschar)
                            (Tcons tulong
                              (Tcons (tptr tschar)
                                (Tcons tulong
                                  (Tcons tlong
                                    (Tcons tint (Tcons (tptr tschar) Tnil))))))))
                        tvoid
                        {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
          ((Etempvar _t'100 (tptr (Tstruct _zlog_category_s noattr))) ::
           (Ebinop Oadd (Evar ___stringlit_2 (tarray tschar 17))
             (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
           (Ebinop Osub (Esizeof (tarray tschar 17) tulong)
             (Ebinop Oadd (Econst_int (Int.repr 1) tint)
               (Econst_int (Int.repr 3) tint) tint) tulong) ::
           (Evar ___func____1 (tarray tschar 15)) ::
           (Ebinop Osub (Esizeof (tarray tschar 15) tulong)
             (Econst_int (Int.repr 1) tint) tulong) ::
           (Econst_int (Int.repr 393) tint) ::
           (Econst_int (Int.repr 20) tint) ::
           (Evar ___stringlit_19 (tarray tschar 26)) ::
           (Efield
             (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
               (Tstruct _flow noattr)) _tuplestr_buff (tarray tschar 128)) ::
           nil)))
      (Ssequence
        (Ssequence
          (Sset _t'99
            (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
          (Scall None
            (Evar _zlog (Tfunction
                          (Tcons (tptr (Tstruct _zlog_category_s noattr))
                            (Tcons (tptr tschar)
                              (Tcons tulong
                                (Tcons (tptr tschar)
                                  (Tcons tulong
                                    (Tcons tlong
                                      (Tcons tint (Tcons (tptr tschar) Tnil))))))))
                          tvoid
                          {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
            ((Etempvar _t'99 (tptr (Tstruct _zlog_category_s noattr))) ::
             (Ebinop Oadd (Evar ___stringlit_2 (tarray tschar 17))
               (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
             (Ebinop Osub (Esizeof (tarray tschar 17) tulong)
               (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                 (Econst_int (Int.repr 3) tint) tint) tulong) ::
             (Evar ___func____1 (tarray tschar 15)) ::
             (Ebinop Osub (Esizeof (tarray tschar 15) tulong)
               (Econst_int (Int.repr 1) tint) tulong) ::
             (Econst_int (Int.repr 396) tint) ::
             (Econst_int (Int.repr 20) tint) ::
             (Evar ___stringlit_20 (tarray tschar 25)) :: nil)))
        (Ssequence
          (Ssequence
            (Sset _p
              (Efield
                (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                  (Tstruct _flow noattr)) _fecBlockHead
                (tptr (Tstruct _packetinfo noattr))))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop One
                               (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'94
                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                  (Ssequence
                    (Sset _t'95
                      (Efield
                        (Ederef
                          (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                          (Tstruct _packetinfo noattr)) _pflow
                        (tptr (Tstruct _flow noattr))))
                    (Ssequence
                      (Sset _t'96
                        (Efield
                          (Ederef
                            (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                            (Tstruct _packetinfo noattr)) _flow_seq tuint))
                      (Ssequence
                        (Sset _t'97
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                              (Tstruct _packetinfo noattr)) _blockIndex tint))
                        (Ssequence
                          (Sset _t'98
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                (Tstruct _packetinfo noattr)) _isParity tint))
                          (Scall None
                            (Evar _zlog (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _zlog_category_s noattr))
                                            (Tcons (tptr tschar)
                                              (Tcons tulong
                                                (Tcons (tptr tschar)
                                                  (Tcons tulong
                                                    (Tcons tlong
                                                      (Tcons tint
                                                        (Tcons (tptr tschar)
                                                          Tnil)))))))) tvoid
                                          {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                            ((Etempvar _t'94 (tptr (Tstruct _zlog_category_s noattr))) ::
                             (Ebinop Oadd
                               (Evar ___stringlit_2 (tarray tschar 17))
                               (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                             (Ebinop Osub (Esizeof (tarray tschar 17) tulong)
                               (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                                 (Econst_int (Int.repr 3) tint) tint) tulong) ::
                             (Evar ___func____1 (tarray tschar 15)) ::
                             (Ebinop Osub (Esizeof (tarray tschar 15) tulong)
                               (Econst_int (Int.repr 1) tint) tulong) ::
                             (Econst_int (Int.repr 398) tint) ::
                             (Econst_int (Int.repr 20) tint) ::
                             (Evar ___stringlit_21 (tarray tschar 60)) ::
                             (Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                             (Etempvar _t'95 (tptr (Tstruct _flow noattr))) ::
                             (Etempvar _t'96 tuint) ::
                             (Etempvar _t'97 tint) ::
                             (Etempvar _t'98 tint) :: nil))))))))
              (Sset _p
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                    (Tstruct _packetinfo noattr)) _next
                  (tptr (Tstruct _packetinfo noattr))))))
          (Ssequence
            (Ssequence
              (Sset _t'93
                (Efield
                  (Ederef
                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                    (Tstruct _packetinfo noattr)) _comp
                  (tptr (Tstruct _composition noattr))))
              (Sset _k
                (Efield
                  (Ederef
                    (Etempvar _t'93 (tptr (Tstruct _composition noattr)))
                    (Tstruct _composition noattr)) _fec_k tuchar)))
            (Ssequence
              (Ssequence
                (Sset _t'92
                  (Efield
                    (Ederef
                      (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                      (Tstruct _packetinfo noattr)) _comp
                    (tptr (Tstruct _composition noattr))))
                (Sset _h
                  (Efield
                    (Ederef
                      (Etempvar _t'92 (tptr (Tstruct _composition noattr)))
                      (Tstruct _composition noattr)) _fec_h tuchar)))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                      (Tstruct _packetinfo noattr)) _fec_k tint)
                  (Etempvar _k tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                        (Tstruct _packetinfo noattr)) _fec_h tint)
                    (Etempvar _h tint))
                  (Ssequence
                    (Ssequence
                      (Sset _t'85
                        (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                      (Ssequence
                        (Sset _t'86
                          (Efield
                            (Ederef
                              (Etempvar _f (tptr (Tstruct _flow noattr)))
                              (Tstruct _flow noattr)) _fec_k tuchar))
                        (Ssequence
                          (Sset _t'87
                            (Efield
                              (Ederef
                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                (Tstruct _flow noattr)) _fec_h tuchar))
                          (Ssequence
                            (Sset _t'88
                              (Efield
                                (Ederef
                                  (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                  (Tstruct _packetinfo noattr)) _comp
                                (tptr (Tstruct _composition noattr))))
                            (Ssequence
                              (Sset _t'89
                                (Efield
                                  (Ederef
                                    (Etempvar _t'88 (tptr (Tstruct _composition noattr)))
                                    (Tstruct _composition noattr)) _fec_k
                                  tuchar))
                              (Ssequence
                                (Sset _t'90
                                  (Efield
                                    (Ederef
                                      (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                      (Tstruct _packetinfo noattr)) _comp
                                    (tptr (Tstruct _composition noattr))))
                                (Ssequence
                                  (Sset _t'91
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'90 (tptr (Tstruct _composition noattr)))
                                        (Tstruct _composition noattr)) _fec_n
                                      tuint))
                                  (Scall None
                                    (Evar _zlog (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                    (Tcons (tptr tschar)
                                                      (Tcons tulong
                                                        (Tcons (tptr tschar)
                                                          (Tcons tulong
                                                            (Tcons tlong
                                                              (Tcons tint
                                                                (Tcons
                                                                  (tptr tschar)
                                                                  Tnil))))))))
                                                  tvoid
                                                  {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                    ((Etempvar _t'85 (tptr (Tstruct _zlog_category_s noattr))) ::
                                     (Ebinop Oadd
                                       (Evar ___stringlit_2 (tarray tschar 17))
                                       (Econst_int (Int.repr 3) tint)
                                       (tptr tschar)) ::
                                     (Ebinop Osub
                                       (Esizeof (tarray tschar 17) tulong)
                                       (Ebinop Oadd
                                         (Econst_int (Int.repr 1) tint)
                                         (Econst_int (Int.repr 3) tint) tint)
                                       tulong) ::
                                     (Evar ___func____1 (tarray tschar 15)) ::
                                     (Ebinop Osub
                                       (Esizeof (tarray tschar 15) tulong)
                                       (Econst_int (Int.repr 1) tint) tulong) ::
                                     (Econst_int (Int.repr 422) tint) ::
                                     (Econst_int (Int.repr 20) tint) ::
                                     (Evar ___stringlit_22 (tarray tschar 57)) ::
                                     (Etempvar _t'86 tuchar) ::
                                     (Etempvar _t'87 tuchar) ::
                                     (Etempvar _t'89 tuchar) ::
                                     (Etempvar _t'91 tuint) :: nil)))))))))
                    (Ssequence
                      (Sset _prepend_pinfo
                        (Ecast (Econst_int (Int.repr 0) tint)
                          (tptr (Tstruct _packetinfo noattr))))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'79
                              (Efield
                                (Ederef
                                  (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                  (Tstruct _packetinfo noattr)) _comp
                                (tptr (Tstruct _composition noattr))))
                            (Ssequence
                              (Sset _t'80
                                (Efield
                                  (Ederef
                                    (Etempvar _t'79 (tptr (Tstruct _composition noattr)))
                                    (Tstruct _composition noattr)) _fec_k
                                  tuchar))
                              (Ssequence
                                (Sset _t'81
                                  (Efield
                                    (Ederef
                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                      (Tstruct _flow noattr)) _fec_k tuchar))
                                (Sifthenelse (Ebinop One
                                               (Etempvar _t'80 tuchar)
                                               (Etempvar _t'81 tuchar) tint)
                                  (Sset _t'2 (Econst_int (Int.repr 1) tint))
                                  (Ssequence
                                    (Sset _t'82
                                      (Efield
                                        (Ederef
                                          (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                          (Tstruct _packetinfo noattr)) _comp
                                        (tptr (Tstruct _composition noattr))))
                                    (Ssequence
                                      (Sset _t'83
                                        (Efield
                                          (Ederef
                                            (Etempvar _t'82 (tptr (Tstruct _composition noattr)))
                                            (Tstruct _composition noattr))
                                          _fec_h tuchar))
                                      (Ssequence
                                        (Sset _t'84
                                          (Efield
                                            (Ederef
                                              (Etempvar _f (tptr (Tstruct _flow noattr)))
                                              (Tstruct _flow noattr)) _fec_h
                                            tuchar))
                                        (Sset _t'2
                                          (Ecast
                                            (Ebinop One
                                              (Etempvar _t'83 tuchar)
                                              (Etempvar _t'84 tuchar) tint)
                                            tbool)))))))))
                          (Sifthenelse (Etempvar _t'2 tint)
                            (Ssequence
                              (Ssequence
                                (Sset _t'75
                                  (Efield
                                    (Ederef
                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                      (Tstruct _flow noattr)) _fecPacketCount
                                    tint))
                                (Sifthenelse (Ebinop Ogt
                                               (Etempvar _t'75 tint)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'76
                                        (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                      (Ssequence
                                        (Sset _t'77
                                          (Efield
                                            (Ederef
                                              (Etempvar _f (tptr (Tstruct _flow noattr)))
                                              (Tstruct _flow noattr)) _fec_k
                                            tuchar))
                                        (Ssequence
                                          (Sset _t'78
                                            (Efield
                                              (Ederef
                                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                (Tstruct _flow noattr))
                                              _fec_h tuchar))
                                          (Scall None
                                            (Evar _zlog (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _zlog_category_s noattr))
                                                            (Tcons
                                                              (tptr tschar)
                                                              (Tcons tulong
                                                                (Tcons
                                                                  (tptr tschar)
                                                                  (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                          tvoid
                                                          {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                            ((Etempvar _t'76 (tptr (Tstruct _zlog_category_s noattr))) ::
                                             (Ebinop Oadd
                                               (Evar ___stringlit_2 (tarray tschar 17))
                                               (Econst_int (Int.repr 3) tint)
                                               (tptr tschar)) ::
                                             (Ebinop Osub
                                               (Esizeof (tarray tschar 17) tulong)
                                               (Ebinop Oadd
                                                 (Econst_int (Int.repr 1) tint)
                                                 (Econst_int (Int.repr 3) tint)
                                                 tint) tulong) ::
                                             (Evar ___func____1 (tarray tschar 15)) ::
                                             (Ebinop Osub
                                               (Esizeof (tarray tschar 15) tulong)
                                               (Econst_int (Int.repr 1) tint)
                                               tulong) ::
                                             (Econst_int (Int.repr 431) tint) ::
                                             (Econst_int (Int.repr 20) tint) ::
                                             (Evar ___stringlit_23 (tarray tschar 62)) ::
                                             (Etempvar _t'77 tuchar) ::
                                             (Etempvar _t'78 tuchar) :: nil)))))
                                    (Ssequence
                                      (Scall (Some _t'1)
                                        (Evar _redFecActuator_generateParity 
                                        (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _flow noattr))
                                            (Tcons
                                              (tptr (Tstruct _packetinfo noattr))
                                              Tnil))
                                          (tptr (Tstruct _packetinfo noattr))
                                          cc_default))
                                        ((Etempvar _f (tptr (Tstruct _flow noattr))) ::
                                         (Econst_int (Int.repr 0) tint) ::
                                         nil))
                                      (Sset _prepend_pinfo
                                        (Etempvar _t'1 (tptr (Tstruct _packetinfo noattr))))))
                                  Sskip))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                      (Tstruct _flow noattr)) _fec_k tuchar)
                                  (Etempvar _k tint))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _f (tptr (Tstruct _flow noattr)))
                                        (Tstruct _flow noattr)) _fec_h
                                      tuchar) (Etempvar _h tint))
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _f (tptr (Tstruct _flow noattr)))
                                          (Tstruct _flow noattr)) _fec_n
                                        tuchar)
                                      (Ebinop Oadd (Etempvar _k tint)
                                        (Etempvar _h tint) tint))
                                    (Ssequence
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _f (tptr (Tstruct _flow noattr)))
                                            (Tstruct _flow noattr))
                                          _fecPacketCount tint)
                                        (Econst_int (Int.repr 0) tint))
                                      (Ssequence
                                        (Sset _t'72
                                          (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                        (Ssequence
                                          (Sset _t'73
                                            (Efield
                                              (Ederef
                                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                (Tstruct _flow noattr))
                                              _fec_k tuchar))
                                          (Ssequence
                                            (Sset _t'74
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _fec_n tuchar))
                                            (Scall None
                                              (Evar _zlog (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _zlog_category_s noattr))
                                                              (Tcons
                                                                (tptr tschar)
                                                                (Tcons tulong
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                            tvoid
                                                            {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                              ((Etempvar _t'72 (tptr (Tstruct _zlog_category_s noattr))) ::
                                               (Ebinop Oadd
                                                 (Evar ___stringlit_2 (tarray tschar 17))
                                                 (Econst_int (Int.repr 3) tint)
                                                 (tptr tschar)) ::
                                               (Ebinop Osub
                                                 (Esizeof (tarray tschar 17) tulong)
                                                 (Ebinop Oadd
                                                   (Econst_int (Int.repr 1) tint)
                                                   (Econst_int (Int.repr 3) tint)
                                                   tint) tulong) ::
                                               (Evar ___func____1 (tarray tschar 15)) ::
                                               (Ebinop Osub
                                                 (Esizeof (tarray tschar 15) tulong)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tulong) ::
                                               (Econst_int (Int.repr 441) tint) ::
                                               (Econst_int (Int.repr 20) tint) ::
                                               (Evar ___stringlit_24 (tarray tschar 32)) ::
                                               (Etempvar _t'73 tuchar) ::
                                               (Etempvar _t'74 tuchar) ::
                                               nil))))))))))
                            Sskip))
                        (Ssequence
                          (Ssequence
                            (Sset _t'71
                              (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                            (Scall None
                              (Evar _zlog (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _zlog_category_s noattr))
                                              (Tcons (tptr tschar)
                                                (Tcons tulong
                                                  (Tcons (tptr tschar)
                                                    (Tcons tulong
                                                      (Tcons tlong
                                                        (Tcons tint
                                                          (Tcons
                                                            (tptr tschar)
                                                            Tnil))))))))
                                            tvoid
                                            {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                              ((Etempvar _t'71 (tptr (Tstruct _zlog_category_s noattr))) ::
                               (Ebinop Oadd
                                 (Evar ___stringlit_2 (tarray tschar 17))
                                 (Econst_int (Int.repr 3) tint)
                                 (tptr tschar)) ::
                               (Ebinop Osub
                                 (Esizeof (tarray tschar 17) tulong)
                                 (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                                   (Econst_int (Int.repr 3) tint) tint)
                                 tulong) ::
                               (Evar ___func____1 (tarray tschar 15)) ::
                               (Ebinop Osub
                                 (Esizeof (tarray tschar 15) tulong)
                                 (Econst_int (Int.repr 1) tint) tulong) ::
                               (Econst_int (Int.repr 446) tint) ::
                               (Econst_int (Int.repr 20) tint) ::
                               (Evar ___stringlit_25 (tarray tschar 52)) ::
                               nil)))
                          (Ssequence
                            (Ssequence
                              (Sset _p
                                (Etempvar _prepend_pinfo (tptr (Tstruct _packetinfo noattr))))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop One
                                                 (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                 (Ecast
                                                   (Econst_int (Int.repr 0) tint)
                                                   (tptr tvoid)) tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _t'66
                                      (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                    (Ssequence
                                      (Sset _t'67
                                        (Efield
                                          (Ederef
                                            (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                            (Tstruct _packetinfo noattr))
                                          _pflow
                                          (tptr (Tstruct _flow noattr))))
                                      (Ssequence
                                        (Sset _t'68
                                          (Efield
                                            (Ederef
                                              (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                              (Tstruct _packetinfo noattr))
                                            _flow_seq tuint))
                                        (Ssequence
                                          (Sset _t'69
                                            (Efield
                                              (Ederef
                                                (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                (Tstruct _packetinfo noattr))
                                              _blockIndex tint))
                                          (Ssequence
                                            (Sset _t'70
                                              (Efield
                                                (Ederef
                                                  (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                  (Tstruct _packetinfo noattr))
                                                _isParity tint))
                                            (Scall None
                                              (Evar _zlog (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _zlog_category_s noattr))
                                                              (Tcons
                                                                (tptr tschar)
                                                                (Tcons tulong
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                            tvoid
                                                            {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                              ((Etempvar _t'66 (tptr (Tstruct _zlog_category_s noattr))) ::
                                               (Ebinop Oadd
                                                 (Evar ___stringlit_2 (tarray tschar 17))
                                                 (Econst_int (Int.repr 3) tint)
                                                 (tptr tschar)) ::
                                               (Ebinop Osub
                                                 (Esizeof (tarray tschar 17) tulong)
                                                 (Ebinop Oadd
                                                   (Econst_int (Int.repr 1) tint)
                                                   (Econst_int (Int.repr 3) tint)
                                                   tint) tulong) ::
                                               (Evar ___func____1 (tarray tschar 15)) ::
                                               (Ebinop Osub
                                                 (Esizeof (tarray tschar 15) tulong)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tulong) ::
                                               (Econst_int (Int.repr 448) tint) ::
                                               (Econst_int (Int.repr 20) tint) ::
                                               (Evar ___stringlit_26 (tarray tschar 61)) ::
                                               (Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                               (Etempvar _t'67 (tptr (Tstruct _flow noattr))) ::
                                               (Etempvar _t'68 tuint) ::
                                               (Etempvar _t'69 tint) ::
                                               (Etempvar _t'70 tint) :: nil))))))))
                                (Sset _p
                                  (Efield
                                    (Ederef
                                      (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                      (Tstruct _packetinfo noattr)) _next
                                    (tptr (Tstruct _packetinfo noattr))))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'65
                                  (Efield
                                    (Ederef
                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                      (Tstruct _flow noattr)) _fecPacketCount
                                    tint))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                      (Tstruct _packetinfo noattr))
                                    _blockIndex tint) (Etempvar _t'65 tint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'63
                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                  (Ssequence
                                    (Sset _t'64
                                      (Efield
                                        (Ederef
                                          (Etempvar _f (tptr (Tstruct _flow noattr)))
                                          (Tstruct _flow noattr))
                                        _fecPacketCount tint))
                                    (Scall None
                                      (Evar _zlog (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _zlog_category_s noattr))
                                                      (Tcons (tptr tschar)
                                                        (Tcons tulong
                                                          (Tcons
                                                            (tptr tschar)
                                                            (Tcons tulong
                                                              (Tcons tlong
                                                                (Tcons tint
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                    tvoid
                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                      ((Etempvar _t'63 (tptr (Tstruct _zlog_category_s noattr))) ::
                                       (Ebinop Oadd
                                         (Evar ___stringlit_2 (tarray tschar 17))
                                         (Econst_int (Int.repr 3) tint)
                                         (tptr tschar)) ::
                                       (Ebinop Osub
                                         (Esizeof (tarray tschar 17) tulong)
                                         (Ebinop Oadd
                                           (Econst_int (Int.repr 1) tint)
                                           (Econst_int (Int.repr 3) tint)
                                           tint) tulong) ::
                                       (Evar ___func____1 (tarray tschar 15)) ::
                                       (Ebinop Osub
                                         (Esizeof (tarray tschar 15) tulong)
                                         (Econst_int (Int.repr 1) tint)
                                         tulong) ::
                                       (Econst_int (Int.repr 457) tint) ::
                                       (Econst_int (Int.repr 20) tint) ::
                                       (Evar ___stringlit_27 (tarray tschar 54)) ::
                                       (Etempvar _t'64 tint) :: nil))))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'62
                                          (Efield
                                            (Ederef
                                              (Etempvar _f (tptr (Tstruct _flow noattr)))
                                              (Tstruct _flow noattr))
                                            _fecPacketCount tint))
                                        (Sset _t'5
                                          (Ecast
                                            (Ebinop Oadd
                                              (Etempvar _t'62 tint)
                                              (Econst_int (Int.repr 1) tint)
                                              tint) tint)))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _f (tptr (Tstruct _flow noattr)))
                                            (Tstruct _flow noattr))
                                          _fecPacketCount tint)
                                        (Etempvar _t'5 tint)))
                                    (Sifthenelse (Ebinop Oge
                                                   (Etempvar _t'5 tint)
                                                   (Etempvar _k tint) tint)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'60
                                            (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                          (Ssequence
                                            (Sset _t'61
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _fecPacketCount tint))
                                            (Scall None
                                              (Evar _zlog (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _zlog_category_s noattr))
                                                              (Tcons
                                                                (tptr tschar)
                                                                (Tcons tulong
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                            tvoid
                                                            {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                              ((Etempvar _t'60 (tptr (Tstruct _zlog_category_s noattr))) ::
                                               (Ebinop Oadd
                                                 (Evar ___stringlit_2 (tarray tschar 17))
                                                 (Econst_int (Int.repr 3) tint)
                                                 (tptr tschar)) ::
                                               (Ebinop Osub
                                                 (Esizeof (tarray tschar 17) tulong)
                                                 (Ebinop Oadd
                                                   (Econst_int (Int.repr 1) tint)
                                                   (Econst_int (Int.repr 3) tint)
                                                   tint) tulong) ::
                                               (Evar ___func____1 (tarray tschar 15)) ::
                                               (Ebinop Osub
                                                 (Esizeof (tarray tschar 15) tulong)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tulong) ::
                                               (Econst_int (Int.repr 463) tint) ::
                                               (Econst_int (Int.repr 20) tint) ::
                                               (Evar ___stringlit_29 (tarray tschar 52)) ::
                                               (Etempvar _t'61 tint) :: nil))))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'3)
                                              (Evar _redFecActuator_generateParity 
                                              (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _flow noattr))
                                                  (Tcons
                                                    (tptr (Tstruct _packetinfo noattr))
                                                    Tnil))
                                                (tptr (Tstruct _packetinfo noattr))
                                                cc_default))
                                              ((Etempvar _f (tptr (Tstruct _flow noattr))) ::
                                               (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                               nil))
                                            (Sset _pinfo
                                              (Etempvar _t'3 (tptr (Tstruct _packetinfo noattr)))))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                (Tstruct _flow noattr))
                                              _fecPacketCount tint)
                                            (Econst_int (Int.repr 0) tint))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'58
                                            (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                          (Ssequence
                                            (Sset _t'59
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _fecPacketCount tint))
                                            (Scall None
                                              (Evar _zlog (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _zlog_category_s noattr))
                                                              (Tcons
                                                                (tptr tschar)
                                                                (Tcons tulong
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                            tvoid
                                                            {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                              ((Etempvar _t'58 (tptr (Tstruct _zlog_category_s noattr))) ::
                                               (Ebinop Oadd
                                                 (Evar ___stringlit_2 (tarray tschar 17))
                                                 (Econst_int (Int.repr 3) tint)
                                                 (tptr tschar)) ::
                                               (Ebinop Osub
                                                 (Esizeof (tarray tschar 17) tulong)
                                                 (Ebinop Oadd
                                                   (Econst_int (Int.repr 1) tint)
                                                   (Econst_int (Int.repr 3) tint)
                                                   tint) tulong) ::
                                               (Evar ___func____1 (tarray tschar 15)) ::
                                               (Ebinop Osub
                                                 (Esizeof (tarray tschar 15) tulong)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tulong) ::
                                               (Econst_int (Int.repr 473) tint) ::
                                               (Econst_int (Int.repr 20) tint) ::
                                               (Evar ___stringlit_28 (tarray tschar 61)) ::
                                               (Etempvar _t'59 tint) :: nil))))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'4)
                                              (Evar _packetinfo_copyWithData 
                                              (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _packetinfo noattr))
                                                  Tnil)
                                                (tptr (Tstruct _packetinfo noattr))
                                                cc_default))
                                              ((Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                               nil))
                                            (Sset _pcopy
                                              (Etempvar _t'4 (tptr (Tstruct _packetinfo noattr)))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'56
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                    (Tstruct _flow noattr))
                                                  _fecBlockHead
                                                  (tptr (Tstruct _packetinfo noattr))))
                                              (Sifthenelse (Ebinop Oeq
                                                             (Etempvar _t'56 (tptr (Tstruct _packetinfo noattr)))
                                                             (Ecast
                                                               (Econst_int (Int.repr 0) tint)
                                                               (tptr tvoid))
                                                             tint)
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                      (Tstruct _flow noattr))
                                                    _fecBlockHead
                                                    (tptr (Tstruct _packetinfo noattr)))
                                                  (Etempvar _pcopy (tptr (Tstruct _packetinfo noattr))))
                                                (Ssequence
                                                  (Sset _t'57
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                        (Tstruct _flow noattr))
                                                      _fecBlockTail
                                                      (tptr (Tstruct _packetinfo noattr))))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t'57 (tptr (Tstruct _packetinfo noattr)))
                                                        (Tstruct _packetinfo noattr))
                                                      _next
                                                      (tptr (Tstruct _packetinfo noattr)))
                                                    (Etempvar _pcopy (tptr (Tstruct _packetinfo noattr)))))))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _fecBlockTail
                                                (tptr (Tstruct _packetinfo noattr)))
                                              (Etempvar _pcopy (tptr (Tstruct _packetinfo noattr)))))))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'55
                                        (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                      (Scall None
                                        (Evar _zlog (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _zlog_category_s noattr))
                                                        (Tcons (tptr tschar)
                                                          (Tcons tulong
                                                            (Tcons
                                                              (tptr tschar)
                                                              (Tcons tulong
                                                                (Tcons tlong
                                                                  (Tcons tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                      tvoid
                                                      {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                        ((Etempvar _t'55 (tptr (Tstruct _zlog_category_s noattr))) ::
                                         (Ebinop Oadd
                                           (Evar ___stringlit_2 (tarray tschar 17))
                                           (Econst_int (Int.repr 3) tint)
                                           (tptr tschar)) ::
                                         (Ebinop Osub
                                           (Esizeof (tarray tschar 17) tulong)
                                           (Ebinop Oadd
                                             (Econst_int (Int.repr 1) tint)
                                             (Econst_int (Int.repr 3) tint)
                                             tint) tulong) ::
                                         (Evar ___func____1 (tarray tschar 15)) ::
                                         (Ebinop Osub
                                           (Esizeof (tarray tschar 15) tulong)
                                           (Econst_int (Int.repr 1) tint)
                                           tulong) ::
                                         (Econst_int (Int.repr 486) tint) ::
                                         (Econst_int (Int.repr 20) tint) ::
                                         (Evar ___stringlit_30 (tarray tschar 56)) ::
                                         nil)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _p
                                          (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
                                        (Sloop
                                          (Ssequence
                                            (Sifthenelse (Ebinop One
                                                           (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                           (Ecast
                                                             (Econst_int (Int.repr 0) tint)
                                                             (tptr tvoid))
                                                           tint)
                                              Sskip
                                              Sbreak)
                                            (Ssequence
                                              (Sset _t'50
                                                (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                              (Ssequence
                                                (Sset _t'51
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                      (Tstruct _packetinfo noattr))
                                                    _pflow
                                                    (tptr (Tstruct _flow noattr))))
                                                (Ssequence
                                                  (Sset _t'52
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                        (Tstruct _packetinfo noattr))
                                                      _flow_seq tuint))
                                                  (Ssequence
                                                    (Sset _t'53
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                          (Tstruct _packetinfo noattr))
                                                        _blockIndex tint))
                                                    (Ssequence
                                                      (Sset _t'54
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                            (Tstruct _packetinfo noattr))
                                                          _isParity tint))
                                                      (Scall None
                                                        (Evar _zlog (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                        ((Etempvar _t'50 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                         (Ebinop Oadd
                                                           (Evar ___stringlit_2 (tarray tschar 17))
                                                           (Econst_int (Int.repr 3) tint)
                                                           (tptr tschar)) ::
                                                         (Ebinop Osub
                                                           (Esizeof (tarray tschar 17) tulong)
                                                           (Ebinop Oadd
                                                             (Econst_int (Int.repr 1) tint)
                                                             (Econst_int (Int.repr 3) tint)
                                                             tint) tulong) ::
                                                         (Evar ___func____1 (tarray tschar 15)) ::
                                                         (Ebinop Osub
                                                           (Esizeof (tarray tschar 15) tulong)
                                                           (Econst_int (Int.repr 1) tint)
                                                           tulong) ::
                                                         (Econst_int (Int.repr 488) tint) ::
                                                         (Econst_int (Int.repr 20) tint) ::
                                                         (Evar ___stringlit_26 (tarray tschar 61)) ::
                                                         (Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                         (Etempvar _t'51 (tptr (Tstruct _flow noattr))) ::
                                                         (Etempvar _t'52 tuint) ::
                                                         (Etempvar _t'53 tint) ::
                                                         (Etempvar _t'54 tint) ::
                                                         nil))))))))
                                          (Sset _p
                                            (Efield
                                              (Ederef
                                                (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                (Tstruct _packetinfo noattr))
                                              _next
                                              (tptr (Tstruct _packetinfo noattr))))))
                                      (Ssequence
                                        (Sifthenelse (Ebinop One
                                                       (Etempvar _prepend_pinfo (tptr (Tstruct _packetinfo noattr)))
                                                       (Ecast
                                                         (Econst_int (Int.repr 0) tint)
                                                         (tptr tvoid)) tint)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'49
                                                (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                              (Scall None
                                                (Evar _zlog (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _zlog_category_s noattr))
                                                                (Tcons
                                                                  (tptr tschar)
                                                                  (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                              tvoid
                                                              {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                ((Etempvar _t'49 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                 (Ebinop Oadd
                                                   (Evar ___stringlit_2 (tarray tschar 17))
                                                   (Econst_int (Int.repr 3) tint)
                                                   (tptr tschar)) ::
                                                 (Ebinop Osub
                                                   (Esizeof (tarray tschar 17) tulong)
                                                   (Ebinop Oadd
                                                     (Econst_int (Int.repr 1) tint)
                                                     (Econst_int (Int.repr 3) tint)
                                                     tint) tulong) ::
                                                 (Evar ___func____1 (tarray tschar 15)) ::
                                                 (Ebinop Osub
                                                   (Esizeof (tarray tschar 15) tulong)
                                                   (Econst_int (Int.repr 1) tint)
                                                   tulong) ::
                                                 (Econst_int (Int.repr 498) tint) ::
                                                 (Econst_int (Int.repr 20) tint) ::
                                                 (Evar ___stringlit_31 (tarray tschar 41)) ::
                                                 nil)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _p
                                                  (Etempvar _prepend_pinfo (tptr (Tstruct _packetinfo noattr))))
                                                (Sloop
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop One
                                                                   (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                   (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                   tint)
                                                      Sskip
                                                      Sbreak)
                                                    (Ssequence
                                                      (Sset _t'48
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                            (Tstruct _packetinfo noattr))
                                                          _next
                                                          (tptr (Tstruct _packetinfo noattr))))
                                                      (Sifthenelse (Ebinop Oeq
                                                                    (Etempvar _t'48 (tptr (Tstruct _packetinfo noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                        (Ssequence
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                (Tstruct _packetinfo noattr))
                                                              _next
                                                              (tptr (Tstruct _packetinfo noattr)))
                                                            (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
                                                          Sbreak)
                                                        Sskip)))
                                                  (Sset _p
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                        (Tstruct _packetinfo noattr))
                                                      _next
                                                      (tptr (Tstruct _packetinfo noattr))))))
                                              (Sset _pinfo
                                                (Etempvar _prepend_pinfo (tptr (Tstruct _packetinfo noattr))))))
                                          Sskip)
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'47
                                              (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                            (Scall None
                                              (Evar _zlog (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _zlog_category_s noattr))
                                                              (Tcons
                                                                (tptr tschar)
                                                                (Tcons tulong
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                            tvoid
                                                            {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                              ((Etempvar _t'47 (tptr (Tstruct _zlog_category_s noattr))) ::
                                               (Ebinop Oadd
                                                 (Evar ___stringlit_2 (tarray tschar 17))
                                                 (Econst_int (Int.repr 3) tint)
                                                 (tptr tschar)) ::
                                               (Ebinop Osub
                                                 (Esizeof (tarray tschar 17) tulong)
                                                 (Ebinop Oadd
                                                   (Econst_int (Int.repr 1) tint)
                                                   (Econst_int (Int.repr 3) tint)
                                                   tint) tulong) ::
                                               (Evar ___func____1 (tarray tschar 15)) ::
                                               (Ebinop Osub
                                                 (Esizeof (tarray tschar 15) tulong)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tulong) ::
                                               (Econst_int (Int.repr 508) tint) ::
                                               (Econst_int (Int.repr 20) tint) ::
                                               (Evar ___stringlit_32 (tarray tschar 23)) ::
                                               nil)))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _p
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                    (Tstruct _flow noattr))
                                                  _fecBlockHead
                                                  (tptr (Tstruct _packetinfo noattr))))
                                              (Sloop
                                                (Ssequence
                                                  (Sifthenelse (Ebinop One
                                                                 (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                 (Ecast
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   (tptr tvoid))
                                                                 tint)
                                                    Sskip
                                                    Sbreak)
                                                  (Ssequence
                                                    (Sset _t'42
                                                      (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                    (Ssequence
                                                      (Sset _t'43
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                            (Tstruct _packetinfo noattr))
                                                          _pflow
                                                          (tptr (Tstruct _flow noattr))))
                                                      (Ssequence
                                                        (Sset _t'44
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                              (Tstruct _packetinfo noattr))
                                                            _flow_seq tuint))
                                                        (Ssequence
                                                          (Sset _t'45
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                (Tstruct _packetinfo noattr))
                                                              _blockIndex
                                                              tint))
                                                          (Ssequence
                                                            (Sset _t'46
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                  (Tstruct _packetinfo noattr))
                                                                _isParity
                                                                tint))
                                                            (Scall None
                                                              (Evar _zlog 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _zlog_category_s noattr))
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                tvoid
                                                                {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                              ((Etempvar _t'42 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                               (Ebinop Oadd
                                                                 (Evar ___stringlit_2 (tarray tschar 17))
                                                                 (Econst_int (Int.repr 3) tint)
                                                                 (tptr tschar)) ::
                                                               (Ebinop Osub
                                                                 (Esizeof (tarray tschar 17) tulong)
                                                                 (Ebinop Oadd
                                                                   (Econst_int (Int.repr 1) tint)
                                                                   (Econst_int (Int.repr 3) tint)
                                                                   tint)
                                                                 tulong) ::
                                                               (Evar ___func____1 (tarray tschar 15)) ::
                                                               (Ebinop Osub
                                                                 (Esizeof (tarray tschar 15) tulong)
                                                                 (Econst_int (Int.repr 1) tint)
                                                                 tulong) ::
                                                               (Econst_int (Int.repr 510) tint) ::
                                                               (Econst_int (Int.repr 20) tint) ::
                                                               (Evar ___stringlit_26 (tarray tschar 61)) ::
                                                               (Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                               (Etempvar _t'43 (tptr (Tstruct _flow noattr))) ::
                                                               (Etempvar _t'44 tuint) ::
                                                               (Etempvar _t'45 tint) ::
                                                               (Etempvar _t'46 tint) ::
                                                               nil))))))))
                                                (Sset _p
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                      (Tstruct _packetinfo noattr))
                                                    _next
                                                    (tptr (Tstruct _packetinfo noattr))))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'41
                                                  (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                (Scall None
                                                  (Evar _zlog (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _zlog_category_s noattr))
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                tvoid
                                                                {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                  ((Etempvar _t'41 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                   (Ebinop Oadd
                                                     (Evar ___stringlit_2 (tarray tschar 17))
                                                     (Econst_int (Int.repr 3) tint)
                                                     (tptr tschar)) ::
                                                   (Ebinop Osub
                                                     (Esizeof (tarray tschar 17) tulong)
                                                     (Ebinop Oadd
                                                       (Econst_int (Int.repr 1) tint)
                                                       (Econst_int (Int.repr 3) tint)
                                                       tint) tulong) ::
                                                   (Evar ___func____1 (tarray tschar 15)) ::
                                                   (Ebinop Osub
                                                     (Esizeof (tarray tschar 15) tulong)
                                                     (Econst_int (Int.repr 1) tint)
                                                     tulong) ::
                                                   (Econst_int (Int.repr 518) tint) ::
                                                   (Econst_int (Int.repr 20) tint) ::
                                                   (Evar ___stringlit_33 (tarray tschar 18)) ::
                                                   nil)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _p
                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
                                                  (Sloop
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop One
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                        Sskip
                                                        Sbreak)
                                                      (Ssequence
                                                        (Sset _t'36
                                                          (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                        (Ssequence
                                                          (Sset _t'37
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                (Tstruct _packetinfo noattr))
                                                              _pflow
                                                              (tptr (Tstruct _flow noattr))))
                                                          (Ssequence
                                                            (Sset _t'38
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                  (Tstruct _packetinfo noattr))
                                                                _flow_seq
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'39
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                  _blockIndex
                                                                  tint))
                                                              (Ssequence
                                                                (Sset _t'40
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _isParity
                                                                    tint))
                                                                (Scall None
                                                                  (Evar _zlog 
                                                                  (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                  ((Etempvar _t'36 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                   (Ebinop Oadd
                                                                    (Evar ___stringlit_2 (tarray tschar 17))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                   (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                   (Evar ___func____1 (tarray tschar 15)) ::
                                                                   (Ebinop Osub
                                                                    (Esizeof (tarray tschar 15) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                   (Econst_int (Int.repr 520) tint) ::
                                                                   (Econst_int (Int.repr 20) tint) ::
                                                                   (Evar ___stringlit_26 (tarray tschar 61)) ::
                                                                   (Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                                   (Etempvar _t'37 (tptr (Tstruct _flow noattr))) ::
                                                                   (Etempvar _t'38 tuint) ::
                                                                   (Etempvar _t'39 tint) ::
                                                                   (Etempvar _t'40 tint) ::
                                                                   nil))))))))
                                                    (Sset _p
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                          (Tstruct _packetinfo noattr))
                                                        _next
                                                        (tptr (Tstruct _packetinfo noattr))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'35
                                                      (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                    (Scall None
                                                      (Evar _zlog (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                      ((Etempvar _t'35 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                       (Ebinop Oadd
                                                         (Evar ___stringlit_2 (tarray tschar 17))
                                                         (Econst_int (Int.repr 3) tint)
                                                         (tptr tschar)) ::
                                                       (Ebinop Osub
                                                         (Esizeof (tarray tschar 17) tulong)
                                                         (Ebinop Oadd
                                                           (Econst_int (Int.repr 1) tint)
                                                           (Econst_int (Int.repr 3) tint)
                                                           tint) tulong) ::
                                                       (Evar ___func____1 (tarray tschar 15)) ::
                                                       (Ebinop Osub
                                                         (Esizeof (tarray tschar 15) tulong)
                                                         (Econst_int (Int.repr 1) tint)
                                                         tulong) ::
                                                       (Econst_int (Int.repr 530) tint) ::
                                                       (Econst_int (Int.repr 20) tint) ::
                                                       (Evar ___stringlit_34 (tarray tschar 23)) ::
                                                       nil)))
                                                  (Ssequence
                                                    (Sset _plisttail
                                                      (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _p
                                                          (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
                                                        (Sloop
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop One
                                                                (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                (Ecast
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  (tptr tvoid))
                                                                tint)
                                                              Sskip
                                                              Sbreak)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'30
                                                                  (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                (Ssequence
                                                                  (Sset _t'31
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _pflow
                                                                    (tptr (Tstruct _flow noattr))))
                                                                  (Ssequence
                                                                    (Sset _t'32
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _flow_seq
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'33
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _blockIndex
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'34
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _isParity
                                                                    tint))
                                                                    (Scall None
                                                                    (Evar _zlog 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'30 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_2 (tarray tschar 17))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____1 (tarray tschar 15)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 15) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 534) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_26 (tarray tschar 61)) ::
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                                    (Etempvar _t'31 (tptr (Tstruct _flow noattr))) ::
                                                                    (Etempvar _t'32 tuint) ::
                                                                    (Etempvar _t'33 tint) ::
                                                                    (Etempvar _t'34 tint) ::
                                                                    nil)))))))
                                                              (Ssequence
                                                                (Sset _plisttail
                                                                  (Etempvar _p (tptr (Tstruct _packetinfo noattr))))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'29
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _fec_k
                                                                    tint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _fecparams (Tstruct _fecParams noattr))
                                                                    _fec_k
                                                                    tuchar)
                                                                    (Etempvar _t'29 tint)))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'28
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _fec_h
                                                                    tint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _fecparams (Tstruct _fecParams noattr))
                                                                    _fec_h
                                                                    tuchar)
                                                                    (Etempvar _t'28 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'27
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _blockIndex
                                                                    tint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _fecparams (Tstruct _fecParams noattr))
                                                                    _fec_seq
                                                                    tuchar)
                                                                    (Etempvar _t'27 tint)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _fecparams (Tstruct _fecParams noattr))
                                                                    _reserved
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'26
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _flow_seq
                                                                    tuint))
                                                                    (Scall (Some _t'6)
                                                                    (Evar _htonl 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Etempvar _t'26 tuint) ::
                                                                    nil)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _fecparams (Tstruct _fecParams noattr))
                                                                    _block_seq
                                                                    tuint)
                                                                    (Etempvar _t'6 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'22
                                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'23
                                                                    (Efield
                                                                    (Evar _fecparams (Tstruct _fecParams noattr))
                                                                    _fec_k
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'24
                                                                    (Efield
                                                                    (Evar _fecparams (Tstruct _fecParams noattr))
                                                                    _fec_h
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'25
                                                                    (Efield
                                                                    (Evar _fecparams (Tstruct _fecParams noattr))
                                                                    _fec_seq
                                                                    tuchar))
                                                                    (Scall None
                                                                    (Evar _zlog 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'22 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_2 (tarray tschar 17))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____1 (tarray tschar 15)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 15) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 547) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_35 (tarray tschar 56)) ::
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                                    (Etempvar _t'23 tuchar) ::
                                                                    (Etempvar _t'24 tuchar) ::
                                                                    (Etempvar _t'25 tuchar) ::
                                                                    nil))))))
                                                                    (Scall None
                                                                    (Evar _packetinfo_addAParam 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _fecparams (Tstruct _fecParams noattr))
                                                                    (tptr (Tstruct _fecParams noattr))) ::
                                                                    (Esizeof (Tstruct _fecParams noattr) tulong) ::
                                                                    nil)))))))))))
                                                          (Sset _p
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                (Tstruct _packetinfo noattr))
                                                              _next
                                                              (tptr (Tstruct _packetinfo noattr))))))
                                                      (Ssequence
                                                        (Sassign
                                                          (Ederef
                                                            (Etempvar _pbeg (tptr (tptr (Tstruct _packetinfo noattr))))
                                                            (tptr (Tstruct _packetinfo noattr)))
                                                          (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
                                                        (Ssequence
                                                          (Sassign
                                                            (Ederef
                                                              (Etempvar _pend (tptr (tptr (Tstruct _packetinfo noattr))))
                                                              (tptr (Tstruct _packetinfo noattr)))
                                                            (Etempvar _plisttail (tptr (Tstruct _packetinfo noattr))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'19
                                                                (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                              (Ssequence
                                                                (Sset _t'20
                                                                  (Ederef
                                                                    (Etempvar _pbeg (tptr (tptr (Tstruct _packetinfo noattr))))
                                                                    (tptr (Tstruct _packetinfo noattr))))
                                                                (Ssequence
                                                                  (Sset _t'21
                                                                    (Ederef
                                                                    (Etempvar _pend (tptr (tptr (Tstruct _packetinfo noattr))))
                                                                    (tptr (Tstruct _packetinfo noattr))))
                                                                  (Scall None
                                                                    (Evar _zlog 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'19 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_2 (tarray tschar 17))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____1 (tarray tschar 15)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 15) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 555) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_36 (tarray tschar 23)) ::
                                                                    (Etempvar _t'20 (tptr (Tstruct _packetinfo noattr))) ::
                                                                    (Etempvar _t'21 (tptr (Tstruct _packetinfo noattr))) ::
                                                                    nil)))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _p
                                                                  (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
                                                                (Sloop
                                                                  (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'18
                                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall (Some _t'8)
                                                                    (Evar _isUsefulLevel 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tint
                                                                    cc_default))
                                                                    ((Etempvar _t'18 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Econst_int (Int.repr 10) tint) ::
                                                                    nil)))
                                                                    (Sifthenelse (Etempvar _t'8 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'15
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _packetdata
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'16
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'17
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Scall (Some _t'7)
                                                                    (Evar _privateHexDump 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil)))
                                                                    (tptr tschar)
                                                                    {|cc_vararg:=(Some 3); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'15 (tptr tuchar)) ::
                                                                    (Etempvar _t'16 tuint) ::
                                                                    (Evar ___stringlit_37 (tarray tschar 25)) ::
                                                                    (Etempvar _t'17 tuint) ::
                                                                    (Evar ___func____1 (tarray tschar 15)) ::
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                                    nil)))))
                                                                    (Sset _buf
                                                                    (Etempvar _t'7 (tptr tschar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'14
                                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall None
                                                                    (Evar _zlog 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tlong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                                                    ((Etempvar _t'14 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_2 (tarray tschar 17))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____1 (tarray tschar 15)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 15) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 557) tint) ::
                                                                    (Econst_int (Int.repr 10) tint) ::
                                                                    (Evar ___stringlit_5 (tarray tschar 3)) ::
                                                                    (Etempvar _buf (tptr tschar)) ::
                                                                    nil)))
                                                                    (Scall None
                                                                    (Evar _free 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _buf (tptr tschar)) ::
                                                                    nil))))
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'13
                                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall None
                                                                    (Evar _packetinfo_log 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'13 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Scall (Some _t'9)
                                                                    (Evar _packetinfo_get_deducehdrFromPacket 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    Tnil)
                                                                    (tptr (Tstruct _deducehdr noattr))
                                                                    cc_default))
                                                                    ((Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sset _t'11
                                                                    (Evar _zc_redFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'12
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _deduceparamsizeWithPad
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _deducehdr_logAll 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr (Tstruct _deducehdr noattr))
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'11 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Etempvar _t'9 (tptr (Tstruct _deducehdr noattr))) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _actuatorParams
                                                                    (tarray tuchar 256)) ::
                                                                    (Etempvar _t'12 tuint) ::
                                                                    nil))))))))
                                                                  (Sset _p
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _next
                                                                    (tptr (Tstruct _packetinfo noattr))))))
                                                              (Ssequence
                                                                (Sset _t'10
                                                                  (Ederef
                                                                    (Etempvar _pbeg (tptr (tptr (Tstruct _packetinfo noattr))))
                                                                    (tptr (Tstruct _packetinfo noattr))))
                                                                (Sifthenelse 
                                                                  (Ebinop Oeq
                                                                    (Etempvar _t'10 (tptr (Tstruct _packetinfo noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                  (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                                                                  (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))))))))))))))))))))
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
   noattr ::
 Composite __12673 Struct
   (Member_plain _uh_sport tushort :: Member_plain _uh_dport tushort ::
    Member_plain _uh_ulen tushort :: Member_plain _uh_sum tushort :: nil)
   noattr ::
 Composite __12674 Struct
   (Member_plain _source tushort :: Member_plain _dest tushort ::
    Member_plain _len tushort :: Member_plain _check tushort :: nil)
   noattr ::
 Composite __12672 Union
   (Member_plain 18727075383868559167%positive (Tstruct __12673 noattr) ::
    Member_plain 19015305760020270911%positive (Tstruct __12674 noattr) ::
    nil)
   noattr ::
 Composite _udphdr Struct
   (Member_plain 18727075383868559167%positive (Tunion __12672 noattr) ::
    nil)
   noattr ::
 Composite _composition Struct
   (Member_plain _compId tint :: Member_plain _description (tptr tschar) ::
    Member_plain _fec_k tuchar :: Member_plain _fec_h tuchar ::
    Member_plain _fec_n tuint ::
    Member_plain _next (tptr (Tstruct _composition noattr)) :: nil)
   noattr ::
 Composite _deducehdr Struct
   (Member_plain _paramSize tuchar :: Member_plain _origIpProtocol tuchar ::
    Member_plain _reserved tushort :: Member_plain _origSrcIpAddr tuint ::
    Member_plain _origDstIpAddr tuint :: nil)
   noattr ::
 Composite _packetinfo Struct
   (Member_plain _queue (tptr tschar) :: Member_plain _number tint ::
    Member_plain _tuple (tptr (Tstruct _flowTuple noattr)) ::
    Member_plain _flowhash tuint ::
    Member_plain _pflow (tptr (Tstruct _flow noattr)) ::
    Member_plain _newFlow tint :: Member_plain _flow_seq tuint ::
    Member_plain _qh (tptr (Tstruct _nfq_q_handle noattr)) ::
    Member_plain _nfPacketId tuint :: Member_plain _compId tint ::
    Member_plain _comp (tptr (Tstruct _composition noattr)) ::
    Member_plain _packetdata (tptr tuchar) ::
    Member_plain _origLength tuint :: Member_plain _length tuint ::
    Member_plain _iphdrsize tuint :: Member_plain _udphdrsize tuint ::
    Member_plain _deducehdrsize tuint ::
    Member_plain _deduceparamsizeWithPad tuint ::
    Member_plain _deduceparamsizeWithoutPad tuint ::
    Member_plain _remaindersize tuint ::
    Member_plain _shim (Tstruct _deducehdr noattr) ::
    Member_plain _actuatorParams (tarray tuchar 256) ::
    Member_plain _actuatorIndex tuint :: Member_plain _origin tint ::
    Member_plain _destination tint :: Member_plain _fec_k tint ::
    Member_plain _fec_h tint :: Member_plain _isParity tint ::
    Member_plain _blockIndex tint ::
    Member_plain _next (tptr (Tstruct _packetinfo noattr)) :: nil)
   noattr ::
 Composite _fecBlock Struct
   (Member_plain _complete tint :: Member_plain _blockSeq tint ::
    Member_plain _k tint :: Member_plain _h tint ::
    Member_plain _packets (tarray (tptr (Tstruct _packetinfo noattr)) 256) ::
    Member_plain _packetCount tint :: Member_plain _timeout tdouble ::
    Member_plain _prev (tptr (Tstruct _fecBlock noattr)) ::
    Member_plain _next (tptr (Tstruct _fecBlock noattr)) :: nil)
   noattr ::
 Composite _fecParams Struct
   (Member_plain _fec_k tuchar :: Member_plain _fec_h tuchar ::
    Member_plain _fec_seq tuchar :: Member_plain _reserved tuchar ::
    Member_plain _block_seq tuint :: nil)
   noattr ::
 Composite _flowTuple Struct
   (Member_plain _ipversion tuchar :: Member_plain _protocol tuchar ::
    Member_plain _srcaddr tuint :: Member_plain _dstaddr tuint ::
    Member_plain _srcport tushort :: Member_plain _dstport tushort :: nil)
   noattr ::
 Composite _flow Struct
   (Member_plain _flowtuple (tptr (Tstruct _flowTuple noattr)) ::
    Member_plain _flowhash tuint :: Member_plain _flowid tuint ::
    Member_plain _comp (tptr (Tstruct _composition noattr)) ::
    Member_plain _flow_seq tuint :: Member_plain _fec_k tuchar ::
    Member_plain _fec_h tuchar :: Member_plain _fec_n tuchar ::
    Member_plain _fecBlockHead (tptr (Tstruct _packetinfo noattr)) ::
    Member_plain _fecBlockTail (tptr (Tstruct _packetinfo noattr)) ::
    Member_plain _fecPacketCount tint ::
    Member_plain _packetptrs (tptr (tptr tuchar)) ::
    Member_plain _packetsizes (tptr tint) ::
    Member_plain _pstat (tptr tschar) ::
    Member_plain _blockListHead (tptr (Tstruct _fecBlock noattr)) ::
    Member_plain _blockListTail (tptr (Tstruct _fecBlock noattr)) ::
    Member_plain _bpacketptrs (tptr (tptr tuchar)) ::
    Member_plain _bpacketsizes (tptr tint) ::
    Member_plain _bpstat (tptr tschar) ::
    Member_plain _next (tptr (Tstruct _flow noattr)) ::
    Member_plain _tuplestr_buff (tarray tschar 128) :: nil)
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
     cc_default)) :: (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_28, Gvar v___stringlit_28) ::
 (___stringlit_20, Gvar v___stringlit_20) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_10, Gvar v___stringlit_10) ::
 (___stringlit_34, Gvar v___stringlit_34) ::
 (___stringlit_19, Gvar v___stringlit_19) ::
 (___stringlit_15, Gvar v___stringlit_15) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_33, Gvar v___stringlit_33) ::
 (___stringlit_21, Gvar v___stringlit_21) ::
 (___stringlit_27, Gvar v___stringlit_27) ::
 (___stringlit_31, Gvar v___stringlit_31) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_14, Gvar v___stringlit_14) ::
 (___stringlit_22, Gvar v___stringlit_22) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_25, Gvar v___stringlit_25) ::
 (___stringlit_29, Gvar v___stringlit_29) ::
 (___stringlit_11, Gvar v___stringlit_11) ::
 (___stringlit_13, Gvar v___stringlit_13) ::
 (___stringlit_35, Gvar v___stringlit_35) ::
 (___stringlit_36, Gvar v___stringlit_36) ::
 (___stringlit_18, Gvar v___stringlit_18) ::
 (___stringlit_30, Gvar v___stringlit_30) ::
 (___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_17, Gvar v___stringlit_17) ::
 (___stringlit_23, Gvar v___stringlit_23) ::
 (___stringlit_24, Gvar v___stringlit_24) ::
 (___stringlit_26, Gvar v___stringlit_26) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_12, Gvar v___stringlit_12) ::
 (___stringlit_32, Gvar v___stringlit_32) ::
 (___stringlit_37, Gvar v___stringlit_37) ::
 (___stringlit_16, Gvar v___stringlit_16) ::
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
 (_calloc,
   Gfun(External (EF_external "calloc"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___assert_fail,
   Gfun(External (EF_external "__assert_fail"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tschar)
       (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
     cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil)))
     (tptr tvoid) cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid)
     cc_default)) ::
 (_htonl,
   Gfun(External (EF_external "htonl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (_htons,
   Gfun(External (EF_external "htons"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (_zlog,
   Gfun(External (EF_external "zlog"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tvoid
                     {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct _zlog_category_s noattr))
       (Tcons (tptr tschar)
         (Tcons tulong
           (Tcons (tptr tschar)
             (Tcons tulong
               (Tcons tlong (Tcons tint (Tcons (tptr tschar) Tnil))))))))
     tvoid {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|})) ::
 (_privateHexDump,
   Gfun(External (EF_external "privateHexDump"
                   (mksignature (AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tlong
                     {|cc_vararg:=(Some 3); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tuchar) (Tcons tuint (Tcons (tptr tschar) Tnil)))
     (tptr tschar)
     {|cc_vararg:=(Some 3); cc_unproto:=false; cc_structret:=false|})) ::
 (_isUsefulLevel,
   Gfun(External (EF_external "isUsefulLevel"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (Tstruct _zlog_category_s noattr)) (Tcons tint Tnil)) tint
     cc_default)) ::
 (_deducehdr_logAll,
   Gfun(External (EF_external "deducehdr_logAll"
                   (mksignature
                     (AST.Tlong :: AST.Tint :: AST.Tlong :: AST.Tlong ::
                      AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _zlog_category_s noattr))
       (Tcons tint
         (Tcons (tptr (Tstruct _deducehdr noattr))
           (Tcons (tptr tuchar) (Tcons tuint Tnil))))) tvoid cc_default)) ::
 (_packetinfo_free,
   Gfun(External (EF_external "packetinfo_free"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _packetinfo noattr)) Tnil) tvoid cc_default)) ::
 (_packetinfo_copyWithData,
   Gfun(External (EF_external "packetinfo_copyWithData"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr (Tstruct _packetinfo noattr)) Tnil)
     (tptr (Tstruct _packetinfo noattr)) cc_default)) ::
 (_packetinfo_get_deducehdrFromPacket,
   Gfun(External (EF_external "packetinfo_get_deducehdrFromPacket"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr (Tstruct _packetinfo noattr)) Tnil)
     (tptr (Tstruct _deducehdr noattr)) cc_default)) ::
 (_packetinfo_addAParam,
   Gfun(External (EF_external "packetinfo_addAParam"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _packetinfo noattr))
       (Tcons (tptr tvoid) (Tcons tulong Tnil))) tvoid cc_default)) ::
 (_packetinfo_log,
   Gfun(External (EF_external "packetinfo_log"
                   (mksignature (AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _zlog_category_s noattr))
       (Tcons tint (Tcons (tptr (Tstruct _packetinfo noattr)) Tnil))) tvoid
     cc_default)) ::
 (_fecCommon_maskHeader,
   Gfun(External (EF_external "fecCommon_maskHeader"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _ip noattr)) Tnil) tvoid cc_default)) ::
 (_rse_init,
   Gfun(External (EF_external "rse_init"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (_rse_code,
   Gfun(External (EF_external "rse_code"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tint
       (Tcons tint
         (Tcons tint
           (Tcons (tptr (tptr tuchar))
             (Tcons (tptr tint) (Tcons (tptr tschar) Tnil)))))) tint
     cc_default)) :: (_zc_redFec, Gvar v_zc_redFec) ::
 (_redFecActuator_init, Gfun(Internal f_redFecActuator_init)) ::
 (___func__, Gvar v___func__) ::
 (_redFecActuator_generateParity, Gfun(Internal f_redFecActuator_generateParity)) ::
 (___func____1, Gvar v___func____1) ::
 (_redFecActuator, Gfun(Internal f_redFecActuator)) :: nil).

Definition public_idents : list ident :=
(_redFecActuator :: _redFecActuator_generateParity :: _redFecActuator_init ::
 _zc_redFec :: _rse_code :: _rse_init :: _fecCommon_maskHeader ::
 _packetinfo_log :: _packetinfo_addAParam ::
 _packetinfo_get_deducehdrFromPacket :: _packetinfo_copyWithData ::
 _packetinfo_free :: _deducehdr_logAll :: _isUsefulLevel ::
 _privateHexDump :: _zlog :: _htons :: _htonl :: _memset :: _memcpy ::
 ___assert_fail :: _free :: _calloc :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


