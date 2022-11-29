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
  Definition source_file := "fecBlock.c".
  Definition normalized := true.
End Info.

Definition _RETURN : ident := $"RETURN".
Definition __2163 : ident := $"_2163".
Definition __2164 : ident := $"_2164".
Definition __2165 : ident := $"_2165".
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
Definition _actuatorIndex : ident := $"actuatorIndex".
Definition _actuatorParams : ident := $"actuatorParams".
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
Definition _calloc : ident := $"calloc".
Definition _check : ident := $"check".
Definition _comp : ident := $"comp".
Definition _compId : ident := $"compId".
Definition _complete : ident := $"complete".
Definition _composition : ident := $"composition".
Definition _currTime : ident := $"currTime".
Definition _currblock : ident := $"currblock".
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
Definition _fec_h : ident := $"fec_h".
Definition _fec_k : ident := $"fec_k".
Definition _fec_n : ident := $"fec_n".
Definition _fec_seq : ident := $"fec_seq".
Definition _fecblock : ident := $"fecblock".
Definition _fecblocknext : ident := $"fecblocknext".
Definition _fecparams : ident := $"fecparams".
Definition _flow : ident := $"flow".
Definition _flowSeq : ident := $"flowSeq".
Definition _flowTuple : ident := $"flowTuple".
Definition _flowTuple_log : ident := $"flowTuple_log".
Definition _flow_seq : ident := $"flow_seq".
Definition _flowhash : ident := $"flowhash".
Definition _flowid : ident := $"flowid".
Definition _flowtuple : ident := $"flowtuple".
Definition _free : ident := $"free".
Definition _h : ident := $"h".
Definition _htons : ident := $"htons".
Definition _i : ident := $"i".
Definition _in_addr : ident := $"in_addr".
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
Definition _k : ident := $"k".
Definition _len : ident := $"len".
Definition _length : ident := $"length".
Definition _main : ident := $"main".
Definition _maxn : ident := $"maxn".
Definition _maxpacketsize : ident := $"maxpacketsize".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
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
Definition _pend : ident := $"pend".
Definition _pflow : ident := $"pflow".
Definition _pindex : ident := $"pindex".
Definition _pinfo : ident := $"pinfo".
Definition _plist : ident := $"plist".
Definition _plisttail : ident := $"plisttail".
Definition _prev : ident := $"prev".
Definition _privateHexDump : ident := $"privateHexDump".
Definition _protocol : ident := $"protocol".
Definition _pstat : ident := $"pstat".
Definition _qh : ident := $"qh".
Definition _queue : ident := $"queue".
Definition _remaindersize : ident := $"remaindersize".
Definition _reserved : ident := $"reserved".
Definition _returnlist : ident := $"returnlist".
Definition _rse_code : ident := $"rse_code".
Definition _rse_init : ident := $"rse_init".
Definition _s_addr : ident := $"s_addr".
Definition _shim : ident := $"shim".
Definition _size : ident := $"size".
Definition _source : ident := $"source".
Definition _srcaddr : ident := $"srcaddr".
Definition _srcport : ident := $"srcport".
Definition _tempBuffer : ident := $"tempBuffer".
Definition _tempLength : ident := $"tempLength".
Definition _timeout : ident := $"timeout".
Definition _tuple : ident := $"tuple".
Definition _tuplestr_buff : ident := $"tuplestr_buff".
Definition _udph : ident := $"udph".
Definition _udphdr : ident := $"udphdr".
Definition _udphdrsize : ident := $"udphdrsize".
Definition _udplen : ident := $"udplen".
Definition _uh_dport : ident := $"uh_dport".
Definition _uh_sport : ident := $"uh_sport".
Definition _uh_sum : ident := $"uh_sum".
Definition _uh_ulen : ident := $"uh_ulen".
Definition _util_getCurrentTime : ident := $"util_getCurrentTime".
Definition _zc_blackFec : ident := $"zc_blackFec".
Definition _zc_blackFec__1 : ident := $"zc_blackFec__1".
Definition _zlog : ident := $"zlog".
Definition _zlog_category_s : ident := $"zlog_category_s".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 47);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 38);
  gvar_init := (Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 29);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 12);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 31);
  gvar_init := (Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_zc_blackFec := {|
  gvar_info := (tptr (Tstruct _zlog_category_s noattr));
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_fecBlock_new := {|
  fn_return := (tptr (Tstruct _fecBlock noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_fecblock, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _calloc (Tfunction (Tcons tulong (Tcons tulong Tnil))
                      (tptr tvoid) cc_default))
      ((Econst_int (Int.repr 1) tint) ::
       (Esizeof (Tstruct _fecBlock noattr) tulong) :: nil))
    (Sset _fecblock
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _fecBlock noattr)))))
  (Sreturn (Some (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))))))
|}.

Definition v___func__ := {|
  gvar_info := (tarray tschar 14);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_fecBlock_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fecblock, (tptr (Tstruct _fecBlock noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'11, tint) :: (_t'10, (tptr tuchar)) ::
               (_t'9, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'8, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'7, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'6, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'5, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'4, (tptr (Tstruct _packetinfo noattr))) :: (_t'3, tint) ::
               (_t'2, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'1, (tptr (Tstruct _packetinfo noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _t'11
            (Efield
              (Ederef (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                (Tstruct _fecBlock noattr)) _packetCount tint))
          (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _t'11 tint)
                         tint)
            Sskip
            Sbreak))
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                    (Tstruct _fecBlock noattr)) _packets
                  (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                (Etempvar _i tint)
                (tptr (tptr (Tstruct _packetinfo noattr))))
              (tptr (Tstruct _packetinfo noattr))))
          (Sifthenelse (Ebinop One
                         (Etempvar _t'1 (tptr (Tstruct _packetinfo noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Ssequence
              (Ssequence
                (Sset _t'7
                  (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                (Ssequence
                  (Sset _t'8
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                            (Tstruct _fecBlock noattr)) _packets
                          (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                        (Etempvar _i tint)
                        (tptr (tptr (Tstruct _packetinfo noattr))))
                      (tptr (Tstruct _packetinfo noattr))))
                  (Ssequence
                    (Sset _t'9
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                              (Tstruct _fecBlock noattr)) _packets
                            (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                          (Etempvar _i tint)
                          (tptr (tptr (Tstruct _packetinfo noattr))))
                        (tptr (Tstruct _packetinfo noattr))))
                    (Ssequence
                      (Sset _t'10
                        (Efield
                          (Ederef
                            (Etempvar _t'9 (tptr (Tstruct _packetinfo noattr)))
                            (Tstruct _packetinfo noattr)) _packetdata
                          (tptr tuchar)))
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
                        ((Etempvar _t'7 (tptr (Tstruct _zlog_category_s noattr))) ::
                         (Ebinop Oadd
                           (Evar ___stringlit_2 (tarray tschar 11))
                           (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                         (Ebinop Osub (Esizeof (tarray tschar 11) tulong)
                           (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                             (Econst_int (Int.repr 3) tint) tint) tulong) ::
                         (Evar ___func__ (tarray tschar 14)) ::
                         (Ebinop Osub (Esizeof (tarray tschar 14) tulong)
                           (Econst_int (Int.repr 1) tint) tulong) ::
                         (Econst_int (Int.repr 78) tint) ::
                         (Econst_int (Int.repr 20) tint) ::
                         (Evar ___stringlit_1 (tarray tschar 47)) ::
                         (Etempvar _t'8 (tptr (Tstruct _packetinfo noattr))) ::
                         (Etempvar _t'10 (tptr tuchar)) :: nil))))))
              (Ssequence
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                            (Tstruct _fecBlock noattr)) _packets
                          (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                        (Etempvar _i tint)
                        (tptr (tptr (Tstruct _packetinfo noattr))))
                      (tptr (Tstruct _packetinfo noattr))))
                  (Ssequence
                    (Sset _t'3
                      (Efield
                        (Ederef
                          (Etempvar _t'2 (tptr (Tstruct _packetinfo noattr)))
                          (Tstruct _packetinfo noattr)) _isParity tint))
                    (Sifthenelse (Etempvar _t'3 tint)
                      (Ssequence
                        (Sset _t'6
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                  (Tstruct _fecBlock noattr)) _packets
                                (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                              (Etempvar _i tint)
                              (tptr (tptr (Tstruct _packetinfo noattr))))
                            (tptr (Tstruct _packetinfo noattr))))
                        (Scall None
                          (Evar _packetinfo_free (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _packetinfo noattr))
                                                     Tnil) tvoid cc_default))
                          ((Etempvar _t'6 (tptr (Tstruct _packetinfo noattr))) ::
                           nil)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'5
                            (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                            ((Etempvar _t'5 (tptr (Tstruct _zlog_category_s noattr))) ::
                             (Ebinop Oadd
                               (Evar ___stringlit_2 (tarray tschar 11))
                               (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                             (Ebinop Osub (Esizeof (tarray tschar 11) tulong)
                               (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                                 (Econst_int (Int.repr 3) tint) tint) tulong) ::
                             (Evar ___func__ (tarray tschar 14)) ::
                             (Ebinop Osub (Esizeof (tarray tschar 14) tulong)
                               (Econst_int (Int.repr 1) tint) tulong) ::
                             (Econst_int (Int.repr 94) tint) ::
                             (Econst_int (Int.repr 20) tint) ::
                             (Evar ___stringlit_3 (tarray tschar 29)) :: nil)))
                        (Ssequence
                          (Sset _t'4
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                    (Tstruct _fecBlock noattr)) _packets
                                  (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                (Etempvar _i tint)
                                (tptr (tptr (Tstruct _packetinfo noattr))))
                              (tptr (Tstruct _packetinfo noattr))))
                          (Scall None
                            (Evar _packetinfo_free (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _packetinfo noattr))
                                                       Tnil) tvoid
                                                     cc_default))
                            ((Etempvar _t'4 (tptr (Tstruct _packetinfo noattr))) ::
                             nil)))))))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                          (Tstruct _fecBlock noattr)) _packets
                        (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                      (Etempvar _i tint)
                      (tptr (tptr (Tstruct _packetinfo noattr))))
                    (tptr (Tstruct _packetinfo noattr)))
                  (Econst_int (Int.repr 0) tint))))
            Sskip)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))) :: nil))
    (Sreturn None)))
|}.

Definition v___func____1 := {|
  gvar_info := (tarray tschar 13);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_fecBlock_log := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_zc_blackFec__1, (tptr (Tstruct _zlog_category_s noattr))) ::
                (_fecblock, (tptr (Tstruct _fecBlock noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'8, tint) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tdouble) :: (_t'3, tint) ::
               (_t'2, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'1, (tptr (Tstruct _fecBlock noattr))) :: nil);
  fn_body :=
(Ssequence
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
    ((Etempvar _zc_blackFec__1 (tptr (Tstruct _zlog_category_s noattr))) ::
     (Ebinop Oadd (Evar ___stringlit_2 (tarray tschar 11))
       (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
     (Ebinop Osub (Esizeof (tarray tschar 11) tulong)
       (Ebinop Oadd (Econst_int (Int.repr 1) tint)
         (Econst_int (Int.repr 3) tint) tint) tulong) ::
     (Evar ___func____1 (tarray tschar 13)) ::
     (Ebinop Osub (Esizeof (tarray tschar 13) tulong)
       (Econst_int (Int.repr 1) tint) tulong) ::
     (Econst_int (Int.repr 117) tint) :: (Econst_int (Int.repr 20) tint) ::
     (Evar ___stringlit_4 (tarray tschar 12)) ::
     (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))) :: nil))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn None)
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
              (Tstruct _fecBlock noattr)) _complete tint))
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                (Tstruct _fecBlock noattr)) _blockSeq tint))
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef
                  (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                  (Tstruct _fecBlock noattr)) _k tint))
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef
                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                    (Tstruct _fecBlock noattr)) _h tint))
              (Scall None
                (Evar _zlog (Tfunction
                              (Tcons (tptr (Tstruct _zlog_category_s noattr))
                                (Tcons (tptr tschar)
                                  (Tcons tulong
                                    (Tcons (tptr tschar)
                                      (Tcons tulong
                                        (Tcons tlong
                                          (Tcons tint
                                            (Tcons (tptr tschar) Tnil))))))))
                              tvoid
                              {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                ((Etempvar _zc_blackFec__1 (tptr (Tstruct _zlog_category_s noattr))) ::
                 (Ebinop Oadd (Evar ___stringlit_2 (tarray tschar 11))
                   (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                 (Ebinop Osub (Esizeof (tarray tschar 11) tulong)
                   (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                     (Econst_int (Int.repr 3) tint) tint) tulong) ::
                 (Evar ___func____1 (tarray tschar 13)) ::
                 (Ebinop Osub (Esizeof (tarray tschar 13) tulong)
                   (Econst_int (Int.repr 1) tint) tulong) ::
                 (Econst_int (Int.repr 121) tint) ::
                 (Econst_int (Int.repr 20) tint) ::
                 (Evar ___stringlit_5 (tarray tschar 38)) ::
                 (Etempvar _t'5 tint) :: (Etempvar _t'6 tint) ::
                 (Etempvar _t'7 tint) :: (Etempvar _t'8 tint) :: nil))))))
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                (Tstruct _fecBlock noattr)) _packetCount tint))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef
                  (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                  (Tstruct _fecBlock noattr)) _timeout tdouble))
            (Scall None
              (Evar _zlog (Tfunction
                            (Tcons (tptr (Tstruct _zlog_category_s noattr))
                              (Tcons (tptr tschar)
                                (Tcons tulong
                                  (Tcons (tptr tschar)
                                    (Tcons tulong
                                      (Tcons tlong
                                        (Tcons tint
                                          (Tcons (tptr tschar) Tnil))))))))
                            tvoid
                            {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
              ((Etempvar _zc_blackFec__1 (tptr (Tstruct _zlog_category_s noattr))) ::
               (Ebinop Oadd (Evar ___stringlit_2 (tarray tschar 11))
                 (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
               (Ebinop Osub (Esizeof (tarray tschar 11) tulong)
                 (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                   (Econst_int (Int.repr 3) tint) tint) tulong) ::
               (Evar ___func____1 (tarray tschar 13)) ::
               (Ebinop Osub (Esizeof (tarray tschar 13) tulong)
                 (Econst_int (Int.repr 1) tint) tulong) ::
               (Econst_int (Int.repr 124) tint) ::
               (Econst_int (Int.repr 20) tint) ::
               (Evar ___stringlit_6 (tarray tschar 31)) ::
               (Etempvar _t'3 tint) :: (Etempvar _t'4 tdouble) :: nil))))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef
                  (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                  (Tstruct _fecBlock noattr)) _prev
                (tptr (Tstruct _fecBlock noattr))))
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef
                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                    (Tstruct _fecBlock noattr)) _next
                  (tptr (Tstruct _fecBlock noattr))))
              (Scall None
                (Evar _zlog (Tfunction
                              (Tcons (tptr (Tstruct _zlog_category_s noattr))
                                (Tcons (tptr tschar)
                                  (Tcons tulong
                                    (Tcons (tptr tschar)
                                      (Tcons tulong
                                        (Tcons tlong
                                          (Tcons tint
                                            (Tcons (tptr tschar) Tnil))))))))
                              tvoid
                              {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                ((Etempvar _zc_blackFec__1 (tptr (Tstruct _zlog_category_s noattr))) ::
                 (Ebinop Oadd (Evar ___stringlit_2 (tarray tschar 11))
                   (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                 (Ebinop Osub (Esizeof (tarray tschar 11) tulong)
                   (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                     (Econst_int (Int.repr 3) tint) tint) tulong) ::
                 (Evar ___func____1 (tarray tschar 13)) ::
                 (Ebinop Osub (Esizeof (tarray tschar 13) tulong)
                   (Econst_int (Int.repr 1) tint) tulong) ::
                 (Econst_int (Int.repr 126) tint) ::
                 (Econst_int (Int.repr 20) tint) ::
                 (Evar ___stringlit_7 (tarray tschar 18)) ::
                 (Etempvar _t'1 (tptr (Tstruct _fecBlock noattr))) ::
                 (Etempvar _t'2 (tptr (Tstruct _fecBlock noattr))) :: nil))))
          (Sreturn None))))))
|}.

Definition composites : list composite_definition :=
(Composite _composition Struct
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
     cc_default)) :: (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
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
 (_packetinfo_free,
   Gfun(External (EF_external "packetinfo_free"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _packetinfo noattr)) Tnil) tvoid cc_default)) ::
 (_zc_blackFec, Gvar v_zc_blackFec) ::
 (_fecBlock_new, Gfun(Internal f_fecBlock_new)) ::
 (___func__, Gvar v___func__) ::
 (_fecBlock_free, Gfun(Internal f_fecBlock_free)) ::
 (___func____1, Gvar v___func____1) ::
 (_fecBlock_log, Gfun(Internal f_fecBlock_log)) :: nil).

Definition public_idents : list ident :=
(_fecBlock_log :: _fecBlock_free :: _fecBlock_new :: _zc_blackFec ::
 _packetinfo_free :: _zlog :: _free :: _calloc :: ___builtin_debug ::
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


