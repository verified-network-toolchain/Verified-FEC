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
  Definition source_file := "blackFecActuator.c".
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
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
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

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 3);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_27 := {|
  gvar_info := (tarray tschar 40);
  gvar_init := (Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 37);
  gvar_init := (Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_48 := {|
  gvar_info := (tarray tschar 45);
  gvar_init := (Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_39 := {|
  gvar_info := (tarray tschar 24);
  gvar_init := (Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_61 := {|
  gvar_info := (tarray tschar 36);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_44 := {|
  gvar_info := (tarray tschar 72);
  gvar_init := (Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_14 := {|
  gvar_info := (tarray tschar 42);
  gvar_init := (Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_15 := {|
  gvar_info := (tarray tschar 36);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_52 := {|
  gvar_info := (tarray tschar 47);
  gvar_init := (Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_65 := {|
  gvar_info := (tarray tschar 28);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_31 := {|
  gvar_info := (tarray tschar 43);
  gvar_init := (Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_64 := {|
  gvar_info := (tarray tschar 32);
  gvar_init := (Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_32 := {|
  gvar_info := (tarray tschar 38);
  gvar_init := (Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_41 := {|
  gvar_info := (tarray tschar 61);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_42 := {|
  gvar_info := (tarray tschar 57);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_49 := {|
  gvar_info := (tarray tschar 37);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 39) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_28 := {|
  gvar_info := (tarray tschar 68);
  gvar_init := (Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_57 := {|
  gvar_info := (tarray tschar 48);
  gvar_init := (Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_46 := {|
  gvar_info := (tarray tschar 33);
  gvar_init := (Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_36 := {|
  gvar_info := (tarray tschar 68);
  gvar_init := (Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_20 := {|
  gvar_info := (tarray tschar 75);
  gvar_init := (Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
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
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 112) ::
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

Definition v___stringlit_47 := {|
  gvar_info := (tarray tschar 46);
  gvar_init := (Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 87) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_59 := {|
  gvar_info := (tarray tschar 59);
  gvar_init := (Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 79) ::
                Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_17 := {|
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

Definition v___stringlit_51 := {|
  gvar_info := (tarray tschar 24);
  gvar_init := (Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_66 := {|
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
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 32) ::
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

Definition v___stringlit_9 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_56 := {|
  gvar_info := (tarray tschar 53);
  gvar_init := (Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 39) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_43 := {|
  gvar_info := (tarray tschar 26);
  gvar_init := (Init_int8 (Int.repr 42) :: Init_int8 (Int.repr 42) ::
                Init_int8 (Int.repr 42) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_55 := {|
  gvar_info := (tarray tschar 36);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 70) ::
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

Definition v___stringlit_23 := {|
  gvar_info := (tarray tschar 52);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_13 := {|
  gvar_info := (tarray tschar 38);
  gvar_init := (Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 50);
  gvar_init := (Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_60 := {|
  gvar_info := (tarray tschar 35);
  gvar_init := (Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_62 := {|
  gvar_info := (tarray tschar 36);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 26);
  gvar_init := (Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_24 := {|
  gvar_info := (tarray tschar 23);
  gvar_init := (Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_29 := {|
  gvar_info := (tarray tschar 53);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_58 := {|
  gvar_info := (tarray tschar 25);
  gvar_init := (Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_45 := {|
  gvar_info := (tarray tschar 60);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 27);
  gvar_init := (Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_54 := {|
  gvar_info := (tarray tschar 20);
  gvar_init := (Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 64);
  gvar_init := (Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_35 := {|
  gvar_info := (tarray tschar 32);
  gvar_init := (Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_34 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_63 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_21 := {|
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
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_25 := {|
  gvar_info := (tarray tschar 54);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_50 := {|
  gvar_info := (tarray tschar 32);
  gvar_init := (Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_38 := {|
  gvar_info := (tarray tschar 48);
  gvar_init := (Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_12 := {|
  gvar_info := (tarray tschar 32);
  gvar_init := (Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_19 := {|
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

Definition v___stringlit_16 := {|
  gvar_info := (tarray tschar 47);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_26 := {|
  gvar_info := (tarray tschar 60);
  gvar_init := (Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_40 := {|
  gvar_info := (tarray tschar 53);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_33 := {|
  gvar_info := (tarray tschar 37);
  gvar_init := (Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_37 := {|
  gvar_info := (tarray tschar 63);
  gvar_init := (Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_30 := {|
  gvar_info := (tarray tschar 73);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 46);
  gvar_init := (Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_11 := {|
  gvar_info := (tarray tschar 10);
  gvar_init := (Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_10 := {|
  gvar_info := (tarray tschar 27);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_53 := {|
  gvar_info := (tarray tschar 27);
  gvar_init := (Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_22 := {|
  gvar_info := (tarray tschar 37);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_18 := {|
  gvar_info := (tarray tschar 68);
  gvar_init := (Init_int8 (Int.repr 91) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 93) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_outstring := {|
  gvar_info := (tarray tschar 1024);
  gvar_init := (Init_space 1024 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_zc_blackFec := {|
  gvar_info := (tptr (Tstruct _zlog_category_s noattr));
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_blackFecActuator_init := {|
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
  gvar_info := (tarray tschar 26);
  gvar_init := (Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_blackFecActuator_unDeduce := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_packetdata, (tptr tuchar)) :: (_length, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_dhdr, (tptr (Tstruct _deducehdr noattr))) ::
               (_newpacket, (tptr tuchar)) :: (_newlength, tushort) ::
               (_ipheader, (tptr (Tstruct _ip noattr))) ::
               (_udph, (tptr (Tstruct _udphdr noattr))) ::
               (_bufptr, (tptr tuchar)) :: (_nbufptr, (tptr tuchar)) ::
               (_iphl, tuint) :: (_size, tuint) :: (_srcport, tushort) ::
               (_dstport, tushort) :: (_iplen, tushort) ::
               (_udplen, tushort) :: (_buf, (tptr tschar)) ::
               (_buf__1, (tptr tschar)) :: (_t'12, (tptr tvoid)) ::
               (_t'11, tint) :: (_t'10, (tptr tschar)) :: (_t'9, tushort) ::
               (_t'8, (tptr tuchar)) :: (_t'7, (tptr tvoid)) ::
               (_t'6, tushort) :: (_t'5, tushort) :: (_t'4, tushort) ::
               (_t'3, tushort) :: (_t'2, tint) :: (_t'1, (tptr tschar)) ::
               (_t'25, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'24, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'23, tuchar) :: (_t'22, tint) :: (_t'21, tushort) ::
               (_t'20, tushort) :: (_t'19, tushort) :: (_t'18, tushort) ::
               (_t'17, tuint) :: (_t'16, tuint) :: (_t'15, tuchar) ::
               (_t'14, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'13, (tptr (Tstruct _zlog_category_s noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sloop
    (Ssequence
      (Ssequence
        (Sset _t'25
          (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
        (Scall (Some _t'2)
          (Evar _isUsefulLevel (Tfunction
                                 (Tcons
                                   (tptr (Tstruct _zlog_category_s noattr))
                                   (Tcons tint Tnil)) tint cc_default))
          ((Etempvar _t'25 (tptr (Tstruct _zlog_category_s noattr))) ::
           (Econst_int (Int.repr 20) tint) :: nil)))
      (Sifthenelse (Etempvar _t'2 tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _privateHexDump (Tfunction
                                      (Tcons (tptr tuchar)
                                        (Tcons tuint
                                          (Tcons (tptr tschar) Tnil)))
                                      (tptr tschar)
                                      {|cc_vararg:=(Some 3); cc_unproto:=false; cc_structret:=false|}))
              ((Etempvar _packetdata (tptr tuchar)) ::
               (Etempvar _length tint) ::
               (Evar ___stringlit_1 (tarray tschar 26)) ::
               (Etempvar _length tint) :: nil))
            (Sset _buf (Etempvar _t'1 (tptr tschar))))
          (Ssequence
            (Ssequence
              (Sset _t'24
                (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                ((Etempvar _t'24 (tptr (Tstruct _zlog_category_s noattr))) ::
                 (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
                   (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                 (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                   (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                     (Econst_int (Int.repr 3) tint) tint) tulong) ::
                 (Evar ___func__ (tarray tschar 26)) ::
                 (Ebinop Osub (Esizeof (tarray tschar 26) tulong)
                   (Econst_int (Int.repr 1) tint) tulong) ::
                 (Econst_int (Int.repr 116) tint) ::
                 (Econst_int (Int.repr 20) tint) ::
                 (Evar ___stringlit_2 (tarray tschar 3)) ::
                 (Etempvar _buf (tptr tschar)) :: nil)))
            (Scall None
              (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
              ((Etempvar _buf (tptr tschar)) :: nil))))
        Sskip))
    Sbreak)
  (Ssequence
    (Sset _bufptr (Etempvar _packetdata (tptr tuchar)))
    (Ssequence
      (Sset _ipheader
        (Ecast (Etempvar _bufptr (tptr tuchar)) (tptr (Tstruct _ip noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'23
            (Efield
              (Ederef (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                (Tstruct _ip noattr)) _ip_p tuchar))
          (Sifthenelse (Ebinop One (Etempvar _t'23 tuchar)
                         (Econst_int (Int.repr 17) tint) tint)
            (Sgoto _no_deducehdr)
            Sskip))
        (Ssequence
          (Ssequence
            (Sset _t'22
              (Efield
                (Ederef (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                  (Tstruct _ip noattr)) _ip_hl tint))
            (Sset _iphl
              (Ebinop Oshl (Etempvar _t'22 tint)
                (Econst_int (Int.repr 2) tint) tint)))
          (Ssequence
            (Sset _bufptr
              (Ebinop Oadd (Etempvar _bufptr (tptr tuchar))
                (Etempvar _iphl tuint) (tptr tuchar)))
            (Ssequence
              (Sset _udph
                (Ecast (Etempvar _bufptr (tptr tuchar))
                  (tptr (Tstruct _udphdr noattr))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'21
                      (Efield
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _udph (tptr (Tstruct _udphdr noattr)))
                              (Tstruct _udphdr noattr))
                            18727075383868559167%positive
                            (Tunion __2163 noattr))
                          18727075383868559167%positive
                          (Tstruct __2164 noattr)) _uh_sport tushort))
                    (Scall (Some _t'3)
                      (Evar _ntohs (Tfunction (Tcons tushort Tnil) tushort
                                     cc_default))
                      ((Etempvar _t'21 tushort) :: nil)))
                  (Sset _srcport (Ecast (Etempvar _t'3 tushort) tushort)))
                (Ssequence
                  (Sifthenelse (Ebinop One (Etempvar _srcport tushort)
                                 (Econst_int (Int.repr 43707) tint) tint)
                    (Sgoto _no_deducehdr)
                    Sskip)
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'20
                          (Efield
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _udph (tptr (Tstruct _udphdr noattr)))
                                  (Tstruct _udphdr noattr))
                                18727075383868559167%positive
                                (Tunion __2163 noattr))
                              18727075383868559167%positive
                              (Tstruct __2164 noattr)) _uh_dport tushort))
                        (Scall (Some _t'4)
                          (Evar _ntohs (Tfunction (Tcons tushort Tnil)
                                         tushort cc_default))
                          ((Etempvar _t'20 tushort) :: nil)))
                      (Sset _dstport (Ecast (Etempvar _t'4 tushort) tushort)))
                    (Ssequence
                      (Sifthenelse (Ebinop One (Etempvar _dstport tushort)
                                     (Econst_int (Int.repr 52445) tint) tint)
                        (Sgoto _no_deducehdr)
                        Sskip)
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'19
                              (Efield
                                (Ederef
                                  (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                                  (Tstruct _ip noattr)) _ip_len tushort))
                            (Scall (Some _t'5)
                              (Evar _ntohs (Tfunction (Tcons tushort Tnil)
                                             tushort cc_default))
                              ((Etempvar _t'19 tushort) :: nil)))
                          (Sset _iplen
                            (Ecast (Etempvar _t'5 tushort) tushort)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'18
                                (Efield
                                  (Efield
                                    (Efield
                                      (Ederef
                                        (Etempvar _udph (tptr (Tstruct _udphdr noattr)))
                                        (Tstruct _udphdr noattr))
                                      18727075383868559167%positive
                                      (Tunion __2163 noattr))
                                    18727075383868559167%positive
                                    (Tstruct __2164 noattr)) _uh_ulen
                                  tushort))
                              (Scall (Some _t'6)
                                (Evar _ntohs (Tfunction (Tcons tushort Tnil)
                                               tushort cc_default))
                                ((Etempvar _t'18 tushort) :: nil)))
                            (Sset _udplen
                              (Ecast (Etempvar _t'6 tushort) tushort)))
                          (Ssequence
                            (Sifthenelse (Ebinop One
                                           (Ebinop Oadd
                                             (Etempvar _bufptr (tptr tuchar))
                                             (Etempvar _udplen tushort)
                                             (tptr tuchar))
                                           (Ebinop Oadd
                                             (Etempvar _packetdata (tptr tuchar))
                                             (Etempvar _iplen tushort)
                                             (tptr tuchar)) tint)
                              (Sgoto _no_deducehdr)
                              Sskip)
                            (Ssequence
                              (Sifthenelse (Ebinop Olt
                                             (Etempvar _udplen tushort)
                                             (Ebinop Oadd
                                               (Esizeof (Tstruct _udphdr noattr) tulong)
                                               (Esizeof (Tstruct _deducehdr noattr) tulong)
                                               tulong) tint)
                                (Sgoto _no_deducehdr)
                                Sskip)
                              (Ssequence
                                (Sset _bufptr
                                  (Ebinop Oadd
                                    (Etempvar _bufptr (tptr tuchar))
                                    (Esizeof (Tstruct _udphdr noattr) tulong)
                                    (tptr tuchar)))
                                (Ssequence
                                  (Sset _dhdr
                                    (Ecast (Etempvar _bufptr (tptr tuchar))
                                      (tptr (Tstruct _deducehdr noattr))))
                                  (Ssequence
                                    (Sset _size
                                      (Efield
                                        (Ederef
                                          (Etempvar _dhdr (tptr (Tstruct _deducehdr noattr)))
                                          (Tstruct _deducehdr noattr))
                                        _paramSize tuchar))
                                    (Ssequence
                                      (Sset _size
                                        (Ebinop Oand
                                          (Ebinop Oadd (Etempvar _size tuint)
                                            (Econst_int (Int.repr 3) tint)
                                            tuint)
                                          (Econst_int (Int.repr 65532) tint)
                                          tuint))
                                      (Ssequence
                                        (Sset _newlength
                                          (Ecast
                                            (Ebinop Osub
                                              (Etempvar _length tint)
                                              (Ebinop Oadd
                                                (Ebinop Oadd
                                                  (Esizeof (Tstruct _udphdr noattr) tulong)
                                                  (Esizeof (Tstruct _deducehdr noattr) tulong)
                                                  tulong)
                                                (Etempvar _size tuint)
                                                tulong) tulong) tushort))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'7)
                                                  (Evar _calloc (Tfunction
                                                                  (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                  (tptr tvoid)
                                                                  cc_default))
                                                  ((Etempvar _newlength tushort) ::
                                                   (Esizeof tuchar tulong) ::
                                                   nil))
                                                (Sset _t'8
                                                  (Ecast
                                                    (Etempvar _t'7 (tptr tvoid))
                                                    (tptr tuchar))))
                                              (Sset _newpacket
                                                (Etempvar _t'8 (tptr tuchar))))
                                            (Sset _nbufptr
                                              (Etempvar _t'8 (tptr tuchar))))
                                          (Ssequence
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
                                              ((Etempvar _newpacket (tptr tuchar)) ::
                                               (Etempvar _packetdata (tptr tuchar)) ::
                                               (Etempvar _iphl tuint) :: nil))
                                            (Ssequence
                                              (Sset _ipheader
                                                (Ecast
                                                  (Etempvar _newpacket (tptr tuchar))
                                                  (tptr (Tstruct _ip noattr))))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'17
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _dhdr (tptr (Tstruct _deducehdr noattr)))
                                                        (Tstruct _deducehdr noattr))
                                                      _origSrcIpAddr tuint))
                                                  (Sassign
                                                    (Efield
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                                                          (Tstruct _ip noattr))
                                                        _ip_src
                                                        (Tstruct _in_addr noattr))
                                                      _s_addr tuint)
                                                    (Etempvar _t'17 tuint)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'16
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _dhdr (tptr (Tstruct _deducehdr noattr)))
                                                          (Tstruct _deducehdr noattr))
                                                        _origDstIpAddr tuint))
                                                    (Sassign
                                                      (Efield
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                                                            (Tstruct _ip noattr))
                                                          _ip_dst
                                                          (Tstruct _in_addr noattr))
                                                        _s_addr tuint)
                                                      (Etempvar _t'16 tuint)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'15
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _dhdr (tptr (Tstruct _deducehdr noattr)))
                                                            (Tstruct _deducehdr noattr))
                                                          _origIpProtocol
                                                          tuchar))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                                                            (Tstruct _ip noattr))
                                                          _ip_p tuchar)
                                                        (Etempvar _t'15 tuchar)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'9)
                                                          (Evar _htons 
                                                          (Tfunction
                                                            (Tcons tushort
                                                              Tnil) tushort
                                                            cc_default))
                                                          ((Etempvar _newlength tushort) ::
                                                           nil))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                                                              (Tstruct _ip noattr))
                                                            _ip_len tushort)
                                                          (Etempvar _t'9 tushort)))
                                                      (Ssequence
                                                        (Sset _nbufptr
                                                          (Ebinop Oadd
                                                            (Etempvar _nbufptr (tptr tuchar))
                                                            (Etempvar _iphl tuint)
                                                            (tptr tuchar)))
                                                        (Ssequence
                                                          (Sset _bufptr
                                                            (Ebinop Oadd
                                                              (Etempvar _bufptr (tptr tuchar))
                                                              (Ebinop Oadd
                                                                (Esizeof (Tstruct _deducehdr noattr) tulong)
                                                                (Etempvar _size tuint)
                                                                tulong)
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
                                                              ((Etempvar _nbufptr (tptr tuchar)) ::
                                                               (Etempvar _bufptr (tptr tuchar)) ::
                                                               (Ebinop Osub
                                                                 (Etempvar _length tint)
                                                                 (Ebinop Osub
                                                                   (Etempvar _bufptr (tptr tuchar))
                                                                   (Etempvar _packetdata (tptr tuchar))
                                                                   tlong)
                                                                 tlong) ::
                                                               nil))
                                                            (Ssequence
                                                              (Sloop
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'14
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall (Some _t'11)
                                                                    (Evar _isUsefulLevel 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tint
                                                                    cc_default))
                                                                    ((Etempvar _t'14 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    nil)))
                                                                  (Sifthenelse (Etempvar _t'11 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'10)
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
                                                                    ((Etempvar _newpacket (tptr tuchar)) ::
                                                                    (Etempvar _newlength tushort) ::
                                                                    (Evar ___stringlit_4 (tarray tschar 27)) ::
                                                                    (Etempvar _newlength tushort) ::
                                                                    nil))
                                                                    (Sset _buf__1
                                                                    (Etempvar _t'10 (tptr tschar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'13
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    ((Etempvar _t'13 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func__ (tarray tschar 26)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 26) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 178) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_2 (tarray tschar 3)) ::
                                                                    (Etempvar _buf__1 (tptr tschar)) ::
                                                                    nil)))
                                                                    (Scall None
                                                                    (Evar _free 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _buf__1 (tptr tschar)) ::
                                                                    nil))))
                                                                    Sskip))
                                                                Sbreak)
                                                              (Ssequence
                                                                (Sreturn (Some (Etempvar _newpacket (tptr tuchar))))
                                                                (Ssequence
                                                                  (Slabel _no_deducehdr
                                                                    (Ssequence
                                                                    (Scall (Some _t'12)
                                                                    (Evar _calloc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Etempvar _length tint) ::
                                                                    (Esizeof tuchar tulong) ::
                                                                    nil))
                                                                    (Sset _newpacket
                                                                    (Etempvar _t'12 (tptr tvoid)))))
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
                                                                    ((Etempvar _newpacket (tptr tuchar)) ::
                                                                    (Etempvar _packetdata (tptr tuchar)) ::
                                                                    (Etempvar _length tint) ::
                                                                    nil))
                                                                    (Sreturn (Some (Etempvar _newpacket (tptr tuchar))))))))))))))))))))))))))))))))))))))
|}.

Definition v___func____1 := {|
  gvar_info := (tarray tschar 31);
  gvar_init := (Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 72) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_blackFecActuator_removeHeaders := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_packetdata, (tptr tuchar)) :: (_length, (tptr tint)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_tempBuffer, (tptr tuchar)) :: (_tempLength, tint) ::
               (_ipheader, (tptr (Tstruct _ip noattr))) :: (_iphl, tint) ::
               (_newBuffer, (tptr tuchar)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, tushort) :: (_t'1, (tptr tuchar)) :: (_t'10, tint) ::
               (_t'9, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'8, tint) :: (_t'7, tushort) ::
               (_t'6, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'5, tint) ::
               (_t'4, (tptr (Tstruct _zlog_category_s noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'9 (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
    (Ssequence
      (Sset _t'10 (Ederef (Etempvar _length (tptr tint)) tint))
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
        ((Etempvar _t'9 (tptr (Tstruct _zlog_category_s noattr))) ::
         (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
           (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
         (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
           (Ebinop Oadd (Econst_int (Int.repr 1) tint)
             (Econst_int (Int.repr 3) tint) tint) tulong) ::
         (Evar ___func____1 (tarray tschar 31)) ::
         (Ebinop Osub (Esizeof (tarray tschar 31) tulong)
           (Econst_int (Int.repr 1) tint) tulong) ::
         (Econst_int (Int.repr 207) tint) ::
         (Econst_int (Int.repr 20) tint) ::
         (Evar ___stringlit_5 (tarray tschar 37)) :: (Etempvar _t'10 tint) ::
         nil))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'8 (Ederef (Etempvar _length (tptr tint)) tint))
        (Scall (Some _t'1)
          (Evar _blackFecActuator_unDeduce (Tfunction
                                             (Tcons (tptr tuchar)
                                               (Tcons tint Tnil))
                                             (tptr tuchar) cc_default))
          ((Etempvar _packetdata (tptr tuchar)) :: (Etempvar _t'8 tint) ::
           nil)))
      (Sset _tempBuffer (Etempvar _t'1 (tptr tuchar))))
    (Ssequence
      (Sset _ipheader
        (Ecast (Etempvar _tempBuffer (tptr tuchar))
          (tptr (Tstruct _ip noattr))))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                  (Tstruct _ip noattr)) _ip_len tushort))
            (Scall (Some _t'2)
              (Evar _ntohs (Tfunction (Tcons tushort Tnil) tushort
                             cc_default)) ((Etempvar _t'7 tushort) :: nil)))
          (Sset _tempLength (Etempvar _t'2 tushort)))
        (Ssequence
          (Ssequence
            (Sset _t'6
              (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
              ((Etempvar _t'6 (tptr (Tstruct _zlog_category_s noattr))) ::
               (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
                 (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
               (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                 (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                   (Econst_int (Int.repr 3) tint) tint) tulong) ::
               (Evar ___func____1 (tarray tschar 31)) ::
               (Ebinop Osub (Esizeof (tarray tschar 31) tulong)
                 (Econst_int (Int.repr 1) tint) tulong) ::
               (Econst_int (Int.repr 212) tint) ::
               (Econst_int (Int.repr 20) tint) ::
               (Evar ___stringlit_6 (tarray tschar 46)) ::
               (Etempvar _tempLength tint) :: nil)))
          (Ssequence
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                    (Tstruct _ip noattr)) _ip_hl tint))
              (Sset _iphl
                (Ebinop Oshl (Etempvar _t'5 tint)
                  (Econst_int (Int.repr 2) tint) tint)))
            (Ssequence
              (Sset _tempLength
                (Ebinop Osub (Etempvar _tempLength tint)
                  (Etempvar _iphl tint) tint))
              (Ssequence
                (Sset _tempLength
                  (Ecast
                    (Ebinop Osub (Etempvar _tempLength tint)
                      (Esizeof (Tstruct _udphdr noattr) tulong) tulong) tint))
                (Ssequence
                  (Ssequence
                    (Sset _t'4
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
                                                  (Tcons (tptr tschar) Tnil))))))))
                                    tvoid
                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                      ((Etempvar _t'4 (tptr (Tstruct _zlog_category_s noattr))) ::
                       (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
                         (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                       (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                         (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                           (Econst_int (Int.repr 3) tint) tint) tulong) ::
                       (Evar ___func____1 (tarray tschar 31)) ::
                       (Ebinop Osub (Esizeof (tarray tschar 31) tulong)
                         (Econst_int (Int.repr 1) tint) tulong) ::
                       (Econst_int (Int.repr 222) tint) ::
                       (Econst_int (Int.repr 20) tint) ::
                       (Evar ___stringlit_7 (tarray tschar 50)) ::
                       (Etempvar _tempLength tint) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _calloc (Tfunction
                                        (Tcons tulong (Tcons tulong Tnil))
                                        (tptr tvoid) cc_default))
                        ((Etempvar _tempLength tint) ::
                         (Esizeof (tptr tuchar) tulong) :: nil))
                      (Sset _newBuffer (Etempvar _t'3 (tptr tvoid))))
                    (Ssequence
                      (Scall None
                        (Evar _memcpy (Tfunction
                                        (Tcons (tptr tvoid)
                                          (Tcons (tptr tvoid)
                                            (Tcons tulong Tnil)))
                                        (tptr tvoid) cc_default))
                        ((Etempvar _newBuffer (tptr tuchar)) ::
                         (Ebinop Oadd
                           (Ebinop Oadd (Etempvar _tempBuffer (tptr tuchar))
                             (Etempvar _iphl tint) (tptr tuchar))
                           (Esizeof (Tstruct _udphdr noattr) tulong)
                           (tptr tuchar)) :: (Etempvar _tempLength tint) ::
                         nil))
                      (Ssequence
                        (Scall None
                          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                        tvoid cc_default))
                          ((Etempvar _tempBuffer (tptr tuchar)) :: nil))
                        (Ssequence
                          (Sassign
                            (Ederef (Etempvar _length (tptr tint)) tint)
                            (Etempvar _tempLength tint))
                          (Sreturn (Some (Etempvar _newBuffer (tptr tuchar)))))))))))))))))
|}.

Definition v___func____2 := {|
  gvar_info := (tarray tschar 42);
  gvar_init := (Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_blackFecActuator_regenerateMissingPackets := {|
  fn_return := (tptr (Tstruct _packetinfo noattr));
  fn_callconv := cc_default;
  fn_params := ((_f, (tptr (Tstruct _flow noattr))) ::
                (_fecblock, (tptr (Tstruct _fecBlock noattr))) ::
                (_pinfo, (tptr (Tstruct _packetinfo noattr))) :: nil);
  fn_vars := ((_length, tint) :: nil);
  fn_temps := ((_i, tint) :: (_maxn, tint) :: (_k, tint) :: (_h, tint) ::
               (_n, tint) :: (_blockIndex, tint) :: (_maxpacketsize, tint) ::
               (_newpinfo, (tptr (Tstruct _packetinfo noattr))) ::
               (_plist, (tptr (Tstruct _packetinfo noattr))) ::
               (_plisttail, (tptr (Tstruct _packetinfo noattr))) ::
               (_ipheader, (tptr (Tstruct _ip noattr))) ::
               (_newipheader, (tptr (Tstruct _ip noattr))) ::
               (_buf, (tptr tschar)) :: (_buf__1, (tptr tschar)) ::
               (_buf__2, (tptr tschar)) :: (_t'19, tint) ::
               (_t'18, (tptr tschar)) :: (_t'17, tushort) ::
               (_t'16, (tptr tvoid)) ::
               (_t'15, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'14, tint) :: (_t'13, (tptr tschar)) :: (_t'12, tint) ::
               (_t'11, (tptr tschar)) :: (_t'10, tuint) :: (_t'9, tuint) ::
               (_t'8, (tptr tuchar)) :: (_t'7, (tptr tuchar)) ::
               (_t'6, tushort) :: (_t'5, (tptr tuchar)) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'141, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'140, tint) :: (_t'139, tint) ::
               (_t'138, (tptr (tptr tuchar))) :: (_t'137, (tptr tint)) ::
               (_t'136, (tptr tschar)) :: (_t'135, (tptr tint)) ::
               (_t'134, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'133, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'132, (tptr tschar)) :: (_t'131, (tptr (tptr tuchar))) ::
               (_t'130, (tptr tint)) ::
               (_t'129, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'128, tuint) ::
               (_t'127, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'126, (tptr tuchar)) ::
               (_t'125, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'124, (tptr (tptr tuchar))) :: (_t'123, (tptr tuchar)) ::
               (_t'122, (tptr (tptr tuchar))) :: (_t'121, tushort) ::
               (_t'120, (tptr tint)) :: (_t'119, (tptr tuchar)) ::
               (_t'118, (tptr (tptr tuchar))) ::
               (_t'117, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'116, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'115, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'114, tuint) ::
               (_t'113, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'112, (tptr tuchar)) ::
               (_t'111, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'110, (tptr (tptr tuchar))) :: (_t'109, tint) ::
               (_t'108, (tptr tint)) ::
               (_t'107, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'106, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'105, tuint) :: (_t'104, (tptr tuchar)) ::
               (_t'103, (tptr (tptr tuchar))) :: (_t'102, tint) ::
               (_t'101, (tptr tint)) :: (_t'100, (tptr tschar)) ::
               (_t'99, (tptr tint)) :: (_t'98, (tptr (tptr tuchar))) ::
               (_t'97, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'96, tschar) :: (_t'95, (tptr tschar)) :: (_t'94, tint) ::
               (_t'93, (tptr tint)) :: (_t'92, (tptr tuchar)) ::
               (_t'91, (tptr (tptr tuchar))) ::
               (_t'90, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'89, (tptr tschar)) :: (_t'88, (tptr tint)) ::
               (_t'87, (tptr (tptr tuchar))) :: (_t'86, tuint) ::
               (_t'85, (tptr tuchar)) :: (_t'84, (tptr (tptr tuchar))) ::
               (_t'83, (tptr tuchar)) :: (_t'82, (tptr (tptr tuchar))) ::
               (_t'81, tschar) :: (_t'80, (tptr tschar)) :: (_t'79, tint) ::
               (_t'78, (tptr tint)) :: (_t'77, tint) ::
               (_t'76, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'75, tuint) :: (_t'74, (tptr tuchar)) ::
               (_t'73, (tptr (tptr tuchar))) :: (_t'72, (tptr tuchar)) ::
               (_t'71, (tptr (tptr tuchar))) :: (_t'70, tschar) ::
               (_t'69, (tptr tschar)) :: (_t'68, tint) ::
               (_t'67, (tptr tint)) :: (_t'66, tint) ::
               (_t'65, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'64, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'63, tint) :: (_t'62, tint) :: (_t'61, tint) ::
               (_t'60, (tptr tint)) :: (_t'59, (tptr tuchar)) ::
               (_t'58, (tptr (tptr tuchar))) ::
               (_t'57, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'56, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'55, (tptr tuchar)) :: (_t'54, (tptr (tptr tuchar))) ::
               (_t'53, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'52, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'51, tint) :: (_t'50, tint) :: (_t'49, (tptr tint)) ::
               (_t'48, (tptr tuchar)) :: (_t'47, (tptr (tptr tuchar))) ::
               (_t'46, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'45, (tptr tuchar)) :: (_t'44, (tptr (tptr tuchar))) ::
               (_t'43, tuchar) :: (_t'42, (tptr tuchar)) ::
               (_t'41, (tptr (tptr tuchar))) :: (_t'40, tint) ::
               (_t'39, (tptr tint)) :: (_t'38, tint) ::
               (_t'37, (tptr tint)) :: (_t'36, (tptr tuchar)) ::
               (_t'35, (tptr (tptr tuchar))) :: (_t'34, (tptr tuchar)) ::
               (_t'33, (tptr tuchar)) :: (_t'32, (tptr tuchar)) ::
               (_t'31, tuchar) :: (_t'30, tushort) :: (_t'29, tuint) ::
               (_t'28, tuint) :: (_t'27, (tptr tuchar)) ::
               (_t'26, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'25, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'24, tuint) :: (_t'23, tuint) :: (_t'22, (tptr tuchar)) ::
               (_t'21, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'20, (tptr (Tstruct _packetinfo noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _maxn (Econst_int (Int.repr 256) tint))
  (Ssequence
    (Sset _plist
      (Ecast (Econst_int (Int.repr 0) tint)
        (tptr (Tstruct _packetinfo noattr))))
    (Ssequence
      (Sset _plisttail
        (Ecast (Econst_int (Int.repr 0) tint)
          (tptr (Tstruct _packetinfo noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'140
            (Efield
              (Ederef (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                (Tstruct _packetinfo noattr)) _isParity tint))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'140 tint) tint)
            (Ssequence
              (Sset _t'141
                (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                ((Etempvar _t'141 (tptr (Tstruct _zlog_category_s noattr))) ::
                 (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
                   (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                 (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                   (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                     (Econst_int (Int.repr 3) tint) tint) tulong) ::
                 (Evar ___func____2 (tarray tschar 42)) ::
                 (Ebinop Osub (Esizeof (tarray tschar 42) tulong)
                   (Econst_int (Int.repr 1) tint) tulong) ::
                 (Econst_int (Int.repr 280) tint) ::
                 (Econst_int (Int.repr 100) tint) ::
                 (Evar ___stringlit_8 (tarray tschar 64)) :: nil)))
            Sskip))
        (Ssequence
          (Ssequence
            (Sset _t'139
              (Efield
                (Ederef (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                  (Tstruct _packetinfo noattr)) _isParity tint))
            (Sifthenelse (Etempvar _t'139 tint)
              Sskip
              (Scall None
                (Evar ___assert_fail (Tfunction
                                       (Tcons (tptr tschar)
                                         (Tcons (tptr tschar)
                                           (Tcons tuint
                                             (Tcons (tptr tschar) Tnil))))
                                       tvoid cc_default))
                ((Evar ___stringlit_9 (tarray tschar 16)) ::
                 (Evar ___stringlit_3 (tarray tschar 19)) ::
                 (Econst_int (Int.repr 282) tint) ::
                 (Evar ___func____2 (tarray tschar 42)) :: nil))))
          (Ssequence
            (Ssequence
              (Sset _t'135
                (Efield
                  (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                    (Tstruct _flow noattr)) _bpacketsizes (tptr tint)))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'135 (tptr tint))
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
                          (Tstruct _flow noattr)) _bpacketptrs
                        (tptr (tptr tuchar))) (Etempvar _t'1 (tptr tvoid))))
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
                            (Tstruct _flow noattr)) _bpacketsizes
                          (tptr tint)) (Etempvar _t'2 (tptr tvoid))))
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
                            (Tstruct _flow noattr)) _bpstat (tptr tschar))
                        (Etempvar _t'3 (tptr tvoid))))))
                (Ssequence
                  (Ssequence
                    (Sset _t'138
                      (Efield
                        (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                          (Tstruct _flow noattr)) _bpacketptrs
                        (tptr (tptr tuchar))))
                    (Scall None
                      (Evar _memset (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons tint (Tcons tulong Tnil)))
                                      (tptr tvoid) cc_default))
                      ((Etempvar _t'138 (tptr (tptr tuchar))) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Ebinop Omul (Etempvar _maxn tint)
                         (Esizeof (tptr tuchar) tulong) tulong) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'137
                        (Efield
                          (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                            (Tstruct _flow noattr)) _bpacketsizes
                          (tptr tint)))
                      (Scall None
                        (Evar _memset (Tfunction
                                        (Tcons (tptr tvoid)
                                          (Tcons tint (Tcons tulong Tnil)))
                                        (tptr tvoid) cc_default))
                        ((Etempvar _t'137 (tptr tint)) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Ebinop Omul (Etempvar _maxn tint)
                           (Esizeof tint tulong) tulong) :: nil)))
                    (Ssequence
                      (Sset _t'136
                        (Efield
                          (Ederef (Etempvar _f (tptr (Tstruct _flow noattr)))
                            (Tstruct _flow noattr)) _bpstat (tptr tschar)))
                      (Scall None
                        (Evar _memset (Tfunction
                                        (Tcons (tptr tvoid)
                                          (Tcons tint (Tcons tulong Tnil)))
                                        (tptr tvoid) cc_default))
                        ((Etempvar _t'136 (tptr tschar)) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Etempvar _maxn tint) :: nil)))))))
            (Ssequence
              (Ssequence
                (Sset _t'134
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
                                              (Tcons (tptr tschar) Tnil))))))))
                                tvoid
                                {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                  ((Etempvar _t'134 (tptr (Tstruct _zlog_category_s noattr))) ::
                   (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
                     (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                   (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                     (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                       (Econst_int (Int.repr 3) tint) tint) tulong) ::
                   (Evar ___func____2 (tarray tschar 42)) ::
                   (Ebinop Osub (Esizeof (tarray tschar 42) tulong)
                     (Econst_int (Int.repr 1) tint) tulong) ::
                   (Econst_int (Int.repr 297) tint) ::
                   (Econst_int (Int.repr 20) tint) ::
                   (Evar ___stringlit_10 (tarray tschar 27)) :: nil)))
              (Ssequence
                (Sset _k
                  (Efield
                    (Ederef
                      (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                      (Tstruct _fecBlock noattr)) _k tint))
                (Ssequence
                  (Sset _h
                    (Efield
                      (Ederef
                        (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                        (Tstruct _fecBlock noattr)) _h tint))
                  (Ssequence
                    (Sset _n
                      (Ebinop Oadd (Etempvar _k tint) (Etempvar _h tint)
                        tint))
                    (Ssequence
                      (Sifthenelse (Ebinop Ole (Etempvar _n tint)
                                     (Etempvar _maxn tint) tint)
                        Sskip
                        (Scall None
                          (Evar ___assert_fail (Tfunction
                                                 (Tcons (tptr tschar)
                                                   (Tcons (tptr tschar)
                                                     (Tcons tuint
                                                       (Tcons (tptr tschar)
                                                         Tnil)))) tvoid
                                                 cc_default))
                          ((Evar ___stringlit_11 (tarray tschar 10)) ::
                           (Evar ___stringlit_3 (tarray tschar 19)) ::
                           (Econst_int (Int.repr 303) tint) ::
                           (Evar ___func____2 (tarray tschar 42)) :: nil)))
                      (Ssequence
                        (Sset _maxpacketsize
                          (Efield
                            (Ederef
                              (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                              (Tstruct _packetinfo noattr)) _length tuint))
                        (Ssequence
                          (Sset _blockIndex
                            (Efield
                              (Ederef
                                (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                (Tstruct _packetinfo noattr)) _blockIndex
                              tint))
                          (Ssequence
                            (Ssequence
                              (Sset _i (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                                 (Etempvar _k tint) tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _t'117
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                              (Tstruct _fecBlock noattr))
                                            _packets
                                            (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                          (Etempvar _i tint)
                                          (tptr (tptr (Tstruct _packetinfo noattr))))
                                        (tptr (Tstruct _packetinfo noattr))))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _t'117 (tptr (Tstruct _packetinfo noattr)))
                                                   (Ecast
                                                     (Econst_int (Int.repr 0) tint)
                                                     (tptr tvoid)) tint)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'133
                                            (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                            ((Etempvar _t'133 (tptr (Tstruct _zlog_category_s noattr))) ::
                                             (Ebinop Oadd
                                               (Evar ___stringlit_3 (tarray tschar 19))
                                               (Econst_int (Int.repr 3) tint)
                                               (tptr tschar)) ::
                                             (Ebinop Osub
                                               (Esizeof (tarray tschar 19) tulong)
                                               (Ebinop Oadd
                                                 (Econst_int (Int.repr 1) tint)
                                                 (Econst_int (Int.repr 3) tint)
                                                 tint) tulong) ::
                                             (Evar ___func____2 (tarray tschar 42)) ::
                                             (Ebinop Osub
                                               (Esizeof (tarray tschar 42) tulong)
                                               (Econst_int (Int.repr 1) tint)
                                               tulong) ::
                                             (Econst_int (Int.repr 318) tint) ::
                                             (Econst_int (Int.repr 20) tint) ::
                                             (Evar ___stringlit_13 (tarray tschar 38)) ::
                                             (Etempvar _i tint) :: nil)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'132
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _bpstat (tptr tschar)))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _t'132 (tptr tschar))
                                                  (Etempvar _i tint)
                                                  (tptr tschar)) tschar)
                                              (Econst_int (Int.repr 1) tint)))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'4)
                                                (Evar _calloc (Tfunction
                                                                (Tcons tulong
                                                                  (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                (tptr tvoid)
                                                                cc_default))
                                                ((Etempvar _maxpacketsize tint) ::
                                                 (Esizeof tuchar tulong) ::
                                                 nil))
                                              (Ssequence
                                                (Sset _t'131
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                      (Tstruct _flow noattr))
                                                    _bpacketptrs
                                                    (tptr (tptr tuchar))))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _t'131 (tptr (tptr tuchar)))
                                                      (Etempvar _i tint)
                                                      (tptr (tptr tuchar)))
                                                    (tptr tuchar))
                                                  (Etempvar _t'4 (tptr tvoid)))))
                                            (Ssequence
                                              (Sset _t'130
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                    (Tstruct _flow noattr))
                                                  _bpacketsizes (tptr tint)))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _t'130 (tptr tint))
                                                    (Etempvar _i tint)
                                                    (tptr tint)) tint)
                                                (Etempvar _maxpacketsize tint))))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'129
                                            (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                            ((Etempvar _t'129 (tptr (Tstruct _zlog_category_s noattr))) ::
                                             (Ebinop Oadd
                                               (Evar ___stringlit_3 (tarray tschar 19))
                                               (Econst_int (Int.repr 3) tint)
                                               (tptr tschar)) ::
                                             (Ebinop Osub
                                               (Esizeof (tarray tschar 19) tulong)
                                               (Ebinop Oadd
                                                 (Econst_int (Int.repr 1) tint)
                                                 (Econst_int (Int.repr 3) tint)
                                                 tint) tulong) ::
                                             (Evar ___func____2 (tarray tschar 42)) ::
                                             (Ebinop Osub
                                               (Esizeof (tarray tschar 42) tulong)
                                               (Econst_int (Int.repr 1) tint)
                                               tulong) ::
                                             (Econst_int (Int.repr 325) tint) ::
                                             (Econst_int (Int.repr 20) tint) ::
                                             (Evar ___stringlit_12 (tarray tschar 32)) ::
                                             (Etempvar _i tint) :: nil)))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'125
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                        (Tstruct _fecBlock noattr))
                                                      _packets
                                                      (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                                    (Etempvar _i tint)
                                                    (tptr (tptr (Tstruct _packetinfo noattr))))
                                                  (tptr (Tstruct _packetinfo noattr))))
                                              (Ssequence
                                                (Sset _t'126
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _t'125 (tptr (Tstruct _packetinfo noattr)))
                                                      (Tstruct _packetinfo noattr))
                                                    _packetdata
                                                    (tptr tuchar)))
                                                (Ssequence
                                                  (Sset _t'127
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                            (Tstruct _fecBlock noattr))
                                                          _packets
                                                          (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                                        (Etempvar _i tint)
                                                        (tptr (tptr (Tstruct _packetinfo noattr))))
                                                      (tptr (Tstruct _packetinfo noattr))))
                                                  (Ssequence
                                                    (Sset _t'128
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _t'127 (tptr (Tstruct _packetinfo noattr)))
                                                          (Tstruct _packetinfo noattr))
                                                        _length tuint))
                                                    (Scall (Some _t'5)
                                                      (Evar _blackFecActuator_unDeduce 
                                                      (Tfunction
                                                        (Tcons (tptr tuchar)
                                                          (Tcons tint Tnil))
                                                        (tptr tuchar)
                                                        cc_default))
                                                      ((Etempvar _t'126 (tptr tuchar)) ::
                                                       (Etempvar _t'128 tuint) ::
                                                       nil))))))
                                            (Ssequence
                                              (Sset _t'124
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                    (Tstruct _flow noattr))
                                                  _bpacketptrs
                                                  (tptr (tptr tuchar))))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _t'124 (tptr (tptr tuchar)))
                                                    (Etempvar _i tint)
                                                    (tptr (tptr tuchar)))
                                                  (tptr tuchar))
                                                (Etempvar _t'5 (tptr tuchar)))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'122
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                    (Tstruct _flow noattr))
                                                  _bpacketptrs
                                                  (tptr (tptr tuchar))))
                                              (Ssequence
                                                (Sset _t'123
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _t'122 (tptr (tptr tuchar)))
                                                      (Etempvar _i tint)
                                                      (tptr (tptr tuchar)))
                                                    (tptr tuchar)))
                                                (Sset _ipheader
                                                  (Ecast
                                                    (Etempvar _t'123 (tptr tuchar))
                                                    (tptr (Tstruct _ip noattr))))))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'121
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                                                        (Tstruct _ip noattr))
                                                      _ip_len tushort))
                                                  (Scall (Some _t'6)
                                                    (Evar _ntohs (Tfunction
                                                                   (Tcons
                                                                    tushort
                                                                    Tnil)
                                                                   tushort
                                                                   cc_default))
                                                    ((Etempvar _t'121 tushort) ::
                                                     nil)))
                                                (Ssequence
                                                  (Sset _t'120
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                        (Tstruct _flow noattr))
                                                      _bpacketsizes
                                                      (tptr tint)))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _t'120 (tptr tint))
                                                        (Etempvar _i tint)
                                                        (tptr tint)) tint)
                                                    (Etempvar _t'6 tushort))))
                                              (Ssequence
                                                (Sset _t'118
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                      (Tstruct _flow noattr))
                                                    _bpacketptrs
                                                    (tptr (tptr tuchar))))
                                                (Ssequence
                                                  (Sset _t'119
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _t'118 (tptr (tptr tuchar)))
                                                        (Etempvar _i tint)
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
                                                       (Etempvar _t'119 (tptr tuchar))
                                                       (tptr (Tstruct _ip noattr))) ::
                                                     nil)))))))))))
                                (Sset _i
                                  (Ebinop Oadd (Etempvar _i tint)
                                    (Econst_int (Int.repr 1) tint) tint))))
                            (Ssequence
                              (Ssequence
                                (Sset _i (Etempvar _k tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _i tint)
                                                   (Etempvar _n tint) tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sifthenelse (Ebinop Oeq
                                                     (Etempvar _i tint)
                                                     (Etempvar _blockIndex tint)
                                                     tint)
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'116
                                              (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                              ((Etempvar _t'116 (tptr (Tstruct _zlog_category_s noattr))) ::
                                               (Ebinop Oadd
                                                 (Evar ___stringlit_3 (tarray tschar 19))
                                                 (Econst_int (Int.repr 3) tint)
                                                 (tptr tschar)) ::
                                               (Ebinop Osub
                                                 (Esizeof (tarray tschar 19) tulong)
                                                 (Ebinop Oadd
                                                   (Econst_int (Int.repr 1) tint)
                                                   (Econst_int (Int.repr 3) tint)
                                                   tint) tulong) ::
                                               (Evar ___func____2 (tarray tschar 42)) ::
                                               (Ebinop Osub
                                                 (Esizeof (tarray tschar 42) tulong)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tulong) ::
                                               (Econst_int (Int.repr 339) tint) ::
                                               (Econst_int (Int.repr 20) tint) ::
                                               (Evar ___stringlit_14 (tarray tschar 42)) ::
                                               (Etempvar _i tint) :: nil)))
                                          Scontinue)
                                        Sskip)
                                      (Ssequence
                                        (Sset _t'107
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                  (Tstruct _fecBlock noattr))
                                                _packets
                                                (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                              (Etempvar _i tint)
                                              (tptr (tptr (Tstruct _packetinfo noattr))))
                                            (tptr (Tstruct _packetinfo noattr))))
                                        (Sifthenelse (Ebinop One
                                                       (Etempvar _t'107 (tptr (Tstruct _packetinfo noattr)))
                                                       (Ecast
                                                         (Econst_int (Int.repr 0) tint)
                                                         (tptr tvoid)) tint)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'115
                                                (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                ((Etempvar _t'115 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                 (Ebinop Oadd
                                                   (Evar ___stringlit_3 (tarray tschar 19))
                                                   (Econst_int (Int.repr 3) tint)
                                                   (tptr tschar)) ::
                                                 (Ebinop Osub
                                                   (Esizeof (tarray tschar 19) tulong)
                                                   (Ebinop Oadd
                                                     (Econst_int (Int.repr 1) tint)
                                                     (Econst_int (Int.repr 3) tint)
                                                     tint) tulong) ::
                                                 (Evar ___func____2 (tarray tschar 42)) ::
                                                 (Ebinop Osub
                                                   (Esizeof (tarray tschar 42) tulong)
                                                   (Econst_int (Int.repr 1) tint)
                                                   tulong) ::
                                                 (Econst_int (Int.repr 344) tint) ::
                                                 (Econst_int (Int.repr 20) tint) ::
                                                 (Evar ___stringlit_15 (tarray tschar 36)) ::
                                                 (Etempvar _i tint) :: nil)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'113
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                          (Tstruct _fecBlock noattr))
                                                        _packets
                                                        (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                                      (Etempvar _i tint)
                                                      (tptr (tptr (Tstruct _packetinfo noattr))))
                                                    (tptr (Tstruct _packetinfo noattr))))
                                                (Ssequence
                                                  (Sset _t'114
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t'113 (tptr (Tstruct _packetinfo noattr)))
                                                        (Tstruct _packetinfo noattr))
                                                      _length tuint))
                                                  (Sassign
                                                    (Evar _length tint)
                                                    (Etempvar _t'114 tuint))))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'111
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                              (Tstruct _fecBlock noattr))
                                                            _packets
                                                            (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                                          (Etempvar _i tint)
                                                          (tptr (tptr (Tstruct _packetinfo noattr))))
                                                        (tptr (Tstruct _packetinfo noattr))))
                                                    (Ssequence
                                                      (Sset _t'112
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _t'111 (tptr (Tstruct _packetinfo noattr)))
                                                            (Tstruct _packetinfo noattr))
                                                          _packetdata
                                                          (tptr tuchar)))
                                                      (Scall (Some _t'7)
                                                        (Evar _blackFecActuator_removeHeaders 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr tuchar)
                                                            (Tcons
                                                              (tptr tint)
                                                              Tnil))
                                                          (tptr tuchar)
                                                          cc_default))
                                                        ((Etempvar _t'112 (tptr tuchar)) ::
                                                         (Eaddrof
                                                           (Evar _length tint)
                                                           (tptr tint)) ::
                                                         nil))))
                                                  (Ssequence
                                                    (Sset _t'110
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                          (Tstruct _flow noattr))
                                                        _bpacketptrs
                                                        (tptr (tptr tuchar))))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _t'110 (tptr (tptr tuchar)))
                                                          (Etempvar _i tint)
                                                          (tptr (tptr tuchar)))
                                                        (tptr tuchar))
                                                      (Etempvar _t'7 (tptr tuchar)))))
                                                (Ssequence
                                                  (Sset _t'108
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                        (Tstruct _flow noattr))
                                                      _bpacketsizes
                                                      (tptr tint)))
                                                  (Ssequence
                                                    (Sset _t'109
                                                      (Evar _length tint))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _t'108 (tptr tint))
                                                          (Etempvar _i tint)
                                                          (tptr tint)) tint)
                                                      (Etempvar _t'109 tint)))))))
                                          Sskip))))
                                  (Sset _i
                                    (Ebinop Oadd (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'106
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
                                                                (Tcons
                                                                  (tptr tschar)
                                                                  Tnil))))))))
                                                  tvoid
                                                  {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                    ((Etempvar _t'106 (tptr (Tstruct _zlog_category_s noattr))) ::
                                     (Ebinop Oadd
                                       (Evar ___stringlit_3 (tarray tschar 19))
                                       (Econst_int (Int.repr 3) tint)
                                       (tptr tschar)) ::
                                     (Ebinop Osub
                                       (Esizeof (tarray tschar 19) tulong)
                                       (Ebinop Oadd
                                         (Econst_int (Int.repr 1) tint)
                                         (Econst_int (Int.repr 3) tint) tint)
                                       tulong) ::
                                     (Evar ___func____2 (tarray tschar 42)) ::
                                     (Ebinop Osub
                                       (Esizeof (tarray tschar 42) tulong)
                                       (Econst_int (Int.repr 1) tint) tulong) ::
                                     (Econst_int (Int.repr 355) tint) ::
                                     (Econst_int (Int.repr 20) tint) ::
                                     (Evar ___stringlit_16 (tarray tschar 47)) ::
                                     (Etempvar _blockIndex tint) :: nil)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'105
                                      (Efield
                                        (Ederef
                                          (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                          (Tstruct _packetinfo noattr))
                                        _length tuint))
                                    (Sassign (Evar _length tint)
                                      (Etempvar _t'105 tuint)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'104
                                          (Efield
                                            (Ederef
                                              (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                              (Tstruct _packetinfo noattr))
                                            _packetdata (tptr tuchar)))
                                        (Scall (Some _t'8)
                                          (Evar _blackFecActuator_removeHeaders 
                                          (Tfunction
                                            (Tcons (tptr tuchar)
                                              (Tcons (tptr tint) Tnil))
                                            (tptr tuchar) cc_default))
                                          ((Etempvar _t'104 (tptr tuchar)) ::
                                           (Eaddrof (Evar _length tint)
                                             (tptr tint)) :: nil)))
                                      (Ssequence
                                        (Sset _t'103
                                          (Efield
                                            (Ederef
                                              (Etempvar _f (tptr (Tstruct _flow noattr)))
                                              (Tstruct _flow noattr))
                                            _bpacketptrs
                                            (tptr (tptr tuchar))))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'103 (tptr (tptr tuchar)))
                                              (Etempvar _blockIndex tint)
                                              (tptr (tptr tuchar)))
                                            (tptr tuchar))
                                          (Etempvar _t'8 (tptr tuchar)))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'101
                                          (Efield
                                            (Ederef
                                              (Etempvar _f (tptr (Tstruct _flow noattr)))
                                              (Tstruct _flow noattr))
                                            _bpacketsizes (tptr tint)))
                                        (Ssequence
                                          (Sset _t'102 (Evar _length tint))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'101 (tptr tint))
                                                (Etempvar _blockIndex tint)
                                                (tptr tint)) tint)
                                            (Etempvar _t'102 tint))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'97
                                            (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                          (Ssequence
                                            (Sset _t'98
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _bpacketptrs
                                                (tptr (tptr tuchar))))
                                            (Ssequence
                                              (Sset _t'99
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                    (Tstruct _flow noattr))
                                                  _bpacketsizes (tptr tint)))
                                              (Ssequence
                                                (Sset _t'100
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                      (Tstruct _flow noattr))
                                                    _bpstat (tptr tschar)))
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
                                                  ((Etempvar _t'97 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                   (Ebinop Oadd
                                                     (Evar ___stringlit_3 (tarray tschar 19))
                                                     (Econst_int (Int.repr 3) tint)
                                                     (tptr tschar)) ::
                                                   (Ebinop Osub
                                                     (Esizeof (tarray tschar 19) tulong)
                                                     (Ebinop Oadd
                                                       (Econst_int (Int.repr 1) tint)
                                                       (Econst_int (Int.repr 3) tint)
                                                       tint) tulong) ::
                                                   (Evar ___func____2 (tarray tschar 42)) ::
                                                   (Ebinop Osub
                                                     (Esizeof (tarray tschar 42) tulong)
                                                     (Econst_int (Int.repr 1) tint)
                                                     tulong) ::
                                                   (Econst_int (Int.repr 362) tint) ::
                                                   (Econst_int (Int.repr 20) tint) ::
                                                   (Evar ___stringlit_17 (tarray tschar 47)) ::
                                                   (Etempvar _k tint) ::
                                                   (Econst_int (Int.repr 0) tint) ::
                                                   (Etempvar _maxpacketsize tint) ::
                                                   (Etempvar _t'98 (tptr (tptr tuchar))) ::
                                                   (Etempvar _t'99 (tptr tint)) ::
                                                   (Etempvar _t'100 (tptr tschar)) ::
                                                   nil))))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _i
                                              (Econst_int (Int.repr 0) tint))
                                            (Sloop
                                              (Ssequence
                                                (Sifthenelse (Ebinop Olt
                                                               (Etempvar _i tint)
                                                               (Etempvar _n tint)
                                                               tint)
                                                  Sskip
                                                  Sbreak)
                                                (Ssequence
                                                  (Sset _t'90
                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                  (Ssequence
                                                    (Sset _t'91
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                          (Tstruct _flow noattr))
                                                        _bpacketptrs
                                                        (tptr (tptr tuchar))))
                                                    (Ssequence
                                                      (Sset _t'92
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _t'91 (tptr (tptr tuchar)))
                                                            (Etempvar _i tint)
                                                            (tptr (tptr tuchar)))
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'93
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                              (Tstruct _flow noattr))
                                                            _bpacketsizes
                                                            (tptr tint)))
                                                        (Ssequence
                                                          (Sset _t'94
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _t'93 (tptr tint))
                                                                (Etempvar _i tint)
                                                                (tptr tint))
                                                              tint))
                                                          (Ssequence
                                                            (Sset _t'95
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                  (Tstruct _flow noattr))
                                                                _bpstat
                                                                (tptr tschar)))
                                                            (Ssequence
                                                              (Sset _t'96
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'95 (tptr tschar))
                                                                    (Etempvar _i tint)
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
                                                                ((Etempvar _t'90 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                 (Ebinop Oadd
                                                                   (Evar ___stringlit_3 (tarray tschar 19))
                                                                   (Econst_int (Int.repr 3) tint)
                                                                   (tptr tschar)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 19) tulong)
                                                                   (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                   tulong) ::
                                                                 (Evar ___func____2 (tarray tschar 42)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 42) tulong)
                                                                   (Econst_int (Int.repr 1) tint)
                                                                   tulong) ::
                                                                 (Econst_int (Int.repr 365) tint) ::
                                                                 (Econst_int (Int.repr 10) tint) ::
                                                                 (Evar ___stringlit_18 (tarray tschar 68)) ::
                                                                 (Etempvar _i tint) ::
                                                                 (Etempvar _t'92 (tptr tuchar)) ::
                                                                 (Etempvar _t'94 tint) ::
                                                                 (Etempvar _t'96 tschar) ::
                                                                 nil))))))))))
                                              (Sset _i
                                                (Ebinop Oadd
                                                  (Etempvar _i tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'87
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                    (Tstruct _flow noattr))
                                                  _bpacketptrs
                                                  (tptr (tptr tuchar))))
                                              (Ssequence
                                                (Sset _t'88
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                      (Tstruct _flow noattr))
                                                    _bpacketsizes
                                                    (tptr tint)))
                                                (Ssequence
                                                  (Sset _t'89
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                        (Tstruct _flow noattr))
                                                      _bpstat (tptr tschar)))
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
                                                    ((Etempvar _k tint) ::
                                                     (Econst_int (Int.repr 0) tint) ::
                                                     (Etempvar _maxpacketsize tint) ::
                                                     (Etempvar _t'87 (tptr (tptr tuchar))) ::
                                                     (Etempvar _t'88 (tptr tint)) ::
                                                     (Etempvar _t'89 (tptr tschar)) ::
                                                     nil)))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _i
                                                  (Econst_int (Int.repr 0) tint))
                                                (Sloop
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Olt
                                                                   (Etempvar _i tint)
                                                                   (Etempvar _n tint)
                                                                   tint)
                                                      Sskip
                                                      Sbreak)
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Etempvar _i tint)
                                                                    (Etempvar _k tint)
                                                                    tint)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'82
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                  (Tstruct _flow noattr))
                                                                _bpacketptrs
                                                                (tptr (tptr tuchar))))
                                                            (Ssequence
                                                              (Sset _t'83
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'82 (tptr (tptr tuchar)))
                                                                    (Etempvar _i tint)
                                                                    (tptr (tptr tuchar)))
                                                                  (tptr tuchar)))
                                                              (Sifthenelse 
                                                                (Ebinop One
                                                                  (Etempvar _t'83 (tptr tuchar))
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _t'84
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketptrs
                                                                    (tptr (tptr tuchar))))
                                                                  (Ssequence
                                                                    (Sset _t'85
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'84 (tptr (tptr tuchar)))
                                                                    (Etempvar _i tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'86
                                                                    (Ederef
                                                                    (Ecast
                                                                    (Etempvar _t'85 (tptr tuchar))
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _t'9
                                                                    (Ecast
                                                                    (Etempvar _t'86 tuint)
                                                                    tuint)))))
                                                                (Sset _t'9
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tuint)))))
                                                          (Ssequence
                                                            (Sset _t'76
                                                              (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                            (Ssequence
                                                              (Sset _t'77
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                  _blockSeq
                                                                  tint))
                                                              (Ssequence
                                                                (Sset _t'78
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketsizes
                                                                    (tptr tint)))
                                                                (Ssequence
                                                                  (Sset _t'79
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'78 (tptr tint))
                                                                    (Etempvar _i tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                  (Ssequence
                                                                    (Sset _t'80
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpstat
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sset _t'81
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'80 (tptr tschar))
                                                                    (Etempvar _i tint)
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
                                                                    ((Etempvar _t'76 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____2 (tarray tschar 42)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 42) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 371) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_20 (tarray tschar 75)) ::
                                                                    (Etempvar _t'77 tint) ::
                                                                    (Etempvar _i tint) ::
                                                                    (Etempvar _t'79 tint) ::
                                                                    (Etempvar _t'81 tschar) ::
                                                                    (Etempvar _t'9 tuint) ::
                                                                    nil)))))))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'71
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                  (Tstruct _flow noattr))
                                                                _bpacketptrs
                                                                (tptr (tptr tuchar))))
                                                            (Ssequence
                                                              (Sset _t'72
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'71 (tptr (tptr tuchar)))
                                                                    (Etempvar _i tint)
                                                                    (tptr (tptr tuchar)))
                                                                  (tptr tuchar)))
                                                              (Sifthenelse 
                                                                (Ebinop One
                                                                  (Etempvar _t'72 (tptr tuchar))
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _t'73
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketptrs
                                                                    (tptr (tptr tuchar))))
                                                                  (Ssequence
                                                                    (Sset _t'74
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'73 (tptr (tptr tuchar)))
                                                                    (Etempvar _i tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'75
                                                                    (Ederef
                                                                    (Ecast
                                                                    (Etempvar _t'74 (tptr tuchar))
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _t'10
                                                                    (Ecast
                                                                    (Etempvar _t'75 tuint)
                                                                    tuint)))))
                                                                (Sset _t'10
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tuint)))))
                                                          (Ssequence
                                                            (Sset _t'65
                                                              (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                            (Ssequence
                                                              (Sset _t'66
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                  _blockSeq
                                                                  tint))
                                                              (Ssequence
                                                                (Sset _t'67
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketsizes
                                                                    (tptr tint)))
                                                                (Ssequence
                                                                  (Sset _t'68
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'67 (tptr tint))
                                                                    (Etempvar _i tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                  (Ssequence
                                                                    (Sset _t'69
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpstat
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sset _t'70
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'69 (tptr tschar))
                                                                    (Etempvar _i tint)
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
                                                                    ((Etempvar _t'65 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____2 (tarray tschar 42)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 42) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 379) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_19 (tarray tschar 71)) ::
                                                                    (Etempvar _t'66 tint) ::
                                                                    (Etempvar _i tint) ::
                                                                    (Etempvar _t'68 tint) ::
                                                                    (Etempvar _t'70 tschar) ::
                                                                    (Etempvar _t'10 tuint) ::
                                                                    nil))))))))))
                                                      (Sloop
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'64
                                                              (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                            (Scall (Some _t'12)
                                                              (Evar _isUsefulLevel 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _zlog_category_s noattr))
                                                                  (Tcons tint
                                                                    Tnil))
                                                                tint
                                                                cc_default))
                                                              ((Etempvar _t'64 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                               (Econst_int (Int.repr 20) tint) ::
                                                               nil)))
                                                          (Sifthenelse (Etempvar _t'12 tint)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'58
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketptrs
                                                                    (tptr (tptr tuchar))))
                                                                  (Ssequence
                                                                    (Sset _t'59
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'58 (tptr (tptr tuchar)))
                                                                    (Etempvar _i tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'60
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketsizes
                                                                    (tptr tint)))
                                                                    (Ssequence
                                                                    (Sset _t'61
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'60 (tptr tint))
                                                                    (Etempvar _i tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'62
                                                                    (Evar _length tint))
                                                                    (Ssequence
                                                                    (Sset _t'63
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _blockSeq
                                                                    tint))
                                                                    (Scall (Some _t'11)
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
                                                                    ((Etempvar _t'59 (tptr tuchar)) ::
                                                                    (Etempvar _t'61 tint) ::
                                                                    (Evar ___stringlit_21 (tarray tschar 38)) ::
                                                                    (Etempvar _t'62 tint) ::
                                                                    (Etempvar _t'63 tint) ::
                                                                    (Etempvar _i tint) ::
                                                                    nil))))))))
                                                                (Sset _buf
                                                                  (Etempvar _t'11 (tptr tschar))))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'57
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    ((Etempvar _t'57 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____2 (tarray tschar 42)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 42) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 386) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_2 (tarray tschar 3)) ::
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
                                                        Sbreak)))
                                                  (Sset _i
                                                    (Ebinop Oadd
                                                      (Etempvar _i tint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tint))))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _i
                                                    (Econst_int (Int.repr 0) tint))
                                                  (Sloop
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Etempvar _i tint)
                                                                    (Etempvar _k tint)
                                                                    tint)
                                                        Sskip
                                                        Sbreak)
                                                      (Ssequence
                                                        (Sset _t'20
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                  (Tstruct _fecBlock noattr))
                                                                _packets
                                                                (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                                              (Etempvar _i tint)
                                                              (tptr (tptr (Tstruct _packetinfo noattr))))
                                                            (tptr (Tstruct _packetinfo noattr))))
                                                        (Sifthenelse 
                                                          (Ebinop Oeq
                                                            (Etempvar _t'20 (tptr (Tstruct _packetinfo noattr)))
                                                            (Ecast
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tvoid))
                                                            tint)
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'56
                                                                (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                ((Etempvar _t'56 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                 (Ebinop Oadd
                                                                   (Evar ___stringlit_3 (tarray tschar 19))
                                                                   (Econst_int (Int.repr 3) tint)
                                                                   (tptr tschar)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 19) tulong)
                                                                   (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                   tulong) ::
                                                                 (Evar ___func____2 (tarray tschar 42)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 42) tulong)
                                                                   (Econst_int (Int.repr 1) tint)
                                                                   tulong) ::
                                                                 (Econst_int (Int.repr 393) tint) ::
                                                                 (Econst_int (Int.repr 20) tint) ::
                                                                 (Evar ___stringlit_22 (tarray tschar 37)) ::
                                                                 (Etempvar _i tint) ::
                                                                 (Etempvar _k tint) ::
                                                                 nil)))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'41
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketptrs
                                                                    (tptr (tptr tuchar))))
                                                                (Ssequence
                                                                  (Sset _t'42
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'41 (tptr (tptr tuchar)))
                                                                    (Etempvar _i tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                  (Ssequence
                                                                    (Sset _t'43
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'42 (tptr tuchar))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'43 tuchar)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'53
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'54
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketptrs
                                                                    (tptr (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'55
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'54 (tptr (tptr tuchar)))
                                                                    (Etempvar _i tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
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
                                                                    ((Etempvar _t'53 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____2 (tarray tschar 42)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 42) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 398) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_23 (tarray tschar 52)) ::
                                                                    (Etempvar _i tint) ::
                                                                    (Etempvar _t'55 (tptr tuchar)) ::
                                                                    nil)))))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'52
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall (Some _t'14)
                                                                    (Evar _isUsefulLevel 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tint
                                                                    cc_default))
                                                                    ((Etempvar _t'52 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Econst_int (Int.repr 10) tint) ::
                                                                    nil)))
                                                                    (Sifthenelse (Etempvar _t'14 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'47
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketptrs
                                                                    (tptr (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'48
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'47 (tptr (tptr tuchar)))
                                                                    (Etempvar _i tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'49
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketsizes
                                                                    (tptr tint)))
                                                                    (Ssequence
                                                                    (Sset _t'50
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'49 (tptr tint))
                                                                    (Etempvar _i tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'51
                                                                    (Evar _length tint))
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
                                                                    ((Etempvar _t'48 (tptr tuchar)) ::
                                                                    (Etempvar _t'50 tint) ::
                                                                    (Evar ___stringlit_24 (tarray tschar 23)) ::
                                                                    (Etempvar _t'51 tint) ::
                                                                    nil)))))))
                                                                    (Sset _buf__1
                                                                    (Etempvar _t'13 (tptr tschar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'46
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____2 (tarray tschar 42)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 42) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 399) tint) ::
                                                                    (Econst_int (Int.repr 10) tint) ::
                                                                    (Evar ___stringlit_2 (tarray tschar 3)) ::
                                                                    (Etempvar _buf__1 (tptr tschar)) ::
                                                                    nil)))
                                                                    (Scall None
                                                                    (Evar _free 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _buf__1 (tptr tschar)) ::
                                                                    nil))))
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'44
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketptrs
                                                                    (tptr (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'45
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'44 (tptr (tptr tuchar)))
                                                                    (Etempvar _i tint)
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
                                                                    ((Etempvar _t'45 (tptr tuchar)) ::
                                                                    nil))))
                                                                    Scontinue)))
                                                                    Sskip))))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Scall (Some _t'15)
                                                                    (Evar _packetinfo_copyNoData 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    Tnil)
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    cc_default))
                                                                    ((Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                                    nil))
                                                                  (Sset _newpinfo
                                                                    (Etempvar _t'15 (tptr (Tstruct _packetinfo noattr)))))
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _plist (tptr (Tstruct _packetinfo noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sset _plist
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _plisttail (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _next
                                                                    (tptr (Tstruct _packetinfo noattr)))
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))))
                                                                  (Ssequence
                                                                    (Sset _plisttail
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'39
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketsizes
                                                                    (tptr tint)))
                                                                    (Ssequence
                                                                    (Sset _t'40
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'39 (tptr tint))
                                                                    (Etempvar _i tint)
                                                                    (tptr tint))
                                                                    tint))
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
                                                                    ((Etempvar _t'40 tint) ::
                                                                    (Esizeof tuchar tulong) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _packetdata
                                                                    (tptr tuchar))
                                                                    (Etempvar _t'16 (tptr tvoid))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'34
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _packetdata
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'35
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketptrs
                                                                    (tptr (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'36
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'35 (tptr (tptr tuchar)))
                                                                    (Etempvar _i tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'37
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _bpacketsizes
                                                                    (tptr tint)))
                                                                    (Ssequence
                                                                    (Sset _t'38
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'37 (tptr tint))
                                                                    (Etempvar _i tint)
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
                                                                    ((Etempvar _t'34 (tptr tuchar)) ::
                                                                    (Etempvar _t'36 (tptr tuchar)) ::
                                                                    (Etempvar _t'38 tint) ::
                                                                    nil)))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'33
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _packetdata
                                                                    (tptr tuchar)))
                                                                    (Sset _ipheader
                                                                    (Ecast
                                                                    (Etempvar _t'33 (tptr tuchar))
                                                                    (tptr (Tstruct _ip noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'32
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _packetdata
                                                                    (tptr tuchar)))
                                                                    (Sset _newipheader
                                                                    (Ecast
                                                                    (Etempvar _t'32 (tptr tuchar))
                                                                    (tptr (Tstruct _ip noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'31
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ipheader (tptr (Tstruct _ip noattr)))
                                                                    (Tstruct _ip noattr))
                                                                    _ip_ttl
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newipheader (tptr (Tstruct _ip noattr)))
                                                                    (Tstruct _ip noattr))
                                                                    _ip_ttl
                                                                    tuchar)
                                                                    (Etempvar _t'31 tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'30
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newipheader (tptr (Tstruct _ip noattr)))
                                                                    (Tstruct _ip noattr))
                                                                    _ip_len
                                                                    tushort))
                                                                    (Scall (Some _t'17)
                                                                    (Evar _ntohs 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tushort
                                                                    Tnil)
                                                                    tushort
                                                                    cc_default))
                                                                    ((Etempvar _t'30 tushort) ::
                                                                    nil)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _length
                                                                    tuint)
                                                                    (Etempvar _t'17 tushort)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _udphdrsize
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _deducehdrsize
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _deduceparamsizeWithPad
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _deduceparamsizeWithoutPad
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'28
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'29
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _iphdrsize
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _remaindersize
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'28 tuint)
                                                                    (Etempvar _t'29 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _blockIndex
                                                                    tint)
                                                                    (Etempvar _i tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _isParity
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'26
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'27
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _packetdata
                                                                    (tptr tuchar)))
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
                                                                    ((Etempvar _t'26 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____2 (tarray tschar 42)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 42) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 446) tint) ::
                                                                    (Econst_int (Int.repr 60) tint) ::
                                                                    (Evar ___stringlit_25 (tarray tschar 54)) ::
                                                                    (Etempvar _i tint) ::
                                                                    (Etempvar _k tint) ::
                                                                    (Etempvar _t'27 (tptr tuchar)) ::
                                                                    nil))))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'25
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall (Some _t'19)
                                                                    (Evar _isUsefulLevel 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tint
                                                                    cc_default))
                                                                    ((Etempvar _t'25 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    nil)))
                                                                    (Sifthenelse (Etempvar _t'19 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'22
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _packetdata
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'23
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'24
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Scall (Some _t'18)
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
                                                                    ((Etempvar _t'22 (tptr tuchar)) ::
                                                                    (Etempvar _t'23 tuint) ::
                                                                    (Evar ___stringlit_26 (tarray tschar 60)) ::
                                                                    (Etempvar _t'24 tuint) ::
                                                                    (Etempvar _i tint) ::
                                                                    (Etempvar _k tint) ::
                                                                    nil)))))
                                                                    (Sset _buf__2
                                                                    (Etempvar _t'18 (tptr tschar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'21
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    ((Etempvar _t'21 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____2 (tarray tschar 42)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 42) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 449) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_2 (tarray tschar 3)) ::
                                                                    (Etempvar _buf__2 (tptr tschar)) ::
                                                                    nil)))
                                                                    (Scall None
                                                                    (Evar _free 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _buf__2 (tptr tschar)) ::
                                                                    nil))))
                                                                    Sskip))
                                                                    Sbreak))))))))))))))))))))
                                                          Sskip)))
                                                    (Sset _i
                                                      (Ebinop Oadd
                                                        (Etempvar _i tint)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tint))))
                                                (Sreturn (Some (Etempvar _plist (tptr (Tstruct _packetinfo noattr)))))))))))))))))))))))))))))
|}.

Definition v___func____3 := {|
  gvar_info := (tarray tschar 37);
  gvar_init := (Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_blackFecActuator_initBlockWithPacket := {|
  fn_return := (tptr (Tstruct _packetinfo noattr));
  fn_callconv := cc_default;
  fn_params := ((_f, (tptr (Tstruct _flow noattr))) ::
                (_fecblock, (tptr (Tstruct _fecBlock noattr))) ::
                (_pinfo, (tptr (Tstruct _packetinfo noattr))) ::
                (_blockSeq, tint) :: (_k, tint) :: (_h, tint) ::
                (_pindex, tint) :: (_isParity, tint) ::
                (_timeout, tdouble) :: nil);
  fn_vars := nil;
  fn_temps := ((_newpinfo, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'2, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'1, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'14, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'13, tint) ::
               (_t'12, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'8, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'7, tint) :: (_t'6, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'5, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'4, tint) :: (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'14 (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
      ((Etempvar _t'14 (tptr (Tstruct _zlog_category_s noattr))) ::
       (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
         (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
       (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
         (Ebinop Oadd (Econst_int (Int.repr 1) tint)
           (Econst_int (Int.repr 3) tint) tint) tulong) ::
       (Evar ___func____3 (tarray tschar 37)) ::
       (Ebinop Osub (Esizeof (tarray tschar 37) tulong)
         (Econst_int (Int.repr 1) tint) tulong) ::
       (Econst_int (Int.repr 482) tint) :: (Econst_int (Int.repr 20) tint) ::
       (Evar ___stringlit_27 (tarray tschar 40)) :: nil)))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
          (Tstruct _fecBlock noattr)) _blockSeq tint)
      (Etempvar _blockSeq tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
            (Tstruct _fecBlock noattr)) _k tint) (Etempvar _k tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
              (Tstruct _fecBlock noattr)) _h tint) (Etempvar _h tint))
        (Ssequence
          (Ssequence
            (Sset _t'13
              (Efield
                (Ederef
                  (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                  (Tstruct _fecBlock noattr)) _packetCount tint))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                  (Tstruct _fecBlock noattr)) _packetCount tint)
              (Ebinop Oadd (Etempvar _t'13 tint)
                (Econst_int (Int.repr 1) tint) tint)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                  (Tstruct _fecBlock noattr)) _timeout tdouble)
              (Etempvar _timeout tdouble))
            (Sifthenelse (Etempvar _isParity tint)
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                          (Tstruct _fecBlock noattr)) _packets
                        (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                      (Etempvar _pindex tint)
                      (tptr (tptr (Tstruct _packetinfo noattr))))
                    (tptr (Tstruct _packetinfo noattr)))
                  (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
                (Ssequence
                  (Sset _t'10
                    (Efield
                      (Ederef
                        (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                        (Tstruct _fecBlock noattr)) _packetCount tint))
                  (Ssequence
                    (Sset _t'11
                      (Efield
                        (Ederef
                          (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                          (Tstruct _fecBlock noattr)) _k tint))
                    (Sifthenelse (Ebinop Oeq (Etempvar _t'10 tint)
                                   (Etempvar _t'11 tint) tint)
                      (Ssequence
                        (Ssequence
                          (Sset _t'12
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
                            ((Etempvar _t'12 (tptr (Tstruct _zlog_category_s noattr))) ::
                             (Ebinop Oadd
                               (Evar ___stringlit_3 (tarray tschar 19))
                               (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                             (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                               (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                                 (Econst_int (Int.repr 3) tint) tint) tulong) ::
                             (Evar ___func____3 (tarray tschar 37)) ::
                             (Ebinop Osub (Esizeof (tarray tschar 37) tulong)
                               (Econst_int (Int.repr 1) tint) tulong) ::
                             (Econst_int (Int.repr 497) tint) ::
                             (Econst_int (Int.repr 20) tint) ::
                             (Evar ___stringlit_30 (tarray tschar 73)) ::
                             nil)))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                (Tstruct _fecBlock noattr)) _complete tint)
                            (Econst_int (Int.repr 1) tint))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'1)
                                (Evar _blackFecActuator_regenerateMissingPackets 
                                (Tfunction
                                  (Tcons (tptr (Tstruct _flow noattr))
                                    (Tcons (tptr (Tstruct _fecBlock noattr))
                                      (Tcons
                                        (tptr (Tstruct _packetinfo noattr))
                                        Tnil)))
                                  (tptr (Tstruct _packetinfo noattr))
                                  cc_default))
                                ((Etempvar _f (tptr (Tstruct _flow noattr))) ::
                                 (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))) ::
                                 (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                 nil))
                              (Sset _newpinfo
                                (Etempvar _t'1 (tptr (Tstruct _packetinfo noattr)))))
                            (Ssequence
                              (Scall None
                                (Evar _packetinfo_free (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _packetinfo noattr))
                                                           Tnil) tvoid
                                                         cc_default))
                                ((Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                 nil))
                              (Sreturn (Some (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))))))))
                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                            (Tstruct _fecBlock noattr)) _packets
                          (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                        (Etempvar _pindex tint)
                        (tptr (tptr (Tstruct _packetinfo noattr))))
                      (tptr (Tstruct _packetinfo noattr))))
                  (Sifthenelse (Ebinop One
                                 (Etempvar _t'6 (tptr (Tstruct _packetinfo noattr)))
                                 (Ecast (Econst_int (Int.repr 0) tint)
                                   (tptr tvoid)) tint)
                    (Ssequence
                      (Ssequence
                        (Sset _t'8
                          (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                        (Ssequence
                          (Sset _t'9
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                    (Tstruct _fecBlock noattr)) _packets
                                  (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                (Etempvar _pindex tint)
                                (tptr (tptr (Tstruct _packetinfo noattr))))
                              (tptr (Tstruct _packetinfo noattr))))
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
                            ((Etempvar _t'8 (tptr (Tstruct _zlog_category_s noattr))) ::
                             (Ebinop Oadd
                               (Evar ___stringlit_3 (tarray tschar 19))
                               (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                             (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                               (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                                 (Econst_int (Int.repr 3) tint) tint) tulong) ::
                             (Evar ___func____3 (tarray tschar 37)) ::
                             (Ebinop Osub (Esizeof (tarray tschar 37) tulong)
                               (Econst_int (Int.repr 1) tint) tulong) ::
                             (Econst_int (Int.repr 534) tint) ::
                             (Econst_int (Int.repr 100) tint) ::
                             (Evar ___stringlit_28 (tarray tschar 68)) ::
                             (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                             (Etempvar _pindex tint) ::
                             (Etempvar _t'9 (tptr (Tstruct _packetinfo noattr))) ::
                             nil))))
                      (Ssequence
                        (Sset _t'7
                          (Efield
                            (Ederef
                              (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                              (Tstruct _fecBlock noattr)) _packetCount tint))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                              (Tstruct _fecBlock noattr)) _packetCount tint)
                          (Ebinop Osub (Etempvar _t'7 tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Sset _t'3
                      (Efield
                        (Ederef
                          (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                          (Tstruct _fecBlock noattr)) _packetCount tint))
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef
                            (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                            (Tstruct _fecBlock noattr)) _k tint))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tint)
                                     (Etempvar _t'4 tint) tint)
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
                                                          (Tcons
                                                            (tptr tschar)
                                                            Tnil))))))))
                                            tvoid
                                            {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                              ((Etempvar _t'5 (tptr (Tstruct _zlog_category_s noattr))) ::
                               (Ebinop Oadd
                                 (Evar ___stringlit_3 (tarray tschar 19))
                                 (Econst_int (Int.repr 3) tint)
                                 (tptr tschar)) ::
                               (Ebinop Osub
                                 (Esizeof (tarray tschar 19) tulong)
                                 (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                                   (Econst_int (Int.repr 3) tint) tint)
                                 tulong) ::
                               (Evar ___func____3 (tarray tschar 37)) ::
                               (Ebinop Osub
                                 (Esizeof (tarray tschar 37) tulong)
                                 (Econst_int (Int.repr 1) tint) tulong) ::
                               (Econst_int (Int.repr 545) tint) ::
                               (Econst_int (Int.repr 20) tint) ::
                               (Evar ___stringlit_29 (tarray tschar 53)) ::
                               nil)))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                  (Tstruct _fecBlock noattr)) _complete tint)
                              (Econst_int (Int.repr 1) tint))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                      (Tstruct _fecBlock noattr)) _packets
                                    (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                  (Etempvar _pindex tint)
                                  (tptr (tptr (Tstruct _packetinfo noattr))))
                                (tptr (Tstruct _packetinfo noattr)))
                              (Econst_int (Int.repr 0) tint))))
                        (Ssequence
                          (Scall (Some _t'2)
                            (Evar _packetinfo_copyWithData (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _packetinfo noattr))
                                                               Tnil)
                                                             (tptr (Tstruct _packetinfo noattr))
                                                             cc_default))
                            ((Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                             nil))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                    (Tstruct _fecBlock noattr)) _packets
                                  (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                (Etempvar _pindex tint)
                                (tptr (tptr (Tstruct _packetinfo noattr))))
                              (tptr (Tstruct _packetinfo noattr)))
                            (Etempvar _t'2 (tptr (Tstruct _packetinfo noattr))))))))
                  (Sreturn (Some (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))))))))))))
|}.

Definition v___func____4 := {|
  gvar_info := (tarray tschar 34);
  gvar_init := (Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_blackFecActuator_addPacketToBlock := {|
  fn_return := (tptr (Tstruct _packetinfo noattr));
  fn_callconv := cc_default;
  fn_params := ((_f, (tptr (Tstruct _flow noattr))) ::
                (_fecblock, (tptr (Tstruct _fecBlock noattr))) ::
                (_pinfo, (tptr (Tstruct _packetinfo noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_newpinfo, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'2, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'1, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'33, tint) :: (_t'32, tint) ::
               (_t'31, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'30, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'29, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'28, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'27, tint) :: (_t'26, tint) :: (_t'25, tint) ::
               (_t'24, tint) ::
               (_t'23, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'22, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'21, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'20, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'19, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'18, tint) ::
               (_t'17, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'16, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'15, tint) :: (_t'14, tint) ::
               (_t'13, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'12, tint) ::
               (_t'11, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'7, tint) ::
               (_t'6, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'31 (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
    (Ssequence
      (Sset _t'32
        (Efield
          (Ederef (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
            (Tstruct _fecBlock noattr)) _complete tint))
      (Ssequence
        (Sset _t'33
          (Efield
            (Ederef (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
              (Tstruct _packetinfo noattr)) _isParity tint))
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
          ((Etempvar _t'31 (tptr (Tstruct _zlog_category_s noattr))) ::
           (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
             (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
           (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
             (Ebinop Oadd (Econst_int (Int.repr 1) tint)
               (Econst_int (Int.repr 3) tint) tint) tulong) ::
           (Evar ___func____4 (tarray tschar 34)) ::
           (Ebinop Osub (Esizeof (tarray tschar 34) tulong)
             (Econst_int (Int.repr 1) tint) tulong) ::
           (Econst_int (Int.repr 574) tint) ::
           (Econst_int (Int.repr 20) tint) ::
           (Evar ___stringlit_31 (tarray tschar 43)) ::
           (Etempvar _t'32 tint) :: (Etempvar _t'33 tint) :: nil)))))
  (Ssequence
    (Ssequence
      (Sset _t'30
        (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
      (Scall None
        (Evar _fecBlock_log (Tfunction
                              (Tcons (tptr (Tstruct _zlog_category_s noattr))
                                (Tcons (tptr (Tstruct _fecBlock noattr))
                                  Tnil)) tvoid cc_default))
        ((Etempvar _t'30 (tptr (Tstruct _zlog_category_s noattr))) ::
         (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))) :: nil)))
    (Ssequence
      (Ssequence
        (Sset _t'27
          (Efield
            (Ederef (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
              (Tstruct _fecBlock noattr)) _complete tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'27 tint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'29
                (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                ((Etempvar _t'29 (tptr (Tstruct _zlog_category_s noattr))) ::
                 (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
                   (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                 (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                   (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                     (Econst_int (Int.repr 3) tint) tint) tulong) ::
                 (Evar ___func____4 (tarray tschar 34)) ::
                 (Ebinop Osub (Esizeof (tarray tschar 34) tulong)
                   (Econst_int (Int.repr 1) tint) tulong) ::
                 (Econst_int (Int.repr 581) tint) ::
                 (Econst_int (Int.repr 20) tint) ::
                 (Evar ___stringlit_32 (tarray tschar 38)) ::
                 (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                 nil)))
            (Ssequence
              (Ssequence
                (Sset _t'28
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
                                              (Tcons (tptr tschar) Tnil))))))))
                                tvoid
                                {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                  ((Etempvar _t'28 (tptr (Tstruct _zlog_category_s noattr))) ::
                   (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
                     (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                   (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                     (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                       (Econst_int (Int.repr 3) tint) tint) tulong) ::
                   (Evar ___func____4 (tarray tschar 34)) ::
                   (Ebinop Osub (Esizeof (tarray tschar 34) tulong)
                     (Econst_int (Int.repr 1) tint) tulong) ::
                   (Econst_int (Int.repr 586) tint) ::
                   (Econst_int (Int.repr 40) tint) ::
                   (Evar ___stringlit_33 (tarray tschar 37)) ::
                   (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                   nil)))
              (Ssequence
                (Scall None
                  (Evar _packetinfo_free (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _packetinfo noattr))
                                             Tnil) tvoid cc_default))
                  ((Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                   nil))
                (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
          Sskip))
      (Ssequence
        (Ssequence
          (Sset _t'26
            (Efield
              (Ederef (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                (Tstruct _fecBlock noattr)) _packetCount tint))
          (Sassign
            (Efield
              (Ederef (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                (Tstruct _fecBlock noattr)) _packetCount tint)
            (Ebinop Oadd (Etempvar _t'26 tint) (Econst_int (Int.repr 1) tint)
              tint)))
        (Ssequence
          (Ssequence
            (Sset _t'23
              (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
            (Ssequence
              (Sset _t'24
                (Efield
                  (Ederef
                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                    (Tstruct _fecBlock noattr)) _packetCount tint))
              (Ssequence
                (Sset _t'25
                  (Efield
                    (Ederef
                      (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                      (Tstruct _fecBlock noattr)) _k tint))
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
                                              (Tcons (tptr tschar) Tnil))))))))
                                tvoid
                                {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                  ((Etempvar _t'23 (tptr (Tstruct _zlog_category_s noattr))) ::
                   (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
                     (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                   (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                     (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                       (Econst_int (Int.repr 3) tint) tint) tulong) ::
                   (Evar ___func____4 (tarray tschar 34)) ::
                   (Ebinop Osub (Esizeof (tarray tschar 34) tulong)
                     (Econst_int (Int.repr 1) tint) tulong) ::
                   (Econst_int (Int.repr 596) tint) ::
                   (Econst_int (Int.repr 20) tint) ::
                   (Evar ___stringlit_34 (tarray tschar 22)) ::
                   (Etempvar _t'24 tint) :: (Etempvar _t'25 tint) :: nil)))))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef
                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                    (Tstruct _fecBlock noattr)) _packetCount tint))
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef
                      (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                      (Tstruct _fecBlock noattr)) _k tint))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tint)
                               (Etempvar _t'4 tint) tint)
                  (Ssequence
                    (Ssequence
                      (Sset _t'22
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
                        ((Etempvar _t'22 (tptr (Tstruct _zlog_category_s noattr))) ::
                         (Ebinop Oadd
                           (Evar ___stringlit_3 (tarray tschar 19))
                           (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                         (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                           (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                             (Econst_int (Int.repr 3) tint) tint) tulong) ::
                         (Evar ___func____4 (tarray tschar 34)) ::
                         (Ebinop Osub (Esizeof (tarray tschar 34) tulong)
                           (Econst_int (Int.repr 1) tint) tulong) ::
                         (Econst_int (Int.repr 601) tint) ::
                         (Econst_int (Int.repr 20) tint) ::
                         (Evar ___stringlit_39 (tarray tschar 24)) :: nil)))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                            (Tstruct _fecBlock noattr)) _complete tint)
                        (Econst_int (Int.repr 1) tint))
                      (Ssequence
                        (Sset _t'18
                          (Efield
                            (Ederef
                              (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                              (Tstruct _packetinfo noattr)) _isParity tint))
                        (Sifthenelse (Etempvar _t'18 tint)
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'1)
                                (Evar _blackFecActuator_regenerateMissingPackets 
                                (Tfunction
                                  (Tcons (tptr (Tstruct _flow noattr))
                                    (Tcons (tptr (Tstruct _fecBlock noattr))
                                      (Tcons
                                        (tptr (Tstruct _packetinfo noattr))
                                        Tnil)))
                                  (tptr (Tstruct _packetinfo noattr))
                                  cc_default))
                                ((Etempvar _f (tptr (Tstruct _flow noattr))) ::
                                 (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))) ::
                                 (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                 nil))
                              (Sset _newpinfo
                                (Etempvar _t'1 (tptr (Tstruct _packetinfo noattr)))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'21
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
                                                              (Tcons
                                                                (tptr tschar)
                                                                Tnil))))))))
                                                tvoid
                                                {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                  ((Etempvar _t'21 (tptr (Tstruct _zlog_category_s noattr))) ::
                                   (Ebinop Oadd
                                     (Evar ___stringlit_3 (tarray tschar 19))
                                     (Econst_int (Int.repr 3) tint)
                                     (tptr tschar)) ::
                                   (Ebinop Osub
                                     (Esizeof (tarray tschar 19) tulong)
                                     (Ebinop Oadd
                                       (Econst_int (Int.repr 1) tint)
                                       (Econst_int (Int.repr 3) tint) tint)
                                     tulong) ::
                                   (Evar ___func____4 (tarray tschar 34)) ::
                                   (Ebinop Osub
                                     (Esizeof (tarray tschar 34) tulong)
                                     (Econst_int (Int.repr 1) tint) tulong) ::
                                   (Econst_int (Int.repr 610) tint) ::
                                   (Econst_int (Int.repr 20) tint) ::
                                   (Evar ___stringlit_41 (tarray tschar 61)) ::
                                   (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                   nil)))
                              (Ssequence
                                (Scall None
                                  (Evar _packetinfo_free (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _packetinfo noattr))
                                                             Tnil) tvoid
                                                           cc_default))
                                  ((Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                   nil))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'20
                                      (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                      ((Etempvar _t'20 (tptr (Tstruct _zlog_category_s noattr))) ::
                                       (Ebinop Oadd
                                         (Evar ___stringlit_3 (tarray tschar 19))
                                         (Econst_int (Int.repr 3) tint)
                                         (tptr tschar)) ::
                                       (Ebinop Osub
                                         (Esizeof (tarray tschar 19) tulong)
                                         (Ebinop Oadd
                                           (Econst_int (Int.repr 1) tint)
                                           (Econst_int (Int.repr 3) tint)
                                           tint) tulong) ::
                                       (Evar ___func____4 (tarray tschar 34)) ::
                                       (Ebinop Osub
                                         (Esizeof (tarray tschar 34) tulong)
                                         (Econst_int (Int.repr 1) tint)
                                         tulong) ::
                                       (Econst_int (Int.repr 623) tint) ::
                                       (Econst_int (Int.repr 20) tint) ::
                                       (Evar ___stringlit_42 (tarray tschar 57)) ::
                                       nil)))
                                  (Sreturn (Some (Etempvar _newpinfo (tptr (Tstruct _packetinfo noattr)))))))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'19
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
                                                            (Tcons
                                                              (tptr tschar)
                                                              Tnil))))))))
                                              tvoid
                                              {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                ((Etempvar _t'19 (tptr (Tstruct _zlog_category_s noattr))) ::
                                 (Ebinop Oadd
                                   (Evar ___stringlit_3 (tarray tschar 19))
                                   (Econst_int (Int.repr 3) tint)
                                   (tptr tschar)) ::
                                 (Ebinop Osub
                                   (Esizeof (tarray tschar 19) tulong)
                                   (Ebinop Oadd
                                     (Econst_int (Int.repr 1) tint)
                                     (Econst_int (Int.repr 3) tint) tint)
                                   tulong) ::
                                 (Evar ___func____4 (tarray tschar 34)) ::
                                 (Ebinop Osub
                                   (Esizeof (tarray tschar 34) tulong)
                                   (Econst_int (Int.repr 1) tint) tulong) ::
                                 (Econst_int (Int.repr 628) tint) ::
                                 (Econst_int (Int.repr 20) tint) ::
                                 (Evar ___stringlit_40 (tarray tschar 53)) ::
                                 nil)))
                            (Sreturn (Some (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))))))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'17
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
                        ((Etempvar _t'17 (tptr (Tstruct _zlog_category_s noattr))) ::
                         (Ebinop Oadd
                           (Evar ___stringlit_3 (tarray tschar 19))
                           (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                         (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                           (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                             (Econst_int (Int.repr 3) tint) tint) tulong) ::
                         (Evar ___func____4 (tarray tschar 34)) ::
                         (Ebinop Osub (Esizeof (tarray tschar 34) tulong)
                           (Econst_int (Int.repr 1) tint) tulong) ::
                         (Econst_int (Int.repr 637) tint) ::
                         (Econst_int (Int.repr 20) tint) ::
                         (Evar ___stringlit_35 (tarray tschar 32)) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'10
                          (Efield
                            (Ederef
                              (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                              (Tstruct _packetinfo noattr)) _blockIndex tint))
                        (Ssequence
                          (Sset _t'11
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                    (Tstruct _fecBlock noattr)) _packets
                                  (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                (Etempvar _t'10 tint)
                                (tptr (tptr (Tstruct _packetinfo noattr))))
                              (tptr (Tstruct _packetinfo noattr))))
                          (Sifthenelse (Ebinop One
                                         (Etempvar _t'11 (tptr (Tstruct _packetinfo noattr)))
                                         (Ecast
                                           (Econst_int (Int.repr 0) tint)
                                           (tptr tvoid)) tint)
                            (Ssequence
                              (Ssequence
                                (Sset _t'13
                                  (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                (Ssequence
                                  (Sset _t'14
                                    (Efield
                                      (Ederef
                                        (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                        (Tstruct _packetinfo noattr))
                                      _blockIndex tint))
                                  (Ssequence
                                    (Sset _t'15
                                      (Efield
                                        (Ederef
                                          (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                          (Tstruct _packetinfo noattr))
                                        _blockIndex tint))
                                    (Ssequence
                                      (Sset _t'16
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                (Tstruct _fecBlock noattr))
                                              _packets
                                              (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                            (Etempvar _t'15 tint)
                                            (tptr (tptr (Tstruct _packetinfo noattr))))
                                          (tptr (Tstruct _packetinfo noattr))))
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
                                        ((Etempvar _t'13 (tptr (Tstruct _zlog_category_s noattr))) ::
                                         (Ebinop Oadd
                                           (Evar ___stringlit_3 (tarray tschar 19))
                                           (Econst_int (Int.repr 3) tint)
                                           (tptr tschar)) ::
                                         (Ebinop Osub
                                           (Esizeof (tarray tschar 19) tulong)
                                           (Ebinop Oadd
                                             (Econst_int (Int.repr 1) tint)
                                             (Econst_int (Int.repr 3) tint)
                                             tint) tulong) ::
                                         (Evar ___func____4 (tarray tschar 34)) ::
                                         (Ebinop Osub
                                           (Esizeof (tarray tschar 34) tulong)
                                           (Econst_int (Int.repr 1) tint)
                                           tulong) ::
                                         (Econst_int (Int.repr 639) tint) ::
                                         (Econst_int (Int.repr 100) tint) ::
                                         (Evar ___stringlit_36 (tarray tschar 68)) ::
                                         (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                         (Etempvar _t'14 tint) ::
                                         (Etempvar _t'16 (tptr (Tstruct _packetinfo noattr))) ::
                                         nil))))))
                              (Ssequence
                                (Sset _t'12
                                  (Efield
                                    (Ederef
                                      (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                      (Tstruct _fecBlock noattr))
                                    _packetCount tint))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                      (Tstruct _fecBlock noattr))
                                    _packetCount tint)
                                  (Ebinop Osub (Etempvar _t'12 tint)
                                    (Econst_int (Int.repr 1) tint) tint))))
                            Sskip)))
                      (Ssequence
                        (Sset _t'5
                          (Efield
                            (Ederef
                              (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                              (Tstruct _packetinfo noattr)) _isParity tint))
                        (Sifthenelse (Etempvar _t'5 tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'9
                                (Efield
                                  (Ederef
                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                    (Tstruct _packetinfo noattr)) _blockIndex
                                  tint))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                        (Tstruct _fecBlock noattr)) _packets
                                      (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                    (Etempvar _t'9 tint)
                                    (tptr (tptr (Tstruct _packetinfo noattr))))
                                  (tptr (Tstruct _packetinfo noattr)))
                                (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'8
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
                                                              (Tcons
                                                                (tptr tschar)
                                                                Tnil))))))))
                                                tvoid
                                                {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                  ((Etempvar _t'8 (tptr (Tstruct _zlog_category_s noattr))) ::
                                   (Ebinop Oadd
                                     (Evar ___stringlit_3 (tarray tschar 19))
                                     (Econst_int (Int.repr 3) tint)
                                     (tptr tschar)) ::
                                   (Ebinop Osub
                                     (Esizeof (tarray tschar 19) tulong)
                                     (Ebinop Oadd
                                       (Econst_int (Int.repr 1) tint)
                                       (Econst_int (Int.repr 3) tint) tint)
                                     tulong) ::
                                   (Evar ___func____4 (tarray tschar 34)) ::
                                   (Ebinop Osub
                                     (Esizeof (tarray tschar 34) tulong)
                                     (Econst_int (Int.repr 1) tint) tulong) ::
                                   (Econst_int (Int.repr 651) tint) ::
                                   (Econst_int (Int.repr 20) tint) ::
                                   (Evar ___stringlit_38 (tarray tschar 48)) ::
                                   nil)))
                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'2)
                                (Evar _packetinfo_copyWithData (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _packetinfo noattr))
                                                                   Tnil)
                                                                 (tptr (Tstruct _packetinfo noattr))
                                                                 cc_default))
                                ((Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                 nil))
                              (Ssequence
                                (Sset _t'7
                                  (Efield
                                    (Ederef
                                      (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                      (Tstruct _packetinfo noattr))
                                    _blockIndex tint))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                          (Tstruct _fecBlock noattr))
                                        _packets
                                        (tarray (tptr (Tstruct _packetinfo noattr)) 256))
                                      (Etempvar _t'7 tint)
                                      (tptr (tptr (Tstruct _packetinfo noattr))))
                                    (tptr (Tstruct _packetinfo noattr)))
                                  (Etempvar _t'2 (tptr (Tstruct _packetinfo noattr))))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'6
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
                                                              (Tcons
                                                                (tptr tschar)
                                                                Tnil))))))))
                                                tvoid
                                                {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                                  ((Etempvar _t'6 (tptr (Tstruct _zlog_category_s noattr))) ::
                                   (Ebinop Oadd
                                     (Evar ___stringlit_3 (tarray tschar 19))
                                     (Econst_int (Int.repr 3) tint)
                                     (tptr tschar)) ::
                                   (Ebinop Osub
                                     (Esizeof (tarray tschar 19) tulong)
                                     (Ebinop Oadd
                                       (Econst_int (Int.repr 1) tint)
                                       (Econst_int (Int.repr 3) tint) tint)
                                     tulong) ::
                                   (Evar ___func____4 (tarray tschar 34)) ::
                                   (Ebinop Osub
                                     (Esizeof (tarray tschar 34) tulong)
                                     (Econst_int (Int.repr 1) tint) tulong) ::
                                   (Econst_int (Int.repr 657) tint) ::
                                   (Econst_int (Int.repr 20) tint) ::
                                   (Evar ___stringlit_37 (tarray tschar 63)) ::
                                   nil)))
                              (Sreturn (Some (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))))))))))))
            (Sreturn (Some (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))))))))))
|}.

Definition v___func____5 := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_blackFecActuator := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_pinfo, (tptr (Tstruct _packetinfo noattr))) ::
                (_pbeg, (tptr (tptr (Tstruct _packetinfo noattr)))) ::
                (_pend, (tptr (tptr (Tstruct _packetinfo noattr)))) :: nil);
  fn_vars := ((_fecparams, (Tstruct _fecParams noattr)) :: nil);
  fn_temps := ((_f, (tptr (Tstruct _flow noattr))) :: (_k, tint) ::
               (_h, tint) :: (_flowSeq, tint) :: (_pindex, tint) ::
               (_isParity, tint) :: (_blockSeq, tint) ::
               (_currTime, tdouble) ::
               (_currblock, (tptr (Tstruct _fecBlock noattr))) ::
               (_fecblock, (tptr (Tstruct _fecBlock noattr))) ::
               (_oldblock, (tptr (Tstruct _fecBlock noattr))) ::
               (_newblock, (tptr (Tstruct _fecBlock noattr))) ::
               (_fecblocknext, (tptr (Tstruct _fecBlock noattr))) ::
               (_returnlist, (tptr (Tstruct _packetinfo noattr))) ::
               (_p, (tptr (Tstruct _packetinfo noattr))) :: (_t'12, tint) ::
               (_t'11, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'10, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'9, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'8, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'7, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'6, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'5, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'4, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'3, tdouble) ::
               (_t'2, (tptr (Tstruct _deducehdr noattr))) :: (_t'1, tuint) ::
               (_t'82, (tptr (Tstruct _flow noattr))) ::
               (_t'81, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'80, tuint) ::
               (_t'79, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'78, (tptr (Tstruct _flowTuple noattr))) ::
               (_t'77, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'76, tuint) ::
               (_t'75, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'74, (tptr (Tstruct _flow noattr))) ::
               (_t'73, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'72, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'71, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'70, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'69, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'68, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'67, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'66, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'65, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'64, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'63, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'62, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'61, (tptr (Tstruct _flow noattr))) ::
               (_t'60, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'59, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'58, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'57, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'56, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'55, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'54, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'53, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'52, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'51, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'50, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'49, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'48, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'47, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'46, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'45, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'44, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'43, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'42, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'41, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'40, tint) :: (_t'39, tdouble) ::
               (_t'38, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'37, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'36, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'35, (tptr (Tstruct _fecBlock noattr))) ::
               (_t'34, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'33, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'32, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'31, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'30, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'29, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'28, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'27, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'26, tint) :: (_t'25, tint) ::
               (_t'24, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'23, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'22, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'21, tint) :: (_t'20, tint) ::
               (_t'19, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'18, tint) :: (_t'17, tint) ::
               (_t'16, (tptr (Tstruct _flow noattr))) ::
               (_t'15, (tptr (Tstruct _zlog_category_s noattr))) ::
               (_t'14, (tptr (Tstruct _packetinfo noattr))) ::
               (_t'13, (tptr (Tstruct _packetinfo noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'81 (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
    (Ssequence
      (Sset _t'82
        (Efield
          (Ederef (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
            (Tstruct _packetinfo noattr)) _pflow
          (tptr (Tstruct _flow noattr))))
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
        ((Etempvar _t'81 (tptr (Tstruct _zlog_category_s noattr))) ::
         (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
           (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
         (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
           (Ebinop Oadd (Econst_int (Int.repr 1) tint)
             (Econst_int (Int.repr 3) tint) tint) tulong) ::
         (Evar ___func____5 (tarray tschar 17)) ::
         (Ebinop Osub (Esizeof (tarray tschar 17) tulong)
           (Econst_int (Int.repr 1) tint) tulong) ::
         (Econst_int (Int.repr 709) tint) ::
         (Econst_int (Int.repr 20) tint) ::
         (Evar ___stringlit_43 (tarray tschar 26)) ::
         (Efield
           (Ederef (Etempvar _t'82 (tptr (Tstruct _flow noattr)))
             (Tstruct _flow noattr)) _tuplestr_buff (tarray tschar 128)) ::
         nil))))
  (Ssequence
    (Scall None
      (Evar _packetinfo_getAParam (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _packetinfo noattr))
                                      (Tcons (tptr tvoid)
                                        (Tcons tulong Tnil))) tvoid
                                    cc_default))
      ((Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
       (Eaddrof (Evar _fecparams (Tstruct _fecParams noattr))
         (tptr (Tstruct _fecParams noattr))) ::
       (Esizeof (Tstruct _fecParams noattr) tulong) :: nil))
    (Ssequence
      (Sset _k
        (Efield (Evar _fecparams (Tstruct _fecParams noattr)) _fec_k tuchar))
      (Ssequence
        (Sset _h
          (Efield (Evar _fecparams (Tstruct _fecParams noattr)) _fec_h
            tuchar))
        (Ssequence
          (Sset _pindex
            (Efield (Evar _fecparams (Tstruct _fecParams noattr)) _fec_seq
              tuchar))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'80
                  (Efield (Evar _fecparams (Tstruct _fecParams noattr))
                    _block_seq tuint))
                (Scall (Some _t'1)
                  (Evar _ntohl (Tfunction (Tcons tuint Tnil) tuint
                                 cc_default))
                  ((Etempvar _t'80 tuint) :: nil)))
              (Sset _flowSeq (Etempvar _t'1 tuint)))
            (Ssequence
              (Sset _blockSeq (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                      (Tstruct _packetinfo noattr)) _blockIndex tint)
                  (Etempvar _pindex tint))
                (Ssequence
                  (Ssequence
                    (Sset _t'79
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
                                                  (Tcons (tptr tschar) Tnil))))))))
                                    tvoid
                                    {|cc_vararg:=(Some 8); cc_unproto:=false; cc_structret:=false|}))
                      ((Etempvar _t'79 (tptr (Tstruct _zlog_category_s noattr))) ::
                       (Ebinop Oadd (Evar ___stringlit_3 (tarray tschar 19))
                         (Econst_int (Int.repr 3) tint) (tptr tschar)) ::
                       (Ebinop Osub (Esizeof (tarray tschar 19) tulong)
                         (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                           (Econst_int (Int.repr 3) tint) tint) tulong) ::
                       (Evar ___func____5 (tarray tschar 17)) ::
                       (Ebinop Osub (Esizeof (tarray tschar 17) tulong)
                         (Econst_int (Int.repr 1) tint) tulong) ::
                       (Econst_int (Int.repr 721) tint) ::
                       (Econst_int (Int.repr 20) tint) ::
                       (Evar ___stringlit_44 (tarray tschar 72)) ::
                       (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                       (Etempvar _k tint) :: (Etempvar _h tint) ::
                       (Etempvar _pindex tint) ::
                       (Etempvar _blockSeq tint) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'77
                        (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                      (Ssequence
                        (Sset _t'78
                          (Efield
                            (Ederef
                              (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                              (Tstruct _packetinfo noattr)) _tuple
                            (tptr (Tstruct _flowTuple noattr))))
                        (Scall None
                          (Evar _flowTuple_log (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _zlog_category_s noattr))
                                                   (Tcons tint
                                                     (Tcons
                                                       (tptr (Tstruct _flowTuple noattr))
                                                       Tnil))) tvoid
                                                 cc_default))
                          ((Etempvar _t'77 (tptr (Tstruct _zlog_category_s noattr))) ::
                           (Econst_int (Int.repr 20) tint) ::
                           (Etempvar _t'78 (tptr (Tstruct _flowTuple noattr))) ::
                           nil))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'2)
                          (Evar _packetinfo_get_deducehdrFromPacket (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    Tnil)
                                                                    (tptr (Tstruct _deducehdr noattr))
                                                                    cc_default))
                          ((Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                           nil))
                        (Ssequence
                          (Sset _t'75
                            (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                          (Ssequence
                            (Sset _t'76
                              (Efield
                                (Ederef
                                  (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                  (Tstruct _packetinfo noattr))
                                _deduceparamsizeWithPad tuint))
                            (Scall None
                              (Evar _deducehdr_logAll (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _zlog_category_s noattr))
                                                          (Tcons tint
                                                            (Tcons
                                                              (tptr (Tstruct _deducehdr noattr))
                                                              (Tcons
                                                                (tptr tuchar)
                                                                (Tcons tuint
                                                                  Tnil)))))
                                                        tvoid cc_default))
                              ((Etempvar _t'75 (tptr (Tstruct _zlog_category_s noattr))) ::
                               (Econst_int (Int.repr 20) tint) ::
                               (Etempvar _t'2 (tptr (Tstruct _deducehdr noattr))) ::
                               (Efield
                                 (Ederef
                                   (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                   (Tstruct _packetinfo noattr))
                                 _actuatorParams (tarray tuchar 256)) ::
                               (Etempvar _t'76 tuint) :: nil)))))
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _pindex tint)
                                       (Etempvar _k tint) tint)
                          (Ssequence
                            (Sset _isParity (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                    (Tstruct _packetinfo noattr)) _isParity
                                  tint) (Econst_int (Int.repr 0) tint))
                              (Sset _blockSeq
                                (Ebinop Osub (Etempvar _flowSeq tint)
                                  (Etempvar _pindex tint) tint))))
                          (Ssequence
                            (Sset _isParity (Econst_int (Int.repr 1) tint))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                    (Tstruct _packetinfo noattr)) _isParity
                                  tint) (Econst_int (Int.repr 1) tint))
                              (Sset _blockSeq (Etempvar _flowSeq tint)))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'73
                              (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                            (Ssequence
                              (Sset _t'74
                                (Efield
                                  (Ederef
                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                    (Tstruct _packetinfo noattr)) _pflow
                                  (tptr (Tstruct _flow noattr))))
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
                                ((Etempvar _t'73 (tptr (Tstruct _zlog_category_s noattr))) ::
                                 (Ebinop Oadd
                                   (Evar ___stringlit_3 (tarray tschar 19))
                                   (Econst_int (Int.repr 3) tint)
                                   (tptr tschar)) ::
                                 (Ebinop Osub
                                   (Esizeof (tarray tschar 19) tulong)
                                   (Ebinop Oadd
                                     (Econst_int (Int.repr 1) tint)
                                     (Econst_int (Int.repr 3) tint) tint)
                                   tulong) ::
                                 (Evar ___func____5 (tarray tschar 17)) ::
                                 (Ebinop Osub
                                   (Esizeof (tarray tschar 17) tulong)
                                   (Econst_int (Int.repr 1) tint) tulong) ::
                                 (Econst_int (Int.repr 749) tint) ::
                                 (Econst_int (Int.repr 20) tint) ::
                                 (Evar ___stringlit_45 (tarray tschar 60)) ::
                                 (Efield
                                   (Ederef
                                     (Etempvar _t'74 (tptr (Tstruct _flow noattr)))
                                     (Tstruct _flow noattr)) _tuplestr_buff
                                   (tarray tschar 128)) ::
                                 (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                 (Etempvar _k tint) :: (Etempvar _h tint) ::
                                 (Etempvar _blockSeq tint) ::
                                 (Etempvar _pindex tint) ::
                                 (Etempvar _isParity tint) :: nil))))
                          (Ssequence
                            (Sset _f
                              (Efield
                                (Ederef
                                  (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                  (Tstruct _packetinfo noattr)) _pflow
                                (tptr (Tstruct _flow noattr))))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'3)
                                  (Evar _util_getCurrentTime (Tfunction Tnil
                                                               tdouble
                                                               {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
                                  nil)
                                (Sset _currTime (Etempvar _t'3 tdouble)))
                              (Ssequence
                                (Sset _currblock
                                  (Efield
                                    (Ederef
                                      (Etempvar _f (tptr (Tstruct _flow noattr)))
                                      (Tstruct _flow noattr)) _blockListTail
                                    (tptr (Tstruct _fecBlock noattr))))
                                (Ssequence
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _currblock (tptr (Tstruct _fecBlock noattr)))
                                                 (Ecast
                                                   (Econst_int (Int.repr 0) tint)
                                                   (tptr tvoid)) tint)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'72
                                          (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                        (Scall None
                                          (Evar _zlog (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _zlog_category_s noattr))
                                                          (Tcons
                                                            (tptr tschar)
                                                            (Tcons tulong
                                                              (Tcons
                                                                (tptr tschar)
                                                                (Tcons tulong
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
                                             (Evar ___stringlit_3 (tarray tschar 19))
                                             (Econst_int (Int.repr 3) tint)
                                             (tptr tschar)) ::
                                           (Ebinop Osub
                                             (Esizeof (tarray tschar 19) tulong)
                                             (Ebinop Oadd
                                               (Econst_int (Int.repr 1) tint)
                                               (Econst_int (Int.repr 3) tint)
                                               tint) tulong) ::
                                           (Evar ___func____5 (tarray tschar 17)) ::
                                           (Ebinop Osub
                                             (Esizeof (tarray tschar 17) tulong)
                                             (Econst_int (Int.repr 1) tint)
                                             tulong) ::
                                           (Econst_int (Int.repr 766) tint) ::
                                           (Econst_int (Int.repr 20) tint) ::
                                           (Evar ___stringlit_46 (tarray tschar 33)) ::
                                           nil)))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'4)
                                            (Evar _fecBlock_new (Tfunction
                                                                  Tnil
                                                                  (tptr (Tstruct _fecBlock noattr))
                                                                  {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
                                            nil)
                                          (Sset _currblock
                                            (Etempvar _t'4 (tptr (Tstruct _fecBlock noattr)))))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                (Tstruct _flow noattr))
                                              _blockListHead
                                              (tptr (Tstruct _fecBlock noattr)))
                                            (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))))
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                  (Tstruct _flow noattr))
                                                _blockListTail
                                                (tptr (Tstruct _fecBlock noattr)))
                                              (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'71
                                                  (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                  ((Etempvar _t'71 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                   (Ebinop Oadd
                                                     (Evar ___stringlit_3 (tarray tschar 19))
                                                     (Econst_int (Int.repr 3) tint)
                                                     (tptr tschar)) ::
                                                   (Ebinop Osub
                                                     (Esizeof (tarray tschar 19) tulong)
                                                     (Ebinop Oadd
                                                       (Econst_int (Int.repr 1) tint)
                                                       (Econst_int (Int.repr 3) tint)
                                                       tint) tulong) ::
                                                   (Evar ___func____5 (tarray tschar 17)) ::
                                                   (Ebinop Osub
                                                     (Esizeof (tarray tschar 17) tulong)
                                                     (Econst_int (Int.repr 1) tint)
                                                     tulong) ::
                                                   (Econst_int (Int.repr 774) tint) ::
                                                   (Econst_int (Int.repr 20) tint) ::
                                                   (Evar ___stringlit_47 (tarray tschar 46)) ::
                                                   nil)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'70
                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                  (Scall None
                                                    (Evar _fecBlock_log 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _zlog_category_s noattr))
                                                        (Tcons
                                                          (tptr (Tstruct _fecBlock noattr))
                                                          Tnil)) tvoid
                                                      cc_default))
                                                    ((Etempvar _t'70 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                     (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))) ::
                                                     nil)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Scall (Some _t'5)
                                                      (Evar _blackFecActuator_initBlockWithPacket 
                                                      (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _flow noattr))
                                                          (Tcons
                                                            (tptr (Tstruct _fecBlock noattr))
                                                            (Tcons
                                                              (tptr (Tstruct _packetinfo noattr))
                                                              (Tcons tint
                                                                (Tcons tint
                                                                  (Tcons tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tdouble
                                                                    Tnil)))))))))
                                                        (tptr (Tstruct _packetinfo noattr))
                                                        cc_default))
                                                      ((Etempvar _f (tptr (Tstruct _flow noattr))) ::
                                                       (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))) ::
                                                       (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                       (Etempvar _blockSeq tint) ::
                                                       (Etempvar _k tint) ::
                                                       (Etempvar _h tint) ::
                                                       (Etempvar _pindex tint) ::
                                                       (Etempvar _isParity tint) ::
                                                       (Ebinop Oadd
                                                         (Etempvar _currTime tdouble)
                                                         (Econst_float (Float.of_bits (Int64.repr 4621819117588971520)) tdouble)
                                                         tdouble) :: nil))
                                                    (Sset _returnlist
                                                      (Etempvar _t'5 (tptr (Tstruct _packetinfo noattr)))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'69
                                                        (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                        ((Etempvar _t'69 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                         (Ebinop Oadd
                                                           (Evar ___stringlit_3 (tarray tschar 19))
                                                           (Econst_int (Int.repr 3) tint)
                                                           (tptr tschar)) ::
                                                         (Ebinop Osub
                                                           (Esizeof (tarray tschar 19) tulong)
                                                           (Ebinop Oadd
                                                             (Econst_int (Int.repr 1) tint)
                                                             (Econst_int (Int.repr 3) tint)
                                                             tint) tulong) ::
                                                         (Evar ___func____5 (tarray tschar 17)) ::
                                                         (Ebinop Osub
                                                           (Esizeof (tarray tschar 17) tulong)
                                                           (Econst_int (Int.repr 1) tint)
                                                           tulong) ::
                                                         (Econst_int (Int.repr 787) tint) ::
                                                         (Econst_int (Int.repr 20) tint) ::
                                                         (Evar ___stringlit_48 (tarray tschar 45)) ::
                                                         nil)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'68
                                                          (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                        (Scall None
                                                          (Evar _fecBlock_log 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _zlog_category_s noattr))
                                                              (Tcons
                                                                (tptr (Tstruct _fecBlock noattr))
                                                                Tnil)) tvoid
                                                            cc_default))
                                                          ((Etempvar _t'68 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                           (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))) ::
                                                           nil)))
                                                      (Sgoto _RETURN))))))))))
                                    Sskip)
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'67
                                        (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                        ((Etempvar _t'67 (tptr (Tstruct _zlog_category_s noattr))) ::
                                         (Ebinop Oadd
                                           (Evar ___stringlit_3 (tarray tschar 19))
                                           (Econst_int (Int.repr 3) tint)
                                           (tptr tschar)) ::
                                         (Ebinop Osub
                                           (Esizeof (tarray tschar 19) tulong)
                                           (Ebinop Oadd
                                             (Econst_int (Int.repr 1) tint)
                                             (Econst_int (Int.repr 3) tint)
                                             tint) tulong) ::
                                         (Evar ___func____5 (tarray tschar 17)) ::
                                         (Ebinop Osub
                                           (Esizeof (tarray tschar 17) tulong)
                                           (Econst_int (Int.repr 1) tint)
                                           tulong) ::
                                         (Econst_int (Int.repr 792) tint) ::
                                         (Econst_int (Int.repr 20) tint) ::
                                         (Evar ___stringlit_49 (tarray tschar 37)) ::
                                         (Etempvar _blockSeq tint) :: nil)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'66
                                          (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                        (Scall None
                                          (Evar _fecBlock_log (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _zlog_category_s noattr))
                                                                  (Tcons
                                                                    (tptr (Tstruct _fecBlock noattr))
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                          ((Etempvar _t'66 (tptr (Tstruct _zlog_category_s noattr))) ::
                                           (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))) ::
                                           nil)))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'20
                                            (Efield
                                              (Ederef
                                                (Etempvar _currblock (tptr (Tstruct _fecBlock noattr)))
                                                (Tstruct _fecBlock noattr))
                                              _blockSeq tint))
                                          (Sifthenelse (Ebinop Oeq
                                                         (Etempvar _blockSeq tint)
                                                         (Etempvar _t'20 tint)
                                                         tint)
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'65
                                                  (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                  ((Etempvar _t'65 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                   (Ebinop Oadd
                                                     (Evar ___stringlit_3 (tarray tschar 19))
                                                     (Econst_int (Int.repr 3) tint)
                                                     (tptr tschar)) ::
                                                   (Ebinop Osub
                                                     (Esizeof (tarray tschar 19) tulong)
                                                     (Ebinop Oadd
                                                       (Econst_int (Int.repr 1) tint)
                                                       (Econst_int (Int.repr 3) tint)
                                                       tint) tulong) ::
                                                   (Evar ___func____5 (tarray tschar 17)) ::
                                                   (Ebinop Osub
                                                     (Esizeof (tarray tschar 17) tulong)
                                                     (Econst_int (Int.repr 1) tint)
                                                     tulong) ::
                                                   (Econst_int (Int.repr 802) tint) ::
                                                   (Econst_int (Int.repr 20) tint) ::
                                                   (Evar ___stringlit_64 (tarray tschar 32)) ::
                                                   nil)))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'6)
                                                    (Evar _blackFecActuator_addPacketToBlock 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _flow noattr))
                                                        (Tcons
                                                          (tptr (Tstruct _fecBlock noattr))
                                                          (Tcons
                                                            (tptr (Tstruct _packetinfo noattr))
                                                            Tnil)))
                                                      (tptr (Tstruct _packetinfo noattr))
                                                      cc_default))
                                                    ((Etempvar _f (tptr (Tstruct _flow noattr))) ::
                                                     (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))) ::
                                                     (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                     nil))
                                                  (Sset _returnlist
                                                    (Etempvar _t'6 (tptr (Tstruct _packetinfo noattr)))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'64
                                                      (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                      ((Etempvar _t'64 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                       (Ebinop Oadd
                                                         (Evar ___stringlit_3 (tarray tschar 19))
                                                         (Econst_int (Int.repr 3) tint)
                                                         (tptr tschar)) ::
                                                       (Ebinop Osub
                                                         (Esizeof (tarray tschar 19) tulong)
                                                         (Ebinop Oadd
                                                           (Econst_int (Int.repr 1) tint)
                                                           (Econst_int (Int.repr 3) tint)
                                                           tint) tulong) ::
                                                       (Evar ___func____5 (tarray tschar 17)) ::
                                                       (Ebinop Osub
                                                         (Esizeof (tarray tschar 17) tulong)
                                                         (Econst_int (Int.repr 1) tint)
                                                         tulong) ::
                                                       (Econst_int (Int.repr 807) tint) ::
                                                       (Econst_int (Int.repr 20) tint) ::
                                                       (Evar ___stringlit_58 (tarray tschar 25)) ::
                                                       nil)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'63
                                                        (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                      (Scall None
                                                        (Evar _fecBlock_log 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _zlog_category_s noattr))
                                                            (Tcons
                                                              (tptr (Tstruct _fecBlock noattr))
                                                              Tnil)) tvoid
                                                          cc_default))
                                                        ((Etempvar _t'63 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                         (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))) ::
                                                         nil)))
                                                    (Sgoto _RETURN)))))
                                            (Ssequence
                                              (Sset _t'21
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _currblock (tptr (Tstruct _fecBlock noattr)))
                                                    (Tstruct _fecBlock noattr))
                                                  _blockSeq tint))
                                              (Sifthenelse (Ebinop Ogt
                                                             (Etempvar _blockSeq tint)
                                                             (Etempvar _t'21 tint)
                                                             tint)
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'62
                                                      (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                      ((Etempvar _t'62 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                       (Ebinop Oadd
                                                         (Evar ___stringlit_3 (tarray tschar 19))
                                                         (Econst_int (Int.repr 3) tint)
                                                         (tptr tschar)) ::
                                                       (Ebinop Osub
                                                         (Esizeof (tarray tschar 19) tulong)
                                                         (Ebinop Oadd
                                                           (Econst_int (Int.repr 1) tint)
                                                           (Econst_int (Int.repr 3) tint)
                                                           tint) tulong) ::
                                                       (Evar ___func____5 (tarray tschar 17)) ::
                                                       (Ebinop Osub
                                                         (Esizeof (tarray tschar 17) tulong)
                                                         (Econst_int (Int.repr 1) tint)
                                                         tulong) ::
                                                       (Econst_int (Int.repr 819) tint) ::
                                                       (Econst_int (Int.repr 20) tint) ::
                                                       (Evar ___stringlit_63 (tarray tschar 30)) ::
                                                       nil)))
                                                  (Ssequence
                                                    (Sset _oldblock
                                                      (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'7)
                                                          (Evar _fecBlock_new 
                                                          (Tfunction Tnil
                                                            (tptr (Tstruct _fecBlock noattr))
                                                            {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
                                                          nil)
                                                        (Sset _currblock
                                                          (Etempvar _t'7 (tptr (Tstruct _fecBlock noattr)))))
                                                      (Ssequence
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _oldblock (tptr (Tstruct _fecBlock noattr)))
                                                              (Tstruct _fecBlock noattr))
                                                            _next
                                                            (tptr (Tstruct _fecBlock noattr)))
                                                          (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))))
                                                        (Ssequence
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _currblock (tptr (Tstruct _fecBlock noattr)))
                                                                (Tstruct _fecBlock noattr))
                                                              _prev
                                                              (tptr (Tstruct _fecBlock noattr)))
                                                            (Etempvar _oldblock (tptr (Tstruct _fecBlock noattr))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'61
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Tstruct _packetinfo noattr))
                                                                  _pflow
                                                                  (tptr (Tstruct _flow noattr))))
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _t'61 (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                  _blockListTail
                                                                  (tptr (Tstruct _fecBlock noattr)))
                                                                (Etempvar _currblock (tptr (Tstruct _fecBlock noattr)))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'60
                                                                  (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                  ((Etempvar _t'60 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                   (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                   (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                   (Evar ___func____5 (tarray tschar 17)) ::
                                                                   (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                   (Econst_int (Int.repr 829) tint) ::
                                                                   (Econst_int (Int.repr 20) tint) ::
                                                                   (Evar ___stringlit_47 (tarray tschar 46)) ::
                                                                   nil)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'59
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                  (Scall None
                                                                    (Evar _fecBlock_log 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _fecBlock noattr))
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'59 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))) ::
                                                                    nil)))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Scall (Some _t'8)
                                                                    (Evar _blackFecActuator_initBlockWithPacket 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _flow noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _fecBlock noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tdouble
                                                                    Tnil)))))))))
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    cc_default))
                                                                    ((Etempvar _f (tptr (Tstruct _flow noattr))) ::
                                                                    (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))) ::
                                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                                    (Etempvar _blockSeq tint) ::
                                                                    (Etempvar _k tint) ::
                                                                    (Etempvar _h tint) ::
                                                                    (Etempvar _pindex tint) ::
                                                                    (Etempvar _isParity tint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _currTime tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4621819117588971520)) tdouble)
                                                                    tdouble) ::
                                                                    nil))
                                                                    (Sset _returnlist
                                                                    (Etempvar _t'8 (tptr (Tstruct _packetinfo noattr)))))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'58
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    ((Etempvar _t'58 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____5 (tarray tschar 17)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 841) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_48 (tarray tschar 45)) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'57
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall None
                                                                    (Evar _fecBlock_log 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _fecBlock noattr))
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'57 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Etempvar _currblock (tptr (Tstruct _fecBlock noattr))) ::
                                                                    nil)))
                                                                    (Sgoto _RETURN))))))))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'56
                                                      (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                      ((Etempvar _t'56 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                       (Ebinop Oadd
                                                         (Evar ___stringlit_3 (tarray tschar 19))
                                                         (Econst_int (Int.repr 3) tint)
                                                         (tptr tschar)) ::
                                                       (Ebinop Osub
                                                         (Esizeof (tarray tschar 19) tulong)
                                                         (Ebinop Oadd
                                                           (Econst_int (Int.repr 1) tint)
                                                           (Econst_int (Int.repr 3) tint)
                                                           tint) tulong) ::
                                                       (Evar ___func____5 (tarray tschar 17)) ::
                                                       (Ebinop Osub
                                                         (Esizeof (tarray tschar 17) tulong)
                                                         (Econst_int (Int.repr 1) tint)
                                                         tulong) ::
                                                       (Econst_int (Int.repr 850) tint) ::
                                                       (Econst_int (Int.repr 20) tint) ::
                                                       (Evar ___stringlit_50 (tarray tschar 32)) ::
                                                       nil)))
                                                  (Ssequence
                                                    (Sset _fecblocknext
                                                      (Ecast
                                                        (Econst_int (Int.repr 0) tint)
                                                        (tptr (Tstruct _fecBlock noattr))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _fecblock
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                              (Tstruct _flow noattr))
                                                            _blockListHead
                                                            (tptr (Tstruct _fecBlock noattr))))
                                                        (Sloop
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop One
                                                                (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                (Etempvar _currblock (tptr (Tstruct _fecBlock noattr)))
                                                                tint)
                                                              Sskip
                                                              Sbreak)
                                                            (Ssequence
                                                              (Sset _fecblocknext
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                  _next
                                                                  (tptr (Tstruct _fecBlock noattr))))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'39
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _timeout
                                                                    tdouble))
                                                                  (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _currTime tdouble)
                                                                    (Etempvar _t'39 tdouble)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'55
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    ((Etempvar _t'55 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____5 (tarray tschar 17)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 863) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_51 (tarray tschar 24)) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'40
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _blockSeq
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Etempvar _blockSeq tint)
                                                                    (Etempvar _t'40 tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _isParity tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'54
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    ((Etempvar _t'54 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____5 (tarray tschar 17)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 871) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_52 (tarray tschar 47)) ::
                                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _packetinfo_free 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                                    nil))
                                                                    (Sset _pinfo
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (Tstruct _packetinfo noattr))))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'47
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _prev
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'47 (tptr (Tstruct _fecBlock noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'53
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _next
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _blockListHead
                                                                    (tptr (Tstruct _fecBlock noattr)))
                                                                    (Etempvar _t'53 (tptr (Tstruct _fecBlock noattr)))))
                                                                    (Ssequence
                                                                    (Sset _t'52
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _next
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'52 (tptr (Tstruct _fecBlock noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _blockListTail
                                                                    (tptr (Tstruct _fecBlock noattr)))
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    Sskip)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'50
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _prev
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'51
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _next
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'50 (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _next
                                                                    (tptr (Tstruct _fecBlock noattr)))
                                                                    (Etempvar _t'51 (tptr (Tstruct _fecBlock noattr))))))
                                                                    (Ssequence
                                                                    (Sset _t'48
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _next
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'48 (tptr (Tstruct _fecBlock noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'49
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _prev
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _blockListTail
                                                                    (tptr (Tstruct _fecBlock noattr)))
                                                                    (Etempvar _t'49 (tptr (Tstruct _fecBlock noattr)))))
                                                                    Sskip)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'44
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _next
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _t'44 (tptr (Tstruct _fecBlock noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'45
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _next
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'46
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _prev
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'45 (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _prev
                                                                    (tptr (Tstruct _fecBlock noattr)))
                                                                    (Etempvar _t'46 (tptr (Tstruct _fecBlock noattr))))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'43
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    ((Etempvar _t'43 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____5 (tarray tschar 17)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 911) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_53 (tarray tschar 27)) ::
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _fecBlock_free 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _fecBlock noattr))
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'42
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____5 (tarray tschar 17)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 913) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_54 (tarray tschar 20)) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'41
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    ((Etempvar _t'41 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____5 (tarray tschar 17)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 918) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_55 (tarray tschar 36)) ::
                                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _returnlist
                                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
                                                                    (Sgoto _RETURN)))))))))
                                                                    Sskip)))
                                                                    Sskip))
                                                                (Ssequence
                                                                  (Sset _t'25
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _blockSeq
                                                                    tint))
                                                                  (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _t'25 tint)
                                                                    (Etempvar _blockSeq tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'38
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    ((Etempvar _t'38 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____5 (tarray tschar 17)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 935) tint) ::
                                                                    (Econst_int (Int.repr 80) tint) ::
                                                                    (Evar ___stringlit_59 (tarray tschar 59)) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'9)
                                                                    (Evar _fecBlock_new 
                                                                    (Tfunction
                                                                    Tnil
                                                                    (tptr (Tstruct _fecBlock noattr))
                                                                    {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
                                                                    nil)
                                                                    (Sset _newblock
                                                                    (Etempvar _t'9 (tptr (Tstruct _fecBlock noattr)))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _next
                                                                    (tptr (Tstruct _fecBlock noattr)))
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'37
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _prev
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _prev
                                                                    (tptr (Tstruct _fecBlock noattr)))
                                                                    (Etempvar _t'37 (tptr (Tstruct _fecBlock noattr)))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _prev
                                                                    (tptr (Tstruct _fecBlock noattr)))
                                                                    (Etempvar _newblock (tptr (Tstruct _fecBlock noattr))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'35
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _prev
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'35 (tptr (Tstruct _fecBlock noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _f (tptr (Tstruct _flow noattr)))
                                                                    (Tstruct _flow noattr))
                                                                    _blockListHead
                                                                    (tptr (Tstruct _fecBlock noattr)))
                                                                    (Etempvar _newblock (tptr (Tstruct _fecBlock noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'36
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _newblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _prev
                                                                    (tptr (Tstruct _fecBlock noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'36 (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _next
                                                                    (tptr (Tstruct _fecBlock noattr)))
                                                                    (Etempvar _newblock (tptr (Tstruct _fecBlock noattr)))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'34
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    ((Etempvar _t'34 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____5 (tarray tschar 17)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 949) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_47 (tarray tschar 46)) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'33
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall None
                                                                    (Evar _fecBlock_log 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _fecBlock noattr))
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'33 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'10)
                                                                    (Evar _blackFecActuator_initBlockWithPacket 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _flow noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _fecBlock noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tdouble
                                                                    Tnil)))))))))
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    cc_default))
                                                                    ((Etempvar _f (tptr (Tstruct _flow noattr))) ::
                                                                    (Etempvar _newblock (tptr (Tstruct _fecBlock noattr))) ::
                                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                                    (Etempvar _blockSeq tint) ::
                                                                    (Etempvar _k tint) ::
                                                                    (Etempvar _h tint) ::
                                                                    (Etempvar _pindex tint) ::
                                                                    (Etempvar _isParity tint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _currTime tdouble)
                                                                    (Econst_float (Float.of_bits (Int64.repr 4621819117588971520)) tdouble)
                                                                    tdouble) ::
                                                                    nil))
                                                                    (Sset _returnlist
                                                                    (Etempvar _t'10 (tptr (Tstruct _packetinfo noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'32
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____5 (tarray tschar 17)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 965) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_48 (tarray tschar 45)) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'31
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall None
                                                                    (Evar _fecBlock_log 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _fecBlock noattr))
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'31 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))) ::
                                                                    nil)))
                                                                    (Sgoto _RETURN))))))))))))
                                                                    (Ssequence
                                                                    (Sset _t'26
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr)))
                                                                    (Tstruct _fecBlock noattr))
                                                                    _blockSeq
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'26 tint)
                                                                    (Etempvar _blockSeq tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'30
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____5 (tarray tschar 17)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 972) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_57 (tarray tschar 48)) ::
                                                                    (Etempvar _blockSeq tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'11)
                                                                    (Evar _blackFecActuator_addPacketToBlock 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _flow noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _fecBlock noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    Tnil)))
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    cc_default))
                                                                    ((Etempvar _f (tptr (Tstruct _flow noattr))) ::
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))) ::
                                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                                    nil))
                                                                    (Sset _returnlist
                                                                    (Etempvar _t'11 (tptr (Tstruct _packetinfo noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'29
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____5 (tarray tschar 17)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 976) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_58 (tarray tschar 25)) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'28
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                                    (Scall None
                                                                    (Evar _fecBlock_log 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _zlog_category_s noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _fecBlock noattr))
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'28 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Etempvar _fecblock (tptr (Tstruct _fecBlock noattr))) ::
                                                                    nil)))
                                                                    (Sgoto _RETURN)))))
                                                                    (Ssequence
                                                                    (Sset _t'27
                                                                    (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                    ((Etempvar _t'27 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Evar ___stringlit_3 (tarray tschar 19))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tschar)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 19) tulong)
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    (Evar ___func____5 (tarray tschar 17)) ::
                                                                    (Ebinop Osub
                                                                    (Esizeof (tarray tschar 17) tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong) ::
                                                                    (Econst_int (Int.repr 981) tint) ::
                                                                    (Econst_int (Int.repr 20) tint) ::
                                                                    (Evar ___stringlit_56 (tarray tschar 53)) ::
                                                                    nil))))))))))
                                                          (Sset _fecblock
                                                            (Etempvar _fecblocknext (tptr (Tstruct _fecBlock noattr))))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'24
                                                            (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                               (Evar ___stringlit_3 (tarray tschar 19))
                                                               (Econst_int (Int.repr 3) tint)
                                                               (tptr tschar)) ::
                                                             (Ebinop Osub
                                                               (Esizeof (tarray tschar 19) tulong)
                                                               (Ebinop Oadd
                                                                 (Econst_int (Int.repr 1) tint)
                                                                 (Econst_int (Int.repr 3) tint)
                                                                 tint)
                                                               tulong) ::
                                                             (Evar ___func____5 (tarray tschar 17)) ::
                                                             (Ebinop Osub
                                                               (Esizeof (tarray tschar 17) tulong)
                                                               (Econst_int (Int.repr 1) tint)
                                                               tulong) ::
                                                             (Econst_int (Int.repr 984) tint) ::
                                                             (Econst_int (Int.repr 20) tint) ::
                                                             (Evar ___stringlit_60 (tarray tschar 35)) ::
                                                             nil)))
                                                        (Sifthenelse (Etempvar _isParity tint)
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'23
                                                                (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                ((Etempvar _t'23 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                                 (Ebinop Oadd
                                                                   (Evar ___stringlit_3 (tarray tschar 19))
                                                                   (Econst_int (Int.repr 3) tint)
                                                                   (tptr tschar)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 19) tulong)
                                                                   (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                   tulong) ::
                                                                 (Evar ___func____5 (tarray tschar 17)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 17) tulong)
                                                                   (Econst_int (Int.repr 1) tint)
                                                                   tulong) ::
                                                                 (Econst_int (Int.repr 988) tint) ::
                                                                 (Econst_int (Int.repr 20) tint) ::
                                                                 (Evar ___stringlit_62 (tarray tschar 36)) ::
                                                                 (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                                 nil)))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _packetinfo_free 
                                                                (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _packetinfo noattr))
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                                                ((Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Sset _pinfo
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (Tstruct _packetinfo noattr))))
                                                                (Sset _returnlist
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr (Tstruct _packetinfo noattr)))))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'22
                                                                (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                                   (Evar ___stringlit_3 (tarray tschar 19))
                                                                   (Econst_int (Int.repr 3) tint)
                                                                   (tptr tschar)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 19) tulong)
                                                                   (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                   tulong) ::
                                                                 (Evar ___func____5 (tarray tschar 17)) ::
                                                                 (Ebinop Osub
                                                                   (Esizeof (tarray tschar 17) tulong)
                                                                   (Econst_int (Int.repr 1) tint)
                                                                   tulong) ::
                                                                 (Econst_int (Int.repr 1015) tint) ::
                                                                 (Econst_int (Int.repr 20) tint) ::
                                                                 (Evar ___stringlit_61 (tarray tschar 36)) ::
                                                                 (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))) ::
                                                                 nil)))
                                                            (Sset _returnlist
                                                              (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))))))))))))
                                        (Ssequence
                                          (Slabel _RETURN
                                            (Ssequence
                                              (Sset _t'19
                                                (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
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
                                                ((Etempvar _t'19 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                 (Ebinop Oadd
                                                   (Evar ___stringlit_3 (tarray tschar 19))
                                                   (Econst_int (Int.repr 3) tint)
                                                   (tptr tschar)) ::
                                                 (Ebinop Osub
                                                   (Esizeof (tarray tschar 19) tulong)
                                                   (Ebinop Oadd
                                                     (Econst_int (Int.repr 1) tint)
                                                     (Econst_int (Int.repr 3) tint)
                                                     tint) tulong) ::
                                                 (Evar ___func____5 (tarray tschar 17)) ::
                                                 (Ebinop Osub
                                                   (Esizeof (tarray tschar 17) tulong)
                                                   (Econst_int (Int.repr 1) tint)
                                                   tulong) ::
                                                 (Econst_int (Int.repr 1021) tint) ::
                                                 (Econst_int (Int.repr 20) tint) ::
                                                 (Evar ___stringlit_65 (tarray tschar 28)) ::
                                                 (Etempvar _returnlist (tptr (Tstruct _packetinfo noattr))) ::
                                                 nil))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _p
                                                (Etempvar _returnlist (tptr (Tstruct _packetinfo noattr))))
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
                                                    (Sset _t'15
                                                      (Evar _zc_blackFec (tptr (Tstruct _zlog_category_s noattr))))
                                                    (Ssequence
                                                      (Sset _t'16
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                            (Tstruct _packetinfo noattr))
                                                          _pflow
                                                          (tptr (Tstruct _flow noattr))))
                                                      (Ssequence
                                                        (Sset _t'17
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                              (Tstruct _packetinfo noattr))
                                                            _blockIndex tint))
                                                        (Ssequence
                                                          (Sset _t'18
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _p (tptr (Tstruct _packetinfo noattr)))
                                                                (Tstruct _packetinfo noattr))
                                                              _isParity tint))
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
                                                            ((Etempvar _t'15 (tptr (Tstruct _zlog_category_s noattr))) ::
                                                             (Ebinop Oadd
                                                               (Evar ___stringlit_3 (tarray tschar 19))
                                                               (Econst_int (Int.repr 3) tint)
                                                               (tptr tschar)) ::
                                                             (Ebinop Osub
                                                               (Esizeof (tarray tschar 19) tulong)
                                                               (Ebinop Oadd
                                                                 (Econst_int (Int.repr 1) tint)
                                                                 (Econst_int (Int.repr 3) tint)
                                                                 tint)
                                                               tulong) ::
                                                             (Evar ___func____5 (tarray tschar 17)) ::
                                                             (Ebinop Osub
                                                               (Esizeof (tarray tschar 17) tulong)
                                                               (Econst_int (Int.repr 1) tint)
                                                               tulong) ::
                                                             (Econst_int (Int.repr 1024) tint) ::
                                                             (Econst_int (Int.repr 20) tint) ::
                                                             (Evar ___stringlit_66 (tarray tschar 61)) ::
                                                             (Etempvar _p (tptr (Tstruct _packetinfo noattr))) ::
                                                             (Etempvar _t'16 (tptr (Tstruct _flow noattr))) ::
                                                             (Etempvar _t'17 tint) ::
                                                             (Etempvar _t'18 tint) ::
                                                             nil)))))))
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
                                                (Etempvar _returnlist (tptr (Tstruct _packetinfo noattr))))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _pinfo
                                                    (Etempvar _returnlist (tptr (Tstruct _packetinfo noattr))))
                                                  (Sloop
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop One
                                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                        (Ssequence
                                                          (Sset _t'14
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                                (Tstruct _packetinfo noattr))
                                                              _next
                                                              (tptr (Tstruct _packetinfo noattr))))
                                                          (Sset _t'12
                                                            (Ecast
                                                              (Ebinop One
                                                                (Etempvar _t'14 (tptr (Tstruct _packetinfo noattr)))
                                                                (Ecast
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  (tptr tvoid))
                                                                tint) tbool)))
                                                        (Sset _t'12
                                                          (Econst_int (Int.repr 0) tint)))
                                                      (Sifthenelse (Etempvar _t'12 tint)
                                                        Sskip
                                                        Sbreak))
                                                    (Sset _pinfo
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr)))
                                                          (Tstruct _packetinfo noattr))
                                                        _next
                                                        (tptr (Tstruct _packetinfo noattr))))))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Etempvar _pend (tptr (tptr (Tstruct _packetinfo noattr))))
                                                      (tptr (Tstruct _packetinfo noattr)))
                                                    (Etempvar _pinfo (tptr (Tstruct _packetinfo noattr))))
                                                  (Ssequence
                                                    (Sset _t'13
                                                      (Ederef
                                                        (Etempvar _pbeg (tptr (tptr (Tstruct _packetinfo noattr))))
                                                        (tptr (Tstruct _packetinfo noattr))))
                                                    (Sifthenelse (Ebinop Oeq
                                                                   (Etempvar _t'13 (tptr (Tstruct _packetinfo noattr)))
                                                                   (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                   tint)
                                                      (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                                                      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))))))))))))))
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
 Composite __2164 Struct
   (Member_plain _uh_sport tushort :: Member_plain _uh_dport tushort ::
    Member_plain _uh_ulen tushort :: Member_plain _uh_sum tushort :: nil)
   noattr ::
 Composite __2165 Struct
   (Member_plain _source tushort :: Member_plain _dest tushort ::
    Member_plain _len tushort :: Member_plain _check tushort :: nil)
   noattr ::
 Composite __2163 Union
   (Member_plain 18727075383868559167%positive (Tstruct __2164 noattr) ::
    Member_plain 19015305760020270911%positive (Tstruct __2165 noattr) ::
    nil)
   noattr ::
 Composite _udphdr Struct
   (Member_plain 18727075383868559167%positive (Tunion __2163 noattr) :: nil)
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
 Composite _fecParams Struct
   (Member_plain _fec_k tuchar :: Member_plain _fec_h tuchar ::
    Member_plain _fec_seq tuchar :: Member_plain _reserved tuchar ::
    Member_plain _block_seq tuint :: nil)
   noattr ::
 Composite _fecBlock Struct
   (Member_plain _complete tint :: Member_plain _blockSeq tint ::
    Member_plain _k tint :: Member_plain _h tint ::
    Member_plain _packets (tarray (tptr (Tstruct _packetinfo noattr)) 256) ::
    Member_plain _packetCount tint :: Member_plain _timeout tdouble ::
    Member_plain _prev (tptr (Tstruct _fecBlock noattr)) ::
    Member_plain _next (tptr (Tstruct _fecBlock noattr)) :: nil)
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
     cc_default)) :: (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_27, Gvar v___stringlit_27) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_48, Gvar v___stringlit_48) ::
 (___stringlit_39, Gvar v___stringlit_39) ::
 (___stringlit_61, Gvar v___stringlit_61) ::
 (___stringlit_44, Gvar v___stringlit_44) ::
 (___stringlit_14, Gvar v___stringlit_14) ::
 (___stringlit_15, Gvar v___stringlit_15) ::
 (___stringlit_52, Gvar v___stringlit_52) ::
 (___stringlit_65, Gvar v___stringlit_65) ::
 (___stringlit_31, Gvar v___stringlit_31) ::
 (___stringlit_64, Gvar v___stringlit_64) ::
 (___stringlit_32, Gvar v___stringlit_32) ::
 (___stringlit_41, Gvar v___stringlit_41) ::
 (___stringlit_42, Gvar v___stringlit_42) ::
 (___stringlit_49, Gvar v___stringlit_49) ::
 (___stringlit_28, Gvar v___stringlit_28) ::
 (___stringlit_57, Gvar v___stringlit_57) ::
 (___stringlit_46, Gvar v___stringlit_46) ::
 (___stringlit_36, Gvar v___stringlit_36) ::
 (___stringlit_20, Gvar v___stringlit_20) ::
 (___stringlit_47, Gvar v___stringlit_47) ::
 (___stringlit_59, Gvar v___stringlit_59) ::
 (___stringlit_17, Gvar v___stringlit_17) ::
 (___stringlit_51, Gvar v___stringlit_51) ::
 (___stringlit_66, Gvar v___stringlit_66) ::
 (___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_56, Gvar v___stringlit_56) ::
 (___stringlit_43, Gvar v___stringlit_43) ::
 (___stringlit_55, Gvar v___stringlit_55) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_23, Gvar v___stringlit_23) ::
 (___stringlit_13, Gvar v___stringlit_13) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_60, Gvar v___stringlit_60) ::
 (___stringlit_62, Gvar v___stringlit_62) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_24, Gvar v___stringlit_24) ::
 (___stringlit_29, Gvar v___stringlit_29) ::
 (___stringlit_58, Gvar v___stringlit_58) ::
 (___stringlit_45, Gvar v___stringlit_45) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_54, Gvar v___stringlit_54) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_35, Gvar v___stringlit_35) ::
 (___stringlit_34, Gvar v___stringlit_34) ::
 (___stringlit_63, Gvar v___stringlit_63) ::
 (___stringlit_21, Gvar v___stringlit_21) ::
 (___stringlit_25, Gvar v___stringlit_25) ::
 (___stringlit_50, Gvar v___stringlit_50) ::
 (___stringlit_38, Gvar v___stringlit_38) ::
 (___stringlit_12, Gvar v___stringlit_12) ::
 (___stringlit_19, Gvar v___stringlit_19) ::
 (___stringlit_16, Gvar v___stringlit_16) ::
 (___stringlit_26, Gvar v___stringlit_26) ::
 (___stringlit_40, Gvar v___stringlit_40) ::
 (___stringlit_33, Gvar v___stringlit_33) ::
 (___stringlit_37, Gvar v___stringlit_37) ::
 (___stringlit_30, Gvar v___stringlit_30) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_11, Gvar v___stringlit_11) ::
 (___stringlit_10, Gvar v___stringlit_10) ::
 (___stringlit_53, Gvar v___stringlit_53) ::
 (___stringlit_22, Gvar v___stringlit_22) ::
 (___stringlit_18, Gvar v___stringlit_18) ::
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
 (_ntohl,
   Gfun(External (EF_external "ntohl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (_ntohs,
   Gfun(External (EF_external "ntohs"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
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
 (_packetinfo_copyNoData,
   Gfun(External (EF_external "packetinfo_copyNoData"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr (Tstruct _packetinfo noattr)) Tnil)
     (tptr (Tstruct _packetinfo noattr)) cc_default)) ::
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
 (_packetinfo_getAParam,
   Gfun(External (EF_external "packetinfo_getAParam"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _packetinfo noattr))
       (Tcons (tptr tvoid) (Tcons tulong Tnil))) tvoid cc_default)) ::
 (_fecCommon_maskHeader,
   Gfun(External (EF_external "fecCommon_maskHeader"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _ip noattr)) Tnil) tvoid cc_default)) ::
 (_fecBlock_new,
   Gfun(External (EF_external "fecBlock_new"
                   (mksignature nil AST.Tlong
                     {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
     Tnil (tptr (Tstruct _fecBlock noattr))
     {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|})) ::
 (_fecBlock_free,
   Gfun(External (EF_external "fecBlock_free"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _fecBlock noattr)) Tnil) tvoid cc_default)) ::
 (_fecBlock_log,
   Gfun(External (EF_external "fecBlock_log"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _zlog_category_s noattr))
       (Tcons (tptr (Tstruct _fecBlock noattr)) Tnil)) tvoid cc_default)) ::
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
     cc_default)) ::
 (_flowTuple_log,
   Gfun(External (EF_external "flowTuple_log"
                   (mksignature (AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _zlog_category_s noattr))
       (Tcons tint (Tcons (tptr (Tstruct _flowTuple noattr)) Tnil))) tvoid
     cc_default)) ::
 (_util_getCurrentTime,
   Gfun(External (EF_external "util_getCurrentTime"
                   (mksignature nil AST.Tfloat
                     {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|}))
     Tnil tdouble
     {|cc_vararg:=None; cc_unproto:=true; cc_structret:=false|})) ::
 (_outstring, Gvar v_outstring) :: (_zc_blackFec, Gvar v_zc_blackFec) ::
 (_blackFecActuator_init, Gfun(Internal f_blackFecActuator_init)) ::
 (___func__, Gvar v___func__) ::
 (_blackFecActuator_unDeduce, Gfun(Internal f_blackFecActuator_unDeduce)) ::
 (___func____1, Gvar v___func____1) ::
 (_blackFecActuator_removeHeaders, Gfun(Internal f_blackFecActuator_removeHeaders)) ::
 (___func____2, Gvar v___func____2) ::
 (_blackFecActuator_regenerateMissingPackets, Gfun(Internal f_blackFecActuator_regenerateMissingPackets)) ::
 (___func____3, Gvar v___func____3) ::
 (_blackFecActuator_initBlockWithPacket, Gfun(Internal f_blackFecActuator_initBlockWithPacket)) ::
 (___func____4, Gvar v___func____4) ::
 (_blackFecActuator_addPacketToBlock, Gfun(Internal f_blackFecActuator_addPacketToBlock)) ::
 (___func____5, Gvar v___func____5) ::
 (_blackFecActuator, Gfun(Internal f_blackFecActuator)) :: nil).

Definition public_idents : list ident :=
(_blackFecActuator :: _blackFecActuator_addPacketToBlock ::
 _blackFecActuator_initBlockWithPacket ::
 _blackFecActuator_regenerateMissingPackets ::
 _blackFecActuator_removeHeaders :: _blackFecActuator_unDeduce ::
 _blackFecActuator_init :: _zc_blackFec :: _outstring ::
 _util_getCurrentTime :: _flowTuple_log :: _rse_code :: _rse_init ::
 _fecBlock_log :: _fecBlock_free :: _fecBlock_new :: _fecCommon_maskHeader ::
 _packetinfo_getAParam :: _packetinfo_get_deducehdrFromPacket ::
 _packetinfo_copyWithData :: _packetinfo_copyNoData :: _packetinfo_free ::
 _deducehdr_logAll :: _isUsefulLevel :: _privateHexDump :: _zlog :: _htons ::
 _ntohs :: _ntohl :: _memset :: _memcpy :: ___assert_fail :: _free ::
 _calloc :: ___builtin_debug :: ___builtin_write32_reversed ::
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


