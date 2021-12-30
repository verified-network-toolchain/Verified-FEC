From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "src/fecActuator/fec.c".
  Definition normalized := true.
End Info.

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
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_6 : ident := $"__stringlit_6".
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
Definition _b : ident := $"b".
Definition _c : ident := $"c".
Definition _data : ident := $"data".
Definition _data_lost_row : ident := $"data_lost_row".
Definition _err : ident := $"err".
Definition _fec_2_index : ident := $"fec_2_index".
Definition _fec_2_power : ident := $"fec_2_power".
Definition _fec_blk_decode : ident := $"fec_blk_decode".
Definition _fec_blk_encode : ident := $"fec_blk_encode".
Definition _fec_display_tables : ident := $"fec_display_tables".
Definition _fec_find_mod : ident := $"fec_find_mod".
Definition _fec_generate_math_tables : ident := $"fec_generate_math_tables".
Definition _fec_generate_weights : ident := $"fec_generate_weights".
Definition _fec_gf_mult : ident := $"fec_gf_mult".
Definition _fec_invefec : ident := $"fec_invefec".
Definition _fec_matrix_display : ident := $"fec_matrix_display".
Definition _fec_matrix_transform : ident := $"fec_matrix_transform".
Definition _fec_weights : ident := $"fec_weights".
Definition _fflush : ident := $"fflush".
Definition _found : ident := $"found".
Definition _fprintf : ident := $"fprintf".
Definition _h : ident := $"h".
Definition _i : ident := $"i".
Definition _i_max : ident := $"i_max".
Definition _inv : ident := $"inv".
Definition _j : ident := $"j".
Definition _j_max : ident := $"j_max".
Definition _k : ident := $"k".
Definition _lost : ident := $"lost".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _mod : ident := $"mod".
Definition _modulus : ident := $"modulus".
Definition _n : ident := $"n".
Definition _p : ident := $"p".
Definition _pdata : ident := $"pdata".
Definition _plen : ident := $"plen".
Definition _pparity : ident := $"pparity".
Definition _printf : ident := $"printf".
Definition _pstat : ident := $"pstat".
Definition _q : ident := $"q".
Definition _r : ident := $"r".
Definition _row : ident := $"row".
Definition _rse_code : ident := $"rse_code".
Definition _rse_code_print : ident := $"rse_code_print".
Definition _rse_init : ident := $"rse_init".
Definition _s : ident := $"s".
Definition _stderr : ident := $"stderr".
Definition _t : ident := $"t".
Definition _temp : ident := $"temp".
Definition _trace : ident := $"trace".
Definition _u : ident := $"u".
Definition _v : ident := $"v".
Definition _w : ident := $"w".
Definition _weight : ident := $"weight".
Definition _x : ident := $"x".
Definition _xh : ident := $"xh".
Definition _xk : ident := $"xk".
Definition _xr : ident := $"xr".
Definition _y : ident := $"y".
Definition _z : ident := $"z".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
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
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_9 := {|
  gvar_info := (tarray tschar 24);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_24 := {|
  gvar_info := (tarray tschar 24);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 87) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_11 := {|
  gvar_info := (tarray tschar 14);
  gvar_init := (Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 88) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_35 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_29 := {|
  gvar_info := (tarray tschar 14);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_37 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_31 := {|
  gvar_info := (tarray tschar 23);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_28 := {|
  gvar_info := (tarray tschar 18);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_12 := {|
  gvar_info := (tarray tschar 24);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 37);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 88) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_25 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 39) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_19 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_26 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_15 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_17 := {|
  gvar_info := (tarray tschar 10);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_21 := {|
  gvar_info := (tarray tschar 45);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_27 := {|
  gvar_info := (tarray tschar 46);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_34 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 63) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_16 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_23 := {|
  gvar_info := (tarray tschar 23);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_13 := {|
  gvar_info := (tarray tschar 36);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_32 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_22 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 52);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_10 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_20 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_30 := {|
  gvar_info := (tarray tschar 32);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 39);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 88) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_18 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 42);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 88) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 72) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_36 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 33);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_14 := {|
  gvar_info := (tarray tschar 14);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 88) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_33 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 40);
  gvar_init := (Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_stderr := {|
  gvar_info := (tptr (Tstruct __IO_FILE noattr));
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_trace := {|
  gvar_info := tint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_fec_2_power := {|
  gvar_info := (tarray tuchar 256);
  gvar_init := (Init_space 256 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_fec_2_index := {|
  gvar_info := (tarray tuchar 256);
  gvar_init := (Init_space 256 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_fec_invefec := {|
  gvar_info := (tarray tuchar 256);
  gvar_init := (Init_space 256 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_fec_weights := {|
  gvar_info := (tarray (tarray tuchar 255) 128);
  gvar_init := (Init_space 32640 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_fec_gf_mult := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_a, tuchar) :: (_b, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'9, tuchar) :: (_t'8, tuchar) ::
               (_t'7, tuchar) :: (_t'6, tuchar) :: (_t'5, tuchar) ::
               (_t'4, tuchar) :: (_t'3, tuchar) :: (_t'2, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Etempvar _a tuchar)
    (Sset _t'1 (Ecast (Etempvar _b tuchar) tbool))
    (Sset _t'1 (Econst_int (Int.repr 0) tint)))
  (Sifthenelse (Etempvar _t'1 tint)
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Evar _fec_2_power (tarray tuchar 256))
            (Etempvar _a tuchar) (tptr tuchar)) tuchar))
      (Ssequence
        (Sset _t'3
          (Ederef
            (Ebinop Oadd (Evar _fec_2_power (tarray tuchar 256))
              (Etempvar _b tuchar) (tptr tuchar)) tuchar))
        (Sifthenelse (Ebinop Ogt
                       (Ebinop Oadd (Etempvar _t'2 tuchar)
                         (Etempvar _t'3 tuchar) tint)
                       (Ebinop Osub (Econst_int (Int.repr 256) tint)
                         (Econst_int (Int.repr 1) tint) tint) tint)
          (Ssequence
            (Sset _t'7
              (Ederef
                (Ebinop Oadd (Evar _fec_2_power (tarray tuchar 256))
                  (Etempvar _a tuchar) (tptr tuchar)) tuchar))
            (Ssequence
              (Sset _t'8
                (Ederef
                  (Ebinop Oadd (Evar _fec_2_power (tarray tuchar 256))
                    (Etempvar _b tuchar) (tptr tuchar)) tuchar))
              (Ssequence
                (Sset _t'9
                  (Ederef
                    (Ebinop Oadd (Evar _fec_2_index (tarray tuchar 256))
                      (Ebinop Osub
                        (Ebinop Oadd (Etempvar _t'7 tuchar)
                          (Etempvar _t'8 tuchar) tint)
                        (Ebinop Osub (Econst_int (Int.repr 256) tint)
                          (Econst_int (Int.repr 1) tint) tint) tint)
                      (tptr tuchar)) tuchar))
                (Sreturn (Some (Etempvar _t'9 tuchar))))))
          (Ssequence
            (Sset _t'4
              (Ederef
                (Ebinop Oadd (Evar _fec_2_power (tarray tuchar 256))
                  (Etempvar _a tuchar) (tptr tuchar)) tuchar))
            (Ssequence
              (Sset _t'5
                (Ederef
                  (Ebinop Oadd (Evar _fec_2_power (tarray tuchar 256))
                    (Etempvar _b tuchar) (tptr tuchar)) tuchar))
              (Ssequence
                (Sset _t'6
                  (Ederef
                    (Ebinop Oadd (Evar _fec_2_index (tarray tuchar 256))
                      (Ebinop Oadd (Etempvar _t'4 tuchar)
                        (Etempvar _t'5 tuchar) tint) (tptr tuchar)) tuchar))
                (Sreturn (Some (Etempvar _t'6 tuchar)))))))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition v___func__ := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_rse_code := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_k, tint) :: (_h, tint) :: (_c, tint) ::
                (_pdata, (tptr (tptr tuchar))) :: (_plen, (tptr tint)) ::
                (_pstat, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'12, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'11, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'10, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'9, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'8, (tptr (Tstruct __IO_FILE noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Econst_int (Int.repr 0) tint)
    (Ssequence
      (Sset _t'12 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
      (Scall None
        (Evar _fprintf (Tfunction
                         (Tcons (tptr (Tstruct __IO_FILE noattr))
                           (Tcons (tptr tschar) Tnil)) tint
                         {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
        ((Etempvar _t'12 (tptr (Tstruct __IO_FILE noattr))) ::
         (Evar ___stringlit_1 (tarray tschar 33)) :: (Etempvar _k tint) ::
         (Etempvar _h tint) :: (Etempvar _c tint) :: nil)))
    Sskip)
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Oge (Etempvar _k tint)
                             (Ebinop Osub (Econst_int (Int.repr 256) tint)
                               (Econst_int (Int.repr 128) tint) tint) tint)
                (Sset _t'1 (Econst_int (Int.repr 1) tint))
                (Sset _t'1
                  (Ecast
                    (Ebinop Ogt (Etempvar _h tint)
                      (Econst_int (Int.repr 128) tint) tint) tbool)))
              (Sifthenelse (Etempvar _t'1 tint)
                (Sset _t'2 (Econst_int (Int.repr 1) tint))
                (Sset _t'2
                  (Ecast
                    (Ebinop Ogt (Etempvar _c tint)
                      (Econst_int (Int.repr 16000) tint) tint) tbool))))
            (Sifthenelse (Etempvar _t'2 tint)
              (Sset _t'3 (Econst_int (Int.repr 1) tint))
              (Sset _t'3
                (Ecast
                  (Ebinop Olt (Etempvar _k tint)
                    (Econst_int (Int.repr 1) tint) tint) tbool))))
          (Sifthenelse (Etempvar _t'3 tint)
            (Sset _t'4 (Econst_int (Int.repr 1) tint))
            (Sset _t'4
              (Ecast
                (Ebinop Olt (Etempvar _h tint) (Econst_int (Int.repr 0) tint)
                  tint) tbool))))
        (Sifthenelse (Etempvar _t'4 tint)
          (Sset _t'5 (Econst_int (Int.repr 1) tint))
          (Sset _t'5
            (Ecast
              (Ebinop Olt (Etempvar _c tint) (Econst_int (Int.repr 1) tint)
                tint) tbool))))
      (Sifthenelse (Etempvar _t'5 tint)
        (Ssequence
          (Ssequence
            (Sset _t'11 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
            (Scall None
              (Evar _fprintf (Tfunction
                               (Tcons (tptr (Tstruct __IO_FILE noattr))
                                 (Tcons (tptr tschar) Tnil)) tint
                               {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
              ((Etempvar _t'11 (tptr (Tstruct __IO_FILE noattr))) ::
               (Evar ___stringlit_2 (tarray tschar 40)) :: nil)))
          (Ssequence
            (Ssequence
              (Sset _t'10 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
              (Scall None
                (Evar _fprintf (Tfunction
                                 (Tcons (tptr (Tstruct __IO_FILE noattr))
                                   (Tcons (tptr tschar) Tnil)) tint
                                 {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                ((Etempvar _t'10 (tptr (Tstruct __IO_FILE noattr))) ::
                 (Evar ___stringlit_3 (tarray tschar 42)) ::
                 (Etempvar _k tint) ::
                 (Ebinop Osub (Econst_int (Int.repr 256) tint)
                   (Econst_int (Int.repr 128) tint) tint) :: nil)))
            (Ssequence
              (Ssequence
                (Sset _t'9 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                (Scall None
                  (Evar _fprintf (Tfunction
                                   (Tcons (tptr (Tstruct __IO_FILE noattr))
                                     (Tcons (tptr tschar) Tnil)) tint
                                   {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                  ((Etempvar _t'9 (tptr (Tstruct __IO_FILE noattr))) ::
                   (Evar ___stringlit_4 (tarray tschar 37)) ::
                   (Etempvar _h tint) :: (Econst_int (Int.repr 128) tint) ::
                   nil)))
              (Ssequence
                (Ssequence
                  (Sset _t'8
                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                  (Scall None
                    (Evar _fprintf (Tfunction
                                     (Tcons (tptr (Tstruct __IO_FILE noattr))
                                       (Tcons (tptr tschar) Tnil)) tint
                                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                    ((Etempvar _t'8 (tptr (Tstruct __IO_FILE noattr))) ::
                     (Evar ___stringlit_5 (tarray tschar 39)) ::
                     (Etempvar _c tint) ::
                     (Econst_int (Int.repr 16000) tint) :: nil)))
                (Ssequence
                  (Scall None
                    (Evar ___assert_fail (Tfunction
                                           (Tcons (tptr tschar)
                                             (Tcons (tptr tschar)
                                               (Tcons tuint
                                                 (Tcons (tptr tschar) Tnil))))
                                           tvoid cc_default))
                    ((Evar ___stringlit_7 (tarray tschar 2)) ::
                     (Evar ___stringlit_6 (tarray tschar 22)) ::
                     (Econst_int (Int.repr 206) tint) ::
                     (Evar ___func__ (tarray tschar 9)) :: nil))
                  (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                   tint))))))))
        Sskip))
    (Sifthenelse (Ebinop Oeq (Etempvar _h tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall (Some _t'6)
          (Evar _fec_blk_decode (Tfunction
                                  (Tcons tint
                                    (Tcons tint
                                      (Tcons (tptr (tptr tuchar))
                                        (Tcons (tptr tint)
                                          (Tcons (tptr tschar) Tnil))))) tint
                                  cc_default))
          ((Etempvar _k tint) :: (Etempvar _c tint) ::
           (Etempvar _pdata (tptr (tptr tuchar))) ::
           (Etempvar _plen (tptr tint)) :: (Etempvar _pstat (tptr tschar)) ::
           nil))
        (Sreturn (Some (Etempvar _t'6 tint))))
      (Ssequence
        (Scall (Some _t'7)
          (Evar _fec_blk_encode (Tfunction
                                  (Tcons tint
                                    (Tcons tint
                                      (Tcons tint
                                        (Tcons (tptr (tptr tuchar))
                                          (Tcons (tptr tint)
                                            (Tcons (tptr tschar) Tnil))))))
                                  tint cc_default))
          ((Etempvar _k tint) :: (Etempvar _h tint) :: (Etempvar _c tint) ::
           (Etempvar _pdata (tptr (tptr tuchar))) ::
           (Etempvar _plen (tptr tint)) :: (Etempvar _pstat (tptr tschar)) ::
           nil))
        (Sreturn (Some (Etempvar _t'7 tint)))))))
|}.

Definition v___func____1 := {|
  gvar_info := (tarray tschar 15);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_fec_blk_encode := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_k, tint) :: (_h, tint) :: (_c, tint) ::
                (_pdata, (tptr (tptr tuchar))) :: (_plen, (tptr tint)) ::
                (_pstat, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_j, tint) :: (_n, tint) :: (_data, tuchar) :: (_i, tuchar) ::
               (_y, tuchar) :: (_z, tuchar) :: (_p, (tptr tuchar)) ::
               (_pparity, (tptr (tptr tuchar))) :: (_t'2, tuchar) ::
               (_t'1, tuchar) ::
               (_t'13, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'12, tschar) ::
               (_t'11, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'10, (tptr tuchar)) ::
               (_t'9, (tptr (Tstruct __IO_FILE noattr))) :: (_t'8, tuchar) ::
               (_t'7, (tptr tuchar)) :: (_t'6, tuchar) :: (_t'5, tint) ::
               (_t'4, (tptr tuchar)) ::
               (_t'3, (tptr (Tstruct __IO_FILE noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _z (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tuchar))
  (Ssequence
    (Sset _pparity
      (Ebinop Oadd (Etempvar _pdata (tptr (tptr tuchar))) (Etempvar _k tint)
        (tptr (tptr tuchar))))
    (Ssequence
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tuchar))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuchar) (Etempvar _k tint)
                           tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'12
                (Ederef
                  (Ebinop Oadd (Etempvar _pstat (tptr tschar))
                    (Etempvar _i tuchar) (tptr tschar)) tschar))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'12 tschar)
                             (Econst_int (Int.repr 1) tint) tint)
                (Ssequence
                  (Sifthenelse (Econst_int (Int.repr 0) tint)
                    (Ssequence
                      (Sset _t'13
                        (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                      (Scall None
                        (Evar _fprintf (Tfunction
                                         (Tcons
                                           (tptr (Tstruct __IO_FILE noattr))
                                           (Tcons (tptr tschar) Tnil)) tint
                                         {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                        ((Etempvar _t'13 (tptr (Tstruct __IO_FILE noattr))) ::
                         (Evar ___stringlit_8 (tarray tschar 52)) :: nil)))
                    Sskip)
                  (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 20) tint)
                                   tint))))
                Sskip)))
          (Sset _i
            (Ecast
              (Ebinop Oadd (Etempvar _i tuchar)
                (Econst_int (Int.repr 1) tint) tint) tuchar))))
      (Ssequence
        (Sifthenelse (Econst_int (Int.repr 0) tint)
          (Ssequence
            (Sset _t'11 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
            (Scall None
              (Evar _fprintf (Tfunction
                               (Tcons (tptr (Tstruct __IO_FILE noattr))
                                 (Tcons (tptr tschar) Tnil)) tint
                               {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
              ((Etempvar _t'11 (tptr (Tstruct __IO_FILE noattr))) ::
               (Evar ___stringlit_9 (tarray tschar 24)) :: nil)))
          Sskip)
        (Ssequence
          (Ssequence
            (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tuchar))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tuchar)
                               (Etempvar _h tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sloop
                    (Ssequence
                      (Ssequence
                        (Sset _t'1
                          (Ecast
                            (Ebinop Oadd (Etempvar _z tuchar)
                              (Econst_int (Int.repr 1) tint) tint) tuchar))
                        (Sset _z (Ecast (Etempvar _t'1 tuchar) tuchar)))
                      (Ssequence
                        (Sset _t'10
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _pparity (tptr (tptr tuchar)))
                              (Etempvar _t'1 tuchar) (tptr (tptr tuchar)))
                            (tptr tuchar)))
                        (Sifthenelse (Eunop Onotbool
                                       (Etempvar _t'10 (tptr tuchar)) tint)
                          Sskip
                          Sbreak)))
                    Sskip)
                  (Ssequence
                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                      (Ssequence
                        (Sset _t'9
                          (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                        (Scall None
                          (Evar _fprintf (Tfunction
                                           (Tcons
                                             (tptr (Tstruct __IO_FILE noattr))
                                             (Tcons (tptr tschar) Tnil)) tint
                                           {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                          ((Etempvar _t'9 (tptr (Tstruct __IO_FILE noattr))) ::
                           (Evar ___stringlit_10 (tarray tschar 11)) ::
                           (Etempvar _z tuchar) :: nil)))
                      Sskip)
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _z tuchar)
                                     (Econst_int (Int.repr 128) tint) tint)
                        Sskip
                        (Scall None
                          (Evar ___assert_fail (Tfunction
                                                 (Tcons (tptr tschar)
                                                   (Tcons (tptr tschar)
                                                     (Tcons tuint
                                                       (Tcons (tptr tschar)
                                                         Tnil)))) tvoid
                                                 cc_default))
                          ((Evar ___stringlit_11 (tarray tschar 14)) ::
                           (Evar ___stringlit_6 (tarray tschar 22)) ::
                           (Econst_int (Int.repr 249) tint) ::
                           (Evar ___func____1 (tarray tschar 15)) :: nil)))
                      (Ssequence
                        (Sset _j (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                           (Etempvar _c tint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _y
                                (Ecast (Econst_int (Int.repr 0) tint) tuchar))
                              (Ssequence
                                (Sset _p
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _fec_weights (tarray (tarray tuchar 255) 128))
                                      (Etempvar _z tuchar)
                                      (tptr (tarray tuchar 255)))
                                    (tarray tuchar 255)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _n (Econst_int (Int.repr 0) tint))
                                    (Sloop
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _n tint)
                                                       (Etempvar _k tint)
                                                       tint)
                                          Sskip
                                          Sbreak)
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'5
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _plen (tptr tint))
                                                  (Etempvar _n tint)
                                                  (tptr tint)) tint))
                                            (Sifthenelse (Ebinop Ogt
                                                           (Etempvar _t'5 tint)
                                                           (Etempvar _j tint)
                                                           tint)
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'7
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _pdata (tptr (tptr tuchar)))
                                                        (Etempvar _n tint)
                                                        (tptr (tptr tuchar)))
                                                      (tptr tuchar)))
                                                  (Ssequence
                                                    (Sset _t'8
                                                      (Ederef
                                                        (Ecast
                                                          (Ebinop Oadd
                                                            (Etempvar _t'7 (tptr tuchar))
                                                            (Etempvar _j tint)
                                                            (tptr tuchar))
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Sset _data
                                                      (Ecast
                                                        (Etempvar _t'8 tuchar)
                                                        tuchar))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'6
                                                      (Ederef
                                                        (Etempvar _p (tptr tuchar))
                                                        tuchar))
                                                    (Scall (Some _t'2)
                                                      (Evar _fec_gf_mult 
                                                      (Tfunction
                                                        (Tcons tuchar
                                                          (Tcons tuchar Tnil))
                                                        tuchar cc_default))
                                                      ((Etempvar _t'6 tuchar) ::
                                                       (Etempvar _data tuchar) ::
                                                       nil)))
                                                  (Sset _y
                                                    (Ecast
                                                      (Ebinop Oxor
                                                        (Etempvar _y tuchar)
                                                        (Etempvar _t'2 tuchar)
                                                        tint) tuchar))))
                                              Sskip))
                                          (Sset _p
                                            (Ebinop Oadd
                                              (Etempvar _p (tptr tuchar))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr tuchar)))))
                                      (Sset _n
                                        (Ebinop Oadd (Etempvar _n tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint))))
                                  (Ssequence
                                    (Sset _t'4
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _pparity (tptr (tptr tuchar)))
                                          (Etempvar _z tuchar)
                                          (tptr (tptr tuchar)))
                                        (tptr tuchar)))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _t'4 (tptr tuchar))
                                          (Etempvar _j tint) (tptr tuchar))
                                        tuchar) (Etempvar _y tuchar)))))))
                          (Sset _j
                            (Ebinop Oadd (Etempvar _j tint)
                              (Econst_int (Int.repr 1) tint) tint))))))))
              (Sset _i
                (Ecast
                  (Ebinop Oadd (Etempvar _i tuchar)
                    (Econst_int (Int.repr 1) tint) tint) tuchar))))
          (Ssequence
            (Sifthenelse (Econst_int (Int.repr 0) tint)
              (Ssequence
                (Sset _t'3 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                (Scall None
                  (Evar _fprintf (Tfunction
                                   (Tcons (tptr (Tstruct __IO_FILE noattr))
                                     (Tcons (tptr tschar) Tnil)) tint
                                   {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                  ((Etempvar _t'3 (tptr (Tstruct __IO_FILE noattr))) ::
                   (Evar ___stringlit_12 (tarray tschar 24)) :: nil)))
              Sskip)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
|}.

Definition v___func____2 := {|
  gvar_info := (tarray tschar 15);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_fec_blk_decode := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_k, tint) :: (_c, tint) :: (_pdata, (tptr (tptr tuchar))) ::
                (_plen, (tptr tint)) :: (_pstat, (tptr tschar)) :: nil);
  fn_vars := ((_v, (tarray (tarray tuchar 256) 128)) ::
              (_s, (tarray (tarray tuchar 16000) 128)) ::
              (_lost, (tarray tuchar 128)) ::
              (_found, (tarray tuchar 128)) :: (_row, (tarray tuchar 128)) ::
              nil);
  fn_temps := ((_i, tuchar) :: (_q, tuchar) :: (_x, tuchar) ::
               (_y, tuchar) :: (_z, tuchar) :: (_weight, tuchar) ::
               (_data, tuchar) :: (_p, (tptr tuchar)) ::
               (_r, (tptr tuchar)) :: (_t, (tptr tuchar)) ::
               (_u, (tptr tuchar)) :: (_n, (tptr tuchar)) ::
               (_m, (tptr tuchar)) :: (_j, tint) :: (_data_lost_row, tint) ::
               (_err, tint) :: (_xh, tuchar) :: (_xk, tuchar) ::
               (_xr, tuchar) :: (_pparity, (tptr (tptr tuchar))) ::
               (_t'9, tuchar) :: (_t'8, tuchar) :: (_t'7, tuchar) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tuchar) ::
               (_t'3, tuchar) :: (_t'2, tuchar) :: (_t'1, tuchar) ::
               (_t'44, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'43, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'42, tschar) :: (_t'41, (tptr tuchar)) ::
               (_t'40, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'39, tuchar) ::
               (_t'38, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'37, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'36, tuchar) ::
               (_t'35, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'34, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'33, tuchar) ::
               (_t'32, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'31, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'30, (tptr (Tstruct __IO_FILE noattr))) :: (_t'29, tint) ::
               (_t'28, tuchar) :: (_t'27, tuchar) :: (_t'26, tuchar) ::
               (_t'25, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'24, tuchar) :: (_t'23, tuchar) :: (_t'22, tuchar) ::
               (_t'21, tuchar) :: (_t'20, (tptr tuchar)) :: (_t'19, tint) ::
               (_t'18, tuchar) :: (_t'17, (tptr tuchar)) ::
               (_t'16, tuchar) :: (_t'15, tuchar) :: (_t'14, tuchar) ::
               (_t'13, (tptr tuchar)) :: (_t'12, tint) ::
               (_t'11, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'10, (tptr (Tstruct __IO_FILE noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _err (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _xh (Ecast (Econst_int (Int.repr 0) tint) tuchar))
    (Ssequence
      (Sset _xk (Ecast (Econst_int (Int.repr 0) tint) tuchar))
      (Ssequence
        (Sset _xr (Ecast (Econst_int (Int.repr 0) tint) tuchar))
        (Ssequence
          (Sset _pparity
            (Ebinop Oadd (Etempvar _pdata (tptr (tptr tuchar)))
              (Etempvar _k tint) (tptr (tptr tuchar))))
          (Ssequence
            (Sifthenelse (Econst_int (Int.repr 0) tint)
              (Ssequence
                (Sset _t'44 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                (Scall None
                  (Evar _fprintf (Tfunction
                                   (Tcons (tptr (Tstruct __IO_FILE noattr))
                                     (Tcons (tptr tschar) Tnil)) tint
                                   {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                  ((Etempvar _t'44 (tptr (Tstruct __IO_FILE noattr))) ::
                   (Evar ___stringlit_13 (tarray tschar 36)) ::
                   (Etempvar _k tint) :: (Etempvar _c tint) :: nil)))
              Sskip)
            (Ssequence
              (Sifthenelse (Econst_int (Int.repr 0) tint)
                (Ssequence
                  (Sset _t'43
                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                  (Scall None
                    (Evar _fflush (Tfunction
                                    (Tcons (tptr (Tstruct __IO_FILE noattr))
                                      Tnil) tint cc_default))
                    ((Etempvar _t'43 (tptr (Tstruct __IO_FILE noattr))) ::
                     nil)))
                Sskip)
              (Ssequence
                (Ssequence
                  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tuchar))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tuchar)
                                     (Etempvar _k tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _t'42
                          (Ederef
                            (Ebinop Oadd (Etempvar _pstat (tptr tschar))
                              (Etempvar _i tuchar) (tptr tschar)) tschar))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'42 tschar)
                                       (Econst_int (Int.repr 1) tint) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'1 (Etempvar _xh tuchar))
                              (Sset _xh
                                (Ecast
                                  (Ebinop Oadd (Etempvar _t'1 tuchar)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tuchar)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _lost (tarray tuchar 128))
                                  (Etempvar _t'1 tuchar) (tptr tuchar))
                                tuchar) (Etempvar _i tuchar)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'2 (Etempvar _xk tuchar))
                              (Sset _xk
                                (Ecast
                                  (Ebinop Oadd (Etempvar _t'2 tuchar)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tuchar)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _found (tarray tuchar 128))
                                  (Etempvar _t'2 tuchar) (tptr tuchar))
                                tuchar) (Etempvar _i tuchar))))))
                    (Sset _i
                      (Ecast
                        (Ebinop Oadd (Etempvar _i tuchar)
                          (Econst_int (Int.repr 1) tint) tint) tuchar))))
                (Ssequence
                  (Sifthenelse (Eunop Onotbool (Etempvar _xh tuchar) tint)
                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                    Sskip)
                  (Ssequence
                    (Sset _q
                      (Ecast
                        (Ebinop Osub (Econst_int (Int.repr 256) tint)
                          (Econst_int (Int.repr 2) tint) tint) tuchar))
                    (Ssequence
                      (Ssequence
                        (Sset _i
                          (Ecast (Econst_int (Int.repr 0) tint) tuchar))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _xr tuchar)
                                           (Etempvar _xh tuchar) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Ssequence
                                (Sset _t'41
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _pparity (tptr (tptr tuchar)))
                                      (Etempvar _i tuchar)
                                      (tptr (tptr tuchar))) (tptr tuchar)))
                                (Sifthenelse (Etempvar _t'41 (tptr tuchar))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'3 (Etempvar _xk tuchar))
                                        (Sset _xk
                                          (Ecast
                                            (Ebinop Oadd
                                              (Etempvar _t'3 tuchar)
                                              (Econst_int (Int.repr 1) tint)
                                              tint) tuchar)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _found (tarray tuchar 128))
                                            (Etempvar _t'3 tuchar)
                                            (tptr tuchar)) tuchar)
                                        (Etempvar _q tuchar)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'4 (Etempvar _xr tuchar))
                                        (Sset _xr
                                          (Ecast
                                            (Ebinop Oadd
                                              (Etempvar _t'4 tuchar)
                                              (Econst_int (Int.repr 1) tint)
                                              tint) tuchar)))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _row (tarray tuchar 128))
                                            (Etempvar _t'4 tuchar)
                                            (tptr tuchar)) tuchar)
                                        (Etempvar _i tuchar))))
                                  Sskip))
                              (Ssequence
                                (Sset _q
                                  (Ecast
                                    (Ebinop Osub (Etempvar _q tuchar)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    tuchar))
                                (Sifthenelse (Ebinop Olt (Etempvar _i tuchar)
                                               (Econst_int (Int.repr 128) tint)
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
                                                           tvoid cc_default))
                                    ((Evar ___stringlit_14 (tarray tschar 14)) ::
                                     (Evar ___stringlit_6 (tarray tschar 22)) ::
                                     (Econst_int (Int.repr 329) tint) ::
                                     (Evar ___func____2 (tarray tschar 15)) ::
                                     nil))))))
                          (Sset _i
                            (Ecast
                              (Ebinop Oadd (Etempvar _i tuchar)
                                (Econst_int (Int.repr 1) tint) tint) tuchar))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'29 (Evar _trace tint))
                          (Sifthenelse (Ebinop Ogt (Etempvar _t'29 tint)
                                         (Econst_int (Int.repr 1) tint) tint)
                            (Ssequence
                              (Sifthenelse (Econst_int (Int.repr 0) tint)
                                (Ssequence
                                  (Sset _t'40
                                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                  (Scall None
                                    (Evar _fprintf (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct __IO_FILE noattr))
                                                       (Tcons (tptr tschar)
                                                         Tnil)) tint
                                                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                    ((Etempvar _t'40 (tptr (Tstruct __IO_FILE noattr))) ::
                                     (Evar ___stringlit_15 (tarray tschar 9)) ::
                                     nil)))
                                Sskip)
                              (Ssequence
                                (Ssequence
                                  (Sset _i
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      tuchar))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i tuchar)
                                                     (Etempvar _xh tuchar)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Sifthenelse (Econst_int (Int.repr 0) tint)
                                        (Ssequence
                                          (Sset _t'38
                                            (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                          (Ssequence
                                            (Sset _t'39
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _lost (tarray tuchar 128))
                                                  (Etempvar _i tuchar)
                                                  (tptr tuchar)) tuchar))
                                            (Scall None
                                              (Evar _fprintf (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct __IO_FILE noattr))
                                                                 (Tcons
                                                                   (tptr tschar)
                                                                   Tnil))
                                                               tint
                                                               {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                              ((Etempvar _t'38 (tptr (Tstruct __IO_FILE noattr))) ::
                                               (Evar ___stringlit_16 (tarray tschar 5)) ::
                                               (Etempvar _t'39 tuchar) ::
                                               nil))))
                                        Sskip))
                                    (Sset _i
                                      (Ecast
                                        (Ebinop Oadd (Etempvar _i tuchar)
                                          (Econst_int (Int.repr 1) tint)
                                          tint) tuchar))))
                                (Ssequence
                                  (Sifthenelse (Econst_int (Int.repr 0) tint)
                                    (Ssequence
                                      (Sset _t'37
                                        (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                      (Scall None
                                        (Evar _fprintf (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct __IO_FILE noattr))
                                                           (Tcons
                                                             (tptr tschar)
                                                             Tnil)) tint
                                                         {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                        ((Etempvar _t'37 (tptr (Tstruct __IO_FILE noattr))) ::
                                         (Evar ___stringlit_17 (tarray tschar 10)) ::
                                         nil)))
                                    Sskip)
                                  (Ssequence
                                    (Ssequence
                                      (Sset _i
                                        (Ecast (Econst_int (Int.repr 0) tint)
                                          tuchar))
                                      (Sloop
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _i tuchar)
                                                         (Etempvar _xk tuchar)
                                                         tint)
                                            Sskip
                                            Sbreak)
                                          (Sifthenelse (Econst_int (Int.repr 0) tint)
                                            (Ssequence
                                              (Sset _t'35
                                                (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                              (Ssequence
                                                (Sset _t'36
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _found (tarray tuchar 128))
                                                      (Etempvar _i tuchar)
                                                      (tptr tuchar)) tuchar))
                                                (Scall None
                                                  (Evar _fprintf (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct __IO_FILE noattr))
                                                                    (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))
                                                                   tint
                                                                   {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                                  ((Etempvar _t'35 (tptr (Tstruct __IO_FILE noattr))) ::
                                                   (Evar ___stringlit_18 (tarray tschar 4)) ::
                                                   (Etempvar _t'36 tuchar) ::
                                                   nil))))
                                            Sskip))
                                        (Sset _i
                                          (Ecast
                                            (Ebinop Oadd (Etempvar _i tuchar)
                                              (Econst_int (Int.repr 1) tint)
                                              tint) tuchar))))
                                    (Ssequence
                                      (Sifthenelse (Econst_int (Int.repr 0) tint)
                                        (Ssequence
                                          (Sset _t'34
                                            (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                          (Scall None
                                            (Evar _fprintf (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct __IO_FILE noattr))
                                                               (Tcons
                                                                 (tptr tschar)
                                                                 Tnil)) tint
                                                             {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                            ((Etempvar _t'34 (tptr (Tstruct __IO_FILE noattr))) ::
                                             (Evar ___stringlit_19 (tarray tschar 9)) ::
                                             nil)))
                                        Sskip)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _i
                                            (Ecast
                                              (Econst_int (Int.repr 0) tint)
                                              tuchar))
                                          (Sloop
                                            (Ssequence
                                              (Sifthenelse (Ebinop Olt
                                                             (Etempvar _i tuchar)
                                                             (Etempvar _xr tuchar)
                                                             tint)
                                                Sskip
                                                Sbreak)
                                              (Sifthenelse (Econst_int (Int.repr 0) tint)
                                                (Ssequence
                                                  (Sset _t'32
                                                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                                  (Ssequence
                                                    (Sset _t'33
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _row (tarray tuchar 128))
                                                          (Etempvar _i tuchar)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Scall None
                                                      (Evar _fprintf 
                                                      (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct __IO_FILE noattr))
                                                          (Tcons
                                                            (tptr tschar)
                                                            Tnil)) tint
                                                        {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                                      ((Etempvar _t'32 (tptr (Tstruct __IO_FILE noattr))) ::
                                                       (Evar ___stringlit_18 (tarray tschar 4)) ::
                                                       (Etempvar _t'33 tuchar) ::
                                                       nil))))
                                                Sskip))
                                            (Sset _i
                                              (Ecast
                                                (Ebinop Oadd
                                                  (Etempvar _i tuchar)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint) tuchar))))
                                        (Ssequence
                                          (Sifthenelse (Econst_int (Int.repr 0) tint)
                                            (Ssequence
                                              (Sset _t'31
                                                (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                              (Scall None
                                                (Evar _fprintf (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct __IO_FILE noattr))
                                                                   (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))
                                                                 tint
                                                                 {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                                ((Etempvar _t'31 (tptr (Tstruct __IO_FILE noattr))) ::
                                                 (Evar ___stringlit_20 (tarray tschar 2)) ::
                                                 nil)))
                                            Sskip)
                                          (Sifthenelse (Econst_int (Int.repr 0) tint)
                                            (Ssequence
                                              (Sset _t'30
                                                (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                              (Scall None
                                                (Evar _fflush (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct __IO_FILE noattr))
                                                                  Tnil) tint
                                                                cc_default))
                                                ((Etempvar _t'30 (tptr (Tstruct __IO_FILE noattr))) ::
                                                 nil)))
                                            Sskip))))))))
                            Sskip))
                        (Ssequence
                          (Ssequence
                            (Sset _j (Econst_int (Int.repr 0) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                               (Etempvar _xh tuchar) tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'28
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _row (tarray tuchar 128))
                                          (Etempvar _j tint) (tptr tuchar))
                                        tuchar))
                                    (Sset _n
                                      (Ecast
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _fec_weights (tarray (tarray tuchar 255) 128))
                                            (Etempvar _t'28 tuchar)
                                            (tptr (tarray tuchar 255)))
                                          (tarray tuchar 255)) (tptr tuchar))))
                                  (Ssequence
                                    (Sset _r
                                      (Ebinop Oadd
                                        (Ederef
                                          (Evar _v (tarray (tarray tuchar 256) 128))
                                          (tarray tuchar 256))
                                        (Ebinop Omul
                                          (Ebinop Omul (Etempvar _j tint)
                                            (Etempvar _xh tuchar) tint)
                                          (Econst_int (Int.repr 2) tint)
                                          tint) (tptr tuchar)))
                                    (Ssequence
                                      (Sset _i
                                        (Ecast (Econst_int (Int.repr 0) tint)
                                          tuchar))
                                      (Sloop
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _i tuchar)
                                                         (Etempvar _xh tuchar)
                                                         tint)
                                            Sskip
                                            Sbreak)
                                          (Ssequence
                                            (Sifthenelse (Ebinop Oeq
                                                           (Ebinop Oadd
                                                             (Ebinop Oadd
                                                               (Etempvar _i tuchar)
                                                               (Etempvar _j tint)
                                                               tint)
                                                             (Econst_int (Int.repr 1) tint)
                                                             tint)
                                                           (Etempvar _xh tuchar)
                                                           tint)
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _r (tptr tuchar))
                                                    (Etempvar _i tuchar)
                                                    (tptr tuchar)) tuchar)
                                                (Econst_int (Int.repr 1) tint))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _r (tptr tuchar))
                                                    (Etempvar _i tuchar)
                                                    (tptr tuchar)) tuchar)
                                                (Econst_int (Int.repr 0) tint)))
                                            (Ssequence
                                              (Sset _t'26
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _lost (tarray tuchar 128))
                                                    (Etempvar _i tuchar)
                                                    (tptr tuchar)) tuchar))
                                              (Ssequence
                                                (Sset _t'27
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _n (tptr tuchar))
                                                      (Etempvar _t'26 tuchar)
                                                      (tptr tuchar)) tuchar))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Ebinop Oadd
                                                        (Etempvar _r (tptr tuchar))
                                                        (Etempvar _i tuchar)
                                                        (tptr tuchar))
                                                      (Etempvar _xh tuchar)
                                                      (tptr tuchar)) tuchar)
                                                  (Etempvar _t'27 tuchar))))))
                                        (Sset _i
                                          (Ecast
                                            (Ebinop Oadd (Etempvar _i tuchar)
                                              (Econst_int (Int.repr 1) tint)
                                              tint) tuchar)))))))
                              (Sset _j
                                (Ebinop Oadd (Etempvar _j tint)
                                  (Econst_int (Int.repr 1) tint) tint))))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'5)
                                    (Evar _fec_matrix_transform (Tfunction
                                                                  (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tuchar
                                                                    (Tcons
                                                                    tuchar
                                                                    Tnil)))
                                                                  tint
                                                                  cc_default))
                                    ((Ecast
                                       (Evar _v (tarray (tarray tuchar 256) 128))
                                       (tptr tuchar)) ::
                                     (Etempvar _xh tuchar) ::
                                     (Ebinop Omul (Etempvar _xh tuchar)
                                       (Econst_int (Int.repr 2) tint) tint) ::
                                     nil))
                                  (Sset _t'6
                                    (Ecast (Etempvar _t'5 tint) tint)))
                                (Sset _err (Etempvar _t'6 tint)))
                              (Sifthenelse (Etempvar _t'6 tint)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'25
                                      (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                    (Scall None
                                      (Evar _fprintf (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct __IO_FILE noattr))
                                                         (Tcons (tptr tschar)
                                                           Tnil)) tint
                                                       {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                      ((Etempvar _t'25 (tptr (Tstruct __IO_FILE noattr))) ::
                                       (Evar ___stringlit_21 (tarray tschar 45)) ::
                                       (Etempvar _err tint) :: nil)))
                                  (Sreturn (Some (Etempvar _err tint))))
                                Sskip))
                            (Ssequence
                              (Ssequence
                                (Sset _i
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    tuchar))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _i tuchar)
                                                   (Etempvar _xh tuchar)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'24
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _row (tarray tuchar 128))
                                              (Etempvar _i tuchar)
                                              (tptr tuchar)) tuchar))
                                        (Sset _p
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _fec_weights (tarray (tarray tuchar 255) 128))
                                              (Etempvar _t'24 tuchar)
                                              (tptr (tarray tuchar 255)))
                                            (tarray tuchar 255))))
                                      (Ssequence
                                        (Sset _t
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _s (tarray (tarray tuchar 16000) 128))
                                              (Etempvar _i tuchar)
                                              (tptr (tarray tuchar 16000)))
                                            (tarray tuchar 16000)))
                                        (Ssequence
                                          (Sset _j
                                            (Econst_int (Int.repr 0) tint))
                                          (Sloop
                                            (Ssequence
                                              (Sifthenelse (Ebinop Olt
                                                             (Etempvar _j tint)
                                                             (Etempvar _c tint)
                                                             tint)
                                                Sskip
                                                Sbreak)
                                              (Ssequence
                                                (Sset _y
                                                  (Ecast
                                                    (Econst_int (Int.repr 0) tint)
                                                    tuchar))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _q
                                                      (Ecast
                                                        (Econst_int (Int.repr 0) tint)
                                                        tuchar))
                                                    (Sloop
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Olt
                                                            (Etempvar _q tuchar)
                                                            (Etempvar _k tint)
                                                            tint)
                                                          Sskip
                                                          Sbreak)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'23
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _found (tarray tuchar 128))
                                                                  (Etempvar _q tuchar)
                                                                  (tptr tuchar))
                                                                tuchar))
                                                            (Sset _z
                                                              (Ecast
                                                                (Etempvar _t'23 tuchar)
                                                                tuchar)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'22
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Etempvar _p (tptr tuchar))
                                                                    (Etempvar _z tuchar)
                                                                    (tptr tuchar))
                                                                  tuchar))
                                                              (Sset _weight
                                                                (Ecast
                                                                  (Etempvar _t'22 tuchar)
                                                                  tuchar)))
                                                            (Sifthenelse 
                                                              (Ebinop Olt
                                                                (Etempvar _z tuchar)
                                                                (Etempvar _k tint)
                                                                tint)
                                                              (Ssequence
                                                                (Sset _t'19
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _plen (tptr tint))
                                                                    (Etempvar _z tuchar)
                                                                    (tptr tint))
                                                                    tint))
                                                                (Sifthenelse 
                                                                  (Ebinop Ogt
                                                                    (Etempvar _t'19 tint)
                                                                    (Etempvar _j tint)
                                                                    tint)
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'20
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pdata (tptr (tptr tuchar)))
                                                                    (Etempvar _z tuchar)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'21
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'20 (tptr tuchar))
                                                                    (Etempvar _j tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _data
                                                                    (Ecast
                                                                    (Etempvar _t'21 tuchar)
                                                                    tuchar))))
                                                                    (Ssequence
                                                                    (Scall (Some _t'7)
                                                                    (Evar _fec_gf_mult 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tuchar
                                                                    (Tcons
                                                                    tuchar
                                                                    Tnil))
                                                                    tuchar
                                                                    cc_default))
                                                                    ((Etempvar _weight tuchar) ::
                                                                    (Etempvar _data tuchar) ::
                                                                    nil))
                                                                    (Sset _y
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Etempvar _y tuchar)
                                                                    (Etempvar _t'7 tuchar)
                                                                    tint)
                                                                    tuchar))))
                                                                  Sskip))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'17
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pparity (tptr (tptr tuchar)))
                                                                    (Ebinop Osub
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 256) tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Etempvar _z tuchar)
                                                                    tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                  (Ssequence
                                                                    (Sset _t'18
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'17 (tptr tuchar))
                                                                    (Etempvar _j tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _data
                                                                    (Ecast
                                                                    (Etempvar _t'18 tuchar)
                                                                    tuchar))))
                                                                (Ssequence
                                                                  (Scall (Some _t'8)
                                                                    (Evar _fec_gf_mult 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tuchar
                                                                    (Tcons
                                                                    tuchar
                                                                    Tnil))
                                                                    tuchar
                                                                    cc_default))
                                                                    ((Etempvar _weight tuchar) ::
                                                                    (Etempvar _data tuchar) ::
                                                                    nil))
                                                                  (Sset _y
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Etempvar _y tuchar)
                                                                    (Etempvar _t'8 tuchar)
                                                                    tint)
                                                                    tuchar))))))))
                                                      (Sset _q
                                                        (Ecast
                                                          (Ebinop Oadd
                                                            (Etempvar _q tuchar)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tint) tuchar))))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _t (tptr tuchar))
                                                        (Etempvar _j tint)
                                                        (tptr tuchar))
                                                      tuchar)
                                                    (Etempvar _y tuchar)))))
                                            (Sset _j
                                              (Ebinop Oadd (Etempvar _j tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint)))))))
                                  (Sset _i
                                    (Ecast
                                      (Ebinop Oadd (Etempvar _i tuchar)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      tuchar))))
                              (Ssequence
                                (Sset _x
                                  (Ecast
                                    (Ebinop Osub (Etempvar _xh tuchar)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    tuchar))
                                (Ssequence
                                  (Sset _u
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _s (tarray (tarray tuchar 16000) 128))
                                        (Etempvar _x tuchar)
                                        (tptr (tarray tuchar 16000)))
                                      (tarray tuchar 16000)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _i
                                        (Ecast (Econst_int (Int.repr 0) tint)
                                          tuchar))
                                      (Sloop
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _i tuchar)
                                                         (Etempvar _xh tuchar)
                                                         tint)
                                            Sskip
                                            Sbreak)
                                          (Ssequence
                                            (Sset _p
                                              (Ebinop Oadd
                                                (Ederef
                                                  (Evar _v (tarray (tarray tuchar 256) 128))
                                                  (tarray tuchar 256))
                                                (Ebinop Omul
                                                  (Ebinop Omul
                                                    (Etempvar _i tuchar)
                                                    (Etempvar _xh tuchar)
                                                    tint)
                                                  (Econst_int (Int.repr 2) tint)
                                                  tint) (tptr tuchar)))
                                            (Ssequence
                                              (Sset _m
                                                (Ebinop Oadd
                                                  (Etempvar _p (tptr tuchar))
                                                  (Etempvar _xh tuchar)
                                                  (tptr tuchar)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'16
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _lost (tarray tuchar 128))
                                                        (Ebinop Osub
                                                          (Etempvar _x tuchar)
                                                          (Etempvar _i tuchar)
                                                          tint)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _pstat (tptr tschar))
                                                        (Etempvar _t'16 tuchar)
                                                        (tptr tschar))
                                                      tschar)
                                                    (Econst_int (Int.repr 0) tint)))
                                                (Ssequence
                                                  (Sset _j
                                                    (Econst_int (Int.repr 0) tint))
                                                  (Sloop
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Etempvar _j tint)
                                                                    (Etempvar _c tint)
                                                                    tint)
                                                        Sskip
                                                        Sbreak)
                                                      (Ssequence
                                                        (Sset _y
                                                          (Ecast
                                                            (Econst_int (Int.repr 0) tint)
                                                            tuchar))
                                                        (Ssequence
                                                          (Sset _r
                                                            (Ebinop Oadd
                                                              (Etempvar _u (tptr tuchar))
                                                              (Etempvar _j tint)
                                                              (tptr tuchar)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _n
                                                                (Etempvar _p (tptr tuchar)))
                                                              (Sloop
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _n (tptr tuchar))
                                                                    (Etempvar _m (tptr tuchar))
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'14
                                                                    (Ederef
                                                                    (Etempvar _n (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'15
                                                                    (Ederef
                                                                    (Etempvar _r (tptr tuchar))
                                                                    tuchar))
                                                                    (Scall (Some _t'9)
                                                                    (Evar _fec_gf_mult 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tuchar
                                                                    (Tcons
                                                                    tuchar
                                                                    Tnil))
                                                                    tuchar
                                                                    cc_default))
                                                                    ((Etempvar _t'14 tuchar) ::
                                                                    (Etempvar _t'15 tuchar) ::
                                                                    nil))))
                                                                    (Sset _y
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Etempvar _y tuchar)
                                                                    (Etempvar _t'9 tuchar)
                                                                    tint)
                                                                    tuchar)))
                                                                    (Sset _r
                                                                    (Ebinop Osub
                                                                    (Etempvar _r (tptr tuchar))
                                                                    (Econst_int (Int.repr 16000) tint)
                                                                    (tptr tuchar)))))
                                                                (Sset _n
                                                                  (Ebinop Oadd
                                                                    (Etempvar _n (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar)))))
                                                            (Ssequence
                                                              (Sset _data_lost_row
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _lost (tarray tuchar 128))
                                                                    (Ebinop Osub
                                                                    (Ebinop Osub
                                                                    (Etempvar _xh tuchar)
                                                                    (Etempvar _i tuchar)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                  tuchar))
                                                              (Ssequence
                                                                (Sset _t'12
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _plen (tptr tint))
                                                                    (Etempvar _data_lost_row tint)
                                                                    (tptr tint))
                                                                    tint))
                                                                (Sifthenelse 
                                                                  (Ebinop Ogt
                                                                    (Etempvar _t'12 tint)
                                                                    (Etempvar _j tint)
                                                                    tint)
                                                                  (Ssequence
                                                                    (Sset _t'13
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pdata (tptr (tptr tuchar)))
                                                                    (Etempvar _data_lost_row tint)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'13 (tptr tuchar))
                                                                    (Etempvar _j tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _y tuchar)))
                                                                  Sskip)))))))
                                                    (Sset _j
                                                      (Ebinop Oadd
                                                        (Etempvar _j tint)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tint))))))))
                                        (Sset _i
                                          (Ecast
                                            (Ebinop Oadd (Etempvar _i tuchar)
                                              (Econst_int (Int.repr 1) tint)
                                              tint) tuchar))))
                                    (Ssequence
                                      (Sifthenelse (Econst_int (Int.repr 0) tint)
                                        (Ssequence
                                          (Sset _t'11
                                            (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                          (Scall None
                                            (Evar _fprintf (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct __IO_FILE noattr))
                                                               (Tcons
                                                                 (tptr tschar)
                                                                 Tnil)) tint
                                                             {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                            ((Etempvar _t'11 (tptr (Tstruct __IO_FILE noattr))) ::
                                             (Evar ___stringlit_22 (tarray tschar 19)) ::
                                             nil)))
                                        Sskip)
                                      (Ssequence
                                        (Sifthenelse (Econst_int (Int.repr 0) tint)
                                          (Ssequence
                                            (Sset _t'10
                                              (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                            (Scall None
                                              (Evar _fflush (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct __IO_FILE noattr))
                                                                Tnil) tint
                                                              cc_default))
                                              ((Etempvar _t'10 (tptr (Tstruct __IO_FILE noattr))) ::
                                               nil)))
                                          Sskip)
                                        (Sreturn (Some (Etempvar _xh tuchar)))))))))))))))))))))))
|}.

Definition f_rse_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _fec_generate_math_tables (Tfunction Tnil tvoid cc_default)) nil)
  (Scall None (Evar _fec_generate_weights (Tfunction Tnil tvoid cc_default))
    nil))
|}.

Definition f_fec_generate_weights := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tuchar) :: (_j, tuchar) :: (_t'3, tuchar) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tuchar))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuchar)
                       (Econst_int (Int.repr 128) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tuchar))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _j tuchar)
                             (Ebinop Osub (Econst_int (Int.repr 256) tint)
                               (Econst_int (Int.repr 1) tint) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd (Evar _fec_2_index (tarray tuchar 256))
                      (Ebinop Omod
                        (Ebinop Omul (Etempvar _i tuchar)
                          (Etempvar _j tuchar) tint)
                        (Ebinop Osub (Econst_int (Int.repr 256) tint)
                          (Econst_int (Int.repr 1) tint) tint) tint)
                      (tptr tuchar)) tuchar))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Ederef
                        (Ebinop Oadd
                          (Evar _fec_weights (tarray (tarray tuchar 255) 128))
                          (Etempvar _i tuchar) (tptr (tarray tuchar 255)))
                        (tarray tuchar 255)) (Etempvar _j tuchar)
                      (tptr tuchar)) tuchar) (Etempvar _t'3 tuchar))))
            (Sset _j
              (Ecast
                (Ebinop Oadd (Etempvar _j tuchar)
                  (Econst_int (Int.repr 1) tint) tint) tuchar)))))
      (Sset _i
        (Ecast
          (Ebinop Oadd (Etempvar _i tuchar) (Econst_int (Int.repr 1) tint)
            tint) tuchar))))
  (Ssequence
    (Ssequence
      (Sset _t'2 (Evar _trace tint))
      (Sifthenelse (Ebinop Ogt (Etempvar _t'2 tint)
                     (Econst_int (Int.repr 1) tint) tint)
        (Ssequence
          (Scall None
            (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                            {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
            ((Evar ___stringlit_23 (tarray tschar 23)) :: nil))
          (Scall None
            (Evar _fec_matrix_display (Tfunction
                                        (Tcons (tptr tuchar)
                                          (Tcons tuchar (Tcons tuchar Tnil)))
                                        tvoid cc_default))
            ((Ecast (Evar _fec_weights (tarray (tarray tuchar 255) 128))
               (tptr tuchar)) :: (Econst_int (Int.repr 128) tint) ::
             (Ebinop Osub (Econst_int (Int.repr 256) tint)
               (Econst_int (Int.repr 1) tint) tint) :: nil)))
        Sskip))
    (Ssequence
      (Scall None
        (Evar _fec_matrix_transform (Tfunction
                                      (Tcons (tptr tuchar)
                                        (Tcons tuchar (Tcons tuchar Tnil)))
                                      tint cc_default))
        ((Ecast (Evar _fec_weights (tarray (tarray tuchar 255) 128))
           (tptr tuchar)) :: (Econst_int (Int.repr 128) tint) ::
         (Ebinop Osub (Econst_int (Int.repr 256) tint)
           (Econst_int (Int.repr 1) tint) tint) :: nil))
      (Ssequence
        (Sset _t'1 (Evar _trace tint))
        (Sifthenelse (Ebinop Ogt (Etempvar _t'1 tint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_24 (tarray tschar 24)) :: nil))
            (Scall None
              (Evar _fec_matrix_display (Tfunction
                                          (Tcons (tptr tuchar)
                                            (Tcons tuchar
                                              (Tcons tuchar Tnil))) tvoid
                                          cc_default))
              ((Ecast (Evar _fec_weights (tarray (tarray tuchar 255) 128))
                 (tptr tuchar)) :: (Econst_int (Int.repr 128) tint) ::
               (Ebinop Osub (Econst_int (Int.repr 256) tint)
                 (Econst_int (Int.repr 1) tint) tint) :: nil)))
          Sskip)))))
|}.

Definition f_fec_matrix_transform := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: (_i_max, tuchar) ::
                (_j_max, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, (tptr tuchar)) :: (_m, (tptr tuchar)) ::
               (_q, (tptr tuchar)) :: (_r, (tptr tuchar)) ::
               (_inv, tuchar) :: (_i, tuchar) :: (_j, tuchar) ::
               (_k, tuchar) :: (_w, tuchar) :: (_t'3, tuchar) ::
               (_t'2, tuchar) :: (_t'1, tuchar) :: (_t'13, tuchar) ::
               (_t'12, tuchar) :: (_t'11, tuchar) :: (_t'10, tuchar) ::
               (_t'9, tuchar) :: (_t'8, tuchar) :: (_t'7, tuchar) ::
               (_t'6, tuchar) :: (_t'5, tuchar) :: (_t'4, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _k (Ecast (Econst_int (Int.repr 0) tint) tuchar))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _k tuchar)
                       (Etempvar _i_max tuchar) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tuchar))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tuchar)
                               (Etempvar _i_max tuchar) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _q
                    (Ebinop Osub
                      (Ebinop Oadd
                        (Ebinop Oadd (Etempvar _p (tptr tuchar))
                          (Ebinop Omul (Etempvar _i tuchar)
                            (Etempvar _j_max tuchar) tint) (tptr tuchar))
                        (Etempvar _j_max tuchar) (tptr tuchar))
                      (Econst_int (Int.repr 1) tint) (tptr tuchar)))
                  (Ssequence
                    (Sset _m
                      (Ebinop Oadd
                        (Ebinop Osub (Etempvar _q (tptr tuchar))
                          (Etempvar _j_max tuchar) (tptr tuchar))
                        (Econst_int (Int.repr 1) tint) (tptr tuchar)))
                    (Ssequence
                      (Sset _w (Ecast (Etempvar _i tuchar) tuchar))
                      (Ssequence
                        (Sloop
                          (Ssequence
                            (Ssequence
                              (Sset _t'13
                                (Ederef
                                  (Ebinop Osub (Etempvar _q (tptr tuchar))
                                    (Etempvar _k tuchar) (tptr tuchar))
                                  tuchar))
                              (Sifthenelse (Ebinop Oeq
                                             (Etempvar _t'13 tuchar)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                Sskip
                                Sbreak))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'1
                                    (Ecast
                                      (Ebinop Oadd (Etempvar _w tuchar)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      tuchar))
                                  (Sset _w
                                    (Ecast (Etempvar _t'1 tuchar) tuchar)))
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _t'1 tuchar)
                                               (Etempvar _i_max tuchar) tint)
                                  (Sreturn (Some (Econst_int (Int.repr 82) tint)))
                                  Sskip))
                              (Ssequence
                                (Sset _t'12
                                  (Ederef
                                    (Ebinop Osub
                                      (Ebinop Osub
                                        (Ebinop Oadd
                                          (Ebinop Oadd
                                            (Etempvar _p (tptr tuchar))
                                            (Ebinop Omul (Etempvar _w tuchar)
                                              (Etempvar _j_max tuchar) tint)
                                            (tptr tuchar))
                                          (Etempvar _j_max tuchar)
                                          (tptr tuchar))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tuchar)) (Etempvar _k tuchar)
                                      (tptr tuchar)) tuchar))
                                (Sifthenelse (Ebinop One
                                               (Etempvar _t'12 tuchar)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  (Sreturn (Some (Econst_int (Int.repr 83) tint)))
                                  Sskip))))
                          Sskip)
                        (Ssequence
                          (Ssequence
                            (Sset _t'10
                              (Ederef
                                (Ebinop Osub (Etempvar _q (tptr tuchar))
                                  (Etempvar _k tuchar) (tptr tuchar)) tuchar))
                            (Ssequence
                              (Sset _t'11
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _fec_invefec (tarray tuchar 256))
                                    (Etempvar _t'10 tuchar) (tptr tuchar))
                                  tuchar))
                              (Sset _inv
                                (Ecast (Etempvar _t'11 tuchar) tuchar))))
                          (Ssequence
                            (Sset _n
                              (Ebinop Oadd (Etempvar _q (tptr tuchar))
                                (Econst_int (Int.repr 1) tint) (tptr tuchar)))
                            (Swhile
                              (Ebinop Ogt (Etempvar _n (tptr tuchar))
                                (Etempvar _m (tptr tuchar)) tint)
                              (Ssequence
                                (Sset _n
                                  (Ebinop Osub (Etempvar _n (tptr tuchar))
                                    (Econst_int (Int.repr 1) tint)
                                    (tptr tuchar)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'9
                                      (Ederef (Etempvar _n (tptr tuchar))
                                        tuchar))
                                    (Scall (Some _t'2)
                                      (Evar _fec_gf_mult (Tfunction
                                                           (Tcons tuchar
                                                             (Tcons tuchar
                                                               Tnil)) tuchar
                                                           cc_default))
                                      ((Etempvar _t'9 tuchar) ::
                                       (Etempvar _inv tuchar) :: nil)))
                                  (Sassign
                                    (Ederef (Etempvar _n (tptr tuchar))
                                      tuchar) (Etempvar _t'2 tuchar))))))))))))
              (Sset _i
                (Ecast
                  (Ebinop Oadd (Etempvar _i tuchar)
                    (Econst_int (Int.repr 1) tint) tint) tuchar))))
          (Ssequence
            (Sset _r
              (Ebinop Osub
                (Ebinop Oadd
                  (Ebinop Oadd (Etempvar _p (tptr tuchar))
                    (Ebinop Omul (Etempvar _k tuchar)
                      (Etempvar _j_max tuchar) tint) (tptr tuchar))
                  (Etempvar _j_max tuchar) (tptr tuchar))
                (Econst_int (Int.repr 1) tint) (tptr tuchar)))
            (Ssequence
              (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tuchar))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tuchar)
                                 (Etempvar _i_max tuchar) tint)
                    Sskip
                    Sbreak)
                  (Sifthenelse (Ebinop One (Etempvar _i tuchar)
                                 (Etempvar _k tuchar) tint)
                    (Ssequence
                      (Sset _q
                        (Ebinop Osub
                          (Ebinop Oadd
                            (Ebinop Oadd (Etempvar _p (tptr tuchar))
                              (Ebinop Omul (Etempvar _i tuchar)
                                (Etempvar _j_max tuchar) tint) (tptr tuchar))
                            (Etempvar _j_max tuchar) (tptr tuchar))
                          (Econst_int (Int.repr 1) tint) (tptr tuchar)))
                      (Ssequence
                        (Sset _j
                          (Ecast (Econst_int (Int.repr 0) tint) tuchar))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _j tuchar)
                                           (Etempvar _j_max tuchar) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _t'7
                                (Ederef
                                  (Ebinop Osub (Etempvar _q (tptr tuchar))
                                    (Etempvar _j tuchar) (tptr tuchar))
                                  tuchar))
                              (Ssequence
                                (Sset _t'8
                                  (Ederef
                                    (Ebinop Osub (Etempvar _r (tptr tuchar))
                                      (Etempvar _j tuchar) (tptr tuchar))
                                    tuchar))
                                (Sassign
                                  (Ederef
                                    (Ebinop Osub (Etempvar _q (tptr tuchar))
                                      (Etempvar _j tuchar) (tptr tuchar))
                                    tuchar)
                                  (Ebinop Oxor (Etempvar _t'7 tuchar)
                                    (Etempvar _t'8 tuchar) tint)))))
                          (Sset _j
                            (Ecast
                              (Ebinop Oadd (Etempvar _j tuchar)
                                (Econst_int (Int.repr 1) tint) tint) tuchar)))))
                    Sskip))
                (Sset _i
                  (Ecast
                    (Ebinop Oadd (Etempvar _i tuchar)
                      (Econst_int (Int.repr 1) tint) tint) tuchar)))))))
      (Sset _k
        (Ecast
          (Ebinop Oadd (Etempvar _k tuchar) (Econst_int (Int.repr 1) tint)
            tint) tuchar))))
  (Ssequence
    (Ssequence
      (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tuchar))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuchar)
                         (Ebinop Osub (Etempvar _i_max tuchar)
                           (Econst_int (Int.repr 1) tint) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _q
              (Ebinop Osub
                (Ebinop Oadd
                  (Ebinop Oadd (Etempvar _p (tptr tuchar))
                    (Ebinop Omul (Etempvar _i tuchar)
                      (Etempvar _j_max tuchar) tint) (tptr tuchar))
                  (Etempvar _j_max tuchar) (tptr tuchar))
                (Econst_int (Int.repr 1) tint) (tptr tuchar)))
            (Ssequence
              (Sset _m
                (Ebinop Oadd
                  (Ebinop Osub (Etempvar _q (tptr tuchar))
                    (Etempvar _j_max tuchar) (tptr tuchar))
                  (Econst_int (Int.repr 1) tint) (tptr tuchar)))
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Ederef
                      (Ebinop Osub (Etempvar _q (tptr tuchar))
                        (Etempvar _i tuchar) (tptr tuchar)) tuchar))
                  (Ssequence
                    (Sset _t'6
                      (Ederef
                        (Ebinop Oadd (Evar _fec_invefec (tarray tuchar 256))
                          (Etempvar _t'5 tuchar) (tptr tuchar)) tuchar))
                    (Sset _inv (Ecast (Etempvar _t'6 tuchar) tuchar))))
                (Ssequence
                  (Sset _n
                    (Ebinop Oadd (Etempvar _q (tptr tuchar))
                      (Econst_int (Int.repr 1) tint) (tptr tuchar)))
                  (Swhile
                    (Ebinop Ogt (Etempvar _n (tptr tuchar))
                      (Etempvar _m (tptr tuchar)) tint)
                    (Ssequence
                      (Sset _n
                        (Ebinop Osub (Etempvar _n (tptr tuchar))
                          (Econst_int (Int.repr 1) tint) (tptr tuchar)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'4
                            (Ederef (Etempvar _n (tptr tuchar)) tuchar))
                          (Scall (Some _t'3)
                            (Evar _fec_gf_mult (Tfunction
                                                 (Tcons tuchar
                                                   (Tcons tuchar Tnil))
                                                 tuchar cc_default))
                            ((Etempvar _t'4 tuchar) ::
                             (Etempvar _inv tuchar) :: nil)))
                        (Sassign (Ederef (Etempvar _n (tptr tuchar)) tuchar)
                          (Etempvar _t'3 tuchar))))))))))
        (Sset _i
          (Ecast
            (Ebinop Oadd (Etempvar _i tuchar) (Econst_int (Int.repr 1) tint)
              tint) tuchar))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_fec_generate_math_tables := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_mod, tint) :: (_temp, tint) :: (_i, tint) :: (_t'1, tint) ::
               (_t'5, tuchar) :: (_t'4, tuchar) :: (_t'3, tuchar) ::
               (_t'2, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _fec_find_mod (Tfunction Tnil tint cc_default))
      nil)
    (Sset _mod (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 256) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _i tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _fec_2_index (tarray tuchar 256))
                    (Etempvar _i tint) (tptr tuchar)) tuchar)
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Ederef
                      (Ebinop Oadd (Evar _fec_2_index (tarray tuchar 256))
                        (Ebinop Osub (Etempvar _i tint)
                          (Econst_int (Int.repr 1) tint) tint) (tptr tuchar))
                      tuchar))
                  (Sset _temp
                    (Ebinop Oshl (Etempvar _t'5 tuchar)
                      (Econst_int (Int.repr 1) tint) tint)))
                (Sifthenelse (Ebinop Oge (Etempvar _temp tint)
                               (Econst_int (Int.repr 256) tint) tint)
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _fec_2_index (tarray tuchar 256))
                        (Etempvar _i tint) (tptr tuchar)) tuchar)
                    (Ebinop Oxor (Etempvar _temp tint) (Etempvar _mod tint)
                      tint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _fec_2_index (tarray tuchar 256))
                        (Etempvar _i tint) (tptr tuchar)) tuchar)
                    (Etempvar _temp tint)))))
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd (Evar _fec_2_index (tarray tuchar 256))
                    (Etempvar _i tint) (tptr tuchar)) tuchar))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _fec_2_power (tarray tuchar 256))
                    (Etempvar _t'4 tuchar) (tptr tuchar)) tuchar)
                (Etempvar _i tint)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 256) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Evar _fec_2_power (tarray tuchar 256))
                  (Etempvar _i tint) (tptr tuchar)) tuchar))
            (Ssequence
              (Sset _t'3
                (Ederef
                  (Ebinop Oadd (Evar _fec_2_index (tarray tuchar 256))
                    (Ebinop Osub
                      (Ebinop Osub (Econst_int (Int.repr 256) tint)
                        (Econst_int (Int.repr 1) tint) tint)
                      (Etempvar _t'2 tuchar) tint) (tptr tuchar)) tuchar))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _fec_invefec (tarray tuchar 256))
                    (Etempvar _t'3 tuchar) (tptr tuchar)) tuchar)
                (Etempvar _i tint)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))))
|}.

Definition f_fec_find_mod := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_modulus, tint) ::
               (_t'1, (tptr (Tstruct __IO_FILE noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sswitch (Econst_int (Int.repr 256) tint)
    (LScons (Some 8)
      (Ssequence (Sset _modulus (Econst_int (Int.repr 11) tint)) Sbreak)
      (LScons (Some 16)
        (Ssequence (Sset _modulus (Econst_int (Int.repr 19) tint)) Sbreak)
        (LScons (Some 32)
          (Ssequence (Sset _modulus (Econst_int (Int.repr 37) tint)) Sbreak)
          (LScons (Some 64)
            (Ssequence
              (Sset _modulus (Econst_int (Int.repr 67) tint))
              Sbreak)
            (LScons (Some 128)
              (Ssequence
                (Sset _modulus (Econst_int (Int.repr 137) tint))
                Sbreak)
              (LScons (Some 256)
                (Ssequence
                  (Sset _modulus (Econst_int (Int.repr 285) tint))
                  Sbreak)
                (LScons None
                  (Ssequence
                    (Ssequence
                      (Sset _t'1
                        (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                      (Scall None
                        (Evar _fprintf (Tfunction
                                         (Tcons
                                           (tptr (Tstruct __IO_FILE noattr))
                                           (Tcons (tptr tschar) Tnil)) tint
                                         {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                        ((Etempvar _t'1 (tptr (Tstruct __IO_FILE noattr))) ::
                         (Evar ___stringlit_25 (tarray tschar 30)) ::
                         (Econst_int (Int.repr 256) tint) :: nil)))
                    (Sreturn (Some (Econst_int (Int.repr 4) tint))))
                  LSnil))))))))
  (Sreturn (Some (Etempvar _modulus tint))))
|}.

Definition f_fec_matrix_display := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: (_i_max, tuchar) ::
                (_j_max, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_j, tint) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _i_max tuchar)
                     tint)
        Sskip
        Sbreak)
      (Ssequence
        (Ssequence
          (Sset _j
            (Ebinop Osub (Etempvar _j_max tuchar)
              (Econst_int (Int.repr 1) tint) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Oge (Etempvar _j tint)
                             (Econst_int (Int.repr 0) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd
                      (Ebinop Oadd (Etempvar _p (tptr tuchar))
                        (Ebinop Omul (Etempvar _i tint)
                          (Etempvar _j_max tuchar) tint) (tptr tuchar))
                      (Etempvar _j tint) (tptr tuchar)) tuchar))
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_26 (tarray tschar 5)) ::
                   (Etempvar _t'1 tuchar) :: nil))))
            (Sset _j
              (Ebinop Osub (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
          ((Evar ___stringlit_20 (tarray tschar 2)) :: nil))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_fec_display_tables := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_mod, tint) :: (_t'1, tint) ::
               (_t'4, tuchar) :: (_t'3, tuchar) :: (_t'2, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _fec_find_mod (Tfunction Tnil tint cc_default))
      nil)
    (Sset _mod (Etempvar _t'1 tint)))
  (Ssequence
    (Scall None
      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                      {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
      ((Evar ___stringlit_27 (tarray tschar 46)) :: (Etempvar _mod tint) ::
       nil))
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Ole (Etempvar _i tint)
                         (Ebinop Osub (Econst_int (Int.repr 256) tint)
                           (Econst_int (Int.repr 1) tint) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd (Evar _fec_2_index (tarray tuchar 256))
                    (Etempvar _i tint) (tptr tuchar)) tuchar))
              (Scall None
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                ((Evar ___stringlit_28 (tarray tschar 18)) ::
                 (Etempvar _i tint) :: (Etempvar _t'4 tuchar) :: nil)))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Evar _fec_2_power (tarray tuchar 256))
                    (Etempvar _i tint) (tptr tuchar)) tuchar))
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd (Evar _fec_invefec (tarray tuchar 256))
                      (Etempvar _i tint) (tptr tuchar)) tuchar))
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_29 (tarray tschar 14)) ::
                   (Etempvar _t'2 tuchar) :: (Etempvar _t'3 tuchar) :: nil))))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))))
|}.

Definition f_rse_code_print := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_k, tint) :: (_h, tint) :: (_c, tint) ::
                (_pdata, (tptr (tptr tuchar))) :: (_plen, (tptr tint)) ::
                (_pstat, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_j, tint) ::
               (_t'22, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'21, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'20, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'19, tuchar) :: (_t'18, (tptr tuchar)) ::
               (_t'17, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'16, (tptr (Tstruct __IO_FILE noattr))) :: (_t'15, tint) ::
               (_t'14, tschar) :: (_t'13, tschar) :: (_t'12, tint) ::
               (_t'11, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'10, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'9, (tptr (Tstruct __IO_FILE noattr))) :: (_t'8, tuchar) ::
               (_t'7, (tptr tuchar)) ::
               (_t'6, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'5, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'4, (tptr tuchar)) ::
               (_t'3, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'2, (tptr (Tstruct __IO_FILE noattr))) :: (_t'1, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Econst_int (Int.repr 0) tint)
    (Ssequence
      (Sset _t'22 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
      (Scall None
        (Evar _fprintf (Tfunction
                         (Tcons (tptr (Tstruct __IO_FILE noattr))
                           (Tcons (tptr tschar) Tnil)) tint
                         {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
        ((Etempvar _t'22 (tptr (Tstruct __IO_FILE noattr))) ::
         (Evar ___stringlit_30 (tarray tschar 32)) :: (Etempvar _c tint) ::
         (Etempvar _h tint) :: (Etempvar _k tint) :: nil)))
    Sskip)
  (Ssequence
    (Sset _t'1 (Evar _trace tint))
    (Sifthenelse (Ebinop Ogt (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 1) tint) tint)
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _k tint)
                             tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'21
                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                  (Scall None
                    (Evar _fprintf (Tfunction
                                     (Tcons (tptr (Tstruct __IO_FILE noattr))
                                       (Tcons (tptr tschar) Tnil)) tint
                                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                    ((Etempvar _t'21 (tptr (Tstruct __IO_FILE noattr))) ::
                     (Evar ___stringlit_31 (tarray tschar 23)) ::
                     (Etempvar _i tint) :: nil)))
                (Ssequence
                  (Ssequence
                    (Sset _j (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                       (Etempvar _c tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Sset _t'14
                            (Ederef
                              (Ebinop Oadd (Etempvar _pstat (tptr tschar))
                                (Etempvar _i tint) (tptr tschar)) tschar))
                          (Sifthenelse (Ebinop Oeq (Etempvar _t'14 tschar)
                                         (Econst_int (Int.repr 1) tint) tint)
                            (Ssequence
                              (Sset _t'20
                                (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                              (Scall None
                                (Evar _fprintf (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct __IO_FILE noattr))
                                                   (Tcons (tptr tschar) Tnil))
                                                 tint
                                                 {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                ((Etempvar _t'20 (tptr (Tstruct __IO_FILE noattr))) ::
                                 (Evar ___stringlit_34 (tarray tschar 5)) ::
                                 nil)))
                            (Ssequence
                              (Sset _t'15
                                (Ederef
                                  (Ebinop Oadd (Etempvar _plen (tptr tint))
                                    (Etempvar _i tint) (tptr tint)) tint))
                              (Sifthenelse (Ebinop Ogt (Etempvar _t'15 tint)
                                             (Etempvar _j tint) tint)
                                (Ssequence
                                  (Sset _t'17
                                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                  (Ssequence
                                    (Sset _t'18
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _pdata (tptr (tptr tuchar)))
                                          (Etempvar _i tint)
                                          (tptr (tptr tuchar)))
                                        (tptr tuchar)))
                                    (Ssequence
                                      (Sset _t'19
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'18 (tptr tuchar))
                                            (Etempvar _j tint) (tptr tuchar))
                                          tuchar))
                                      (Scall None
                                        (Evar _fprintf (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct __IO_FILE noattr))
                                                           (Tcons
                                                             (tptr tschar)
                                                             Tnil)) tint
                                                         {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                        ((Etempvar _t'17 (tptr (Tstruct __IO_FILE noattr))) ::
                                         (Evar ___stringlit_33 (tarray tschar 6)) ::
                                         (Etempvar _t'19 tuchar) :: nil)))))
                                (Ssequence
                                  (Sset _t'16
                                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                  (Scall None
                                    (Evar _fprintf (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct __IO_FILE noattr))
                                                       (Tcons (tptr tschar)
                                                         Tnil)) tint
                                                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                    ((Etempvar _t'16 (tptr (Tstruct __IO_FILE noattr))) ::
                                     (Evar ___stringlit_32 (tarray tschar 5)) ::
                                     nil))))))))
                      (Sset _j
                        (Ebinop Oadd (Etempvar _j tint)
                          (Econst_int (Int.repr 1) tint) tint))))
                  (Ssequence
                    (Sset _t'11
                      (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                    (Ssequence
                      (Sset _t'12
                        (Ederef
                          (Ebinop Oadd (Etempvar _plen (tptr tint))
                            (Etempvar _i tint) (tptr tint)) tint))
                      (Ssequence
                        (Sset _t'13
                          (Ederef
                            (Ebinop Oadd (Etempvar _pstat (tptr tschar))
                              (Etempvar _i tint) (tptr tschar)) tschar))
                        (Scall None
                          (Evar _fprintf (Tfunction
                                           (Tcons
                                             (tptr (Tstruct __IO_FILE noattr))
                                             (Tcons (tptr tschar) Tnil)) tint
                                           {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                          ((Etempvar _t'11 (tptr (Tstruct __IO_FILE noattr))) ::
                           (Evar ___stringlit_35 (tarray tschar 18)) ::
                           (Etempvar _t'12 tint) ::
                           (Etempvar _t'13 tschar) :: nil))))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Ssequence
            (Sset _t'10 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
            (Scall None
              (Evar _fprintf (Tfunction
                               (Tcons (tptr (Tstruct __IO_FILE noattr))
                                 (Tcons (tptr tschar) Tnil)) tint
                               {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
              ((Etempvar _t'10 (tptr (Tstruct __IO_FILE noattr))) ::
               (Evar ___stringlit_36 (tarray tschar 30)) :: nil)))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Etempvar _h tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'9
                        (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                      (Scall None
                        (Evar _fprintf (Tfunction
                                         (Tcons
                                           (tptr (Tstruct __IO_FILE noattr))
                                           (Tcons (tptr tschar) Tnil)) tint
                                         {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                        ((Etempvar _t'9 (tptr (Tstruct __IO_FILE noattr))) ::
                         (Evar ___stringlit_37 (tarray tschar 18)) ::
                         (Etempvar _i tint) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Sset _j (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                           (Etempvar _c tint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _t'4
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _pdata (tptr (tptr tuchar)))
                                    (Ebinop Oadd (Etempvar _k tint)
                                      (Etempvar _i tint) tint)
                                    (tptr (tptr tuchar))) (tptr tuchar)))
                              (Sifthenelse (Etempvar _t'4 (tptr tuchar))
                                (Ssequence
                                  (Sset _t'6
                                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                  (Ssequence
                                    (Sset _t'7
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _pdata (tptr (tptr tuchar)))
                                          (Ebinop Oadd (Etempvar _k tint)
                                            (Etempvar _i tint) tint)
                                          (tptr (tptr tuchar)))
                                        (tptr tuchar)))
                                    (Ssequence
                                      (Sset _t'8
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'7 (tptr tuchar))
                                            (Etempvar _j tint) (tptr tuchar))
                                          tuchar))
                                      (Scall None
                                        (Evar _fprintf (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct __IO_FILE noattr))
                                                           (Tcons
                                                             (tptr tschar)
                                                             Tnil)) tint
                                                         {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                        ((Etempvar _t'6 (tptr (Tstruct __IO_FILE noattr))) ::
                                         (Evar ___stringlit_33 (tarray tschar 6)) ::
                                         (Etempvar _t'8 tuchar) :: nil)))))
                                (Ssequence
                                  (Sset _t'5
                                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                  (Scall None
                                    (Evar _fprintf (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct __IO_FILE noattr))
                                                       (Tcons (tptr tschar)
                                                         Tnil)) tint
                                                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                    ((Etempvar _t'5 (tptr (Tstruct __IO_FILE noattr))) ::
                                     (Evar ___stringlit_34 (tarray tschar 5)) ::
                                     nil))))))
                          (Sset _j
                            (Ebinop Oadd (Etempvar _j tint)
                              (Econst_int (Int.repr 1) tint) tint))))
                      (Ssequence
                        (Sset _t'3
                          (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                        (Scall None
                          (Evar _fprintf (Tfunction
                                           (Tcons
                                             (tptr (Tstruct __IO_FILE noattr))
                                             (Tcons (tptr tschar) Tnil)) tint
                                           {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                          ((Etempvar _t'3 (tptr (Tstruct __IO_FILE noattr))) ::
                           (Evar ___stringlit_20 (tarray tschar 2)) :: nil))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sset _t'2 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
              (Scall None
                (Evar _fprintf (Tfunction
                                 (Tcons (tptr (Tstruct __IO_FILE noattr))
                                   (Tcons (tptr tschar) Tnil)) tint
                                 {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                ((Etempvar _t'2 (tptr (Tstruct __IO_FILE noattr))) ::
                 (Evar ___stringlit_20 (tarray tschar 2)) :: nil))))))
      Sskip)))
|}.

Definition composites : list composite_definition :=
(Composite __IO_FILE Struct
   ((__flags, tint) :: (__IO_read_ptr, (tptr tschar)) ::
    (__IO_read_end, (tptr tschar)) :: (__IO_read_base, (tptr tschar)) ::
    (__IO_write_base, (tptr tschar)) :: (__IO_write_ptr, (tptr tschar)) ::
    (__IO_write_end, (tptr tschar)) :: (__IO_buf_base, (tptr tschar)) ::
    (__IO_buf_end, (tptr tschar)) :: (__IO_save_base, (tptr tschar)) ::
    (__IO_backup_base, (tptr tschar)) :: (__IO_save_end, (tptr tschar)) ::
    (__markers, (tptr (Tstruct __IO_marker noattr))) ::
    (__chain, (tptr (Tstruct __IO_FILE noattr))) :: (__fileno, tint) ::
    (__flags2, tint) :: (__old_offset, tlong) :: (__cur_column, tushort) ::
    (__vtable_offset, tschar) :: (__shortbuf, (tarray tschar 1)) ::
    (__lock, (tptr tvoid)) :: (__offset, tlong) ::
    (__codecvt, (tptr (Tstruct __IO_codecvt noattr))) ::
    (__wide_data, (tptr (Tstruct __IO_wide_data noattr))) ::
    (__freeres_list, (tptr (Tstruct __IO_FILE noattr))) ::
    (__freeres_buf, (tptr tvoid)) :: (___pad5, tulong) :: (__mode, tint) ::
    (__unused2, (tarray tschar 20)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_24, Gvar v___stringlit_24) ::
 (___stringlit_11, Gvar v___stringlit_11) ::
 (___stringlit_35, Gvar v___stringlit_35) ::
 (___stringlit_29, Gvar v___stringlit_29) ::
 (___stringlit_37, Gvar v___stringlit_37) ::
 (___stringlit_31, Gvar v___stringlit_31) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_28, Gvar v___stringlit_28) ::
 (___stringlit_12, Gvar v___stringlit_12) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_25, Gvar v___stringlit_25) ::
 (___stringlit_19, Gvar v___stringlit_19) ::
 (___stringlit_26, Gvar v___stringlit_26) ::
 (___stringlit_15, Gvar v___stringlit_15) ::
 (___stringlit_17, Gvar v___stringlit_17) ::
 (___stringlit_21, Gvar v___stringlit_21) ::
 (___stringlit_27, Gvar v___stringlit_27) ::
 (___stringlit_34, Gvar v___stringlit_34) ::
 (___stringlit_16, Gvar v___stringlit_16) ::
 (___stringlit_23, Gvar v___stringlit_23) ::
 (___stringlit_13, Gvar v___stringlit_13) ::
 (___stringlit_32, Gvar v___stringlit_32) ::
 (___stringlit_22, Gvar v___stringlit_22) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_10, Gvar v___stringlit_10) ::
 (___stringlit_20, Gvar v___stringlit_20) ::
 (___stringlit_30, Gvar v___stringlit_30) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_18, Gvar v___stringlit_18) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_36, Gvar v___stringlit_36) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_14, Gvar v___stringlit_14) ::
 (___stringlit_33, Gvar v___stringlit_33) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
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
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
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
 (_stderr, Gvar v_stderr) ::
 (_fflush,
   Gfun(External (EF_external "fflush"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct __IO_FILE noattr)) Tnil) tint cc_default)) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct __IO_FILE noattr)) (Tcons (tptr tschar) Tnil))
     tint {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|})) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___assert_fail,
   Gfun(External (EF_external "__assert_fail"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tschar)
       (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
     cc_default)) :: (_trace, Gvar v_trace) ::
 (_fec_2_power, Gvar v_fec_2_power) :: (_fec_2_index, Gvar v_fec_2_index) ::
 (_fec_invefec, Gvar v_fec_invefec) :: (_fec_weights, Gvar v_fec_weights) ::
 (_fec_gf_mult, Gfun(Internal f_fec_gf_mult)) ::
 (___func__, Gvar v___func__) :: (_rse_code, Gfun(Internal f_rse_code)) ::
 (___func____1, Gvar v___func____1) ::
 (_fec_blk_encode, Gfun(Internal f_fec_blk_encode)) ::
 (___func____2, Gvar v___func____2) ::
 (_fec_blk_decode, Gfun(Internal f_fec_blk_decode)) ::
 (_rse_init, Gfun(Internal f_rse_init)) ::
 (_fec_generate_weights, Gfun(Internal f_fec_generate_weights)) ::
 (_fec_matrix_transform, Gfun(Internal f_fec_matrix_transform)) ::
 (_fec_generate_math_tables, Gfun(Internal f_fec_generate_math_tables)) ::
 (_fec_find_mod, Gfun(Internal f_fec_find_mod)) ::
 (_fec_matrix_display, Gfun(Internal f_fec_matrix_display)) ::
 (_fec_display_tables, Gfun(Internal f_fec_display_tables)) ::
 (_rse_code_print, Gfun(Internal f_rse_code_print)) :: nil).

Definition public_idents : list ident :=
(_rse_code_print :: _fec_display_tables :: _fec_matrix_display ::
 _fec_find_mod :: _fec_generate_math_tables :: _fec_matrix_transform ::
 _fec_generate_weights :: _rse_init :: _fec_blk_decode :: _fec_blk_encode ::
 _rse_code :: _fec_gf_mult :: _fec_weights :: _fec_invefec :: _fec_2_index ::
 _fec_2_power :: _trace :: ___assert_fail :: _printf :: _fprintf ::
 _fflush :: _stderr :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___builtin_expect :: ___builtin_unreachable ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


