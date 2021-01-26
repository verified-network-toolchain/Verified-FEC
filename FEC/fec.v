From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.7"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "fec.c"%string.
  Definition normalized := true.
End Info.

Definition __IO_FILE : ident := 15%positive.
Definition __IO_backup_base : ident := 11%positive.
Definition __IO_buf_base : ident := 8%positive.
Definition __IO_buf_end : ident := 9%positive.
Definition __IO_codecvt : ident := 25%positive.
Definition __IO_marker : ident := 13%positive.
Definition __IO_read_base : ident := 4%positive.
Definition __IO_read_end : ident := 3%positive.
Definition __IO_read_ptr : ident := 2%positive.
Definition __IO_save_base : ident := 10%positive.
Definition __IO_save_end : ident := 12%positive.
Definition __IO_wide_data : ident := 27%positive.
Definition __IO_write_base : ident := 5%positive.
Definition __IO_write_end : ident := 7%positive.
Definition __IO_write_ptr : ident := 6%positive.
Definition ___assert_fail : ident := 90%positive.
Definition ___builtin_ais_annot : ident := 34%positive.
Definition ___builtin_annot : ident := 43%positive.
Definition ___builtin_annot_intval : ident := 44%positive.
Definition ___builtin_bswap : ident := 36%positive.
Definition ___builtin_bswap16 : ident := 38%positive.
Definition ___builtin_bswap32 : ident := 37%positive.
Definition ___builtin_bswap64 : ident := 35%positive.
Definition ___builtin_clz : ident := 69%positive.
Definition ___builtin_clzl : ident := 70%positive.
Definition ___builtin_clzll : ident := 71%positive.
Definition ___builtin_ctz : ident := 72%positive.
Definition ___builtin_ctzl : ident := 73%positive.
Definition ___builtin_ctzll : ident := 74%positive.
Definition ___builtin_debug : ident := 85%positive.
Definition ___builtin_fabs : ident := 39%positive.
Definition ___builtin_fmadd : ident := 77%positive.
Definition ___builtin_fmax : ident := 75%positive.
Definition ___builtin_fmin : ident := 76%positive.
Definition ___builtin_fmsub : ident := 78%positive.
Definition ___builtin_fnmadd : ident := 79%positive.
Definition ___builtin_fnmsub : ident := 80%positive.
Definition ___builtin_fsqrt : ident := 40%positive.
Definition ___builtin_membar : ident := 45%positive.
Definition ___builtin_memcpy_aligned : ident := 41%positive.
Definition ___builtin_read16_reversed : ident := 81%positive.
Definition ___builtin_read32_reversed : ident := 82%positive.
Definition ___builtin_sel : ident := 42%positive.
Definition ___builtin_va_arg : ident := 47%positive.
Definition ___builtin_va_copy : ident := 48%positive.
Definition ___builtin_va_end : ident := 49%positive.
Definition ___builtin_va_start : ident := 46%positive.
Definition ___builtin_write16_reversed : ident := 83%positive.
Definition ___builtin_write32_reversed : ident := 84%positive.
Definition ___compcert_i64_dtos : ident := 54%positive.
Definition ___compcert_i64_dtou : ident := 55%positive.
Definition ___compcert_i64_sar : ident := 66%positive.
Definition ___compcert_i64_sdiv : ident := 60%positive.
Definition ___compcert_i64_shl : ident := 64%positive.
Definition ___compcert_i64_shr : ident := 65%positive.
Definition ___compcert_i64_smod : ident := 62%positive.
Definition ___compcert_i64_smulh : ident := 67%positive.
Definition ___compcert_i64_stod : ident := 56%positive.
Definition ___compcert_i64_stof : ident := 58%positive.
Definition ___compcert_i64_udiv : ident := 61%positive.
Definition ___compcert_i64_umod : ident := 63%positive.
Definition ___compcert_i64_umulh : ident := 68%positive.
Definition ___compcert_i64_utod : ident := 57%positive.
Definition ___compcert_i64_utof : ident := 59%positive.
Definition ___compcert_va_composite : ident := 53%positive.
Definition ___compcert_va_float64 : ident := 52%positive.
Definition ___compcert_va_int32 : ident := 50%positive.
Definition ___compcert_va_int64 : ident := 51%positive.
Definition ___func__ : ident := 99%positive.
Definition ___func____1 : ident := 116%positive.
Definition ___func____2 : ident := 130%positive.
Definition ___pad5 : ident := 31%positive.
Definition ___stringlit_1 : ident := 106%positive.
Definition ___stringlit_10 : ident := 127%positive.
Definition ___stringlit_11 : ident := 128%positive.
Definition ___stringlit_12 : ident := 129%positive.
Definition ___stringlit_13 : ident := 148%positive.
Definition ___stringlit_14 : ident := 149%positive.
Definition ___stringlit_15 : ident := 150%positive.
Definition ___stringlit_16 : ident := 151%positive.
Definition ___stringlit_17 : ident := 152%positive.
Definition ___stringlit_18 : ident := 153%positive.
Definition ___stringlit_19 : ident := 154%positive.
Definition ___stringlit_2 : ident := 107%positive.
Definition ___stringlit_20 : ident := 155%positive.
Definition ___stringlit_21 : ident := 157%positive.
Definition ___stringlit_22 : ident := 158%positive.
Definition ___stringlit_23 : ident := 162%positive.
Definition ___stringlit_24 : ident := 164%positive.
Definition ___stringlit_25 : ident := 173%positive.
Definition ___stringlit_26 : ident := 174%positive.
Definition ___stringlit_27 : ident := 175%positive.
Definition ___stringlit_28 : ident := 176%positive.
Definition ___stringlit_29 : ident := 177%positive.
Definition ___stringlit_3 : ident := 108%positive.
Definition ___stringlit_30 : ident := 179%positive.
Definition ___stringlit_31 : ident := 180%positive.
Definition ___stringlit_32 : ident := 181%positive.
Definition ___stringlit_33 : ident := 182%positive.
Definition ___stringlit_34 : ident := 183%positive.
Definition ___stringlit_35 : ident := 184%positive.
Definition ___stringlit_36 : ident := 185%positive.
Definition ___stringlit_37 : ident := 186%positive.
Definition ___stringlit_4 : ident := 109%positive.
Definition ___stringlit_5 : ident := 110%positive.
Definition ___stringlit_6 : ident := 111%positive.
Definition ___stringlit_7 : ident := 112%positive.
Definition ___stringlit_8 : ident := 125%positive.
Definition ___stringlit_9 : ident := 126%positive.
Definition __chain : ident := 16%positive.
Definition __codecvt : ident := 26%positive.
Definition __cur_column : ident := 20%positive.
Definition __fileno : ident := 17%positive.
Definition __flags : ident := 1%positive.
Definition __flags2 : ident := 18%positive.
Definition __freeres_buf : ident := 30%positive.
Definition __freeres_list : ident := 29%positive.
Definition __lock : ident := 23%positive.
Definition __markers : ident := 14%positive.
Definition __mode : ident := 32%positive.
Definition __offset : ident := 24%positive.
Definition __old_offset : ident := 19%positive.
Definition __shortbuf : ident := 22%positive.
Definition __unused2 : ident := 33%positive.
Definition __vtable_offset : ident := 21%positive.
Definition __wide_data : ident := 28%positive.
Definition _a : ident := 96%positive.
Definition _b : ident := 97%positive.
Definition _c : ident := 102%positive.
Definition _data : ident := 119%positive.
Definition _data_lost_row : ident := 140%positive.
Definition _err : ident := 141%positive.
Definition _fec_2_index : ident := 93%positive.
Definition _fec_2_power : ident := 92%positive.
Definition _fec_blk_decode : ident := 114%positive.
Definition _fec_blk_encode : ident := 113%positive.
Definition _fec_display_tables : ident := 178%positive.
Definition _fec_find_mod : ident := 171%positive.
Definition _fec_generate_math_tables : ident := 159%positive.
Definition _fec_generate_weights : ident := 160%positive.
Definition _fec_gf_mult : ident := 98%positive.
Definition _fec_invefec : ident := 94%positive.
Definition _fec_matrix_display : ident := 163%positive.
Definition _fec_matrix_transform : ident := 156%positive.
Definition _fec_weights : ident := 95%positive.
Definition _fflush : ident := 87%positive.
Definition _found : ident := 146%positive.
Definition _fprintf : ident := 88%positive.
Definition _h : ident := 101%positive.
Definition _i : ident := 120%positive.
Definition _i_max : ident := 165%positive.
Definition _inv : ident := 167%positive.
Definition _j : ident := 117%positive.
Definition _j_max : ident := 166%positive.
Definition _k : ident := 100%positive.
Definition _lost : ident := 145%positive.
Definition _m : ident := 139%positive.
Definition _main : ident := 188%positive.
Definition _mod : ident := 169%positive.
Definition _modulus : ident := 172%positive.
Definition _n : ident := 118%positive.
Definition _p : ident := 123%positive.
Definition _pdata : ident := 103%positive.
Definition _plen : ident := 104%positive.
Definition _pparity : ident := 124%positive.
Definition _printf : ident := 89%positive.
Definition _pstat : ident := 105%positive.
Definition _q : ident := 131%positive.
Definition _r : ident := 136%positive.
Definition _row : ident := 147%positive.
Definition _rse_code : ident := 115%positive.
Definition _rse_code_print : ident := 187%positive.
Definition _rse_init : ident := 161%positive.
Definition _s : ident := 135%positive.
Definition _stderr : ident := 86%positive.
Definition _t : ident := 137%positive.
Definition _temp : ident := 170%positive.
Definition _trace : ident := 91%positive.
Definition _u : ident := 138%positive.
Definition _v : ident := 134%positive.
Definition _w : ident := 168%positive.
Definition _weight : ident := 133%positive.
Definition _x : ident := 132%positive.
Definition _xh : ident := 142%positive.
Definition _xk : ident := 143%positive.
Definition _xr : ident := 144%positive.
Definition _y : ident := 121%positive.
Definition _z : ident := 122%positive.
Definition _t'1 : ident := 189%positive.
Definition _t'10 : ident := 198%positive.
Definition _t'11 : ident := 199%positive.
Definition _t'12 : ident := 200%positive.
Definition _t'13 : ident := 201%positive.
Definition _t'14 : ident := 202%positive.
Definition _t'15 : ident := 203%positive.
Definition _t'16 : ident := 204%positive.
Definition _t'17 : ident := 205%positive.
Definition _t'18 : ident := 206%positive.
Definition _t'19 : ident := 207%positive.
Definition _t'2 : ident := 190%positive.
Definition _t'20 : ident := 208%positive.
Definition _t'21 : ident := 209%positive.
Definition _t'22 : ident := 210%positive.
Definition _t'23 : ident := 211%positive.
Definition _t'24 : ident := 212%positive.
Definition _t'25 : ident := 213%positive.
Definition _t'26 : ident := 214%positive.
Definition _t'27 : ident := 215%positive.
Definition _t'28 : ident := 216%positive.
Definition _t'29 : ident := 217%positive.
Definition _t'3 : ident := 191%positive.
Definition _t'30 : ident := 218%positive.
Definition _t'31 : ident := 219%positive.
Definition _t'32 : ident := 220%positive.
Definition _t'33 : ident := 221%positive.
Definition _t'34 : ident := 222%positive.
Definition _t'35 : ident := 223%positive.
Definition _t'36 : ident := 224%positive.
Definition _t'37 : ident := 225%positive.
Definition _t'38 : ident := 226%positive.
Definition _t'39 : ident := 227%positive.
Definition _t'4 : ident := 192%positive.
Definition _t'40 : ident := 228%positive.
Definition _t'41 : ident := 229%positive.
Definition _t'42 : ident := 230%positive.
Definition _t'43 : ident := 231%positive.
Definition _t'44 : ident := 232%positive.
Definition _t'45 : ident := 233%positive.
Definition _t'46 : ident := 234%positive.
Definition _t'47 : ident := 235%positive.
Definition _t'48 : ident := 236%positive.
Definition _t'49 : ident := 237%positive.
Definition _t'5 : ident := 193%positive.
Definition _t'50 : ident := 238%positive.
Definition _t'51 : ident := 239%positive.
Definition _t'52 : ident := 240%positive.
Definition _t'53 : ident := 241%positive.
Definition _t'54 : ident := 242%positive.
Definition _t'55 : ident := 243%positive.
Definition _t'56 : ident := 244%positive.
Definition _t'57 : ident := 245%positive.
Definition _t'58 : ident := 246%positive.
Definition _t'59 : ident := 247%positive.
Definition _t'6 : ident := 194%positive.
Definition _t'60 : ident := 248%positive.
Definition _t'61 : ident := 249%positive.
Definition _t'62 : ident := 250%positive.
Definition _t'63 : ident := 251%positive.
Definition _t'64 : ident := 252%positive.
Definition _t'65 : ident := 253%positive.
Definition _t'66 : ident := 254%positive.
Definition _t'67 : ident := 255%positive.
Definition _t'68 : ident := 256%positive.
Definition _t'69 : ident := 257%positive.
Definition _t'7 : ident := 195%positive.
Definition _t'70 : ident := 258%positive.
Definition _t'71 : ident := 259%positive.
Definition _t'72 : ident := 260%positive.
Definition _t'73 : ident := 261%positive.
Definition _t'74 : ident := 262%positive.
Definition _t'8 : ident := 196%positive.
Definition _t'9 : ident := 197%positive.

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

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 0) :: nil);
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
                         {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                               {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
              ((Etempvar _t'11 (tptr (Tstruct __IO_FILE noattr))) ::
               (Evar ___stringlit_2 (tarray tschar 40)) :: nil)))
          (Ssequence
            (Ssequence
              (Sset _t'10 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
              (Scall None
                (Evar _fprintf (Tfunction
                                 (Tcons (tptr (Tstruct __IO_FILE noattr))
                                   (Tcons (tptr tschar) Tnil)) tint
                                 {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                   {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                     (Evar ___stringlit_6 (tarray tschar 6)) ::
                     (Econst_int (Int.repr 178) tint) ::
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
               (_pparity, (tptr (tptr tuchar))) :: (_t'2, tint) ::
               (_t'1, tuchar) ::
               (_t'24, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'23, tschar) ::
               (_t'22, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'21, (tptr tuchar)) ::
               (_t'20, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'19, tuchar) :: (_t'18, (tptr tuchar)) ::
               (_t'17, tuchar) :: (_t'16, tuchar) :: (_t'15, tuchar) ::
               (_t'14, tuchar) :: (_t'13, tuchar) :: (_t'12, tuchar) ::
               (_t'11, tuchar) :: (_t'10, tuchar) :: (_t'9, tuchar) ::
               (_t'8, tuchar) :: (_t'7, tuchar) :: (_t'6, tuchar) ::
               (_t'5, tint) :: (_t'4, (tptr tuchar)) ::
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
              (Sset _t'23
                (Ederef
                  (Ebinop Oadd (Etempvar _pstat (tptr tschar))
                    (Etempvar _i tuchar) (tptr tschar)) tschar))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'23 tschar)
                             (Econst_int (Int.repr 1) tint) tint)
                (Ssequence
                  (Sifthenelse (Econst_int (Int.repr 0) tint)
                    (Ssequence
                      (Sset _t'24
                        (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                      (Scall None
                        (Evar _fprintf (Tfunction
                                         (Tcons
                                           (tptr (Tstruct __IO_FILE noattr))
                                           (Tcons (tptr tschar) Tnil)) tint
                                         {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                        ((Etempvar _t'24 (tptr (Tstruct __IO_FILE noattr))) ::
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
            (Sset _t'22 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
            (Scall None
              (Evar _fprintf (Tfunction
                               (Tcons (tptr (Tstruct __IO_FILE noattr))
                                 (Tcons (tptr tschar) Tnil)) tint
                               {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
              ((Etempvar _t'22 (tptr (Tstruct __IO_FILE noattr))) ::
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
                        (Sset _t'21
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _pparity (tptr (tptr tuchar)))
                              (Etempvar _t'1 tuchar) (tptr (tptr tuchar)))
                            (tptr tuchar)))
                        (Sifthenelse (Eunop Onotbool
                                       (Etempvar _t'21 (tptr tuchar)) tint)
                          Sskip
                          Sbreak)))
                    Sskip)
                  (Ssequence
                    (Sifthenelse (Econst_int (Int.repr 0) tint)
                      (Ssequence
                        (Sset _t'20
                          (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                        (Scall None
                          (Evar _fprintf (Tfunction
                                           (Tcons
                                             (tptr (Tstruct __IO_FILE noattr))
                                             (Tcons (tptr tschar) Tnil)) tint
                                           {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                          ((Etempvar _t'20 (tptr (Tstruct __IO_FILE noattr))) ::
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
                           (Evar ___stringlit_6 (tarray tschar 6)) ::
                           (Econst_int (Int.repr 221) tint) ::
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
                                                  (Sset _t'18
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _pdata (tptr (tptr tuchar)))
                                                        (Etempvar _n tint)
                                                        (tptr (tptr tuchar)))
                                                      (tptr tuchar)))
                                                  (Ssequence
                                                    (Sset _t'19
                                                      (Ederef
                                                        (Ecast
                                                          (Ebinop Oadd
                                                            (Etempvar _t'18 (tptr tuchar))
                                                            (Etempvar _j tint)
                                                            (tptr tuchar))
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Sset _data
                                                      (Ecast
                                                        (Etempvar _t'19 tuchar)
                                                        tuchar))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'17
                                                      (Ederef
                                                        (Etempvar _p (tptr tuchar))
                                                        tuchar))
                                                    (Sifthenelse (Etempvar _t'17 tuchar)
                                                      (Sset _t'2
                                                        (Ecast
                                                          (Etempvar _data tuchar)
                                                          tbool))
                                                      (Sset _t'2
                                                        (Econst_int (Int.repr 0) tint))))
                                                  (Sifthenelse (Etempvar _t'2 tint)
                                                    (Ssequence
                                                      (Sset _t'6
                                                        (Ederef
                                                          (Etempvar _p (tptr tuchar))
                                                          tuchar))
                                                      (Ssequence
                                                        (Sset _t'7
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _fec_2_power (tarray tuchar 256))
                                                              (Etempvar _t'6 tuchar)
                                                              (tptr tuchar))
                                                            tuchar))
                                                        (Ssequence
                                                          (Sset _t'8
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _fec_2_power (tarray tuchar 256))
                                                                (Etempvar _data tuchar)
                                                                (tptr tuchar))
                                                              tuchar))
                                                          (Sifthenelse 
                                                            (Ebinop Ogt
                                                              (Ebinop Oadd
                                                                (Etempvar _t'7 tuchar)
                                                                (Etempvar _t'8 tuchar)
                                                                tint)
                                                              (Ebinop Osub
                                                                (Econst_int (Int.repr 256) tint)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tint) tint)
                                                            (Ssequence
                                                              (Sset _t'13
                                                                (Ederef
                                                                  (Etempvar _p (tptr tuchar))
                                                                  tuchar))
                                                              (Ssequence
                                                                (Sset _t'14
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _t'13 tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                (Ssequence
                                                                  (Sset _t'15
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _data tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                  (Ssequence
                                                                    (Sset _t'16
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_index (tarray tuchar 256))
                                                                    (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'14 tuchar)
                                                                    (Etempvar _t'15 tuchar)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 256) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _y
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Etempvar _y tuchar)
                                                                    (Etempvar _t'16 tuchar)
                                                                    tint)
                                                                    tuchar))))))
                                                            (Ssequence
                                                              (Sset _t'9
                                                                (Ederef
                                                                  (Etempvar _p (tptr tuchar))
                                                                  tuchar))
                                                              (Ssequence
                                                                (Sset _t'10
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _t'9 tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                (Ssequence
                                                                  (Sset _t'11
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _data tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                  (Ssequence
                                                                    (Sset _t'12
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_index (tarray tuchar 256))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'10 tuchar)
                                                                    (Etempvar _t'11 tuchar)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _y
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Etempvar _y tuchar)
                                                                    (Etempvar _t'12 tuchar)
                                                                    tint)
                                                                    tuchar))))))))))
                                                    Sskip)))
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
                                   {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tuchar) ::
               (_t'3, tuchar) :: (_t'2, tuchar) :: (_t'1, tuchar) ::
               (_t'74, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'73, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'72, tschar) :: (_t'71, (tptr tuchar)) ::
               (_t'70, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'69, tuchar) ::
               (_t'68, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'67, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'66, tuchar) ::
               (_t'65, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'64, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'63, tuchar) ::
               (_t'62, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'61, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'60, (tptr (Tstruct __IO_FILE noattr))) :: (_t'59, tint) ::
               (_t'58, tuchar) :: (_t'57, tuchar) :: (_t'56, tuchar) ::
               (_t'55, (tptr (Tstruct __IO_FILE noattr))) ::
               (_t'54, tuchar) :: (_t'53, tuchar) :: (_t'52, tuchar) ::
               (_t'51, tuchar) :: (_t'50, (tptr tuchar)) ::
               (_t'49, tuchar) :: (_t'48, tuchar) :: (_t'47, tuchar) ::
               (_t'46, tuchar) :: (_t'45, tuchar) :: (_t'44, tuchar) ::
               (_t'43, tuchar) :: (_t'42, tuchar) :: (_t'41, tint) ::
               (_t'40, tuchar) :: (_t'39, (tptr tuchar)) ::
               (_t'38, tuchar) :: (_t'37, tuchar) :: (_t'36, tuchar) ::
               (_t'35, tuchar) :: (_t'34, tuchar) :: (_t'33, tuchar) ::
               (_t'32, tuchar) :: (_t'31, tuchar) :: (_t'30, tuchar) ::
               (_t'29, tuchar) :: (_t'28, tuchar) :: (_t'27, tuchar) ::
               (_t'26, tuchar) :: (_t'25, tuchar) :: (_t'24, tuchar) ::
               (_t'23, tuchar) :: (_t'22, tuchar) :: (_t'21, tuchar) ::
               (_t'20, tuchar) :: (_t'19, tuchar) :: (_t'18, tuchar) ::
               (_t'17, tuchar) :: (_t'16, tuchar) :: (_t'15, tuchar) ::
               (_t'14, tuchar) :: (_t'13, (tptr tuchar)) :: (_t'12, tint) ::
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
                (Sset _t'74 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                (Scall None
                  (Evar _fprintf (Tfunction
                                   (Tcons (tptr (Tstruct __IO_FILE noattr))
                                     (Tcons (tptr tschar) Tnil)) tint
                                   {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                  ((Etempvar _t'74 (tptr (Tstruct __IO_FILE noattr))) ::
                   (Evar ___stringlit_13 (tarray tschar 36)) ::
                   (Etempvar _k tint) :: (Etempvar _c tint) :: nil)))
              Sskip)
            (Ssequence
              (Sifthenelse (Econst_int (Int.repr 0) tint)
                (Ssequence
                  (Sset _t'73
                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                  (Scall None
                    (Evar _fflush (Tfunction
                                    (Tcons (tptr (Tstruct __IO_FILE noattr))
                                      Tnil) tint cc_default))
                    ((Etempvar _t'73 (tptr (Tstruct __IO_FILE noattr))) ::
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
                        (Sset _t'72
                          (Ederef
                            (Ebinop Oadd (Etempvar _pstat (tptr tschar))
                              (Etempvar _i tuchar) (tptr tschar)) tschar))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'72 tschar)
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
                                (Sset _t'71
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _pparity (tptr (tptr tuchar)))
                                      (Etempvar _i tuchar)
                                      (tptr (tptr tuchar))) (tptr tuchar)))
                                (Sifthenelse (Etempvar _t'71 (tptr tuchar))
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
                                     (Evar ___stringlit_6 (tarray tschar 6)) ::
                                     (Econst_int (Int.repr 301) tint) ::
                                     (Evar ___func____2 (tarray tschar 15)) ::
                                     nil))))))
                          (Sset _i
                            (Ecast
                              (Ebinop Oadd (Etempvar _i tuchar)
                                (Econst_int (Int.repr 1) tint) tint) tuchar))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'59 (Evar _trace tint))
                          (Sifthenelse (Ebinop Ogt (Etempvar _t'59 tint)
                                         (Econst_int (Int.repr 1) tint) tint)
                            (Ssequence
                              (Sifthenelse (Econst_int (Int.repr 0) tint)
                                (Ssequence
                                  (Sset _t'70
                                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                  (Scall None
                                    (Evar _fprintf (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct __IO_FILE noattr))
                                                       (Tcons (tptr tschar)
                                                         Tnil)) tint
                                                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                    ((Etempvar _t'70 (tptr (Tstruct __IO_FILE noattr))) ::
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
                                          (Sset _t'68
                                            (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                          (Ssequence
                                            (Sset _t'69
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
                                                               {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                              ((Etempvar _t'68 (tptr (Tstruct __IO_FILE noattr))) ::
                                               (Evar ___stringlit_16 (tarray tschar 5)) ::
                                               (Etempvar _t'69 tuchar) ::
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
                                      (Sset _t'67
                                        (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                      (Scall None
                                        (Evar _fprintf (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct __IO_FILE noattr))
                                                           (Tcons
                                                             (tptr tschar)
                                                             Tnil)) tint
                                                         {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                        ((Etempvar _t'67 (tptr (Tstruct __IO_FILE noattr))) ::
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
                                              (Sset _t'65
                                                (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                              (Ssequence
                                                (Sset _t'66
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
                                                                   {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                  ((Etempvar _t'65 (tptr (Tstruct __IO_FILE noattr))) ::
                                                   (Evar ___stringlit_18 (tarray tschar 4)) ::
                                                   (Etempvar _t'66 tuchar) ::
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
                                          (Sset _t'64
                                            (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                          (Scall None
                                            (Evar _fprintf (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct __IO_FILE noattr))
                                                               (Tcons
                                                                 (tptr tschar)
                                                                 Tnil)) tint
                                                             {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                            ((Etempvar _t'64 (tptr (Tstruct __IO_FILE noattr))) ::
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
                                                  (Sset _t'62
                                                    (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                                  (Ssequence
                                                    (Sset _t'63
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
                                                        {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                      ((Etempvar _t'62 (tptr (Tstruct __IO_FILE noattr))) ::
                                                       (Evar ___stringlit_18 (tarray tschar 4)) ::
                                                       (Etempvar _t'63 tuchar) ::
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
                                              (Sset _t'61
                                                (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                              (Scall None
                                                (Evar _fprintf (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct __IO_FILE noattr))
                                                                   (Tcons
                                                                    (tptr tschar)
                                                                    Tnil))
                                                                 tint
                                                                 {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                                ((Etempvar _t'61 (tptr (Tstruct __IO_FILE noattr))) ::
                                                 (Evar ___stringlit_20 (tarray tschar 2)) ::
                                                 nil)))
                                            Sskip)
                                          (Sifthenelse (Econst_int (Int.repr 0) tint)
                                            (Ssequence
                                              (Sset _t'60
                                                (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                              (Scall None
                                                (Evar _fflush (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct __IO_FILE noattr))
                                                                  Tnil) tint
                                                                cc_default))
                                                ((Etempvar _t'60 (tptr (Tstruct __IO_FILE noattr))) ::
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
                                    (Sset _t'58
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
                                            (Etempvar _t'58 tuchar)
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
                                              (Sset _t'56
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _lost (tarray tuchar 128))
                                                    (Etempvar _i tuchar)
                                                    (tptr tuchar)) tuchar))
                                              (Ssequence
                                                (Sset _t'57
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _n (tptr tuchar))
                                                      (Etempvar _t'56 tuchar)
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
                                                  (Etempvar _t'57 tuchar))))))
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
                                    (Sset _t'55
                                      (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
                                    (Scall None
                                      (Evar _fprintf (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct __IO_FILE noattr))
                                                         (Tcons (tptr tschar)
                                                           Tnil)) tint
                                                       {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                      ((Etempvar _t'55 (tptr (Tstruct __IO_FILE noattr))) ::
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
                                        (Sset _t'54
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _row (tarray tuchar 128))
                                              (Etempvar _i tuchar)
                                              (tptr tuchar)) tuchar))
                                        (Sset _p
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _fec_weights (tarray (tarray tuchar 255) 128))
                                              (Etempvar _t'54 tuchar)
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
                                                            (Sset _t'53
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _found (tarray tuchar 128))
                                                                  (Etempvar _q tuchar)
                                                                  (tptr tuchar))
                                                                tuchar))
                                                            (Sset _z
                                                              (Ecast
                                                                (Etempvar _t'53 tuchar)
                                                                tuchar)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'52
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Etempvar _p (tptr tuchar))
                                                                    (Etempvar _z tuchar)
                                                                    (tptr tuchar))
                                                                  tuchar))
                                                              (Sset _weight
                                                                (Ecast
                                                                  (Etempvar _t'52 tuchar)
                                                                  tuchar)))
                                                            (Sifthenelse 
                                                              (Ebinop Olt
                                                                (Etempvar _z tuchar)
                                                                (Etempvar _k tint)
                                                                tint)
                                                              (Ssequence
                                                                (Sset _t'41
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _plen (tptr tint))
                                                                    (Etempvar _z tuchar)
                                                                    (tptr tint))
                                                                    tint))
                                                                (Sifthenelse 
                                                                  (Ebinop Ogt
                                                                    (Etempvar _t'41 tint)
                                                                    (Etempvar _j tint)
                                                                    tint)
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'50
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pdata (tptr (tptr tuchar)))
                                                                    (Etempvar _z tuchar)
                                                                    (tptr (tptr tuchar)))
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'51
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'50 (tptr tuchar))
                                                                    (Etempvar _j tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _data
                                                                    (Ecast
                                                                    (Etempvar _t'51 tuchar)
                                                                    tuchar))))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _weight tuchar)
                                                                    (Sset _t'7
                                                                    (Ecast
                                                                    (Etempvar _data tuchar)
                                                                    tbool))
                                                                    (Sset _t'7
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'7 tint)
                                                                    (Ssequence
                                                                    (Sset _t'42
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _weight tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'43
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _data tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'42 tuchar)
                                                                    (Etempvar _t'43 tuchar)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 256) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'47
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _weight tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'48
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _data tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'49
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_index (tarray tuchar 256))
                                                                    (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'47 tuchar)
                                                                    (Etempvar _t'48 tuchar)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 256) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _y
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Etempvar _y tuchar)
                                                                    (Etempvar _t'49 tuchar)
                                                                    tint)
                                                                    tuchar)))))
                                                                    (Ssequence
                                                                    (Sset _t'44
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _weight tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'45
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _data tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'46
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_index (tarray tuchar 256))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'44 tuchar)
                                                                    (Etempvar _t'45 tuchar)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _y
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Etempvar _y tuchar)
                                                                    (Etempvar _t'46 tuchar)
                                                                    tint)
                                                                    tuchar))))))))
                                                                    Sskip)))
                                                                  Sskip))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'39
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
                                                                    (Sset _t'40
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'39 (tptr tuchar))
                                                                    (Etempvar _j tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _data
                                                                    (Ecast
                                                                    (Etempvar _t'40 tuchar)
                                                                    tuchar))))
                                                                (Ssequence
                                                                  (Sifthenelse (Etempvar _weight tuchar)
                                                                    (Sset _t'8
                                                                    (Ecast
                                                                    (Etempvar _data tuchar)
                                                                    tbool))
                                                                    (Sset _t'8
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                  (Sifthenelse (Etempvar _t'8 tint)
                                                                    (Ssequence
                                                                    (Sset _t'31
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _weight tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'32
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _data tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'31 tuchar)
                                                                    (Etempvar _t'32 tuchar)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 256) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'36
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _weight tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'37
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _data tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'38
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_index (tarray tuchar 256))
                                                                    (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'36 tuchar)
                                                                    (Etempvar _t'37 tuchar)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 256) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _y
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Etempvar _y tuchar)
                                                                    (Etempvar _t'38 tuchar)
                                                                    tint)
                                                                    tuchar)))))
                                                                    (Ssequence
                                                                    (Sset _t'33
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _weight tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'34
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _data tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'35
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_index (tarray tuchar 256))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'33 tuchar)
                                                                    (Etempvar _t'34 tuchar)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _y
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Etempvar _y tuchar)
                                                                    (Etempvar _t'35 tuchar)
                                                                    tint)
                                                                    tuchar))))))))
                                                                    Sskip)))))))
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
                                                  (Sset _t'30
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
                                                        (Etempvar _t'30 tuchar)
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
                                                                    (Sset _t'28
                                                                    (Ederef
                                                                    (Etempvar _n (tptr tuchar))
                                                                    tuchar))
                                                                    (Sifthenelse (Etempvar _t'28 tuchar)
                                                                    (Ssequence
                                                                    (Sset _t'29
                                                                    (Ederef
                                                                    (Etempvar _r (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _t'9
                                                                    (Ecast
                                                                    (Etempvar _t'29 tuchar)
                                                                    tbool)))
                                                                    (Sset _t'9
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'9 tint)
                                                                    (Ssequence
                                                                    (Sset _t'14
                                                                    (Ederef
                                                                    (Etempvar _n (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'15
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _t'14 tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'16
                                                                    (Ederef
                                                                    (Etempvar _r (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'17
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _t'16 tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'15 tuchar)
                                                                    (Etempvar _t'17 tuchar)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 256) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'23
                                                                    (Ederef
                                                                    (Etempvar _n (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'24
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _t'23 tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'25
                                                                    (Ederef
                                                                    (Etempvar _r (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'26
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _t'25 tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'27
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_index (tarray tuchar 256))
                                                                    (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'24 tuchar)
                                                                    (Etempvar _t'26 tuchar)
                                                                    tint)
                                                                    (Ebinop Osub
                                                                    (Econst_int (Int.repr 256) tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _y
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Etempvar _y tuchar)
                                                                    (Etempvar _t'27 tuchar)
                                                                    tint)
                                                                    tuchar)))))))
                                                                    (Ssequence
                                                                    (Sset _t'18
                                                                    (Ederef
                                                                    (Etempvar _n (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'19
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _t'18 tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'20
                                                                    (Ederef
                                                                    (Etempvar _r (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'21
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_power (tarray tuchar 256))
                                                                    (Etempvar _t'20 tuchar)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'22
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _fec_2_index (tarray tuchar 256))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'19 tuchar)
                                                                    (Etempvar _t'21 tuchar)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _y
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Etempvar _y tuchar)
                                                                    (Etempvar _t'22 tuchar)
                                                                    tint)
                                                                    tuchar))))))))))))
                                                                    Sskip))
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
                                                             {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                         {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                  {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_26 (tarray tschar 5)) ::
                   (Etempvar _t'1 tuchar) :: nil))))
            (Sset _j
              (Ebinop Osub (Etempvar _j tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                      {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                  {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                         {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                                 {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                                         {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                           {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                               {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                         {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                                         {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                           {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
                                 {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
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
    (__flags2, tint) :: (__old_offset, tint) :: (__cur_column, tushort) ::
    (__vtable_offset, tschar) :: (__shortbuf, (tarray tschar 1)) ::
    (__lock, (tptr tvoid)) :: (__offset, tlong) ::
    (__codecvt, (tptr (Tstruct __IO_codecvt noattr))) ::
    (__wide_data, (tptr (Tstruct __IO_wide_data noattr))) ::
    (__freeres_list, (tptr (Tstruct __IO_FILE noattr))) ::
    (__freeres_buf, (tptr tvoid)) :: (___pad5, tuint) :: (__mode, tint) ::
    (__unused2, (tarray tschar 40)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_24, Gvar v___stringlit_24) ::
 (___stringlit_11, Gvar v___stringlit_11) ::
 (___stringlit_35, Gvar v___stringlit_35) ::
 (___stringlit_29, Gvar v___stringlit_29) ::
 (___stringlit_37, Gvar v___stringlit_37) ::
 (___stringlit_31, Gvar v___stringlit_31) ::
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
 (___stringlit_6, Gvar v___stringlit_6) ::
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
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
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
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
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
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_stderr, Gvar v_stderr) ::
 (_fflush,
   Gfun(External (EF_external "fflush"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct __IO_FILE noattr)) Tnil) tint cc_default)) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct __IO_FILE noattr)) (Tcons (tptr tschar) Tnil))
     tint {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) AST.Tint
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___assert_fail,
   Gfun(External (EF_external "__assert_fail"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
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
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


