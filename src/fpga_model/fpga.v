From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Module Info.
  Definition version := "3.8".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "fpga.c".
  Definition normalized := true.
End Info.

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
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _batch_packet_size : ident := $"batch_packet_size".
Definition _batchnum : ident := $"batchnum".
Definition _encode_packet : ident := $"encode_packet".
Definition _encode_parity : ident := $"encode_parity".
Definition _fec_2_index : ident := $"fec_2_index".
Definition _fec_2_power : ident := $"fec_2_power".
Definition _generate_field_tables : ident := $"generate_field_tables".
Definition _h : ident := $"h".
Definition _i : ident := $"i".
Definition _initialize : ident := $"initialize".
Definition _j : ident := $"j".
Definition _k : ident := $"k".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _mod : ident := $"mod".
Definition _mult : ident := $"mult".
Definition _n : ident := $"n".
Definition _packet : ident := $"packet".
Definition _packet_size : ident := $"packet_size".
Definition _packet_sizes : ident := $"packet_sizes".
Definition _parity_buffers : ident := $"parity_buffers".
Definition _start_batch : ident := $"start_batch".
Definition _temp : ident := $"temp".
Definition _weights : ident := $"weights".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v_weights := {|
  gvar_info := (tarray (tarray tuchar 6) 3);
  gvar_init := (Init_int8 (Int.repr 124) :: Init_int8 (Int.repr 140) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 127) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 147) ::
                Init_int8 (Int.repr 64) :: Init_int8 (Int.repr 93) ::
                Init_int8 (Int.repr 43) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 138) :: Init_int8 (Int.repr 140) ::
                Init_int8 (Int.repr 96) :: Init_int8 (Int.repr 190) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 133) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_parity_buffers := {|
  gvar_info := (tarray (tarray (tarray tuchar 100) 3) 300);
  gvar_init := (Init_space 90000 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_packet_sizes := {|
  gvar_info := (tarray tuint 300);
  gvar_init := (Init_space 1200 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_fec_2_index := {|
  gvar_info := (tarray tuchar 256);
  gvar_init := (Init_space 256 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_fec_2_power := {|
  gvar_info := (tarray tuchar 256);
  gvar_init := (Init_space 256 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_generate_field_tables := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_mod, tint) :: (_i, tint) :: (_temp, tint) ::
               (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _mod (Econst_int (Int.repr 285) tint))
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
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd (Evar _fec_2_index (tarray tuchar 256))
                      (Ebinop Osub (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint) (tptr tuchar))
                    tuchar))
                (Sset _temp
                  (Ebinop Oshl (Etempvar _t'2 tuchar)
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
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Evar _fec_2_index (tarray tuchar 256))
                  (Etempvar _i tint) (tptr tuchar)) tuchar))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _fec_2_power (tarray tuchar 256))
                  (Etempvar _t'1 tuchar) (tptr tuchar)) tuchar)
              (Etempvar _i tint)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_mult := {|
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

Definition f_initialize := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None (Evar _generate_field_tables (Tfunction Tnil tvoid cc_default))
    nil)
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_start_batch := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_batchnum, tuint) :: (_k, tuint) :: (_h, tuint) ::
                (_batch_packet_size, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_j, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Evar _packet_sizes (tarray tuint 300))
        (Etempvar _batchnum tuint) (tptr tuint)) tuint)
    (Etempvar _batch_packet_size tuint))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _h tuint)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _j (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                               (Etempvar _batch_packet_size tuint) tint)
                  Sskip
                  Sbreak)
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Ederef
                        (Ebinop Oadd
                          (Ederef
                            (Ebinop Oadd
                              (Evar _parity_buffers (tarray (tarray (tarray tuchar 100) 3) 300))
                              (Etempvar _batchnum tuint)
                              (tptr (tarray (tarray tuchar 100) 3)))
                            (tarray (tarray tuchar 100) 3))
                          (Etempvar _i tint) (tptr (tarray tuchar 100)))
                        (tarray tuchar 100)) (Etempvar _j tint)
                      (tptr tuchar)) tuchar) (Econst_int (Int.repr 0) tint)))
              (Sset _j
                (Ebinop Oadd (Etempvar _j tint)
                  (Econst_int (Int.repr 1) tint) tint)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_encode_packet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_batchnum, tuint) :: (_j, tuint) :: (_packet_size, tuint) ::
                (_packet, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_m, tint) :: (_n, tint) :: (_t'1, tuchar) ::
               (_t'4, tuchar) :: (_t'3, tuchar) :: (_t'2, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _m (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _m tint)
                       (Econst_int (Int.repr 3) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _n (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _n tint)
                             (Etempvar _packet_size tuint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Ederef
                      (Ebinop Oadd
                        (Ederef
                          (Ebinop Oadd
                            (Evar _weights (tarray (tarray tuchar 6) 3))
                            (Etempvar _m tint) (tptr (tarray tuchar 6)))
                          (tarray tuchar 6)) (Etempvar _j tuint)
                        (tptr tuchar)) tuchar))
                  (Ssequence
                    (Sset _t'4
                      (Ederef
                        (Ebinop Oadd (Etempvar _packet (tptr tuchar))
                          (Etempvar _n tint) (tptr tuchar)) tuchar))
                    (Scall (Some _t'1)
                      (Evar _mult (Tfunction
                                    (Tcons tuchar (Tcons tuchar Tnil)) tuchar
                                    cc_default))
                      ((Etempvar _t'3 tuchar) :: (Etempvar _t'4 tuchar) ::
                       nil))))
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd
                        (Ederef
                          (Ebinop Oadd
                            (Ederef
                              (Ebinop Oadd
                                (Evar _parity_buffers (tarray (tarray (tarray tuchar 100) 3) 300))
                                (Etempvar _batchnum tuint)
                                (tptr (tarray (tarray tuchar 100) 3)))
                              (tarray (tarray tuchar 100) 3))
                            (Etempvar _m tint) (tptr (tarray tuchar 100)))
                          (tarray tuchar 100)) (Etempvar _n tint)
                        (tptr tuchar)) tuchar))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Ederef
                          (Ebinop Oadd
                            (Ederef
                              (Ebinop Oadd
                                (Evar _parity_buffers (tarray (tarray (tarray tuchar 100) 3) 300))
                                (Etempvar _batchnum tuint)
                                (tptr (tarray (tarray tuchar 100) 3)))
                              (tarray (tarray tuchar 100) 3))
                            (Etempvar _m tint) (tptr (tarray tuchar 100)))
                          (tarray tuchar 100)) (Etempvar _n tint)
                        (tptr tuchar)) tuchar)
                    (Ebinop Oxor (Etempvar _t'2 tuchar)
                      (Etempvar _t'1 tuchar) tint)))))
            (Sset _n
              (Ebinop Oadd (Etempvar _n tint) (Econst_int (Int.repr 1) tint)
                tint)))))
      (Sset _m
        (Ebinop Oadd (Etempvar _m tint) (Econst_int (Int.repr 1) tint) tint))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_encode_parity := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_batchnum, tuint) :: (_i, tuint) ::
                (_packet, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_j, tint) :: (_t'2, tuint) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _j (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Ederef
              (Ebinop Oadd (Evar _packet_sizes (tarray tuint 300))
                (Etempvar _batchnum tuint) (tptr tuint)) tuint))
          (Sifthenelse (Ebinop Olt (Etempvar _j tint) (Etempvar _t'2 tuint)
                         tint)
            Sskip
            Sbreak))
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd
                (Ederef
                  (Ebinop Oadd
                    (Ederef
                      (Ebinop Oadd
                        (Evar _parity_buffers (tarray (tarray (tarray tuchar 100) 3) 300))
                        (Etempvar _batchnum tuint)
                        (tptr (tarray (tarray tuchar 100) 3)))
                      (tarray (tarray tuchar 100) 3)) (Etempvar _i tuint)
                    (tptr (tarray tuchar 100))) (tarray tuchar 100))
                (Etempvar _j tint) (tptr tuchar)) tuchar))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _packet (tptr tuchar))
                (Etempvar _j tint) (tptr tuchar)) tuchar)
            (Etempvar _t'1 tuchar))))
      (Sset _j
        (Ebinop Oadd (Etempvar _j tint) (Econst_int (Int.repr 1) tint) tint))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
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
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
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
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_weights, Gvar v_weights) :: (_parity_buffers, Gvar v_parity_buffers) ::
 (_packet_sizes, Gvar v_packet_sizes) ::
 (_fec_2_index, Gvar v_fec_2_index) :: (_fec_2_power, Gvar v_fec_2_power) ::
 (_generate_field_tables, Gfun(Internal f_generate_field_tables)) ::
 (_mult, Gfun(Internal f_mult)) ::
 (_initialize, Gfun(Internal f_initialize)) ::
 (_start_batch, Gfun(Internal f_start_batch)) ::
 (_encode_packet, Gfun(Internal f_encode_packet)) ::
 (_encode_parity, Gfun(Internal f_encode_parity)) :: nil).

Definition public_idents : list ident :=
(_encode_parity :: _encode_packet :: _start_batch :: _initialize :: _mult ::
 _generate_field_tables :: _fec_2_power :: _fec_2_index :: _packet_sizes ::
 _parity_buffers :: _weights :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
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


