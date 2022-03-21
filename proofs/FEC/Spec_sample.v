Variable tran_f: transcript -> mpred.

(*Concrete types for flow data, packet *)
Variable flow_state : Type.
Variable packet_type : Type.

Variable flow_state_rep: share -> flow_state -> Values.val -> mpred.

Variable packet_rep: share -> packet -> packet_type -> Values.val -> mpred.

Variable packet_list_rep : share -> list packet -> list packet_type -> Values.val -> Values.val -> mpred.

(*IMPORTANT: we want our packet, flow state to be consistent with transcript *)
Variable consistent : transcript -> packet_type -> flow_state -> Prop.

(* u_int32_t redFecActuator(struct packetinfo *pinfo, struct packetinfo **pbeg,
			 struct packetinfo **pend)
*)

Definition redFecActuator_spec (enc: encoder) (dec: decoder) :=
  DECLARE _redFecActuator
  WITH gv : globals, sh: share, t: transcript, p: packet, p_ty: packet_type, p_ptr: Values.val, 
      pbeg: Values.val, pend: Values.val, f: flow_state, f_ptr: Values.val
  PRE [tptr tpacketinfo, tptr (tptr tpacketinfo), tptr (tptr tpacketinfo)]
    PROP (valid_transcript t enc dec; consistent t p_ty f)
    PARAMS (p_ptr; pbeg; pend)
    GLOBALS (gv)
    SEP (flow_state_rep sh f f_ptr;
         tran_f (t <| orig := (orig t) ++ [p] |>);
         packet_rep sh p p_ty p_ptr;
         data_at_ sh (tptr tpacketinfo) pbeg;
         data_at_ sh (tptr tpacketinfo) pend)
  POST [tuint ]
    PROP ()
    RETURN (Vint (Int.zero))
    SEP (tran_f (t <| orig := (orig t) ++ [p] |>);
         EX (l: list packet) (p_tys: list packet_type) (f': flow_state) (p1 p2: Values.val),
          flow_state_rep sh f' f_ptr *
          data_at sh (tptr tpacketinfo) p1 pbeg *
          data_at sh (tptr tpacketinfo) p2 pend *
          packet_list_rep sh l p_tys p1 p2 *
          let new_t := (t <| orig := (orig t) ++ [p] |> <| encoded := (encoded t) ++ l |>) in
          !!(packet_list_flow_prop new_t p_tys f') &&
          !!(valid_transcript new_t enc dec)),