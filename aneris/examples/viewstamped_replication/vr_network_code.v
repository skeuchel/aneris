(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/viewstamped_replication/vr_network_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib Require Import list_code.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.aneris_lang.lib Require Import queue_code.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.examples.viewstamped_replication Require Import vr_serialization_code.

(**  Implementation of Retransmission/Acknowledgment (R/A) and
    Network/Application (N/A) communication layers of VR protocols  *)

Definition cfg_cell : val :=
  λ: "cfg" "i" "j",
  let: "cfg_i" := unSOME (list_nth "cfg" "i") in
  let: "addr_ij" := unSOME (list_nth "cfg_i" "j") in
  "addr_ij".

Definition init_socket_ij : val :=
  λ: "cfg" "i" "j",
  let: "sh" := NewSocket #() in
  let: "addr" := cfg_cell "cfg" "i" "j" in
  (if: "i" = "j"
   then  SetReceiveTimeout "sh" #2 #0
   else
     (if: "j" = #0
     then  SetReceiveTimeout "sh" #15 #0
     else  SetReceiveTimeout "sh" #3 #0));;
  SocketBind "sh" "addr";;
  "sh".

Definition init_sockets : val :=
  λ: "cfg" "i",
  let: "len" := list_length "cfg" in
  letrec: "aux" "j" :=
    (if: "len" ≤ "j"
     then  []
     else
       let: "sh" := init_socket_ij "cfg" "i" "j" in
       "sh" :: "aux" ("j" + #1)) in
    "aux" #0.

(**  -------------------------------------------------------------------------  *)

(**  ------------------------------- RECEIVING -------------------------------  *)

(**  -------------------------------------------------------------------------  *)

Definition msgId_serializer :=
  sum_serializer int_serializer
  (prod_serializer int_serializer string_serializer).

Definition update_outQueue_j_at_ack : val :=
  λ: "ack_j" "lk_j" "outQ_j" "ack",
  letrec: "aux" "queue" :=
    (if: queue_is_empty "queue"
     then  "queue"
     else
       let: "q" := unSOME (queue_take_opt "queue") in
       let: "msg" := Fst "q" in
       let: "queue'" := Snd "q" in
       (if: (Fst "msg") ≤ "ack"
        then  "aux" "queue'"
        else  "queue")) in
    acquire "lk_j";;
    (if: "ack" ≤ ! "ack_j"
     then  #()
     else
       "ack_j" <- "ack";;
       let: "queue" := "aux" ! "outQ_j" in
       "outQ_j" <- "queue");;
    release "lk_j".

Definition receive_from_j_at_i val_ser : val :=
  λ: "lk" "sh" "mon" "inQ" "outData_j",
  let: "lk_j" := Fst (Fst (Fst (Fst "outData_j"))) in
  let: "_seqid_j" := Snd (Fst (Fst (Fst "outData_j"))) in
  let: "seen_j" := Snd (Fst (Fst "outData_j")) in
  let: "ack_j" := Snd (Fst "outData_j") in
  let: "outQ_j" := Snd "outData_j" in
  letrec: "loop" <> :=
    match: ReceiveFrom "sh" with
      NONE => acquire "lk";;
              "mon" <- #false;;
              release "lk"
    | SOME "msg" =>
        let: "mbody" := Fst "msg" in
        let: "msrc" := Snd "msg" in
        let: "msgid" := msgId_serializer.(s_deser) "mbody" in
        match: "msgid" with
          InjL "ack" =>
          update_outQueue_j_at_ack "ack_j" "lk_j" "outQ_j" "ack"
        | InjR "mid" =>
            let: "msg_id" := Fst "mid" in
            let: "msg_body" := Snd "mid" in
            acquire "lk_j";;
            let: "msg_ack" := msgId_serializer.(s_ser) (InjL ! "seen_j") in
            let: "_sendack" := SendTo "sh" "msg_ack" "msrc" in
            (if: "msg_id" ≤ ! "seen_j"
             then  release "lk_j"
             else
               "seen_j" <- "msg_id";;
               release "lk_j";;
               acquire "lk";;
               let: "event" := (msg_serializer val_ser).(s_deser) "msg_body" in
               "inQ" <- (queue_add (InjL "event") ! "inQ");;
               "mon" <- #true;;
               release "lk")
        end
    end;;
    "loop" #() in
    "loop" #().

Definition receive_from_clients_at_ii val_ser : val :=
  λ: "lk" "sh" "mon" "inQ",
  letrec: "loop" <> :=
    let: "<>" := match: ReceiveFrom "sh" with
      NONE => acquire "lk";;
              "mon" <- #false;;
              release "lk"
    | SOME "msg" =>
        let: "event" := (request_serializer val_ser).(s_deser) (Fst "msg") in
        acquire "lk";;
        "mon" <- #true;;
        "inQ" <- (queue_add (InjR "event") ! "inQ");;
        release "lk"
    end in
    "loop" #() in
    "loop" #().

Definition fork_receive_threads val_ser : val :=
  λ: "i" "lk" "shl" "mnl" "outData" "inQ",
  let: "len" := list_length "shl" in
  letrec: "aux" "j" :=
    (if: "j" < "len"
     then
       let: "sh" := unSOME (list_nth "shl" "j") in
       let: "mn" := unSOME (list_nth "mnl" "j") in
       let: "<>" := (if: "j" = "i"
        then  Fork (receive_from_clients_at_ii val_ser "lk" "sh" "mn" "inQ")
        else
          let: "outData_j" := unSOME (list_nth "outData" "j") in
          Fork (receive_from_j_at_i val_ser "lk" "sh" "mn" "inQ" "outData_j")) in
       "aux" ("j" + #1)
     else  #()) in
    "aux" #0.

(**  -------------------------------------------------------------------------  *)

(**  --------------------------------- SENDING -------------------------------  *)

(**  -------------------------------------------------------------------------  *)

Definition outqueue_msg : val :=
  λ: "outData" "j" "msg",
  let: "data_j" := unSOME (list_nth "outData" "j") in
  let: "lk_j" := Fst (Fst (Fst (Fst "data_j"))) in
  let: "seqid_j" := Snd (Fst (Fst (Fst "data_j"))) in
  let: "_seen_j" := Snd (Fst (Fst "data_j")) in
  let: "_ack_j" := Snd (Fst "data_j") in
  let: "outQ_j" := Snd "data_j" in
  acquire "lk_j";;
  let: "idj" := ! "seqid_j" + #1 in
  "seqid_j" <- "idj";;
  "outQ_j" <- (queue_add ("idj", "msg") ! "outQ_j");;
  release "lk_j".

Definition outqueue_event_to_group val_ser : val :=
  λ: "len" "i" "outData" "event",
  let: "msg" := (msg_serializer val_ser).(s_ser) "event" in
  letrec: "aux" "j" :=
    (if: "j" < "len"
     then
       (if: "i" = "j"
       then  "aux" ("j" + #1)
       else
         let: "<>" := outqueue_msg "outData" "j" "msg" in
         "aux" ("j" + #1))
     else  #()) in
    "aux" #0.

Definition outqueue_msg_to_view_primary val_ser : val :=
  λ: "len" "outData" "event" "v",
  let: "j" := "v" `rem` "len" in
  let: "msg" := (msg_serializer val_ser).(s_ser) "event" in
  outqueue_msg "outData" "j" "msg".

Definition send_prp val_ser : val :=
  λ: "len" "i" "outData" "prp_ev",
  outqueue_event_to_group val_ser "len" "i" "outData" "prp_ev".

Definition send_cmt val_ser : val :=
  λ: "len" "i" "outData" "cmt_ev",
  outqueue_event_to_group val_ser "len" "i" "outData" "cmt_ev".

Definition send_pok val_ser : val :=
  λ: "len" "outData" "pok_ev",
  let: "v" := Fst (Fst "pok_ev") in
  let: "n" := Snd (Fst "pok_ev") in
  let: "i" := Snd "pok_ev" in
  outqueue_msg_to_view_primary val_ser "len" "outData" (pok "v" "n" "i") "v".

Definition send_svc val_ser : val :=
  λ: "len" "i" "outData" "svc",
  outqueue_event_to_group val_ser "len" "i" "outData" "svc".

Definition send_dvc val_ser : val :=
  λ: "len" "outData" "dvc_ev",
  let: "v" := Fst (Fst (Fst (Fst (Fst "dvc_ev")))) in
  let: "l" := Snd (Fst (Fst (Fst (Fst "dvc_ev")))) in
  let: "v'" := Snd (Fst (Fst (Fst "dvc_ev"))) in
  let: "n" := Snd (Fst (Fst "dvc_ev")) in
  let: "k" := Snd (Fst "dvc_ev") in
  let: "i" := Snd "dvc_ev" in
  outqueue_msg_to_view_primary val_ser "len" "outData"
  (dvc "v" "l" "v'" "n" "k" "i") "v".

Definition send_snv val_ser : val :=
  λ: "len" "i" "outData" "snv_ev",
  outqueue_event_to_group val_ser "len" "i" "outData" "snv_ev".

Definition send_gst val_ser : val :=
  λ: "len" "outData" "gst_ev",
  let: "v" := Fst (Fst "gst_ev") in
  let: "n" := Snd (Fst "gst_ev") in
  let: "i" := Snd "gst_ev" in
  outqueue_msg_to_view_primary val_ser "len" "outData" (gst "v" "n" "i") "v".

Definition send_nst val_ser : val :=
  λ: "outData" "nst_ev",
  let: "v" := Fst (Fst (Fst (Fst "nst_ev"))) in
  let: "l" := Snd (Fst (Fst (Fst "nst_ev"))) in
  let: "n" := Snd (Fst (Fst "nst_ev")) in
  let: "k" := Snd (Fst "nst_ev") in
  let: "j" := Snd "nst_ev" in
  let: "msg" := (msg_serializer val_ser).(s_ser) (nst "v" "l" "n" "k" "j") in
  outqueue_msg "outData" "j" "msg".

Definition send_rpl val_ser : val :=
  λ: "i" "shl" "reply_ev",
  let: "_bdy" := Fst "reply_ev" in
  let: "caddr" := Snd "reply_ev" in
  let: "msg" := (reply_serializer val_ser).(s_ser) "reply_ev" in
  let: "sh_ii" := unSOME (list_nth "shl" "i") in
  SendTo "sh_ii" "msg" "caddr";;
  #().

Definition event_out_loop val_ser : val :=
  λ: "len" "i" "lk" "shl" "outData" "outQ",
  letrec: "loop" <> :=
    (if: queue_is_empty ! "outQ"
     then  #() (* unsafe (fun () -> Unix.sleepf 0.5) *)
     else
       acquire "lk";;
       let: "tmp" := ! "outQ" in
       (if: ~ (queue_is_empty "tmp")
        then
          let: "q" := unSOME (queue_take_opt "tmp") in
          let: "event" := Fst "q" in
          let: "outq" := Snd "q" in
          "outQ" <- "outq";;
          release "lk";;
          match: "event" with
            InjL "l___" =>
            match: "l___" with
              InjL "ll__" =>
              match: "ll__" with
                InjL "lll_" =>
                match: "lll_" with
                  InjL "_llll" => send_prp val_ser "len" "i" "outData" "l___"
                | InjR "_lllr" => send_cmt val_ser "len" "i" "outData" "l___"
                end
              | InjR "llr_" =>
                  match: "llr_" with
                    InjL "llrl" => send_pok val_ser "len" "outData" "llrl"
                  | InjR "_llrr" =>
                      send_svc val_ser "len" "i" "outData" "l___"
                  end
              end
            | InjR "lr__" =>
                match: "lr__" with
                  InjL "lrl_" =>
                  match: "lrl_" with
                    InjL "lrll" => send_dvc val_ser "len" "outData" "lrll"
                  | InjR "_lrlr" =>
                      send_snv val_ser "len" "i" "outData" "l___"
                  end
                | InjR "rr_" =>
                    match: "rr_" with
                      InjL "lrrl" => send_gst val_ser "len" "outData" "lrrl"
                    | InjR "lrrr" => send_nst val_ser "outData" "lrrr"
                    end
                end
            end
          | InjR "r___" => send_rpl val_ser "i" "shl" "r___"
          end
        else  release "lk";;
              #()));;
    "loop" #() in
    "loop" #().

Definition send_from_i_to_j : val :=
  λ: "lk_j" "sh_ij" "addr_ji" "outQ_j",
  letrec: "sendAll" "q" :=
    (if: queue_is_empty "q"
     then  #()
     else
       let: "q'" := unSOME (queue_take_opt "q") in
       let: "id" := Fst (Fst "q'") in
       let: "msg" := Snd (Fst "q'") in
       let: "tl" := Snd "q'" in
       let: "msg" := msgId_serializer.(s_ser) (InjR ("id", "msg")) in
       SendTo "sh_ij" "msg" "addr_ji";;
       #();;
       "sendAll" "tl") in
    letrec: "loop" <> :=
      acquire "lk_j";;
      let: "queue" := ! "outQ_j" in
      "sendAll" "queue";;
      release "lk_j";;
      "loop" #() in
      "loop" #().

Definition fork_send_within_group_threads : val :=
  λ: "cfg" "i" "shl" "outData",
  let: "len" := list_length "cfg" in
  letrec: "aux" "j" :=
    (if: "j" < "len"
     then
       (if: "i" = "j"
       then  "aux" ("j" + #1)
       else
         let: "sh_ij" := unSOME (list_nth "shl" "j") in
         let: "addr_ji" := cfg_cell "cfg" "j" "i" in
         let: "data_j" := unSOME (list_nth "outData" "j") in
         let: "lk_j" := Fst (Fst (Fst (Fst "data_j"))) in
         let: "_seqid_j" := Snd (Fst (Fst (Fst "data_j"))) in
         let: "_seen_j" := Snd (Fst (Fst "data_j")) in
         let: "_ack_j" := Snd (Fst "data_j") in
         let: "outQ_j" := Snd "data_j" in
         Fork (send_from_i_to_j "lk_j" "sh_ij" "addr_ji" "outQ_j");;
         "aux" ("j" + #1))
     else  #()) in
    "aux" #0.

Definition init_network val_ser : val :=
  λ: "cfg" "i",
  let: "cfg_i" := unSOME (list_nth "cfg" "i") in
  let: "len" := list_length "cfg_i" in
  let: "shl" := init_sockets "cfg" "i" in
  let: "monitors" := list_init "len" (λ: "_j", ref #true) in
  let: "lk" := newlock #() in
  let: "inQ" := ref (queue_empty #()) in
  let: "outQ" := ref (queue_empty #()) in
  let: "create_data_j" := λ: "_j",
  let: "lock_j" := newlock #() in
  let: "seqid_j" := ref #0 in
  let: "seen_j" := ref #0 in
  let: "ack_j" := ref #0 in
  let: "outQ_j" := ref (queue_empty #()) in
  ("lock_j", "seqid_j", "seen_j", "ack_j", "outQ_j") in
  let: "outData" := list_init "len" "create_data_j" in
  fork_send_within_group_threads "cfg" "i" "shl" "outData";;
  fork_receive_threads val_ser "i" "lk" "shl" "monitors" "outData" "inQ";;
  Fork (event_out_loop val_ser "len" "i" "lk" "shl" "outData" "outQ");;
  ("lk", "inQ", "outQ", "monitors", "shl").
