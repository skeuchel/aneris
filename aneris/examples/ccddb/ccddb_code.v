(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/ccddb/ccddb_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib Require Import list_code.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_code.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.aneris_lang.lib Require Import map_code.

Definition store_update : val :=
  λ: "db" "t" "m",
  let: "key" := Fst (Fst (Fst "m")) in
  let: "value" := Snd (Fst (Fst "m")) in
  let: "_vc" := Snd (Fst "m") in
  let: "origin" := Snd "m" in
  "t" <- (vect_inc ! "t" "origin");;
  "db" <- (map_insert "key" "value" ! "db").

Definition store_test : val :=
  λ: "t" "i",
  let: "l" := list_length "t" in
  λ: "w",
  let: "s" := Snd (Fst "w") in
  let: "j" := Snd "w" in
  (if: "i" = "j"
   then  #false
   else  (if: "j" < "l"
     then  vect_applicable "s" "t" "j"
     else  #false)).

Definition store_apply : val :=
  λ: "db" "t" "lock" "inQueue" "i",
  letrec: "apply" <> :=
    acquire "lock";;
    let: "x" := list_find_remove (store_test ! "t" "i") ! "inQueue" in
    match: "x" with
      SOME "a" =>
      let: "msg" := Fst "a" in
      let: "rest" := Snd "a" in
      "inQueue" <- "rest";;
      store_update "db" "t" "msg"
    | NONE => #()
    end;;
    release "lock";;
    "apply" #() in
    "apply" #().

Definition write_event_ser val_ser :=
  prod_ser (prod_ser (prod_ser string_ser val_ser) vect_serialize) int_ser.

Definition write_event_deser val_deser :=
  prod_deser (prod_deser (prod_deser string_deser val_deser) vect_deserialize)
  int_deser.

Definition send_thread val_ser : val :=
  λ: "i" "socket_handler" "lock" "nodes" "outQueue",
  letrec: "out" <> :=
    acquire "lock";;
    let: "tmp" := ! "outQueue" in
    (if: ~ (list_is_empty "tmp")
     then
       "outQueue" <- (list_tail "tmp");;
       release "lock";;
       let: "we" := unSOME (list_head "tmp") in
       let: "msg" := write_event_ser val_ser "we" in
       letrec: "send" "j" :=
         (if: "j" < (list_length "nodes")
          then
            (if: "i" = "j"
            then  "send" ("j" + #1)
            else
              let: "n" := unSOME (list_nth "nodes" "j") in
              SendTo "socket_handler" "msg" "n";;
              #();;
              "send" ("j" + #1))
          else  #()) in
         "send" #0;;
         "out" #()
     else  release "lock";;
           "out" #()) in
    "out" #().

Definition recv_thread val_deser : val :=
  λ: "socket_handler" "lock" "inQueue",
  letrec: "loop" <> :=
    let: "msg" := Fst (unSOME (ReceiveFrom "socket_handler")) in
    acquire "lock";;
    let: "we" := write_event_deser val_deser "msg" in
    "inQueue" <- ("we" :: ! "inQueue");;
    release "lock";;
    "loop" #() in
    "loop" #().

Definition store_read : val :=
  λ: "db" "lock" "key",
  acquire "lock";;
  let: "r" := map_lookup "key" ! "db" in
  release "lock";;
  "r".

Definition store_write : val :=
  λ: "db" "t" "outQueue" "lock" "i" "key" "value",
  acquire "lock";;
  "t" <- (vect_inc ! "t" "i");;
  "db" <- (map_insert "key" "value" ! "db");;
  "outQueue" <- (("key", "value", ! "t", "i") :: ! "outQueue");;
  release "lock".

Definition ccddb_init val_ser val_deser : val :=
  λ: "addrlst" "i",
  let: "db" := ref (map_empty #()) in
  let: "n" := list_length "addrlst" in
  let: "t" := ref (vect_make "n" #0) in
  let: "inQueue" := ref [] in
  let: "outQueue" := ref [] in
  let: "lock" := newlock #() in
  let: "socket_handler" := NewSocket #PF_INET #SOCK_DGRAM #IPPROTO_UDP in
  let: "addr" := unSOME (list_nth "addrlst" "i") in
  SocketBind "socket_handler" "addr";;
  Fork (store_apply "db" "t" "lock" "inQueue" "i");;
  Fork (send_thread val_ser "i" "socket_handler" "lock" "addrlst" "outQueue");;
  Fork (recv_thread val_deser "socket_handler" "lock" "inQueue");;
  (store_read "db" "lock", store_write "db" "t" "outQueue" "lock" "i").