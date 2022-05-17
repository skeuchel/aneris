(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/reliable_communication/examples/hello_world/hello_world_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.examples.reliable_communication Require Import client_server_code.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.

Definition server : val :=
  λ: "srv_addr",
  let: "skt" := make_server_skt string_serializer string_serializer
                "srv_addr" in
  server_listen "skt";;
  let: "new_conn" := accept "skt" in
  let: "c" := Fst "new_conn" in
  let: "_clt_addr" := Snd "new_conn" in
  let: "req" := recv "c" in
  send "c" "req".

Definition client : val :=
  λ: "clt_addr" "srv_addr",
  let: "skt" := make_client_skt string_serializer string_serializer
                "clt_addr" in
  let: "ch" := connect "skt" "srv_addr" in
  send "ch" #"Hello World!".