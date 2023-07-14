(* (* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/snapshot_isolation/examples/no_serializability/no_serializability_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.examples.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.util Require Import util_code.

Definition transaction1 : val :=
  λ: "cst",
  start "cst";;
  write "cst" #"x" #1;;
  write "cst" #"y" #1;;
  write "cst" #"z" #1;;
  commitU "cst".

Definition transaction2 : val :=
  λ: "cst",
  start "cst";;
  wait_on_keyT "cst" (λ: "v", "v" = #1) #"z";;
  let: "vx" := read "cst" #"x" in
  (if: "vx" = (SOME #1)
   then  write "cst" #"y" #(-1)
   else  #());;
  commitU "cst".

Definition transaction3 : val :=
  λ: "cst",
  start "cst";;
  wait_on_keyT "cst" (λ: "v", "v" = #1) #"z";;
  let: "vy" := read "cst" #"y" in
  (if: "vy" = (SOME #1)
   then  write "cst" #"x" #(-1)
   else  #());;
  commitU "cst".

Definition transaction4 : val :=
  λ: "cst",
  start "cst";;
  wait_on_keyT "cst" (λ: "v", "v" = #1) #"z";;
  let: "vx" := unSOME (read "cst" #"x") in
  let: "vy" := unSOME (read "cst" #"y") in
  let: "r" := "vx" + "vy" in
  assert: (("r" = #(-2)) || (#0 ≤ "r"));;
  commitU "cst".

Definition transaction1_client : val :=
  λ: "caddr" "kvs_addr",
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  transaction1 "cst".

Definition transaction2_client : val :=
  λ: "caddr" "kvs_addr",
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  transaction2 "cst".

Definition transaction3_client : val :=
  λ: "caddr" "kvs_addr",
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  transaction3 "cst".

Definition transaction4_client : val :=
  λ: "caddr" "kvs_addr",
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  transaction4 "cst".

Definition server : val := λ: "srv", init_server int_serializer "srv". *)
