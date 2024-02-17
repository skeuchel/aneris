(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/snapshot_isolation/util/util_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.examples.snapshot_isolation Require Import snapshot_isolation_code.

Definition commitU : val := λ: "cst", let: "_b" := commit "cst" in
                                       #().

Definition commitT : val := λ: "cst", assert: (commit "cst").

Definition wait_transaction : val :=
  λ: "cst" "cond" "k",
  letrec: "aux" <> :=
    start "cst";;
    match: read "cst" "k" with
      NONE => commitT "cst";;
              "aux" #()
    | SOME "v" =>
        (if: "cond" "v"
         then  commitT "cst"
         else  commitT "cst";;
               "aux" #())
    end in
    "aux" #().

Definition run : val :=
  λ: "cst" "handler", start "cst";;
                       "handler" "cst";;
                       commit "cst".

Definition run_client : val :=
  λ: "caddr" "kvs_addr" "tbody",
  #() (* unsafe (fun () -> Printf.printf "Start client.\n%!"); *);;
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  #() (* unsafe (fun () -> Printf.printf "Client started.\n%!"); *);;
  let: "b" := run "cst" "tbody" in
  #() (* unsafe (fun () -> Printf.printf "Transaction %s.\n%!"
             (if b then "committed" else "aborted") *).
