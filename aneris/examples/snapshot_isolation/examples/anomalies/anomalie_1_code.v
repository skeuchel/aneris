(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/snapshot_isolation/examples/anomalies/anomalie_1_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.examples.snapshot_isolation Require Import snapshot_isolation_code.

Definition run_client : val :=
  λ: "caddr" "kvs_addr" "tbody",
  #() (* unsafe (fun () -> Printf.printf "Start client.\n%!"); *);;
  let: "cst" := init_client_proxy int_serializer "caddr" "kvs_addr" in
  #() (* unsafe (fun () -> Printf.printf "Client started.\n%!"); *);;
  let: "b" := run "cst" "tbody" in
  #() (* unsafe (fun () -> Printf.printf "Transaction %s.\n%!"
             (if b then "committed" else "aborted") *).

Definition tbody_init : val :=
  λ: "s", write "s" #"x" #1;;
           write "s" #"y" #1;;
           write "s" #"s0" #1.

Definition wait_s0 : val :=
  rec: "wait_s0" "s" :=
  match: read "s" #"s0" with
    NONE => let: "_b" := commit "s" in
            start "s";;
            "wait_s0" "s"
  | SOME "v" =>
      (if: "v" = #1
       then  let: "_b" := commit "s" in
             start "s"
       else  let: "_b" := commit "s" in
             start "s";;
             "wait_s0" "s")
  end.

Definition tbody_xy : val :=
  λ: "s",
  wait_s0 "s";;
  match: read "s" #"x" with
    NONE => assert: #false
  | SOME "n" =>
      (if: #0 < "n"
       then
         write "s" #"y" #(-1);;
         write "s" #"s1" #1;;
         #() (* unsafe (fun () -> Printf.printf "Set y to -1 \n%!"); *)
       else  #())
  end.

Definition tbody_yx : val :=
  λ: "s",
  wait_s0 "s";;
  match: read "s" #"y" with
    NONE => assert: #false
  | SOME "n" =>
      (if: #0 < "n"
       then
         write "s" #"x" #(-1);;
         write "s" #"s2" #1;;
         #() (* unsafe (fun () -> Printf.printf "Set x to -1 \n%!"); *)
       else  #())
  end.

Definition tbody_read : val :=
  λ: "s",
  wait_s0 "s";;
  #() (* unsafe (fun () -> Unix.sleepf 2.0); *);;
  let: "vx" := read "s" #"x" in
  let: "vy" := read "s" #"y" in
  match: "vx" with
    SOME "n1" =>
    match: "vy" with
      SOME "n2" =>
      let: "vs1" := read "s" #"s1" in
      let: "vs2" := read "s" #"s2" in
      #() (* unsafe (fun () -> Printf.printf "(x,y) = (%d, %d) \n%!" n1 n2); *);;
      let: "b" := #0 ≤ ("n1" + "n2") in
      (if: ("vs1" = (SOME #1)) && ("vs2" = (SOME #1))
       then  assert: (~ "b")
       else  assert: "b")
    | NONE => assert: #false
    end
  | NONE => assert: #false
  end.

Definition node_init : val :=
  λ: "caddr" "kvs_addr", run_client "caddr" "kvs_addr" tbody_init.

Definition node_xy : val :=
  λ: "caddr" "kvs_addr", run_client "caddr" "kvs_addr" tbody_xy.

Definition node_yx : val :=
  λ: "caddr" "kvs_addr", run_client "caddr" "kvs_addr" tbody_yx.

Definition node_read : val :=
  λ: "caddr" "kvs_addr", run_client "caddr" "kvs_addr" tbody_read.

Definition server : val :=
  λ: "srv",
  #() (* unsafe (fun () -> Printf.printf "Start server.\n%!"); *);;
  init_server int_serializer "srv";;
  #() (* unsafe (fun () -> Printf.printf "Server started.\n%!") *).
