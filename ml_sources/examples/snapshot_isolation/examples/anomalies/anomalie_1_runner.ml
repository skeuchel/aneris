open Unix
open Ast
open Anomalie_1_code


let ip = (gethostbyname "localhost").h_addr_list.(0)
let srv_addr = makeAddress (string_of_inet_addr ip) 1100
let clt_addr n = makeAddress (string_of_inet_addr ip) (1100 + n)

let runner () =
  if Array.length Sys.argv < 1
  then (prerr_endline "Usage: <node> \n\
                      \ where <node> is in {0-4}"; exit 2);
  (* sendTo_sim_flag := true; *)
  (* set_send_fault_flags 200 700 100; *)
  (* Printf.printf "Press any key to start the node %!"; *)
  (* let _ = read_line () in *)
  let n = int_of_string (Sys.argv.(1)) in
  if n = 0
  then
    (server srv_addr;
     fork (let rec loop () = Unix.sleepf 10.0; loop () in loop ()) ())
  else if n = 1
  then node_init (clt_addr 1) srv_addr
  else if n = 2
  then node_xy (clt_addr 2) srv_addr
  else if n = 3
  then node_yx (clt_addr 3) srv_addr
  else if n = 4
  then node_read (clt_addr 4) srv_addr
  else assert false
  (* fork (let rec loop () = Unix.sleepf 10.0; loop () in loop ()) () *)

let () = runner ()
