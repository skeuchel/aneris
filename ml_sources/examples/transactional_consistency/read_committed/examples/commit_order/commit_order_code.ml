open !Ast
open Serialization_code
open Snapshot_isolation_code
open Util_code

let transaction1 cst =
  start cst;
  write cst "x" 1;
  let vy = read cst "y" in
  if (vy = Some 1) then (
    write cst "a" 1;
  );
  commitU cst

let transaction2 cst =
  start cst;
  write cst "y" 1;
  let vx = read cst "x" in
  if (vx = Some 1) then (
    write cst "b" 1;
  );
  commitU cst

let transaction3 cst =
  start cst;
  let va = read cst "a" in
  let vb = read cst "b" in
  assert (not (va = Some 1 && vb = Some 1));
  commitU cst

let transaction1_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction1 cst

let transaction2_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction2 cst

let transaction3_client caddr kvs_addr =
  let cst = init_client_proxy int_serializer caddr kvs_addr in
  transaction3 cst

let server srv =
  init_server int_serializer srv
