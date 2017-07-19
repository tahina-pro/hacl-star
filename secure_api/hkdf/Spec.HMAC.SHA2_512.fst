module Spec.HMAC.SHA2_512

module Hash = Spec.SHA2_512

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

(* Base types *)
type bytes  = Seq.seq UInt8.t
type lbytes (l:nat) = m:Seq.seq UInt8.t{Seq.length m == l}

val xor_bytes: b0:bytes -> b1:bytes{Seq.length b0 == Seq.length b1} -> bytes
let xor_bytes b0 b1 = Spec.Lib.map2 (fun x y -> UInt8.logxor x y) b0 b1


val wrap_key: key:bytes{Seq.length key < Hash.max_input_len_8} -> okey:lbytes Hash.size_block
let wrap_key key =
  if Seq.length key <= Hash.size_block then
    let pad = Seq.create (Hash.size_block - Seq.length key) 0uy in
    Seq.append key pad
  else
    let nkey = Hash.hash key in
    let pad = Seq.create (Hash.size_block - Hash.size_hash) 0uy in
    Seq.append nkey pad

private let ipad: lbytes Hash.size_block = Seq.create Hash.size_block 0x36uy
private let opad: lbytes Hash.size_block = Seq.create Hash.size_block 0x5cuy

(** See https://tools.ietf.org/html/rfc2104.html#section-2 *)
val hmac_core:
  key :lbytes Hash.size_block ->
  data:bytes{Seq.length data + Hash.size_block < Hash.max_input_len_8} ->
  mac :lbytes Hash.size_hash{
    mac ==
    Hash.hash (Seq.append (xor_bytes opad key)
                          (Hash.hash (Seq.append (xor_bytes ipad key) data)))
    }
let hmac_core key data =
  (* Step 2: xor result of step 1 with ipad *)
  let s2 = xor_bytes ipad key in
  (* Step 3: append data to result of step 2 *)
  let s3 = Seq.append s2 data in
  (* Step 4: apply H to result of step 3 *)
  let s4 = Hash.hash s3 in
  (* Step 5: xor result of step 1 with opad *)
  let s5 = xor_bytes opad key in
  (* Step 6: append result of step 4 to result of step 5 *)
  let s6 = Seq.append s5 s4 in
  (* Step 7: apply H to result of step 6 *)
  Hash.hash s6

val hmac:
  key :bytes{Seq.length key < Hash.max_input_len_8} ->
  data:bytes{Seq.length data + Hash.size_block < Hash.max_input_len_8} ->
  mac :lbytes Hash.size_hash
let hmac key data =
  (* Step 1: make sure the key has the proper length *)
  let okey = wrap_key key in
  hmac_core okey data
