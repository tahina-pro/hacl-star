module Spec.HMAC.SHA2_512

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq
open FStar.UInt32

open Spec.Loops
open Spec.Lib

module U8 = FStar.UInt8

module Hash = Spec.SHA2_512


#set-options "--max_fuel 0 --z3rlimit 10"

(* Base types *)
type bytes = m:seq UInt8.t

val xor_bytes: (b0:bytes) -> (b1:bytes{length b0 = length b1}) -> Tot bytes
let xor_bytes b0 b1 = Spec.Lib.map2 (fun x y -> U8.logxor x y) b0 b1


#reset-options "--max_fuel 0 --z3rlimit 25"

let wrap_key (key:bytes{Seq.length key < Hash.max_input_len_8}) : Tot (okey:bytes{Seq.length okey = Hash.size_block}) =
  if Seq.length key <= Hash.size_block then
    let pad = Seq.create (Hash.size_block - (Seq.length key)) 0uy in
    Seq.append key pad
  else begin
    let nkey = Hash.hash key in
    let pad = Seq.create (Hash.size_block - Hash.size_hash) 0uy in
    Seq.append nkey pad
  end


#reset-options "--max_fuel 0 --z3rlimit 10"

val hmac_core:
  key  :bytes{Seq.length key = Hash.size_block} ->
  data :bytes{Seq.length data + Hash.size_block < Hash.max_input_len_8} ->
  Tot (mac:bytes{Seq.length mac = Hash.size_hash})

#reset-options "--max_fuel 0 --z3rlimit 25"

let hmac_core key data =

  (* Define ipad and opad *)
  let ipad = Seq.create Hash.size_block 0x36uy in
  let opad = Seq.create Hash.size_block 0x5cuy in

  (* Step 1: the key has the proper length *)
  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = xor_bytes ipad key in

  (* Step 3: append data to "result of step 2" *)
  let s3 = Seq.append s2 data in

  (* Step 4: apply H to "result of step 3" *)
  let s4 = Hash.hash s3 in

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = xor_bytes opad key in

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = Seq.append s5 s4 in

  (* Step 7: apply H to "result of step 6" *)
  Hash.hash s6


#reset-options "--max_fuel 0 --z3rlimit 10"

val hmac:
  key  :bytes{Seq.length key < Hash.max_input_len_8} ->
  data :bytes{Seq.length data + Hash.size_block < Hash.max_input_len_8} ->
  Tot (mac:bytes{Seq.length mac = Hash.size_hash})

#reset-options "--max_fuel 0 --z3rlimit 25"

let hmac key data =

  (* Step 1: make sure the key has the proper length *)
  let okey = wrap_key key in

  (* Step 2-7: call hmac_core *)
  hmac_core okey data


#reset-options "--max_fuel 0 --z3rlimit 25"

let lemma_eq_hmac (key :bytes{Seq.length key = Hash.size_block}) (data :bytes{Seq.length data + Hash.size_block < Hash.max_input_len_8}) :
  Lemma (ensures (
    hmac_core key data
    ==
    Hash.hash (Seq.append (xor_bytes (Seq.create Hash.size_block 0x5cuy) key) (Hash.hash (Seq.append (xor_bytes (Seq.create Hash.size_block 0x36uy) key) data))))) = ()


//
// Test 1
//

let test_key1 = [
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy
]

let test_data1 = [
  0x48uy; 0x69uy; 0x20uy; 0x54uy; 0x68uy; 0x65uy; 0x72uy; 0x65uy
]

let test_expected1 = [
  0x87uy; 0xaauy; 0x7cuy; 0xdeuy; 0xa5uy; 0xefuy; 0x61uy; 0x9duy;
  0x4fuy; 0xf0uy; 0xb4uy; 0x24uy; 0x1auy; 0x1duy; 0x6cuy; 0xb0uy;
  0x23uy; 0x79uy; 0xf4uy; 0xe2uy; 0xceuy; 0x4euy; 0xc2uy; 0x78uy;
  0x7auy; 0xd0uy; 0xb3uy; 0x05uy; 0x45uy; 0xe1uy; 0x7cuy; 0xdeuy;
  0xdauy; 0xa8uy; 0x33uy; 0xb7uy; 0xd6uy; 0xb8uy; 0xa7uy; 0x02uy;
  0x03uy; 0x8buy; 0x27uy; 0x4euy; 0xaeuy; 0xa3uy; 0xf4uy; 0xe4uy;
  0xbeuy; 0x9duy; 0x91uy; 0x4euy; 0xebuy; 0x61uy; 0xf1uy; 0x70uy;
  0x2euy; 0x69uy; 0x6cuy; 0x20uy; 0x3auy; 0x12uy; 0x68uy; 0x54uy
]

//
// Test 2
//

let test_key2 = [
  0x4auy; 0x65uy; 0x66uy; 0x65uy
]

let test_data2 = [
  0x77uy; 0x68uy; 0x61uy; 0x74uy; 0x20uy; 0x64uy; 0x6fuy; 0x20uy;
  0x79uy; 0x61uy; 0x20uy; 0x77uy; 0x61uy; 0x6euy; 0x74uy; 0x20uy;
  0x66uy; 0x6fuy; 0x72uy; 0x20uy; 0x6euy; 0x6fuy; 0x74uy; 0x68uy;
  0x69uy; 0x6euy; 0x67uy; 0x3fuy
]

let test_expected2 = [
  0x16uy; 0x4buy; 0x7auy; 0x7buy; 0xfcuy; 0xf8uy; 0x19uy; 0xe2uy;
  0xe3uy; 0x95uy; 0xfbuy; 0xe7uy; 0x3buy; 0x56uy; 0xe0uy; 0xa3uy;
  0x87uy; 0xbduy; 0x64uy; 0x22uy; 0x2euy; 0x83uy; 0x1fuy; 0xd6uy;
  0x10uy; 0x27uy; 0x0cuy; 0xd7uy; 0xeauy; 0x25uy; 0x05uy; 0x54uy;
  0x97uy; 0x58uy; 0xbfuy; 0x75uy; 0xc0uy; 0x5auy; 0x99uy; 0x4auy;
  0x6duy; 0x03uy; 0x4fuy; 0x65uy; 0xf8uy; 0xf0uy; 0xe6uy; 0xfduy;
  0xcauy; 0xeauy; 0xb1uy; 0xa3uy; 0x4duy; 0x4auy; 0x6buy; 0x4buy;
  0x63uy; 0x6euy; 0x07uy; 0x0auy; 0x38uy; 0xbcuy; 0xe7uy; 0x37uy
]

//
// Test 3
//

let test_key3 = [
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy
]

let test_data3 = [
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy
]

let test_expected3 = [
  0xfauy; 0x73uy; 0xb0uy; 0x08uy; 0x9duy; 0x56uy; 0xa2uy; 0x84uy;
  0xefuy; 0xb0uy; 0xf0uy; 0x75uy; 0x6cuy; 0x89uy; 0x0buy; 0xe9uy;
  0xb1uy; 0xb5uy; 0xdbuy; 0xdduy; 0x8euy; 0xe8uy; 0x1auy; 0x36uy;
  0x55uy; 0xf8uy; 0x3euy; 0x33uy; 0xb2uy; 0x27uy; 0x9duy; 0x39uy;
  0xbfuy; 0x3euy; 0x84uy; 0x82uy; 0x79uy; 0xa7uy; 0x22uy; 0xc8uy;
  0x06uy; 0xb4uy; 0x85uy; 0xa4uy; 0x7euy; 0x67uy; 0xc8uy; 0x07uy;
  0xb9uy; 0x46uy; 0xa3uy; 0x37uy; 0xbeuy; 0xe8uy; 0x94uy; 0x26uy;
  0x74uy; 0x27uy; 0x88uy; 0x59uy; 0xe1uy; 0x32uy; 0x92uy; 0xfbuy
]

//
// Test 4
//

let test_key4 = [
  0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy; 0x08uy;
  0x09uy; 0x0auy; 0x0buy; 0x0cuy; 0x0duy; 0x0euy; 0x0fuy; 0x10uy;
  0x11uy; 0x12uy; 0x13uy; 0x14uy; 0x15uy; 0x16uy; 0x17uy; 0x18uy;
  0x19uy
]

let test_data4 = [
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy
]

let test_expected4 = [
  0xb0uy; 0xbauy; 0x46uy; 0x56uy; 0x37uy; 0x45uy; 0x8cuy; 0x69uy;
  0x90uy; 0xe5uy; 0xa8uy; 0xc5uy; 0xf6uy; 0x1duy; 0x4auy; 0xf7uy;
  0xe5uy; 0x76uy; 0xd9uy; 0x7fuy; 0xf9uy; 0x4buy; 0x87uy; 0x2duy;
  0xe7uy; 0x6fuy; 0x80uy; 0x50uy; 0x36uy; 0x1euy; 0xe3uy; 0xdbuy;
  0xa9uy; 0x1cuy; 0xa5uy; 0xc1uy; 0x1auy; 0xa2uy; 0x5euy; 0xb4uy;
  0xd6uy; 0x79uy; 0x27uy; 0x5cuy; 0xc5uy; 0x78uy; 0x80uy; 0x63uy;
  0xa5uy; 0xf1uy; 0x97uy; 0x41uy; 0x12uy; 0x0cuy; 0x4fuy; 0x2duy;
  0xe2uy; 0xaduy; 0xebuy; 0xebuy; 0x10uy; 0xa2uy; 0x98uy; 0xdduy
]

//
// Test 5
//

let test_key5 = [
  0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy;
  0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy;
  0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy
]

let test_data5 = [
  0x54uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x57uy; 0x69uy; 0x74uy;
  0x68uy; 0x20uy; 0x54uy; 0x72uy; 0x75uy; 0x6euy; 0x63uy; 0x61uy;
  0x74uy; 0x69uy; 0x6fuy; 0x6euy
]

let test_expected5 = [
  0x41uy; 0x5fuy; 0xaduy; 0x62uy; 0x71uy; 0x58uy; 0x0auy; 0x53uy;
  0x1duy; 0x41uy; 0x79uy; 0xbcuy; 0x89uy; 0x1duy; 0x87uy; 0xa6uy
]

//
// Test 6
//

let test_key6 = [
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy
]

let test_data6 = [
  0x54uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x55uy; 0x73uy; 0x69uy;
  0x6euy; 0x67uy; 0x20uy; 0x4cuy; 0x61uy; 0x72uy; 0x67uy; 0x65uy;
  0x72uy; 0x20uy; 0x54uy; 0x68uy; 0x61uy; 0x6euy; 0x20uy; 0x42uy;
  0x6cuy; 0x6fuy; 0x63uy; 0x6buy; 0x2duy; 0x53uy; 0x69uy; 0x7auy;
  0x65uy; 0x20uy; 0x4buy; 0x65uy; 0x79uy; 0x20uy; 0x2duy; 0x20uy;
  0x48uy; 0x61uy; 0x73uy; 0x68uy; 0x20uy; 0x4buy; 0x65uy; 0x79uy;
  0x20uy; 0x46uy; 0x69uy; 0x72uy; 0x73uy; 0x74uy
]

let test_expected6 = [
  0x80uy; 0xb2uy; 0x42uy; 0x63uy; 0xc7uy; 0xc1uy; 0xa3uy; 0xebuy;
  0xb7uy; 0x14uy; 0x93uy; 0xc1uy; 0xdduy; 0x7buy; 0xe8uy; 0xb4uy;
  0x9buy; 0x46uy; 0xd1uy; 0xf4uy; 0x1buy; 0x4auy; 0xeeuy; 0xc1uy;
  0x12uy; 0x1buy; 0x01uy; 0x37uy; 0x83uy; 0xf8uy; 0xf3uy; 0x52uy;
  0x6buy; 0x56uy; 0xd0uy; 0x37uy; 0xe0uy; 0x5fuy; 0x25uy; 0x98uy;
  0xbduy; 0x0fuy; 0xd2uy; 0x21uy; 0x5duy; 0x6auy; 0x1euy; 0x52uy;
  0x95uy; 0xe6uy; 0x4fuy; 0x73uy; 0xf6uy; 0x3fuy; 0x0auy; 0xecuy;
  0x8buy; 0x91uy; 0x5auy; 0x98uy; 0x5duy; 0x78uy; 0x65uy; 0x98uy
]

//
// Test 7
//

let test_key7 = [
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy
]

let test_data7 = [
  0x54uy; 0x68uy; 0x69uy; 0x73uy; 0x20uy; 0x69uy; 0x73uy; 0x20uy;
  0x61uy; 0x20uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x75uy;
  0x73uy; 0x69uy; 0x6euy; 0x67uy; 0x20uy; 0x61uy; 0x20uy; 0x6cuy;
  0x61uy; 0x72uy; 0x67uy; 0x65uy; 0x72uy; 0x20uy; 0x74uy; 0x68uy;
  0x61uy; 0x6euy; 0x20uy; 0x62uy; 0x6cuy; 0x6fuy; 0x63uy; 0x6buy;
  0x2duy; 0x73uy; 0x69uy; 0x7auy; 0x65uy; 0x20uy; 0x6buy; 0x65uy;
  0x79uy; 0x20uy; 0x61uy; 0x6euy; 0x64uy; 0x20uy; 0x61uy; 0x20uy;
  0x6cuy; 0x61uy; 0x72uy; 0x67uy; 0x65uy; 0x72uy; 0x20uy; 0x74uy;
  0x68uy; 0x61uy; 0x6euy; 0x20uy; 0x62uy; 0x6cuy; 0x6fuy; 0x63uy;
  0x6buy; 0x2duy; 0x73uy; 0x69uy; 0x7auy; 0x65uy; 0x20uy; 0x64uy;
  0x61uy; 0x74uy; 0x61uy; 0x2euy; 0x20uy; 0x54uy; 0x68uy; 0x65uy;
  0x20uy; 0x6buy; 0x65uy; 0x79uy; 0x20uy; 0x6euy; 0x65uy; 0x65uy;
  0x64uy; 0x73uy; 0x20uy; 0x74uy; 0x6fuy; 0x20uy; 0x62uy; 0x65uy;
  0x20uy; 0x68uy; 0x61uy; 0x73uy; 0x68uy; 0x65uy; 0x64uy; 0x20uy;
  0x62uy; 0x65uy; 0x66uy; 0x6fuy; 0x72uy; 0x65uy; 0x20uy; 0x62uy;
  0x65uy; 0x69uy; 0x6euy; 0x67uy; 0x20uy; 0x75uy; 0x73uy; 0x65uy;
  0x64uy; 0x20uy; 0x62uy; 0x79uy; 0x20uy; 0x74uy; 0x68uy; 0x65uy;
  0x20uy; 0x48uy; 0x4duy; 0x41uy; 0x43uy; 0x20uy; 0x61uy; 0x6cuy;
  0x67uy; 0x6fuy; 0x72uy; 0x69uy; 0x74uy; 0x68uy; 0x6duy; 0x2euy
]

let test_expected7 = [
  0xe3uy; 0x7buy; 0x6auy; 0x77uy; 0x5duy; 0xc8uy; 0x7duy; 0xbauy;
  0xa4uy; 0xdfuy; 0xa9uy; 0xf9uy; 0x6euy; 0x5euy; 0x3fuy; 0xfduy;
  0xdeuy; 0xbduy; 0x71uy; 0xf8uy; 0x86uy; 0x72uy; 0x89uy; 0x86uy;
  0x5duy; 0xf5uy; 0xa3uy; 0x2duy; 0x20uy; 0xcduy; 0xc9uy; 0x44uy;
  0xb6uy; 0x02uy; 0x2cuy; 0xacuy; 0x3cuy; 0x49uy; 0x82uy; 0xb1uy;
  0x0duy; 0x5euy; 0xebuy; 0x55uy; 0xc3uy; 0xe4uy; 0xdeuy; 0x15uy;
  0x13uy; 0x46uy; 0x76uy; 0xfbuy; 0x6duy; 0xe0uy; 0x44uy; 0x60uy;
  0x65uy; 0xc9uy; 0x74uy; 0x40uy; 0xfauy; 0x8cuy; 0x6auy; 0x58uy
]



//
// Main
//

let test () =
  assert_norm(List.Tot.length test_key1 = 20);
  assert_norm(List.Tot.length test_data1 = 8);
  assert_norm(List.Tot.length test_expected1 = 64);
  assert_norm(List.Tot.length test_key2 = 4);
  assert_norm(List.Tot.length test_data2 = 28);
  assert_norm(List.Tot.length test_expected2 = 64);
  assert_norm(List.Tot.length test_key3 = 20);
  assert_norm(List.Tot.length test_data3 = 50);
  assert_norm(List.Tot.length test_expected3 = 64);
  assert_norm(List.Tot.length test_key4 = 25);
  assert_norm(List.Tot.length test_data4 = 50);
  assert_norm(List.Tot.length test_expected4 = 64);
  assert_norm(List.Tot.length test_key5 = 20);
  assert_norm(List.Tot.length test_data5 = 20);
  assert_norm(List.Tot.length test_expected5 = 16);
  assert_norm(List.Tot.length test_key6 = 131);
  assert_norm(List.Tot.length test_data6 = 54);
  assert_norm(List.Tot.length test_expected6 = 64);
  assert_norm(List.Tot.length test_key7 = 131);
  assert_norm(List.Tot.length test_data7 = 152);
  assert_norm(List.Tot.length test_expected7 = 64);
  let test_key1 = createL test_key1 in
  let test_data1 = createL test_data1 in
  let test_expected1 = createL test_expected1 in
  let test_key2 = createL test_key2 in
  let test_data2 = createL test_data2 in
  let test_expected2 = createL test_expected2 in
  let test_key3 = createL test_key3 in
  let test_data3 = createL test_data3 in
  let test_expected3 = createL test_expected3 in
  let test_key4 = createL test_key4 in
  let test_data4 = createL test_data4 in
  let test_expected4 = createL test_expected4 in
  let test_key5 = createL test_key5 in
  let test_data5 = createL test_data5 in
  let test_expected5 = createL test_expected5 in
  let test_key6 = createL test_key6 in
  let test_data6 = createL test_data6 in
  let test_expected6 = createL test_expected6 in
  let test_key7 = createL test_key7 in
  let test_data7 = createL test_data7 in
  let test_expected7 = createL test_expected7 in

  (hmac test_key1 test_data1 = test_expected1) &&
  (hmac test_key2 test_data2 = test_expected2) &&
  (hmac test_key3 test_data3 = test_expected3) &&
  (hmac test_key4 test_data4 = test_expected4) &&
  (let hmac_truncated5 = Seq.slice (hmac test_key5 test_data5) 0 16 in
  (hmac_truncated5 = test_expected5)) &&
  (hmac test_key6 test_data6 = test_expected6) &&
  (hmac test_key7 test_data7 = test_expected7)
