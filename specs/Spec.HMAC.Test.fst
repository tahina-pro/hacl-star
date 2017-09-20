module Spec.HMAC.Test

open FStar.Seq
module Hash = Spec.SHA2
module HMAC = Spec.HMAC


//
// Test 1
//

let test1_key = [
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy
]

let test1_data = [
  0x48uy; 0x69uy; 0x20uy; 0x54uy; 0x68uy; 0x65uy; 0x72uy; 0x65uy
]

let test1_expected224 = [
  0x89uy; 0x6fuy; 0xb1uy; 0x12uy; 0x8auy; 0xbbuy; 0xdfuy; 0x19uy;
  0x68uy; 0x32uy; 0x10uy; 0x7cuy; 0xd4uy; 0x9duy; 0xf3uy; 0x3fuy;
  0x47uy; 0xb4uy; 0xb1uy; 0x16uy; 0x99uy; 0x12uy; 0xbauy; 0x4fuy;
  0x53uy; 0x68uy; 0x4buy; 0x22uy
]

let test1_expected256 = [
  0xb0uy; 0x34uy; 0x4cuy; 0x61uy; 0xd8uy; 0xdbuy; 0x38uy; 0x53uy;
  0x5cuy; 0xa8uy; 0xafuy; 0xceuy; 0xafuy; 0x0buy; 0xf1uy; 0x2buy;
  0x88uy; 0x1duy; 0xc2uy; 0x00uy; 0xc9uy; 0x83uy; 0x3duy; 0xa7uy;
  0x26uy; 0xe9uy; 0x37uy; 0x6cuy; 0x2euy; 0x32uy; 0xcfuy; 0xf7uy
]

let test1_expected384 = [
  0xafuy; 0xd0uy; 0x39uy; 0x44uy; 0xd8uy; 0x48uy; 0x95uy; 0x62uy;
  0x6buy; 0x08uy; 0x25uy; 0xf4uy; 0xabuy; 0x46uy; 0x90uy; 0x7fuy;
  0x15uy; 0xf9uy; 0xdauy; 0xdbuy; 0xe4uy; 0x10uy; 0x1euy; 0xc6uy;
  0x82uy; 0xaauy; 0x03uy; 0x4cuy; 0x7cuy; 0xebuy; 0xc5uy; 0x9cuy;
  0xfauy; 0xeauy; 0x9euy; 0xa9uy; 0x07uy; 0x6euy; 0xdeuy; 0x7fuy;
  0x4auy; 0xf1uy; 0x52uy; 0xe8uy; 0xb2uy; 0xfauy; 0x9cuy; 0xb6uy
]

let test1_expected512 = [
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

let test2_key = [
  0x4auy; 0x65uy; 0x66uy; 0x65uy
]

let test2_data = [
  0x77uy; 0x68uy; 0x61uy; 0x74uy; 0x20uy; 0x64uy; 0x6fuy; 0x20uy;
  0x79uy; 0x61uy; 0x20uy; 0x77uy; 0x61uy; 0x6euy; 0x74uy; 0x20uy;
  0x66uy; 0x6fuy; 0x72uy; 0x20uy; 0x6euy; 0x6fuy; 0x74uy; 0x68uy;
  0x69uy; 0x6euy; 0x67uy; 0x3fuy
]

let test2_expected224 = [
  0xa3uy; 0x0euy; 0x01uy; 0x09uy; 0x8buy; 0xc6uy; 0xdbuy; 0xbfuy;
  0x45uy; 0x69uy; 0x0fuy; 0x3auy; 0x7euy; 0x9euy; 0x6duy; 0x0fuy;
  0x8buy; 0xbeuy; 0xa2uy; 0xa3uy; 0x9euy; 0x61uy; 0x48uy; 0x00uy;
  0x8fuy; 0xd0uy; 0x5euy; 0x44uy
]

let test2_expected256 = [
  0x5buy; 0xdcuy; 0xc1uy; 0x46uy; 0xbfuy; 0x60uy; 0x75uy; 0x4euy;
  0x6auy; 0x04uy; 0x24uy; 0x26uy; 0x08uy; 0x95uy; 0x75uy; 0xc7uy;
  0x5auy; 0x00uy; 0x3fuy; 0x08uy; 0x9duy; 0x27uy; 0x39uy; 0x83uy;
  0x9duy; 0xecuy; 0x58uy; 0xb9uy; 0x64uy; 0xecuy; 0x38uy; 0x43uy
]

let test2_expected384 = [
  0xafuy; 0x45uy; 0xd2uy; 0xe3uy; 0x76uy; 0x48uy; 0x40uy; 0x31uy;
  0x61uy; 0x7fuy; 0x78uy; 0xd2uy; 0xb5uy; 0x8auy; 0x6buy; 0x1buy;
  0x9cuy; 0x7euy; 0xf4uy; 0x64uy; 0xf5uy; 0xa0uy; 0x1buy; 0x47uy;
  0xe4uy; 0x2euy; 0xc3uy; 0x73uy; 0x63uy; 0x22uy; 0x44uy; 0x5euy;
  0x8euy; 0x22uy; 0x40uy; 0xcauy; 0x5euy; 0x69uy; 0xe2uy; 0xc7uy;
  0x8buy; 0x32uy; 0x39uy; 0xecuy; 0xfauy; 0xb2uy; 0x16uy; 0x49uy
]

let test2_expected512 = [
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

let test3_key = [
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
  0xaauy; 0xaauy; 0xaauy; 0xaauy
]

let test3_data = [
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
  0xdduy; 0xdduy
]

let test3_expected224 = [
  0x7fuy; 0xb3uy; 0xcbuy; 0x35uy; 0x88uy; 0xc6uy; 0xc1uy; 0xf6uy;
  0xffuy; 0xa9uy; 0x69uy; 0x4duy; 0x7duy; 0x6auy; 0xd2uy; 0x64uy;
  0x93uy; 0x65uy; 0xb0uy; 0xc1uy; 0xf6uy; 0x5duy; 0x69uy; 0xd1uy;
  0xecuy; 0x83uy; 0x33uy; 0xeauy
]

let test3_expected256 = [
  0x77uy; 0x3euy; 0xa9uy; 0x1euy; 0x36uy; 0x80uy; 0x0euy; 0x46uy;
  0x85uy; 0x4duy; 0xb8uy; 0xebuy; 0xd0uy; 0x91uy; 0x81uy; 0xa7uy;
  0x29uy; 0x59uy; 0x09uy; 0x8buy; 0x3euy; 0xf8uy; 0xc1uy; 0x22uy;
  0xd9uy; 0x63uy; 0x55uy; 0x14uy; 0xceuy; 0xd5uy; 0x65uy; 0xfeuy
]

let test3_expected384 = [
  0x88uy; 0x06uy; 0x26uy; 0x08uy; 0xd3uy; 0xe6uy; 0xaduy; 0x8auy;
  0x0auy; 0xa2uy; 0xacuy; 0xe0uy; 0x14uy; 0xc8uy; 0xa8uy; 0x6fuy;
  0x0auy; 0xa6uy; 0x35uy; 0xd9uy; 0x47uy; 0xacuy; 0x9fuy; 0xebuy;
  0xe8uy; 0x3euy; 0xf4uy; 0xe5uy; 0x59uy; 0x66uy; 0x14uy; 0x4buy;
  0x2auy; 0x5auy; 0xb3uy; 0x9duy; 0xc1uy; 0x38uy; 0x14uy; 0xb9uy;
  0x4euy; 0x3auy; 0xb6uy; 0xe1uy; 0x01uy; 0xa3uy; 0x4fuy; 0x27uy
]

let test3_expected512 = [
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

let test4_key = [
  0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy; 0x08uy;
  0x09uy; 0x0auy; 0x0buy; 0x0cuy; 0x0duy; 0x0euy; 0x0fuy; 0x10uy;
  0x11uy; 0x12uy; 0x13uy; 0x14uy; 0x15uy; 0x16uy; 0x17uy; 0x18uy;
  0x19uy
]

let test4_data = [
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
  0xcduy; 0xcduy
]

let test4_expected224 = [
  0x6cuy; 0x11uy; 0x50uy; 0x68uy; 0x74uy; 0x01uy; 0x3cuy; 0xacuy;
  0x6auy; 0x2auy; 0xbcuy; 0x1buy; 0xb3uy; 0x82uy; 0x62uy; 0x7cuy;
  0xecuy; 0x6auy; 0x90uy; 0xd8uy; 0x6euy; 0xfcuy; 0x01uy; 0x2duy;
  0xe7uy; 0xafuy; 0xecuy; 0x5auy

]

let test4_expected256 = [
  0x82uy; 0x55uy; 0x8auy; 0x38uy; 0x9auy; 0x44uy; 0x3cuy; 0x0euy;
  0xa4uy; 0xccuy; 0x81uy; 0x98uy; 0x99uy; 0xf2uy; 0x08uy; 0x3auy;
  0x85uy; 0xf0uy; 0xfauy; 0xa3uy; 0xe5uy; 0x78uy; 0xf8uy; 0x07uy;
  0x7auy; 0x2euy; 0x3fuy; 0xf4uy; 0x67uy; 0x29uy; 0x66uy; 0x5buy
]

let test4_expected384 = [
  0x3euy; 0x8auy; 0x69uy; 0xb7uy; 0x78uy; 0x3cuy; 0x25uy; 0x85uy;
  0x19uy; 0x33uy; 0xabuy; 0x62uy; 0x90uy; 0xafuy; 0x6cuy; 0xa7uy;
  0x7auy; 0x99uy; 0x81uy; 0x48uy; 0x08uy; 0x50uy; 0x00uy; 0x9cuy;
  0xc5uy; 0x57uy; 0x7cuy; 0x6euy; 0x1fuy; 0x57uy; 0x3buy; 0x4euy;
  0x68uy; 0x01uy; 0xdduy; 0x23uy; 0xc4uy; 0xa7uy; 0xd6uy; 0x79uy;
  0xccuy; 0xf8uy; 0xa3uy; 0x86uy; 0xc6uy; 0x74uy; 0xcfuy; 0xfbuy
]

let test4_expected512 = [
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

let test5_key = [
  0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy;
  0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy;
  0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy
]

let test5_data = [
  0x54uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x57uy; 0x69uy; 0x74uy;
  0x68uy; 0x20uy; 0x54uy; 0x72uy; 0x75uy; 0x6euy; 0x63uy; 0x61uy;
]

let test5_expected224 = [
  0x0euy; 0x2auy; 0xeauy; 0x68uy; 0xa9uy; 0x0cuy; 0x8duy; 0x37uy;
  0xc9uy; 0x88uy; 0xbcuy; 0xdbuy; 0x9fuy; 0xcauy; 0x6fuy; 0xa8uy;
]

let test5_expected256 = [
  0xa3uy; 0xb6uy; 0x16uy; 0x74uy; 0x73uy; 0x10uy; 0x0euy; 0xe0uy;
  0x6euy; 0x0cuy; 0x79uy; 0x6cuy; 0x29uy; 0x55uy; 0x55uy; 0x2buy
]

let test5_expected384 = [
  0x3auy; 0xbfuy; 0x34uy; 0xc3uy; 0x50uy; 0x3buy; 0x2auy; 0x23uy;
  0xa4uy; 0x6euy; 0xfcuy; 0x61uy; 0x9buy; 0xaeuy; 0xf8uy; 0x97uy
]

let test5_expected512 = [
  0x41uy; 0x5fuy; 0xaduy; 0x62uy; 0x71uy; 0x58uy; 0x0auy; 0x53uy;
  0x1duy; 0x41uy; 0x79uy; 0xbcuy; 0x89uy; 0x1duy; 0x87uy; 0xa6uy
]

//
// Test 6
//

let test6_key = [
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

let test6_data = [
  0x54uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x55uy; 0x73uy; 0x69uy;
  0x6euy; 0x67uy; 0x20uy; 0x4cuy; 0x61uy; 0x72uy; 0x67uy; 0x65uy;
  0x72uy; 0x20uy; 0x54uy; 0x68uy; 0x61uy; 0x6euy; 0x20uy; 0x42uy;
  0x6cuy; 0x6fuy; 0x63uy; 0x6buy; 0x2duy; 0x53uy; 0x69uy; 0x7auy;
  0x65uy; 0x20uy; 0x4buy; 0x65uy; 0x79uy; 0x20uy; 0x2duy; 0x20uy;
  0x48uy; 0x61uy; 0x73uy; 0x68uy; 0x20uy; 0x4buy; 0x65uy; 0x79uy;
  0x20uy; 0x46uy; 0x69uy; 0x72uy; 0x73uy; 0x74uy
]

let test6_expected224 = [
  0x95uy; 0xe9uy; 0xa0uy; 0xdbuy; 0x96uy; 0x20uy; 0x95uy; 0xaduy;
  0xaeuy; 0xbeuy; 0x9buy; 0x2duy; 0x6fuy; 0x0duy; 0xbcuy; 0xe2uy;
  0xd4uy; 0x99uy; 0xf1uy; 0x12uy; 0xf2uy; 0xd2uy; 0xb7uy; 0x27uy;
  0x3fuy; 0xa6uy; 0x87uy; 0x0euy
]

let test6_expected256 = [
  0x60uy; 0xe4uy; 0x31uy; 0x59uy; 0x1euy; 0xe0uy; 0xb6uy; 0x7fuy;
  0x0duy; 0x8auy; 0x26uy; 0xaauy; 0xcbuy; 0xf5uy; 0xb7uy; 0x7fuy;
  0x8euy; 0x0buy; 0xc6uy; 0x21uy; 0x37uy; 0x28uy; 0xc5uy; 0x14uy;
  0x05uy; 0x46uy; 0x04uy; 0x0fuy; 0x0euy; 0xe3uy; 0x7fuy; 0x54uy
]

let test6_expected384 = [
  0x4euy; 0xceuy; 0x08uy; 0x44uy; 0x85uy; 0x81uy; 0x3euy; 0x90uy;
  0x88uy; 0xd2uy; 0xc6uy; 0x3auy; 0x04uy; 0x1buy; 0xc5uy; 0xb4uy;
  0x4fuy; 0x9euy; 0xf1uy; 0x01uy; 0x2auy; 0x2buy; 0x58uy; 0x8fuy;
  0x3cuy; 0xd1uy; 0x1fuy; 0x05uy; 0x03uy; 0x3auy; 0xc4uy; 0xc6uy;
  0x0cuy; 0x2euy; 0xf6uy; 0xabuy; 0x40uy; 0x30uy; 0xfeuy; 0x82uy;
  0x96uy; 0x24uy; 0x8duy; 0xf1uy; 0x63uy; 0xf4uy; 0x49uy; 0x52uy
]

let test6_expected512 = [
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

let test7_key = [
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

let test7_data = [
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

let test7_expected224 = [
  0x3auy; 0x85uy; 0x41uy; 0x66uy; 0xacuy; 0x5duy; 0x9fuy; 0x02uy;
  0x3fuy; 0x54uy; 0xd5uy; 0x17uy; 0xd0uy; 0xb3uy; 0x9duy; 0xbduy;
  0x94uy; 0x67uy; 0x70uy; 0xdbuy; 0x9cuy; 0x2buy; 0x95uy; 0xc9uy;
  0xf6uy; 0xf5uy; 0x65uy; 0xd1uy
]

let test7_expected256 = [
  0x9buy; 0x09uy; 0xffuy; 0xa7uy; 0x1buy; 0x94uy; 0x2fuy; 0xcbuy;
  0x27uy; 0x63uy; 0x5fuy; 0xbcuy; 0xd5uy; 0xb0uy; 0xe9uy; 0x44uy;
  0xbfuy; 0xdcuy; 0x63uy; 0x64uy; 0x4fuy; 0x07uy; 0x13uy; 0x93uy;
  0x8auy; 0x7fuy; 0x51uy; 0x53uy; 0x5cuy; 0x3auy; 0x35uy; 0xe2uy
]

let test7_expected384 = [
  0x66uy; 0x17uy; 0x17uy; 0x8euy; 0x94uy; 0x1fuy; 0x02uy; 0x0duy;
  0x35uy; 0x1euy; 0x2fuy; 0x25uy; 0x4euy; 0x8fuy; 0xd3uy; 0x2cuy;
  0x60uy; 0x24uy; 0x20uy; 0xfeuy; 0xb0uy; 0xb8uy; 0xfbuy; 0x9auy;
  0xdcuy; 0xceuy; 0xbbuy; 0x82uy; 0x46uy; 0x1euy; 0x99uy; 0xc5uy;
  0xa6uy; 0x78uy; 0xccuy; 0x31uy; 0xe7uy; 0x99uy; 0x17uy; 0x6duy;
  0x38uy; 0x60uy; 0xe6uy; 0x11uy; 0x0cuy; 0x46uy; 0x52uy; 0x3euy
]

let test7_expected512 = [
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
  (HMAC.hmac Hash.SHA2_224 (createL test1_key) (createL test1_data) = createL test1_expected224) &&
  (HMAC.hmac Hash.SHA2_224 (createL test2_key) (createL test2_data) = createL test2_expected224) &&
  (HMAC.hmac Hash.SHA2_224 (createL test3_key) (createL test3_data) = createL test3_expected224) &&
  (HMAC.hmac Hash.SHA2_224 (createL test4_key) (createL test4_data) = createL test4_expected224) &&
//  (HMAC.hmac Hash.SHA2_224 (createL test5_key) (createL test5_data) = createL test5_expected224) &&
  (HMAC.hmac Hash.SHA2_224 (createL test6_key) (createL test6_data) = createL test6_expected224) &&
  (HMAC.hmac Hash.SHA2_224 (createL test7_key) (createL test7_data) = createL test7_expected224) &&

  (HMAC.hmac Hash.SHA2_256 (createL test1_key) (createL test1_data) = createL test1_expected256) &&
  (HMAC.hmac Hash.SHA2_256 (createL test2_key) (createL test2_data) = createL test2_expected256) &&
  (HMAC.hmac Hash.SHA2_256 (createL test3_key) (createL test3_data) = createL test3_expected256) &&
  (HMAC.hmac Hash.SHA2_256 (createL test4_key) (createL test4_data) = createL test4_expected256) &&
//  (HMAC.hmac Hash.SHA2_256 (createL test5_key) (createL test5_data) = createL test5_expected256) &&
  (HMAC.hmac Hash.SHA2_256 (createL test6_key) (createL test6_data) = createL test6_expected256) &&
  (HMAC.hmac Hash.SHA2_256 (createL test7_key) (createL test7_data) = createL test7_expected256) &&

  (HMAC.hmac Hash.SHA2_384 (createL test1_key) (createL test1_data) = createL test1_expected384) &&
  (HMAC.hmac Hash.SHA2_384 (createL test2_key) (createL test2_data) = createL test2_expected384) &&
  (HMAC.hmac Hash.SHA2_384 (createL test3_key) (createL test3_data) = createL test3_expected384) &&
  (HMAC.hmac Hash.SHA2_384 (createL test4_key) (createL test4_data) = createL test4_expected384) &&
//  (HMAC.hmac Hash.SHA2_384 (createL test5_key) (createL test5_data) = createL test5_expected384) &&
  (HMAC.hmac Hash.SHA2_384 (createL test6_key) (createL test6_data) = createL test6_expected384) &&
  (HMAC.hmac Hash.SHA2_384 (createL test7_key) (createL test7_data) = createL test7_expected384) &&

  (HMAC.hmac Hash.SHA2_512 (createL test1_key) (createL test1_data) = createL test1_expected512) &&
  (HMAC.hmac Hash.SHA2_512 (createL test2_key) (createL test2_data) = createL test2_expected512) &&
  (HMAC.hmac Hash.SHA2_512 (createL test3_key) (createL test3_data) = createL test3_expected512) &&
  (HMAC.hmac Hash.SHA2_512 (createL test4_key) (createL test4_data) = createL test4_expected512) &&
//  (HMAC.hmac Hash.SHA2_512 (createL test5_key) (createL test5_data) = createL test5_expected512) &&
  (HMAC.hmac Hash.SHA2_512 (createL test6_key) (createL test6_data) = createL test6_expected512) &&
  (HMAC.hmac Hash.SHA2_512 (createL test7_key) (createL test7_data) = createL test7_expected512)
