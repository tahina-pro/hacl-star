module Hacl.Hash.SHA2

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
// open Hacl.Cast
// open Hacl.UInt8
// open Hacl.UInt32
open FStar.UInt32
open C.Loops

open Hacl.Spec.Endianness
open Hacl.Hash.Lib.Create
open Hacl.Hash.Lib.LoadStore
open Spec.SHA2


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module H32 = Hacl.UInt32
module H64 = Hacl.UInt64
module H128 = Hacl.UInt128

module HS = FStar.HyperStack
module Cast = Hacl.Cast

module Spec = Spec.SHA2
// module Lemmas = Hacl.Hash.SHA2_512.Lemmas


(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let uint8_ht  = Hacl.UInt8.t
private let uint32_ht = Hacl.UInt32.t
private let uint64_ht = Hacl.UInt64.t
private let uint128_ht = Hacl.UInt128.t

private let uint32_p = Buffer.buffer uint32_ht
private let uint64_p = Buffer.buffer uint64_ht
private let uint8_p  = Buffer.buffer uint8_ht


(* Definitions of aliases for functions *)
inline_for_extraction let  u8_to_h8 = Cast.uint8_to_sint8
inline_for_extraction let  u32_to_h32 = Cast.uint32_to_sint32
inline_for_extraction let  u32_to_u64 = FStar.Int.Cast.uint32_to_uint64
inline_for_extraction let  u32_to_h64 = Cast.uint32_to_sint64
inline_for_extraction let  h32_to_h8  = Cast.sint32_to_sint8
inline_for_extraction let  h32_to_h64 = Cast.sint32_to_sint64
inline_for_extraction let  u32_to_h128 = Cast.uint32_to_sint128
inline_for_extraction let  u64_to_u32 = FStar.Int.Cast.uint64_to_uint32
inline_for_extraction let  u64_to_h64 = Cast.uint64_to_sint64
inline_for_extraction let  u64_to_h128 = Cast.uint64_to_sint128
inline_for_extraction let  h64_to_h128 = Cast.sint64_to_sint128


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 25"

//
// SHA2
//

(* Definition of a word depending on the algorithm *)
let word = Spec.word

let word_v: a:hash_alg -> Tot (word a -> Tot nat) = function
  | SHA2_224 | SHA2_256 -> UInt32.v
  | SHA2_384 | SHA2_512 -> UInt64.v


(* List the Hash algorithms *)
type hash_alg = Spec.SHA2.hash_alg

(* Defines the size of the word for each algorithm *)
inline_for_extraction
let size_word: a:hash_alg -> Tot (z:UInt32.t{v z = Spec.size_word a}) = function
  | SHA2_224 | SHA2_256 -> 4ul
  | SHA2_384 | SHA2_512 -> 8ul

(* Number of words for intermediate hash *)
let size_hash_w : c:UInt32.t{v c = Spec.size_hash_w} = 8ul

(* Number of words for final hash *)
inline_for_extraction
let size_hash_final_w: a:hash_alg -> Tot (z:UInt32.t{v z = Spec.size_hash_final_w a}) = function
  | SHA2_224 -> 7ul
  | SHA2_256 -> 8ul
  | SHA2_384 -> 6ul
  | SHA2_512 -> 8ul

(* Define the final hash length in bytes *)
let size_hash a : c:UInt32.t{v c = Spec.size_hash a} = size_word a *^ size_hash_final_w a

(* Number of words for a block size *)
let size_block_w : c:UInt32.t{v c = Spec.size_block_w} = 16ul

(* Define the size block in bytes *)
let size_block a : c:UInt32.t{v c = Spec.size_block a} = size_word a *^ size_block_w

(* Define the length of the constants *)
inline_for_extraction
let size_k_w: a:hash_alg -> Tot (z:UInt32.t{v z = Spec.size_k_w a}) = function
  | SHA2_224 | SHA2_256 -> 64ul
  | SHA2_384 | SHA2_512 -> 80ul

(* Define the length of scheduling block *)
let size_ws_w = size_k_w

(* Define the length of the encoded lenght in the padding *)
inline_for_extraction
let size_len_8: a:hash_alg -> Tot (z:UInt32.t{v z = Spec.size_len_8 a}) = function
  | SHA2_224 | SHA2_256 -> 8ul
  | SHA2_384 | SHA2_512 -> 16ul

let size_len_ul_8 = Spec.size_len_ul_8

(* Definition of structures in memory *)
let hash_w  (a:hash_alg) = m:Buffer.buffer (word a){length m = Spec.size_hash_w}
let k_w     (a:hash_alg) = m:Buffer.buffer (word a){length m = Spec.size_k_w a}
let ws_w    (a:hash_alg) = m:Buffer.buffer (word a){length m = Spec.size_ws_w a}
let block_w (a:hash_alg) = m:Buffer.buffer (word a){length m = Spec.size_block_w}
let block   (a:hash_alg) = m:Buffer.buffer (word a){length m = Spec.size_word a * Spec.size_block_w}

///////////////////////////////

// Corespondance variables
let size_whash_w = size_hash_w

///////////////////////////////

(* Define the space taken by the counter in the state *)
let size_count_w = 1ul

(* Sizes of objects in the state *)
inline_for_extraction let size_state a = size_k_w a +^ size_ws_w a +^ size_whash_w +^ size_count_w
let state (a:hash_alg) = m:Buffer.buffer (word a){length m = word_v a (size_state a)}

(* Positions of objects in the state *)
inline_for_extraction let pos_k_w = 0ul
inline_for_extraction let pos_ws_w (a:hash_alg) = size_k_w a
inline_for_extraction let pos_whash_w (a:hash_alg) = size_k_w a +^ size_ws_w a
inline_for_extraction let pos_count_w (a:hash_alg) = size_k_w a +^ size_ws_w a +^ size_whash_w

(* Definition of the SHA2 word functions *)
inline_for_extraction val _Ch: a:hash_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
let _Ch a x y z = Spec._Ch a x y z

inline_for_extraction val _Maj: a:hash_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
let _Maj a x y z = Spec._Maj a x y z

inline_for_extraction val _Sigma0: a:hash_alg -> x:(word a) -> Tot (word a)
let _Sigma0 a x = Spec._Sigma0 a x

inline_for_extraction val _Sigma1: a:hash_alg -> x:(word a) -> Tot (word a)
let _Sigma1 a x = Spec._Sigma1 a x

inline_for_extraction val _sigma0: a:hash_alg -> x:(word a) -> Tot (word a)
let _sigma0 a x = Spec._sigma0 a x

inline_for_extraction val _sigma1: a:hash_alg -> x:(word a) -> Tot (word a)
let _sigma1 a x = Spec._sigma1 a x


#reset-options " --z3refresh --max_fuel 0 --z3rlimit 25"

(* Define a Ghost function to reveal the HaCl bytes as normal bytes *)
let buffer_reveal : (a:hash_alg) -> GTot (Seq.seq (word a) -> GTot (Seq.seq (word a))) = function
  | SHA2_224 | SHA2_256 -> Hacl.Spec.Endianness.reveal_h32s
  | SHA2_384 | SHA2_512 -> Hacl.Spec.Endianness.reveal_h64s


(* Define a type and function to update SHA2 constants *)
let constants_k_update_t (a:hash_alg) =
  match a with
  | SHA2_224 | SHA2_256 -> update_32bit_64_t
  | SHA2_384 | SHA2_512 -> update_64bit_80_t

let constants_k_update : (a:hash_alg) -> constants_k_update_t a = function
  | SHA2_224 | SHA2_256 -> update_32bit_64
  | SHA2_384 | SHA2_512 -> update_64bit_80

(* Define a type and function to update SHA2 constants *)
let constants_h_update_t (a:hash_alg) =
  match a with
  | SHA2_224 | SHA2_256 -> update_32bit_8_t
  | SHA2_384 | SHA2_512 -> update_64bit_8_t

let constants_h_update : (a:hash_alg) -> constants_h_update_t a = function
  | SHA2_224 | SHA2_256 -> update_32bit_8
  | SHA2_384 | SHA2_512 -> update_64bit_8


let constants_k_init_224_256 k =
  update_32bit_64 k
  0x428a2f98ul 0x71374491ul 0xb5c0fbcful 0xe9b5dba5ul
  0x3956c25bul 0x59f111f1ul 0x923f82a4ul 0xab1c5ed5ul
  0xd807aa98ul 0x12835b01ul 0x243185beul 0x550c7dc3ul
  0x72be5d74ul 0x80deb1feul 0x9bdc06a7ul 0xc19bf174ul
  0xe49b69c1ul 0xefbe4786ul 0x0fc19dc6ul 0x240ca1ccul
  0x2de92c6ful 0x4a7484aaul 0x5cb0a9dcul 0x76f988daul
  0x983e5152ul 0xa831c66dul 0xb00327c8ul 0xbf597fc7ul
  0xc6e00bf3ul 0xd5a79147ul 0x06ca6351ul 0x14292967ul
  0x27b70a85ul 0x2e1b2138ul 0x4d2c6dfcul 0x53380d13ul
  0x650a7354ul 0x766a0abbul 0x81c2c92eul 0x92722c85ul
  0xa2bfe8a1ul 0xa81a664bul 0xc24b8b70ul 0xc76c51a3ul
  0xd192e819ul 0xd6990624ul 0xf40e3585ul 0x106aa070ul
  0x19a4c116ul 0x1e376c08ul 0x2748774cul 0x34b0bcb5ul
  0x391c0cb3ul 0x4ed8aa4aul 0x5b9cca4ful 0x682e6ff3ul
  0x748f82eeul 0x78a5636ful 0x84c87814ul 0x8cc70208ul
  0x90befffaul 0xa4506cebul 0xbef9a3f7ul 0xc67178f2ul

let constants_k_init_384_512 k =
  update_64bit_80 k
  0x428a2f98d728ae22uL 0x7137449123ef65cduL 0xb5c0fbcfec4d3b2fuL 0xe9b5dba58189dbbcuL
  0x3956c25bf348b538uL 0x59f111f1b605d019uL 0x923f82a4af194f9buL 0xab1c5ed5da6d8118uL
  0xd807aa98a3030242uL 0x12835b0145706fbeuL 0x243185be4ee4b28cuL 0x550c7dc3d5ffb4e2uL
  0x72be5d74f27b896fuL 0x80deb1fe3b1696b1uL 0x9bdc06a725c71235uL 0xc19bf174cf692694uL
  0xe49b69c19ef14ad2uL 0xefbe4786384f25e3uL 0x0fc19dc68b8cd5b5uL 0x240ca1cc77ac9c65uL
  0x2de92c6f592b0275uL 0x4a7484aa6ea6e483uL 0x5cb0a9dcbd41fbd4uL 0x76f988da831153b5uL
  0x983e5152ee66dfabuL 0xa831c66d2db43210uL 0xb00327c898fb213fuL 0xbf597fc7beef0ee4uL
  0xc6e00bf33da88fc2uL 0xd5a79147930aa725uL 0x06ca6351e003826fuL 0x142929670a0e6e70uL
  0x27b70a8546d22ffcuL 0x2e1b21385c26c926uL 0x4d2c6dfc5ac42aeduL 0x53380d139d95b3dfuL
  0x650a73548baf63deuL 0x766a0abb3c77b2a8uL 0x81c2c92e47edaee6uL 0x92722c851482353buL
  0xa2bfe8a14cf10364uL 0xa81a664bbc423001uL 0xc24b8b70d0f89791uL 0xc76c51a30654be30uL
  0xd192e819d6ef5218uL 0xd69906245565a910uL 0xf40e35855771202auL 0x106aa07032bbd1b8uL
  0x19a4c116b8d2d0c8uL 0x1e376c085141ab53uL 0x2748774cdf8eeb99uL 0x34b0bcb5e19b48a8uL
  0x391c0cb3c5c95a63uL 0x4ed8aa4ae3418acbuL 0x5b9cca4f7763e373uL 0x682e6ff3d6b2b8a3uL
  0x748f82ee5defb2fcuL 0x78a5636f43172f60uL 0x84c87814a1f0ab72uL 0x8cc702081a6439ecuL
  0x90befffa23631e28uL 0xa4506cebde82bde9uL 0xbef9a3f7b2c67915uL 0xc67178f2e372532buL
  0xca273eceea26619cuL 0xd186b8c721c0c207uL 0xeada7dd6cde0eb1euL 0xf57d4f7fee6ed178uL
  0x06f067aa72176fbauL 0x0a637dc5a2c898a6uL 0x113f9804bef90daeuL 0x1b710b35131c471buL
  0x28db77f523047d84uL 0x32caab7b40c72493uL 0x3c9ebe0a15c9bebcuL 0x431d67c49c100d4cuL
  0x4cc5d4becb3e42b6uL 0x597f299cfc657e2auL 0x5fcb6fab3ad6faecuL 0x6c44198c4a475817uL


let constants_h_init_224 k =
  update_32bit_8 k
  0xc1059ed8ul 0x367cd507ul 0x3070dd17ul 0xf70e5939ul
  0xffc00b31ul 0x68581511ul 0x64f98fa7ul 0xbefa4fa4ul

let constants_h_init_256 k =
  update_32bit_8 k
  0x6a09e667ul 0xbb67ae85ul 0x3c6ef372ul 0xa54ff53aul
  0x510e527ful 0x9b05688cul 0x1f83d9abul 0x5be0cd19ul

let constants_h_init_384 k =
  update_64bit_8 k
  0xcbbb9d5dc1059ed8uL 0x629a292a367cd507uL 0x9159015a3070dd17uL 0x152fecd8f70e5939uL
  0x67332667ffc00b31uL 0x8eb44a8768581511uL 0xdb0c2e0d64f98fa7uL 0x47b5481dbefa4fa4uL

let constants_h_init_512 k =
  update_64bit_8 k
  0x6a09e667f3bcc908uL 0xbb67ae8584caa73buL 0x3c6ef372fe94f82buL 0xa54ff53a5f1d36f1uL
  0x510e527fade682d1uL 0x9b05688c2b3e6c1fuL 0x1f83d9abfb41bd6buL 0x5be0cd19137e2179uL


let constants_k_init_t =
  a:hash_alg ->
  k:k_w a ->
  Stack unit
    (requires (fun h -> live h k))
    (ensures (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1
             /\ (buffer_reveal a (as_seq h1 k) == Spec.h0 a)))
val constants_k_init : constants_k_init_t
let constants_k_init : (a:hash_alg) -> constants_k_update_t a = function
  | SHA2_224 | SHA2_256 -> constants_k_init_224_256
  | SHA2_384 | SHA2_512 -> constants_k_init_384_512


let constants_h_init_t =
  a:hash_alg ->
  hash:hash_w a ->
  Stack unit
    (requires (fun h -> live h hash))
    (ensures (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1
             /\ (buffer_reveal a (as_seq h1 hash) == Spec.h0 a)))
val constants_h_init : constants_h_init_t
let constants_h_init : (a:hash_alg) -> constants_h_update_t a = function
  | SHA2_224 -> constants_h_init_224
  | SHA2_256 -> constants_h_init_256
  | SHA2_384 -> constants_h_init_384
  | SHA2_512 -> constants_h_init_512


[@ "substitute"]
private
val ws_part_1_core:
  a:hash_alg ->
  ws_w:ws_w a ->
  block_w:block_w a{disjoint ws_w block_w} ->
  i:UInt32.t{UInt32.v i < 16} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w
                  /\ (let seq_ws = buffer_reveal a (as_seq h ws_w) in
                  let seq_block = buffer_reveal a (as_seq h block_w) in
                  (forall (j:nat). {:pattern (Seq.index seq_ws j)} j < UInt32.v i ==> Seq.index seq_ws j == Spec.ws a seq_block j))))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1 /\
                  as_seq h1 block_w == as_seq h0 block_w
                  /\ (let w = buffer_reveal a (as_seq h1 ws_w) in
                  let b = buffer_reveal a (as_seq h0 block_w) in
                  (forall (j:nat). {:pattern (Seq.index w j)} j < UInt32.v i+1 ==> Seq.index w j == Spec.ws a b j))))

[@ "substitute"]
let ws_part_1_core a ws_w block_w t =
  (**) let h0 = ST.get() in
  (**) let h = ST.get() in
  ws_w.(t) <- block_w.(t);
  (**) let h1 = ST.get() in
  (**) let h' = ST.get() in
  (**) no_upd_lemma_1 h0 h1 ws_w block_w;
//  (**) Lemmas.lemma_spec_ws_def (buffer_reveal a (as_seq h block_w)) (UInt32.v t);
  (**) assert(Seq.index (buffer_reveal a (as_seq h1 ws_w)) (UInt32.v t) == Seq.index (reveal_h64s(as_seq h block_w)) (UInt32.v t))


[@"substitute"]
private val ws_part_1:
  a:hash_alg ->
  ws_w:ws_w a ->
  block_w:block_w a{disjoint ws_w block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = buffer_reveal a (as_seq h1 ws_w) in
                  let b = buffer_reveal a (as_seq h0 block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 16 ==> Seq.index w i == Spec.ws a b i))))

[@"substitute"]
let ws_part_1 a ws_w block_w =
  (**) let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat) : Type0 =
    i <= 16 /\ live h1 ws_w /\ live h1 block_w /\ modifies_1 ws_w h0 h1 /\
    as_seq h1 block_w == as_seq h0 block_w
    /\ (let seq_block = buffer_reveal a (as_seq h0 block_w) in
       let w = buffer_reveal a (as_seq h1 ws_w) in
    (forall (j:nat). {:pattern (Seq.index w j)} j < i ==> Seq.index w j == Spec.ws a seq_block j))
  in
  let f' (t:uint32_t {v t < 16}) :
    Stack unit
      (requires (fun h -> inv h (UInt32.v t)))
      (ensures (fun h_1 _ h_2 -> inv h_2 (UInt32.v t + 1)))
    =
    ws_part_1_core a ws_w block_w t
  in
  // (**) Lemmas.lemma_modifies_0_is_modifies_1 h0 ws_w;
  for 0ul 16ul inv f';
  (**) let h1 = ST.get() in ()


[@ "substitute"]
private
val ws_part_2_core:
  a:hash_alg ->
  ws_w    :ws_w a ->
  block_w :block_w a{disjoint ws_w block_w} ->
  i:UInt32.t{16 <= UInt32.v i /\ UInt32.v i < Spec.size_k_w a} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w /\
                  (let w = buffer_reveal a (as_seq h ws_w) in
                  let b = buffer_reveal a (as_seq h block_w) in
                  (forall (j:nat). {:pattern (Seq.index w j)} j < UInt32.v i ==> Seq.index w j == Spec.ws a b j))))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1 /\
                  buffer_reveal a (as_seq h1 block_w) == buffer_reveal a (as_seq h0 block_w)
                  /\ (let w = buffer_reveal a (as_seq h1 ws_w) in
                  let b = buffer_reveal a (as_seq h0 block_w) in
                  (forall (j:nat). {:pattern (Seq.index w j)} j < UInt32.v i+1 ==> Seq.index w j == Spec.ws a b j))))

[@ "substitute"]
let ws_part_2_core a ws_w block_w t =
  (**) let h0 = ST.get () in
  let t16 = ws_w.(t -^ 16ul) in
  let t15 = ws_w.(t -^ 15ul) in
  let t7  = ws_w.(t -^ 7ul) in
  let t2  = ws_w.(t -^ 2ul) in
  ws_w.(t) <- (Spec.word_add_mod (_sigma1 a t2) (Spec.word_add_mod t7 (Spec.word_add_mod (_sigma0 a t15) t16)));
  (**) let h1 = ST.get () in
  (**) no_upd_lemma_1 h0 h1 ws_w block_w;
//  (**) Lemmas.lemma_spec_ws_def2 (reveal_h64s (as_seq h0 block_w)) (UInt32.v t);
  (**) assert(Seq.index (reveal_h64s (as_seq h1 ws_w)) (UInt32.v t) == Spec.ws a (buffer_reveal a (as_seq h0 block_w)) (UInt32.v t))


[@"substitute"]
private val ws_part_2:
  a:hash_alg ->
  ws_w :ws_w a ->
  block_w :block_w a{disjoint ws_w block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w
                  /\ (let w = buffer_reveal a (as_seq h ws_w) in
                  let b = buffer_reveal a (as_seq h block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 16 ==> Seq.index w i == Spec.ws a b i))))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = buffer_reveal a (as_seq h1 ws_w) in
                  let b = buffer_reveal a (as_seq h0 block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws a b i))))

[@"substitute"]
let ws_part_2 a ws_w block_w =
  (**) let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat) : Type0 =
    live h1 ws_w /\ live h1 block_w /\ modifies_1 ws_w h0 h1 /\ 16 <= i /\ i <= Spec.size_k_w a
    /\ buffer_reveal a (as_seq h1 block_w) == buffer_reveal a (as_seq h0 block_w)
    /\ (let seq_block = buffer_reveal a (as_seq h0 block_w) in
       let w = buffer_reveal a (as_seq h1 ws_w) in
    (forall (j:nat). {:pattern (Seq.index w j)} j < i ==> Seq.index w j == Spec.ws a seq_block j))
  in
  let f' (t:uint32_t {16 <= v t /\ v t < v (size_ws_w a)}) :
    Stack unit
      (requires (fun h -> inv h (UInt32.v t)))
      (ensures (fun h_1 _ h_2 -> inv h_2 (UInt32.v t + 1)))
    =
    ws_part_2_core a ws_w block_w t
  in
//  (**) Lemmas.lemma_modifies_0_is_modifies_1 h0 ws_w;
  for 16ul (size_ws_w a) inv f';
  (**) let h1 = ST.get() in ()


[@"substitute"]
private val ws:
  a: hash_alg ->
  ws_w:ws_w a ->
  block_w :block_w a{disjoint ws_w block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = buffer_reveal a (as_seq h1 ws_w) in
                  let b = buffer_reveal a (as_seq h0 block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < (Spec.size_ws_w a) ==> Seq.index w i == Spec.ws a b i))))

[@"substitute"]
let ws a ws_w block_w =
  ws_part_1 a ws_w block_w;
  ws_part_2 a ws_w block_w


[@"substitute"]
private val shuffle_core:
  a:hash_alg ->
  hash_w :hash_w a ->
  block_w:block_w a ->
  ws_w   :ws_w a ->
  k_w    :k_w a ->
  t      :uint32_t {v t < v (size_k_w a)} ->
  Stack unit
        (requires (fun h -> live h hash_w /\ live h ws_w /\ live h k_w /\ live h block_w /\
          buffer_reveal a (as_seq h k_w) == Spec.k0 a /\
          (let w = buffer_reveal a (as_seq h ws_w) in
           let b = buffer_reveal a (as_seq h block_w) in
           (forall (i:nat). {:pattern (Seq.index w i)} i < Spec.size_ws_w a ==> Seq.index w i == Spec.ws a b i)) ))
        (ensures  (fun h0 r h1 -> live h0 hash_w /\ live h0 ws_w /\ live h0 k_w /\ live h0 block_w
                  /\ live h1 hash_w /\ modifies_1 hash_w h0 h1
                  /\ (let seq_hash_0 = buffer_reveal a (as_seq h0 hash_w) in
                  let seq_hash_1 = buffer_reveal a (as_seq h1 hash_w) in
                  let seq_block = buffer_reveal a (as_seq h0 block_w) in
                  seq_hash_1 == Spec.shuffle_core a seq_block seq_hash_0 (U32.v t))))

[@"substitute"]
let shuffle_core a hash_w block_w ws_w k_w t =
  let a0 = hash_w.(0ul) in
  let b0 = hash_w.(1ul) in
  let c0 = hash_w.(2ul) in
  let d0 = hash_w.(3ul) in
  let e0 = hash_w.(4ul) in
  let f0 = hash_w.(5ul) in
  let g0 = hash_w.(6ul) in
  let h0 = hash_w.(7ul) in

  (* Perform computations *)
  let k_t = k_w.(t) in
  let ws_t = ws_w.(t) in
  let t1 = Spec.word_add_mod h0 (Spec.word_add_mod (_Sigma1 a e0)
                                (Spec.word_add_mod (_Ch a e0 f0 g0) (Spec.word_add_mod k_t ws_t))) in
  let t2 = Spec.word_add_mod (_Sigma0 a a0) (_Maj a a0 b0 c0) in

  (* Store the new working hash_w in the state *)
  () //constants_h_update a hash_w (Spec.word_add_mod t1 t2) a0 b0 c0 (Spec.word_add_mod d0 t1) e0 f0 g0


[@"substitute"]
private val shuffle:
  a: hash_alg ->
  hash_w :hash_w a ->
  block_w:block_w a{disjoint block_w hash_w} ->
  ws_w   :ws_w a{disjoint ws_w hash_w} ->
  k_w    :k_w a{disjoint k_w hash_w} ->
  Stack unit
        (requires (fun h -> live h hash_w /\ live h ws_w /\ live h k_w /\ live h block_w /\
          buffer_reveal a (as_seq h k_w) == Spec.k0 a /\
          (let w = buffer_reveal a (as_seq h ws_w) in
           let b = buffer_reveal a (as_seq h block_w) in
           (forall (i:nat). {:pattern (Seq.index w i)} i < (Spec.size_k_w a) ==> Seq.index w i == Spec.ws a b i)) ))
        (ensures  (fun h0 r h1 -> live h1 hash_w /\ modifies_1 hash_w h0 h1 /\ live h0 block_w
                  /\ live h0 hash_w
                  /\ (let seq_hash_0 = buffer_reveal a (as_seq h0 hash_w) in
                  let seq_hash_1 = buffer_reveal a (as_seq h1 hash_w) in
                  let seq_block = buffer_reveal a (as_seq h0 block_w) in
                  seq_hash_1 == Spec.shuffle a seq_hash_0 seq_block)))

[@"substitute"]
let shuffle a hash block ws k =
  (**) let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat) : Type0 =
    live h1 hash /\ modifies_1 hash h0 h1 /\ i <= v (size_ws_w a)
    /\ (let seq_block = buffer_reveal a (as_seq h0 block) in
    buffer_reveal a (as_seq h1 hash) == repeat_range_spec 0 i (Spec.shuffle_core a seq_block) (buffer_reveal a (as_seq h0 hash)))
  in
  let f' (t:uint32_t {v t < v (size_ws_w a)}) :
    Stack unit
      (requires (fun h -> inv h (UInt32.v t)))
      (ensures (fun h_1 _ h_2 -> inv h_2 (UInt32.v t + 1)))
    =
    shuffle_core a hash block ws k t;
    (**) C.Loops.lemma_repeat_range_spec 0 (UInt32.v t + 1) (Spec.shuffle_core a (buffer_reveal a (as_seq h0 block))) (buffer_reveal a (as_seq h0 hash))
  in
  (**) C.Loops.lemma_repeat_range_0 0 0 (Spec.shuffle_core a (buffer_reveal a (as_seq h0 block))) (buffer_reveal a (as_seq h0 hash));
  for 0ul (size_ws_w a) inv f'

[@"substitute"]
private val sum_hash:
  a:hash_alg ->
  hash_0:hash_w a ->
  hash_1:hash_w a{disjoint hash_0 hash_1} ->
  Stack unit
    (requires (fun h -> live h hash_0 /\ live h hash_1))
    (ensures  (fun h0 _ h1 -> live h0 hash_0 /\ live h1 hash_0 /\ live h0 hash_1 /\ modifies_1 hash_0 h0 h1
              /\ (let new_seq_hash_0 = buffer_reveal a (as_seq h1 hash_0) in
              let seq_hash_0 = buffer_reveal a (as_seq h0 hash_0) in
              let seq_hash_1 = buffer_reveal a (as_seq h0 hash_1) in
              let res        = Spec.Loops.seq_map2 (fun x y -> Spec.word_add_mod a x y) seq_hash_0 seq_hash_1 in
              new_seq_hash_0 == res)))

[@"substitute"]
let sum_hash a hash_0 hash_1 =
  (**) let h0 = ST.get() in
  C.Loops.in_place_map2 hash_0 hash_1 size_hash_w (fun x y -> Spec.word_add_mod a x y);
  (**) let h1 = ST.get() in

  // NIK : Should the following (commented) even typecheck ?
  // It does while I think it should not for SHA2_224 nor SHA2_256 which are UInt32 based
  // (**) Seq.lemma_eq_intro (Spec.Loops.seq_map2 (fun x y -> FStar.UInt64.(x +%^ y)) (buffer_reveal a (as_seq h0 hash_0))
  //                         (buffer_reveal a (as_seq  h0 hash_1))) (buffer_reveal a (as_seq h1 hash_0))
  (**) Seq.lemma_eq_intro (Spec.Loops.seq_map2 (fun x y -> Spec.word_add_mod a x y) (buffer_reveal a (as_seq h0 hash_0))
                          (buffer_reveal a (as_seq  h0 hash_1))) (buffer_reveal a (as_seq h1 hash_0))



[@"c_inline"]
val alloc:
  a:hash_alg ->
  StackInline (state:state a)
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> ~(contains h0 st) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
             /\ Map.domain h1.h == Map.domain h0.h))

[@"c_inline"]
let alloc a = Buffer.create (u32_to_h64 0ul) (size_state a)



val init:
  a:hash_alg ->
  state:state a ->
  Stack unit
    (requires (fun h0 -> live h0 state
              /\ (let seq_counter = Seq.slice (as_seq h0 state) (word_v a pos_count_w) ((word_v a pos_count_w + word_v a size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              H64.v counter = 0)))
    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1
              /\ (let slice_k = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v (size_k_w a))) in
              let slice_h_0 = Seq.slice (as_seq h1 state) (U32.v (pos_whash_w a)) (U32.(v (pos_whash_w a) + v size_whash_w)) in
              let seq_counter = Seq.slice (as_seq h1 state) (U32.v (pos_count_w a)) (U32.(v (pos_count_w a) + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              let seq_k = buffer_reveal a slice_k in
              let seq_h_0 = buffer_reveal a slice_h_0 in
              seq_k == Spec.k0 a /\ seq_h_0 == Spec.h0 a /\ word_v a counter = 0)))

let init a state =
  (**) let h0 = ST.get () in
  let n = Buffer.sub state (pos_count_w a) size_count_w in
  let k = Buffer.sub state pos_k_w (size_k_w a) in
  let h0 = Buffer.sub state (pos_whash_w a) size_whash_w in
  constants_k_init a k;
  constants_h_init a h0; ()
  // (**) let h1 = ST.get () in
  // (**) no_upd_lemma_2 h0 h1 k h0 n


[@"substitute"]
private val copy_hash:
  a:hash_alg ->
  hash_w_1 :hash_w a ->
  hash_w_2 :hash_w a{disjoint hash_w_1 hash_w_2} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w_1 /\ live h0 hash_w_2))
        (ensures  (fun h0 _ h1 -> live h0 hash_w_1 /\ live h0 hash_w_2 /\ live h1 hash_w_1 /\ modifies_1 hash_w_1 h0 h1
                  /\ (as_seq h1 hash_w_1 == as_seq h0 hash_w_2)))

[@"substitute"]
let copy_hash a hash_w_1 hash_w_2 =
  (**) let h0 = ST.get () in
  Buffer.blit hash_w_2 0ul hash_w_1 0ul size_hash_w; ()
  // (**) let h1 = ST.get () in
  // (**) assert(Seq.slice (as_seq h1 hash_w_1) 0 (v size_hash_w) == Seq.slice (as_seq h0 hash_w_2) 0 (v size_hash_w));
  // (**) Lemmas.lemma_blit_slices_eq h0 h1 hash_w_1 hash_w_2 (v size_hash_w)


[@"substitute"]
private val update_core:
  a: hash_alg ->
  hash_w :hash_w a ->
  data   :block a {disjoint data hash_w} ->
  data_w :block_w a{disjoint data_w hash_w} ->
  ws_w   :ws_w a{disjoint ws_w hash_w} ->
  k_w    :k_w a{disjoint k_w hash_w} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w /\ live h0 data /\ live h0 data_w /\ live h0 ws_w /\ live h0 k_w
                  /\ buffer_reveal a (as_seq h0 k_w) == Spec.k0 a
                  /\ (buffer_reveal a (as_seq h0 data_w) = Spec.words_from_be a (v size_block_w) (reveal_sbytes (as_seq h0 data)))
                  /\ (let w = buffer_reveal a (as_seq h0 ws_w) in
                  let b = buffer_reveal a (as_seq h0 data_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < (Spec.size_ws_w a) ==> Seq.index w i == Spec.ws a b i))))
        (ensures  (fun h0 r h1 -> live h0 hash_w /\ live h0 data /\ live h0 data_w /\ live h1 hash_w /\ modifies_1 hash_w h0 h1
                  /\ (let seq_hash_0 = buffer_reveal a (as_seq h0 hash_w) in
                  let seq_hash_1 = buffer_reveal a (as_seq h1 hash_w) in
                  let seq_block = reveal_sbytes (as_seq h0 data) in
                  let res = Spec.update a seq_hash_0 seq_block in
                  seq_hash_1 == res)))


[@"substitute"]
let update_core a hash_w data data_w ws_w k_w =
  (**) assert_norm(pow2 32 = 0x100000000);
  (**) assert_norm(pow2 64 = 0x10000000000000000);
  (**) assert_norm(pow2 125 = 42535295865117307932921825928971026432);
  (**) let h0 = ST.get() in

  (* Push a new frame *)
  (**) push_frame();
  (**) let h1 = ST.get() in
  (**) assert(let b = Spec.words_from_be a Spec.size_block_w (reveal_sbytes (as_seq h0 data)) in
              buffer_reveal a (as_seq h0 data_w) == b);

  (* Allocate space for converting the data block *)
  let hash_0 = Buffer.create (u64_to_h64 0uL) size_hash_w in
  (**) let h2 = ST.get() in
  (**) no_upd_lemma_0 h1 h2 data;
  (**) no_upd_lemma_0 h1 h2 data_w;
  (**) no_upd_lemma_0 h1 h2 ws_w;
  (**) no_upd_lemma_0 h1 h2 k_w;
  (**) no_upd_lemma_0 h1 h2 hash_w;

  (* Keep track of the the current working hash from the state *)
  copy_hash a hash_0 hash_w;
  (**) let h3 = ST.get() in
  (**) no_upd_lemma_1 h2 h3 hash_0 data;
  (**) no_upd_lemma_1 h2 h3 hash_0 data_w;
  (**) no_upd_lemma_1 h2 h3 hash_0 ws_w;
  (**) no_upd_lemma_1 h2 h3 hash_0 k_w;
  (**) no_upd_lemma_1 h2 h3 hash_0 hash_w;

  (* Step 2 : Initialize the eight working variables *)
  (* Step 3 : Perform logical operations on the working variables *)
  (* Step 4 : Compute the ith intermediate hash value *)
  shuffle a hash_0 data_w ws_w k_w;
  (**) let h4 = ST.get() in
  (**) assert(let b = Spec.words_from_be a Spec.size_block_w (reveal_sbytes (as_seq h0 data)) in
              let ha = Spec.shuffle a (buffer_reveal a (as_seq h0 hash_w)) b in
              as_seq h4 hash_w == as_seq h0 hash_w /\
              reveal_h64s (as_seq h4 hash_0) == ha);
  (**) no_upd_lemma_1 h3 h4 hash_0 data;
  (**) no_upd_lemma_1 h3 h4 hash_0 data_w;
  (**) no_upd_lemma_1 h3 h4 hash_0 ws_w;
  (**) no_upd_lemma_1 h3 h4 hash_0 k_w;
  (**) no_upd_lemma_1 h3 h4 hash_0 hash_w;

  (* Use the previous one to update it inplace *)
  sum_hash a hash_w hash_0;
  (**) let h5 = ST.get() in
  (**) assert(let x = reveal_h64s (as_seq h4 hash_w) in
          let y = reveal_h64s (as_seq h4 hash_0) in
          x == reveal_h64s (as_seq h0 hash_w) /\
          y == Spec.shuffle a (reveal_h64s (as_seq h0 hash_w)) (Spec.words_from_be a Spec.size_block_w (reveal_sbytes (as_seq h0 data))));
  (**) assert(let x = reveal_h64s (as_seq h0 hash_w) in
         let y = Spec.shuffle a (reveal_h64s (as_seq h0 hash_w)) (Spec.words_from_be a Spec.size_block_w (reveal_sbytes (as_seq h0 data))) in
         let z = reveal_h64s (as_seq h5 hash_w) in
         let z' = Spec.Loops.seq_map2 (fun x y -> FStar.UInt64.(x +%^ y)) x y in
         z == z');
  (**) no_upd_lemma_1 h4 h5 hash_w data;
  (**) no_upd_lemma_1 h4 h5 hash_w data_w;
  (**) no_upd_lemma_1 h4 h5 hash_w ws_w;
  (**) no_upd_lemma_1 h4 h5 hash_w k_w;

  (* Pop the frame *)
  (**) pop_frame()


[@"substitute"]
val counter_increment:
  a: hash_alg ->
  counter_w :word a ->
  Stack unit
        (requires (fun h -> live h counter_w
                  /\ (let counter = Seq.index (as_seq h counter_w) 0 in
                  (word_v a counter) < ((Spec.pow2_values a) - 1))))
        (ensures  (fun h0 _ h1 -> live h1 counter_w /\ live h0 counter_w /\ modifies_1 counter_w h0 h1
                  /\ (let counter_0 = Seq.index (as_seq h0 counter_w) 0 in
                  let counter_1 = Seq.index (as_seq h1 counter_w) 0 in
                  word_v a counter_1 = word_v a counter_0 + 1 /\ word_v counter_1 < Spec.pow2_values a)))

[@"substitute"]
let counter_increment a counter_w =
  let c0 = counter_w.(0ul) in
  let one = u32_to_h64 1ul in
  counter_w.(0ul) <- (Spec.word_add_mod c0 one)


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 75"

val update:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {length data = v size_block /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  reveal_h64s seq_k == Spec.k0 a /\ H64.v counter < (Spec.pow2_values a - 1))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_k_0 = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_k_1 = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_block = as_seq h0 data in
                  let seq_counter_0 = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let seq_counter_1 = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter_0 = Seq.index seq_counter_0 0 in
                  let counter_1 = Seq.index seq_counter_1 0 in
                  seq_k_0 == seq_k_1
                  /\ H64.v counter_1 = H64.v counter_0 + 1 /\ H64.v counter_1 < pow2 64
                  /\ reveal_h64s seq_hash_1 == Spec.update (reveal_h64s seq_hash_0) (reveal_sbytes seq_block))))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 250"

let update state data =

  (* Push a new frame *)
  (**) let h0 = ST.get () in
  (**) push_frame();
  (**) let h1 = ST.get () in
  (**) Lemmas.lemma_eq_state_k_sub_slice h1 state;
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)))
  (**)                    (Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)));
  (**) Lemmas.lemma_eq_state_counter_sub_slice h1 state;
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)))
                          (Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)));
  (**) Lemmas.lemma_eq_state_hash_sub_slice h1 state;
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))
                          (Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)));

  (* Allocate space for converting the data block *)
  let data_w = Buffer.create (u32_to_h64 0ul) size_block_w in
  (**) let h2 = ST.get () in
  (**) no_upd_lemma_0 h1 h2 data;
  (**) no_upd_lemma_0 h1 h2 (Buffer.sub state pos_k_w size_k_w);
  (**) no_upd_lemma_0 h1 h2 (Buffer.sub state pos_whash_w size_whash_w);
  (**) no_upd_lemma_0 h1 h2 (Buffer.sub state pos_count_w size_count_w);

  (* Cast the data bytes into a uint32_t buffer *)
  uint64s_from_be_bytes data_w data size_block_w;
  (**) let h3 = ST.get () in
  (**) no_upd_lemma_1 h2 h3 data_w (Buffer.sub state pos_k_w size_k_w);
  (**) no_upd_lemma_1 h2 h3 data_w (Buffer.sub state pos_whash_w size_whash_w);
  (**) no_upd_lemma_1 h2 h3 data_w (Buffer.sub state pos_count_w size_count_w);
  (**) no_upd_lemma_1 h2 h3 data_w data;
  (**) assert(reveal_h64s (as_seq h3 data_w) == Spec.Lib.uint64s_from_be (U32.v size_block_w) (reveal_sbytes (as_seq h3 data)));

  (* Retreive values from the state *)
  let hash_w = Buffer.sub state pos_whash_w size_whash_w in
  let ws_w = Buffer.sub state pos_ws_w size_ws_w in
  let k_w = Buffer.sub state pos_k_w size_k_w in
  let counter_w = Buffer.sub state pos_count_w size_count_w in

  (* Step 1 : Scheduling function for sixty-four 32 bit words *)
  ws ws_w data_w;
  (**) let h4 = ST.get () in
  (**) no_upd_lemma_1 h3 h4 ws_w data;
  (**) no_upd_lemma_1 h3 h4 ws_w k_w;
  (**) no_upd_lemma_1 h3 h4 ws_w hash_w;
  (**) no_upd_lemma_1 h3 h4 ws_w counter_w;

  (* Step 2 : Initialize the eight working variables *)
  (* Step 3 : Perform logical operations on the working variables *)
  (* Step 4 : Compute the ith intermediate hash value *)
  (**) assert(reveal_h64s (as_seq h4 k_w) == Spec.k);
  update_core hash_w data data_w ws_w k_w;
  (**) let h5 = ST.get () in
  (**) no_upd_lemma_1 h4 h5 hash_w data;
  (**) no_upd_lemma_1 h4 h5 hash_w k_w;
  (**) no_upd_lemma_1 h4 h5 hash_w counter_w;
  (**) Lemmas.lemma_eq_state_k_sub_slice h5 state;
  (**) Lemmas.lemma_eq_state_counter_sub_slice h5 state;
  (**) Lemmas.lemma_eq_state_hash_sub_slice h5 state;
  (**) Seq.lemma_eq_intro (as_seq h1 hash_w) (as_seq h4 hash_w);
  (**) Seq.lemma_eq_intro (as_seq h1 data) (as_seq h4 data);
  (**) assert(reveal_h64s (as_seq h5 hash_w) == Spec.update (reveal_h64s (as_seq h0 hash_w)) (reveal_sbytes (as_seq h0 data)));

  (* Increment the total number of blocks processed *)
  counter_increment counter_w;
  (**) let h6 = ST.get () in
  (**) no_upd_lemma_1 h5 h6 counter_w data;
  (**) no_upd_lemma_1 h5 h6 counter_w k_w;
  (**) no_upd_lemma_1 h5 h6 counter_w hash_w;
  (**) Lemmas.lemma_eq_state_k_sub_slice h6 state;
  (**) Lemmas.lemma_eq_state_counter_sub_slice h6 state;
  (**) Lemmas.lemma_eq_state_hash_sub_slice h6 state;
  (**) assert(let seq_k_0 = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let seq_k_1 = Seq.slice (as_seq h6 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              seq_k_0 == seq_k_1);
  (**) assert(let seq_counter_0 = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let seq_counter_1 = Seq.slice (as_seq h6 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter_0 = Seq.index seq_counter_0 0 in
                  let counter_1 = Seq.index seq_counter_1 0 in
                  H64.v counter_1 = H64.v counter_0 + 1 /\ H64.v counter_1 < pow2 64);
  (**) assert(let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h6 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_block = as_seq h0 data in
                  reveal_h64s seq_hash_1 == Spec.update (reveal_h64s seq_hash_0) (reveal_sbytes seq_block));

  (* Pop the memory frame *)
  (**) pop_frame();
  (**) let h7 = ST.get () in
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h6 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)))
                          (Seq.slice (as_seq h7 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)));
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h6 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)))
                          (Seq.slice (as_seq h7 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)));
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h6 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))
                          (Seq.slice (as_seq h7 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 100"

val update_multi:
  state :uint64_p{length state = v size_state} ->
  data  :uint8_p {length data % v size_block = 0 /\ disjoint state data} ->
  n     :uint32_t{v n * v size_block = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  reveal_h64s seq_k == Spec.k /\ H64.v counter < (pow2 64 - (v n)))))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_k_0 = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_k_1 = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_blocks = as_seq h0 data in
                  let seq_counter_0 = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let seq_counter_1 = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter_0 = Seq.index seq_counter_0 0 in
                  let counter_1 = Seq.index seq_counter_1 0 in
                  seq_k_0 == seq_k_1
                  /\ H64.v counter_1 = H64.v counter_0 + (v n) /\ H64.v counter_1 < pow2 64
                  /\ reveal_h64s seq_hash_1 == Spec.update_multi (reveal_h64s seq_hash_0) (reveal_sbytes seq_blocks))))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 200"

let rec update_multi state data n =
  (**) let h0 = ST.get() in
  if n =^ 0ul then (
    (**) assert (v n = 0);
    (**) Lemmas.lemma_aux_1 (v n) (v size_block);
    (**) assert (length data = 0);
    (**) Lemmas.lemma_modifies_0_is_modifies_1 h0 state;
    (**) Lemmas.lemma_update_multi_def (reveal_h64s (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))) (reveal_sbytes (as_seq h0 data))
  )
  else
    begin
    (**) assert(v n > 0);
    (**) Lemmas.lemma_aux_2 (v n) (v size_block);
    (**) assert(length data > 0);
    (**) Lemmas.lemma_update_multi_def (reveal_h64s (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))) (reveal_sbytes (as_seq h0 data));

    (* Get the current block for the data *)
    let b = Buffer.sub data 0ul size_block in

    (* Remove the current block from the data left to process *)
    let data = Buffer.offset data size_block in
    (**) assert(disjoint b data);

    (* Call the update function on the current block *)
    update state b;

    (* Recursive call *)
    update_multi state data (n -^ 1ul) end


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 50"

inline_for_extraction
val pad0_length: (len:uint32_t{v len + 1 + v size_len_8 <= 2 * v size_block}) ->
  Tot (n:uint32_t{v n = Spec.pad0_length (v len)})
let pad0_length len =
  (size_block +^ size_block -^ (len +^ size_len_8 +^ 1ul)) %^ size_block


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 50"

inline_for_extraction
let encode_length (count:uint64_ht) (len:uint64_t{H64.v count * v size_block + U64.v len < Spec.max_input_len_8}) : Tot (l:uint128_ht{H128.v l = (H64.v count * v size_block + U64.v len) * 8}) =
  let l0 = H128.mul_wide count (u32_to_h64 size_block) in
  let l1 = u64_to_h128 len in
  (**) assert(H128.v l0 + H128.v l1 < pow2 125);
  (**) assert_norm(pow2 3 = 8);
  (**) Math.Lemmas.modulo_lemma Hacl.UInt128.(v (shift_left (l0 +^ l1) 3ul)) (pow2 128);
  H128.(H128.shift_left (l0 +^ l1) 3ul) // Multiplication by 2^3


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"substitute"]
val set_pad_part1:
  buf1 :uint8_p {length buf1 = 1} ->
  Stack unit
        (requires (fun h0 -> live h0 buf1))
        (ensures  (fun h0 _ h1 -> live h0 buf1 /\ live h1 buf1 /\ modifies_1 buf1 h0 h1
                             /\ (let seq_buf1 = reveal_sbytes (as_seq h1 buf1) in
                             seq_buf1 = Seq.create 1 0x80uy)))

#reset-options "--z3refresh --max_fuel 0 --z3rlimit 100"

[@"substitute"]
let set_pad_part1 buf1 =
  Buffer.upd buf1 0ul (u8_to_h8 0x80uy);
  (**) let h = ST.get () in
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h buf1)) (Seq.create 1 0x80uy)


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"substitute"]
val set_pad_part2:
  buf2       :uint8_p{length buf2 = v size_len_8} ->
  encodedlen :uint128_ht ->
  Stack unit
        (requires (fun h0 -> live h0 buf2))
        (ensures  (fun h0 _ h1 -> live h0 buf2 /\ live h1 buf2 /\ modifies_1 buf2 h0 h1
                  /\ (let seq_buf2 = reveal_sbytes (as_seq h1 buf2) in
                  seq_buf2 == Endianness.big_bytes size_len_8 (H128.v encodedlen))))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 30"

[@"substitute"]
let set_pad_part2 buf2 encodedlen =
  Hacl.Endianness.hstore128_be buf2 encodedlen;
  (**) let h = ST.get () in
  (**) Lemmas.lemma_eq_endianness h buf2 encodedlen


#reset-options "--z3refresh --max_fuel 0 --z3rlimit 50"

val lemma_downcast: (len:uint64_t) -> Lemma
  (requires (UInt64.v len + 1 + UInt32.v size_len_8 <= 2 * UInt32.v size_block))
  (ensures ((UInt64.v len + 1 + UInt32.v size_len_8 <= 2 * UInt32.v size_block) ==> (UInt32.v (Int.Cast.uint64_to_uint32 len) + 1 + UInt32.v size_len_8 <= 2 * UInt32.v size_block) ))
let lemma_downcast len =
  (**) assert(UInt64.v len + 1 + UInt32.v size_len_8 <= 2 * UInt32.v size_block);
  (**) assert(UInt32.v (Int.Cast.uint64_to_uint32 len) + 1 + UInt32.v size_len_8 <= 2 * UInt32.v size_block)


#reset-options "--z3refresh --max_fuel 0 --z3rlimit 50"

val lemma_padding_bounds:
  padding :uint8_p ->
  len     :uint32_t {U32.v len + 1 + v size_len_8 <= 2 * v size_block
                     /\ length padding = (1 + v size_len_8 + Spec.pad0_length (U32.v len))}
  -> Lemma
  (ensures (let p0 = pad0_length len in
    1 <= length padding
    /\ 1 + UInt32.v p0 <= length padding
    /\ 1 + UInt32.v p0 + UInt32.v size_len_8 <= length padding))
let lemma_padding_bounds padding len = ()


#reset-options "--z3refresh --max_fuel 0 --z3rlimit 100"

val lemma_eq_pad0_downcast: len:UInt64.t -> Lemma (ensures (Spec.pad0_length (UInt32.v (u64_to_u32 len)) = Spec.pad0_length (U64.v len)))
let lemma_eq_pad0_downcast len = ()


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 50"

[@"substitute"]
val pad:
  padding :uint8_p ->
  n       :uint64_ht ->
  len     :uint64_t {U64.v len + 1 + v size_len_8 <= 2 * v size_block
                     /\ H64.v n * v size_block + U64.v len < Spec.max_input_len_8
                     /\ length padding = (1 + v size_len_8 + Spec.pad0_length (U64.v len))
                     /\ (length padding + U64.v len) % v size_block = 0} ->
  Stack unit
        (requires (fun h0 -> live h0 padding
                  /\ (let seq_padding = reveal_sbytes (as_seq h0 padding) in
                  seq_padding == Seq.create (1 + v size_len_8 + Spec.pad0_length (U64.v len)) 0uy)))
        (ensures  (fun h0 _ h1 -> live h0 padding /\ live h1 padding /\ modifies_1 padding h0 h1
                  /\ (let seq_padding = reveal_sbytes (as_seq h1 padding) in
                  seq_padding == Spec.pad (H64.v n * v size_block) (U64.v len))))

#reset-options "--z3refresh --max_fuel 0 --z3rlimit 500"

[@"substitute"]
let pad padding n len =

  (* Compute and encode the total length *)
  let encodedlen = encode_length n len in
  assert(H128.v encodedlen = ((H64.v n * v size_block + U64.v len) * 8));

  (* Get the memory *)
  (**) let h0 = ST.get () in

  (* Compute the length of zeros *)
  (**) assert(U64.v len + 1 + v size_len_8 <= 2 * v size_block);
  (**) lemma_downcast len;
  (**) assert(U32.v (u64_to_u32 len) + 1 + v size_len_8 <= 2 * v size_block);
  let pad0len = pad0_length (u64_to_u32 len) in
  (**) assert(UInt32.v pad0len = Spec.pad0_length (UInt32.v (u64_to_u32 len)));
  (**) lemma_eq_pad0_downcast len;
  (**) assert(UInt32.v pad0len = Spec.pad0_length (UInt64.v len));

  (* Retreive the different parts of the padding *)
  (**) assert(length padding = (1 + v size_len_8 + Spec.pad0_length (U64.v len)));
  (**) assert(1 <= length padding);
  let buf1 = Buffer.sub padding 0ul 1ul in
  (**) let h1 = ST.get () in
  (**) assert(length padding = (1 + v size_len_8 + Spec.pad0_length (U64.v len)));
  (**) lemma_eq_pad0_downcast len;
  (**) assert(1 + UInt32.v pad0len <= length padding);
  let zeros = Buffer.sub padding 1ul pad0len in
  (**) let h2 = ST.get () in
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h2 zeros)) (Seq.create (v pad0len) 0uy);
  (**) assert(reveal_sbytes (as_seq h2 zeros) == Seq.create (v pad0len) 0uy);
  (**) assert(v (1ul +^ pad0len) + v size_len_8 <= length padding);
  let buf2 = Buffer.sub padding (1ul +^ pad0len) size_len_8 in

  (* Set the first byte of the padding *)
  set_pad_part1 buf1;
  (**) no_upd_lemma_1 h0 h1 buf1 zeros;
  (**) no_upd_lemma_1 h0 h1 buf1 buf2;

  (* Encode the total length at the end of the padding *)
  set_pad_part2 buf2 encodedlen;

  (* Proof that this is the concatenation of the three parts *)
  (**) let h3 = ST.get () in
  (**) Buffer.no_upd_lemma_2 h2 h3 buf1 buf2 zeros;
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h3 zeros)) (Seq.create (v pad0len) 0uy);
  (**) assert(reveal_sbytes (as_seq h3 zeros) == Seq.create (v pad0len) 0uy);
  (**) assert(reveal_sbytes (as_seq h3 buf1) == Seq.create 1 0x80uy);
  (**) assert(reveal_sbytes (as_seq h3 buf2) == Endianness.big_bytes size_len_8 (H128.v encodedlen));
  (**) Lemmas.lemma_sub_append_3 h3 padding 0ul buf1 1ul zeros (1ul +^ pad0len) buf2 (1ul +^ pad0len +^ size_len_8);
  (**) Lemmas.lemma_pad_aux h3 n len buf1 zeros buf2


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 100"

val update_last:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint64_t {U64.v len = length data /\ (length data + v size_len_8 + 1) < 2 * v size_block} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  let nb = U64.div len (u32_to_u64 size_block) in
                  reveal_h64s seq_k == Spec.k /\ H64.v counter < (pow2 64 - 2))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_data = reveal_sbytes (as_seq h0 data) in
                  let count = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.v pos_count_w + 1) in
                  let prevlen = H64.((H64.v (Seq.index count 0)) * (U32.v size_block)) in
                  reveal_h64s seq_hash_1 == Spec.update_last (reveal_h64s seq_hash_0) prevlen seq_data)))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 750"

let update_last state data len =
  (**) assert_norm(pow2 32 = 0x100000000);

  (* Push a new memory frame *)
  (**) push_frame();

  (* Alocate memory set to zeros for the last two blocks of data *)
  let blocks = Buffer.create (uint8_to_sint8 0uy) (size_block +^ size_block) in

  (**) let h0 = ST.get () in
  // (**) assert(reveal_sbytes (as_seq h0 blocks) == Seq.create (2 * v size_block) 0uy);

  (* Verification of how many blocks are necessary *)
  (* Threat model. The length is public ! *)
  let nb = if U64.(len <^ 112uL) then 1ul else 2ul in
  let final_blocks =
    (**) let h1 = ST.get () in
    if U64.(len <^ 112uL) then begin
      (**) assert(v size_block <= length blocks);
      (**) assert(live h1 blocks);
      Buffer.offset blocks size_block end
    else begin
      (**) assert(live h1 blocks);
      blocks end in

  (**) let h2 = ST.get () in
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h2 final_blocks))
                          (if U64.(len <^ 112uL) then
                              Seq.create (v size_block) 0uy
                           else Seq.create (v size_block + v size_block) 0uy);
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h2 final_blocks)) (Seq.create (
                          v (if U64.(len <^ 112uL) then 1ul else 2ul)  * v size_block) 0uy);
  (**) assert(reveal_sbytes (as_seq h2 final_blocks) == Seq.create (v nb * v size_block) 0uy);

  (* Copy the data to the final construct *)
  (* Leakage model : allowed because the length is public *)
//  (**) assert(length final_blocks)
  Buffer.blit data 0ul final_blocks 0ul (u64_to_u32 len);
  (**) let h3 = ST.get () in
  (**) Seq.lemma_eq_intro (as_seq h3 data) (Seq.slice (as_seq h3 data) 0 (U64.v len));
  (**) Seq.lemma_eq_intro (as_seq h3 data) (Seq.slice (as_seq h3 final_blocks) 0 (U64.v len));
  (**) assert(as_seq h3 data == Seq.slice (as_seq h3 final_blocks) 0 (U64.v len));

  (* Compute the final length of the data *)
  let n = state.(pos_count_w) in

  (* Set the padding *)
  let padding = Buffer.offset final_blocks (u64_to_u32 len) in
  (**) assert(U64.v len + v size_len_8 + 1 < 2 * v size_block);
  (**) assert(H64.v n * v size_block + U64.v len < Spec.max_input_len_8);
  (**) assert(length padding = (1 + (Spec.pad0_length (U64.v len)) + v size_len_8));
  (**) assert((length padding + U64.v len) % v size_block = 0);
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h3 padding)) (Seq.create (1 + (Spec.pad0_length (U64.v len)) + v size_len_8) 0uy);
  (**) assert(reveal_sbytes (as_seq h3 padding) == Seq.create (1 + (Spec.pad0_length (U64.v len)) + v size_len_8) 0uy);
  pad padding n len;

  (* Proof that final_blocks = data @| padding *)
  (**) let h4 = ST.get () in
  (**) assert(disjoint padding data);
  (**) no_upd_lemma_1 h3 h4 padding data;
  (**) Seq.lemma_eq_intro (as_seq h4 (Buffer.sub final_blocks 0ul (u64_to_u32 len))) (Seq.slice (as_seq h4 final_blocks) 0 (U64.v len));
  (**) no_upd_lemma_1 h3 h4 padding (Buffer.sub final_blocks 0ul (u64_to_u32 len));
  (**) assert(reveal_sbytes (as_seq h4 data) == Seq.slice (reveal_sbytes (as_seq h4 final_blocks)) 0 (U64.v len));

  (**) Seq.lemma_eq_intro (as_seq h4 (Buffer.offset final_blocks (u64_to_u32 len))) (Seq.slice (as_seq h4 final_blocks) (U64.v len) (v nb * v size_block));
  (**) Seq.lemma_eq_intro (as_seq h4 padding) (Seq.slice (as_seq h4 final_blocks) (U64.v len) (v nb * v size_block));
  (**) assert(as_seq h4 padding == Seq.slice (as_seq h4 final_blocks) (U64.v len) (v nb * v size_block));
  (**) Lemmas.lemma_sub_append_2 h4 final_blocks 0ul data (u64_to_u32 len) padding (nb *^ size_block);
  (**) assert(as_seq h4 final_blocks == Seq.append (as_seq h4 data) (as_seq h4 padding));

  (* Call the update function on one or two blocks *)
  (**) assert(length final_blocks % v size_block = 0 /\ disjoint state data);
  (**) assert(v nb * v size_block = length final_blocks);
  (**) assert(live h4 state /\ live h4 final_blocks);
  (**) assert(let seq_k = Seq.slice (as_seq h4 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let seq_counter = Seq.slice (as_seq h4 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              reveal_h64s seq_k == Spec.k /\ H64.v counter < (pow2 64 - 2));

  update_multi state final_blocks nb;

  (* Pop the memory frame *)
  (**) pop_frame()


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"substitute"]
val finish_core:
  hash_w :uint64_p {length hash_w = v size_hash_w} ->
  hash   :uint8_p  {length hash = v size_hash /\ disjoint hash_w hash} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 hash_w /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = reveal_h64s (as_seq h0 hash_w) in
                  let seq_hash = reveal_sbytes (as_seq h1 hash) in
                  seq_hash = Spec.words_to_be (U32.v size_hash_w) seq_hash_w)))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 50"

[@"substitute"]
let finish_core hash_w hash = uint64s_to_be_bytes hash hash_w size_hash_w


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

val finish:
  state :uint64_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v size_hash /\ disjoint state hash} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash = reveal_sbytes (as_seq h1 hash) in
                  seq_hash = Spec.finish (reveal_h64s seq_hash_w))))

let finish state hash =
  let hash_w = Buffer.sub state pos_whash_w size_whash_w in
  finish_core hash_w hash


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

val hash:
  hash :uint8_p {length hash = v size_hash} ->
  input:uint8_p {length input < Spec.max_input_len_8 /\ disjoint hash input} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_input = reveal_sbytes (as_seq h0 input) in
                  let seq_hash = reveal_sbytes (as_seq h1 hash) in
                  seq_hash == Spec.hash seq_input)))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 100"

let hash hash input len =

  (* Push a new memory frame *)
  (**) push_frame ();

  (* Allocate memory for the hash state *)
  let state = Buffer.create (u32_to_h64 0ul) size_state in

  (* Compute the number of blocks to process *)
  let n = U32.div len size_block in
  let r = U32.rem len size_block in

  (* Get all full blocks the last block *)
  let input_blocks = Buffer.sub input 0ul (n *%^ size_block) in
  let input_last = Buffer.sub input (n *%^ size_block) r in

  (* Initialize the hash function *)
  init state;

  (* Update the state with input blocks *)
  update_multi state input_blocks n;

  (* Process the last block of input *)
  update_last state input_last (u32_to_u64 r);

  (* Finalize the hash output *)
  finish state hash;

  (* Pop the memory frame *)
  (**) pop_frame ()
