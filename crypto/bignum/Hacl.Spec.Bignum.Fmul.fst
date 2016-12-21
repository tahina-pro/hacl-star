module Hacl.Spec.Bignum.Fmul

open FStar.Mul

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Modulo
open Hacl.Spec.Bignum.Fproduct

module U32 = FStar.UInt32


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

let shift_reduce_pre (s:seqelem) : GTot Type0 = reduce_pre (shift_spec s)


val shift_reduce_spec: s:seqelem{shift_reduce_pre s} -> Tot (s':seqelem)
let shift_reduce_spec s =
  reduce_spec (shift_spec s)

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_shift_spec_eq: s:seqelem -> Lemma
  (Seq.append (Seq.slice (shift_spec s) 1 (len)) (Seq.slice (shift_spec s) 0 1) == s)
let lemma_shift_spec_eq s =
  Seq.lemma_eq_intro (Seq.append (Seq.slice (shift_spec s) 1 (len)) (Seq.slice (shift_spec s) 0 1)) (s)


val lemma_shift_reduce_spec: s:seqelem{shift_reduce_pre s} -> Lemma
  (seval (shift_reduce_spec s) % prime = (pow2 limb_size * seval s) % prime)
let lemma_shift_reduce_spec s =
  lemma_shift_spec_eq s;
  lemma_reduce_spec (shift_spec s)


#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"

let rec mul_shift_reduce_pre_ (output:seqelem_wide) (input:seqelem) (input2:seqelem) (ctr:nat{ctr <= len}) : GTot Type0 (decreases ctr) =
  (if ctr > 0 then (
    sum_scalar_multiplication_pre_ output input (Seq.index input2 (len-ctr)) len
    /\ (let output' = sum_scalar_multiplication_spec output input (Seq.index input2 (len-ctr)) len in
       (ctr > 1 ==> shift_reduce_pre input) /\
         (let input'  = if ctr > 1 then shift_reduce_spec input else input in
          mul_shift_reduce_pre_ output' input' input2 (ctr-1))))
          else true)


let mul_shift_reduce_pre (output:seqelem_wide) (input_init:seqelem) (input:seqelem) (input2:seqelem) (ctr:nat{ctr <= len}) : GTot Type0 (decreases ctr) =
  seval_wide output % prime = (seval input_init * seval_ input2 (len - ctr)) % prime
  /\ (ctr > 0 ==> seval input % prime = (pow2 ((len - ctr) * limb_size) * seval input_init) % prime)
  /\ mul_shift_reduce_pre_ output input input2 ctr


#set-options "--z3rlimit 10 --initial_fuel 1 --max_fuel 1"

val lemma_mod_mul_distr: a:nat -> b:nat -> p:pos -> Lemma ((a+b)%p = ((a%p) + b) % p)
let lemma_mod_mul_distr a b p = Math.Lemmas.lemma_mod_plus_distr_l a b p
val lemma_mod_mul_comm: a:nat -> b:nat -> p:pos -> Lemma ((a*b)%p = ((a%p)*b)%p)
let lemma_mod_mul_comm a b p = Math.Lemmas.lemma_mod_mul_distr_l a b p


#set-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0"

val lemma_mul_shift_reduce_spec_1_1:
  o':seqelem_wide -> o:seqelem_wide ->
  i0:seqelem -> i:seqelem ->i2:seqelem -> ij:nat ->
  ctr:pos{ctr <= len /\ ij = v (Seq.index i2 (len-ctr))} -> Lemma
  (requires (
    seval_wide o' = seval_wide o + (seval i * ij)
    /\ seval i % prime = (pow2 ((len-ctr)*limb_size) * seval i0) % prime
    /\ seval_wide o % prime = (seval i0 * seval_ i2 (len-ctr)) % prime))
  (ensures (seval_wide o' % prime = (seval i0 * seval_ i2 (len-ctr+1)) % prime))
let lemma_mul_shift_reduce_spec_1_1 o' o i0 i i2 ij ctr =
  let so' = seval_wide o' % prime in
  Math.Lemmas.lemma_mod_plus_distr_l (seval_wide o) (seval i * ij) prime;
  cut (so' = (((seval i0 * seval_ i2 (len-ctr)) % prime) + (seval i * ij)) % prime);
  Math.Lemmas.lemma_mod_plus_distr_l ((seval i0 * seval_ i2 (len-ctr))) (seval i * ij) prime;
  cut (so' = ((seval i0 * seval_ i2 (len-ctr)) + seval i * ij) % prime);
  Math.Lemmas.lemma_mod_plus_distr_l (seval i * ij) ((seval i0 * seval_ i2 (len-ctr))) prime;
  cut (so' = (((seval i * ij) % prime) + (seval i0 * seval_ i2 (len-ctr))) % prime);
  Math.Lemmas.lemma_mod_mul_distr_l (seval i) ij prime;
  cut (so' = ((((seval i % prime) * ij) % prime) + (seval i0 * seval_ i2 (len-ctr))) % prime);
  Math.Lemmas.lemma_mod_mul_distr_l (pow2 ((len-ctr)*limb_size) * seval i0) ij prime;
  cut (so' = ((((pow2 ((len-ctr)*limb_size) * seval i0) * ij) % prime) + (seval i0 * seval_ i2 (len-ctr))) % prime);
  Math.Lemmas.lemma_mod_plus_distr_l ((pow2 ((len-ctr)*limb_size) * seval i0) * ij) 
                                     (seval i0 * seval_ i2 (len-ctr)) prime;
  cut (so' = (seval i0 * pow2 ((len-ctr)*limb_size) * ij + seval i0 * seval_ i2 (len-ctr)) % prime);
  Math.Lemmas.distributivity_add_right (seval i0) (pow2 ((len-ctr)*limb_size) * ij) (seval_ i2 (len-ctr));
  cut (so' = (seval i0 * (pow2 ((len-ctr)*limb_size) * ij + seval_ i2 (len-ctr))) % prime);
  lemma_seval_def i2 (len-ctr+1)


val lemma_mul_shift_reduce_spec_1_2:
  o':seqelem_wide -> o:seqelem_wide ->
  i0:seqelem -> i:seqelem -> i':seqelem -> i2:seqelem -> ij:nat ->
  ctr:pos{ctr <= len /\ ij = v (Seq.index i2 (len-ctr))} -> Lemma
  (requires (
    seval_wide o' = seval_wide o + (seval i * ij)
    /\ seval i % prime = (pow2 ((len-ctr)*limb_size) * seval i0) % prime
    /\ seval i' % prime = (pow2 limb_size * seval i) % prime
    /\ seval_wide o % prime = (seval i0 * seval_ i2 (len-ctr)) % prime))
  (ensures (seval i' % prime = (pow2 ((len-ctr+1) * limb_size) * seval i0) % prime))
let lemma_mul_shift_reduce_spec_1_2 o' o i0 i i' i2 ij ctr =
  let si' = seval i' % prime in
  Math.Lemmas.lemma_mod_mul_distr_l (seval i) (pow2 limb_size) prime;
  Math.Lemmas.lemma_mod_mul_distr_l (pow2 ((len-ctr)*limb_size) * seval i0) (pow2 limb_size) prime;
  Math.Lemmas.pow2_plus ((len-ctr) * limb_size) limb_size


val lemma_mul_shift_reduce_spec_1:
  o':seqelem_wide -> o:seqelem_wide ->
  i0:seqelem -> i:seqelem -> i':seqelem -> i2:seqelem -> ij:nat ->
  ctr:pos{ctr <= len /\ ij = v (Seq.index i2 (len-ctr))} -> Lemma
  (requires (
    seval_wide o' = seval_wide o + (seval i * ij)
    /\ seval i % prime = (pow2 ((len-ctr)*limb_size) * seval i0) % prime
    /\ seval i' % prime = (pow2 limb_size * seval i) % prime
    /\ seval_wide o % prime = (seval i0 * seval_ i2 (len-ctr)) % prime))
  (ensures (seval_wide o' % prime = (seval i0 * seval_ i2 (len-ctr+1)) % prime
    /\ seval i' % prime = (pow2 ((len-ctr+1) * limb_size) * seval i0) % prime))
let lemma_mul_shift_reduce_spec_1 o' o i0 i i' i2 ij ctr =
  lemma_mul_shift_reduce_spec_1_1 o' o i0 i i2 ij ctr;
  lemma_mul_shift_reduce_spec_1_2 o' o i0 i i' i2 ij ctr


val lemma_mul_shift_reduce_spec_2:
  o':seqelem_wide -> o:seqelem_wide ->
  i0:seqelem -> i:seqelem -> i':seqelem -> i2:seqelem -> ij:nat{ij = v (Seq.index i2 (len-1))} -> Lemma
  (requires (
    seval_wide o' = seval_wide o + (seval i * ij)
    /\ seval i % prime = (pow2 ((len-1)*limb_size) * seval i0) % prime
    /\ seval_wide o % prime = (seval i0 * seval_ i2 (len-1)) % prime))
  (ensures (seval_wide o' % prime = (seval i0 * seval i2) % prime))
let lemma_mul_shift_reduce_spec_2 o' o i0 i i' i2 ij =
  let ctr = 1 in
  lemma_mul_shift_reduce_spec_1_1 o' o i0 i i2 ij ctr


val mul_shift_reduce_spec_:
  output:seqelem_wide ->
  input_init:seqelem ->
  input:seqelem ->
  input2:seqelem ->
  ctr:nat{ctr <= len /\ mul_shift_reduce_pre output input_init input input2 ctr} ->
  Tot (s:seqelem_wide{seval_wide s % prime = (seval input_init * seval input2) % prime})
  (decreases ctr)

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1"


let rec mul_shift_reduce_spec_ output input_init input input2 ctr =
  if ctr = 0 then output
  else (
    let i = ctr - 1 in
    let j = len - i - 1 in
    let input2j = Seq.index input2 j in
    let output' = sum_scalar_multiplication_spec output input input2j len in
    lemma_sum_scalar_multiplication_ output input input2j len;
    cut (seval_wide output' = seval_wide output + (seval input * v input2j));
    let input'  = if ctr > 1 then shift_reduce_spec input else input in
    if ctr = 1 then (
      lemma_mul_shift_reduce_spec_2 output' output input_init input input' input2 (v input2j);
      ()
    ) else (
      lemma_shift_reduce_spec input;
      lemma_mul_shift_reduce_spec_1 output' output input_init input input' input2 (v input2j) ctr;
      ()
    );
    mul_shift_reduce_spec_ output' input_init input' input2 i
  )


val lemma_seval_wide_null: a:seqelem_wide -> ctr:nat{ctr <= len} -> Lemma
  (requires (a == Seq.create len wide_zero))
  (ensures (seval_wide_ a ctr = 0))
let rec lemma_seval_wide_null a ctr =
  if ctr = 0 then () else lemma_seval_wide_null a (ctr-1)


val mul_shift_reduce_spec:
  input:seqelem -> input2:seqelem{mul_shift_reduce_pre (Seq.create len wide_zero) input input input2 len} ->
  Tot (s:seqelem_wide{seval_wide s % prime = (seval input * seval input2) % prime})
let rec mul_shift_reduce_spec input input2 =
  lemma_seval_wide_null (Seq.create len wide_zero) len;
  assert_norm (pow2 0 = 1);
  mul_shift_reduce_spec_ (Seq.create len wide_zero) input input input2 len


#set-options "--z3rlimit 5 --initial_fuel 2 --max_fuel 2"

let fmul_pre (input:seqelem) (input2:seqelem) : GTot Type0 =
  mul_shift_reduce_pre (Seq.create len wide_zero) input input input2 len
