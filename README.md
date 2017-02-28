Non-anonymous supplementary materials for ICFP submission
=========================================================

Companion paper
---------------

The `companion-paper.pdf` file provides another paper by the same authors,
to appear at IEEE S&P'17. It describes the security proof of our TLS 1.3
implementation, and briefly mentions our toolchain and the performance results.

Proofs
------

The present directory contains the proof artefacts mentioned in our ICFP
submission. In order of appearance in the paper:
- **Fig. 2, "A snippet from Chacha20"**:
  `code/salsa-family/Hacl.Impl.Chacha20.fst`:777 for the implementation, and
  `code/salsa-family/Chacha20.fsti` for the interface
- **2.2, Low\* heap model**:
  + `dependencies/FStar/ulib/FStar.HyperHeap.fst`, for the definition of `rid`,
    `root`, etc.
  + `dependencies/FStar/ulib/FStar.HyperStack.fst`, for the definition of
    `is_stack_region`, `sid`, the `mem` type, etc.
  + `dependencies/FStar/ulib/hyperstack/FStar.ST.fst`, for the definition of
    `push_frame`, the allocation functions, the `Stack` and `StackInline`
    effects, etc.
- **2.2, Modeling arrays:**
  in `dependencies/FStar/ulib/FStar.Buffer.fst`
- **2.2, Modeling structs:**
  in `dependencies/FStar/ulib/FStar.Struct.fst`
- **2.2, Modeling structs, in-progress unified model of flat, inline arrays within
  structs:**
  in `dependencies/FStar/ulib/FStar.StructNG.fst`
- **2.3, abstract limb type:**
  in `code/bignum/Hacl.Bignum.Limb.fst`, including the the definition of `v` and
  `eq_mask`
- **Fig. 3, Poly1305 bigint:**
  + since the paper was written, our Poly1305 version was ported to 64-bits; the
    new normalization functions are in `code/poly1305/Hacl.Bignum.Modulo.fst`, and
    the closest equivalent of `poly1305_mac` is `poly1305_last_pass_` in
    `code/poly1305/Hacl.Impl.Poly1305_64.fst`
  + we also include an older version of
    our codebase for reference purposes; the `normalize` function is in
    `dependencies/FStar/examples/low-level/crypto/Crypto.Symmetric.Poly1305.Bignum.fst`
    and is called `finalize`; the `poly1305_mac` function is in
    `dependencies/FStar/examples/low-level/crypto/Crypto.Symmetric.Poly1305.fst`:1083.
- **2.4, AEAD security proof:**
  the AEAD development has not been integrated with the HACL* library yet; the
  top-level AEAD proof statement, `encrypt`, is in
  `dependencies/FStar/examples/low-level/crypto/Crypto.AEAD.Encrypt.fst`

Tools
-----

- **4, the KreMLin tool:**
  the source of KreMLin are included in `dependencies/kremlin`; of notable
  interest are the files
  `dependencies/kremlin/src/Simplify.ml` (many rewriting passes),
  `dependencies/kremlin/src/Inlining.ml` (inlining of the `StackInline` effect),
  `dependencies/kremlin/src/DataTypes.ml` (compilation of data types and pattern
  matches),
  `dependencies/kremlin/src/AstToCStar.ml` (the transformation from λow\* to
  C\*)

Performance & running the code
------------------------------

Reproducing the performance measurements may be achieved in two different ways.
- One may follow the instructions in `INSTALL.md`.
- One may use our Docker image that comes with all the prerequisites for
  building all of our projects, via:
  `docker run projecteverest/everest-icfp2017 -it /bin/bash --login`, followed by
  `./everest pull make test`

As a proof that we have not pushed any commits to our image after the submission
deadline, we provide the git sha1 of the icfp2017 branch above:
`ceb78311053d3dd91d412bb344fcfc1c5258d94c`. We do not intend to leverage the recent
SHA1 collision attacks to push further commits.
