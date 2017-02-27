# INSTALLATION

Hacl* relies on [F*](https://github.com/FStarLang/FStar) and
[KreMLin](https://github.com/FStarLang/kremlin) for verification.

### Installing prerequisites

The main prerequisite to install F* and KreMLin is OCaml. Please install the
OCaml compiler and the OPAM package manager. A couple other tools are also
needed, including `cmake`. If you've never installed any of these, on Ubuntu
derivates, run:

```
sudo apt-get install ocaml opam m4 build-essential cmake
opam --init
eval $(opam config env)
opam depext ocamlfind batteries sqlite3 fileutils stdint zarith yojson pprint menhir \
  ppx_deriving_yojson zarith pprint menhir ulex process fix wasm
opam install ocamlfind batteries sqlite3 fileutils stdint zarith yojson pprint menhir \
  ppx_deriving_yojson zarith pprint menhir ulex process fix wasm
```

### Installing FStar and KreMLin

Please run:

```
git submodule update --init
make -C dependencies/FStar/src/ocaml-output
make -C dependencies/kremlin
```

### Environment

Please set FSTAR_HOME and KREMLIN_HOME in your environnement. Unless you already
have these tools in a custom location, from this directory, run:

```
export FSTAR_HOME=$(pwd)/dependencies/FStar
export KREMLIN_HOME=$(pwd)/dependencies/kremlin
```

### Verifying / extracting the code (optional)

To verify and extract the code *Makefiles* are present in the [code](code)
directory, and its sub directories. Run `make verify` to run the verification
targets, or `make extract-c` to compile to F* code to C (optional).

NB: verification will take some time (~12h). While the verification targets are
parallelizable, some files require large amounts of RAM (i.e.
`code/salsa-family/Hacl.Impl.Salsa20.fst`).

### C code

Already extracted C code can be found in the [snapshots/hacl-c](snapshots/hacl-c) directory.

You can also extract the code directly from F*, running `make extract-c` in the
present directory.
This will create a `snapshot` directory in `test/`, containing the extracted code alongside with test files.
Note that to test the code you will need various other cryptographic libraries (OpemSSL, NaCl, LibSodium, TweetNaCl). Please checkout the corresponding submodules:

```
cd dependencies
git submodule update --init
cd openssl
./config no-asm
make
cd ../libsodium
./autogen.sh
./configure --disable-asm --enable-opt
make
sudo make install
```

Then simply run `make -C test/snapshot test`.

### Functional specifications

The functional specifications of the HACL primitives are located in the ./specs directory.
While those files cannot be extracted to C code, they are runnable in OCaml for sanity checks.

Run `make -C specs` to run the functional specifications.
