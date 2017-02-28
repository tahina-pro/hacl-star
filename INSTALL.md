# INSTALLATION

The C code can be compiled using gcc-6, and tested against various
other cryptographic libraries.

However, the C code can also be extracted from its proof. To this end,
Hacl* relies on [F*](https://github.com/FStarLang/FStar) and
[KreMLin](https://github.com/FStarLang/kremlin) for both code
extraction and verification.

This file linearly describes the whole testing, code extraction,
testing and verification processes along with all prerequisites
required for each step.

### Prerequisites for compiling the code

To compile the C code, you need to use GCC 6.

To install GCC 6 on Ubuntu 16.04 or derivatives, use the following
sequence of commands.

```
sudo apt-get install software-properties-common
sudo add-apt-repository ppa:ubuntu-toolchain-r/test
sudo apt-get update
sudo apt-get install gcc-6 g++-6
```

### Prerequisites for testing the code

Testing the code involves comparisons with various other cryptographic
libraries (OpenSSL, NaCl, LibSodium, TweetNaCl), which you will need
to download, compile and install prior to testing. To this end, please
checkout the corresponding submodules and compile and install using
the following sequence of commands:

```
cd other_providers
git submodule update --init
cd openssl
./config no-asm
make
cd ../libsodium
sudo apt-get install libtool autoconf automake
./autogen.sh
./configure --disable-asm --enable-opt
make
sudo make install
export LD_LIBRARY_PATH=/usr/local/lib
```

### Testing the already extracted code

Already extracted C code can be found in the
[snapshots/hacl-c](snapshots/hacl-c) directory.

You can test it by `make -C snapshots/hacl-c test`.


### Extracting the code, testing it and verifying it  (optional)

#### Prerequisites for code extraction and verification

Please set `FSTAR_HOME` and `KREMLIN_HOME` in your environnement. Unless
you already have F* and KreMLin in a custom location, from this
directory, run:

```
export FSTAR_HOME=$(pwd)/dependencies/FStar
export KREMLIN_HOME=$(pwd)/dependencies/kremlin
```

If you have not installed FStar or KreMLin, you can install them into
the directories specified above, using the following procedure.

The main prerequisite to install F* and KreMLin is OCaml. Please
install the OCaml compiler and the OPAM package manager. A couple
other tools are also needed, including `cmake`. If you've never
installed any of these, on Ubuntu derivates, run:

```
sudo apt-get install ocaml opam m4 build-essential cmake
opam --init
eval $(opam config env)
opam depext ocamlfind batteries sqlite3 fileutils stdint zarith yojson pprint menhir \
  ppx_deriving_yojson zarith pprint menhir ulex process fix wasm
opam install ocamlfind batteries sqlite3 fileutils stdint zarith yojson pprint menhir \
  ppx_deriving_yojson zarith pprint menhir ulex process fix wasm
```

Then, you can compile FStar and KreMLin by:

```
git submodule update --init
make -C dependencies/FStar/src/ocaml-output
make -C dependencies/kremlin
```

#### Extracting and testing the code

You can extract the code directly from F*, running `make extract-c` in
the present directory. This will create a `snapshot` directory in
`test/`, containing the extracted code alongside with test files.

Once extracted, you can test that code by `make -C test/snapshot test`.

*Makefiles* are also present in the [code](code) directory, and its
sub directories. There, run `make extract-c` to extract the
corresponding code if you wish to do so separately.

#### Functional specifications

The functional specifications of the HACL primitives are located in
the ./specs directory. While those files cannot be extracted to C
code, they are runnable in OCaml for sanity checks.

Run `make -C specs` to run the functional specifications.

#### Verifying the code

NB: verification will take some time (~12h). While the verification
targets are parallelizable, some files require large amounts of RAM
(i.e.  `code/salsa-family/Hacl.Impl.Salsa20.fst`).

Just run `make verify`.

*Makefiles* are also present in the [code](code) directory, and its
sub directories. There, run `make verify` to run the verification
targets if you wish to do so separately.

### Uninstalling the custom libsodium

After testing, you can uninstall the custom copy of libsodium that was
compiled in the testing prerequisites above by the following command:

```
sudo make -C other_providers/libsodium uninstall
```
