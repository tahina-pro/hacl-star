# INSTALLATION

Hacl* relies on [F*](https://github.com/FStarLang/FStar) and [KreMLin](https://github.com/FStarLang/kremlin) for verification.
The submodules are automatically installed when running the makefile targets.

### Environment

Please set FSTAR_HOME and KREMLIN_HOME in your environnement variables:
```
export FSTAR_HOME= <path-to hacl-star/dependencies/FStar>
export KREMLIN_HOME= <path-to hacl-star/dependencies/kremlin>
```

### Installing FStar and KreMLin

The only prerequisite to install F* and KreMLin is OCaml.
Please install the OCaml compiler and the OPAM package manager.

### Verifying / extracting the code

To verify and extract the code *Makefiles* are present in the [code](code) directory, and its sub directories.
Run `make verify` to run the verification targets, or `make extract-c` to compile to F* code to c.

NB: verification will take some times (~12h). While the verification targets are parallelizable, some files require in large amount of RAM (i.e. code/salsa-family/Hacl.Impl.Salsa20.fst).

### C code

Already extracted C code can be found in the [snapshots/hacl-c](snapshots/hacl-c) directory.

You can also extract the code directly from F*, running `make extract-c` in this directory.
This will create a `snapshot` directory in `./test`, containing the extracted code alongside with test files.
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