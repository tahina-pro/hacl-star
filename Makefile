#
# Main HACL* Makefile for NSS
#

.PHONY: verify extract nss-verify nss-extract nss-test clean

all: nss


lax:
	make lax -C specs
	make lax -C code

verify:
	make verify -C specs
	make verify -C code

extract:
	make test -C specs
	make extract-c -C code


nss: nss-verify nss-extract

nss-lax:
	make nss-lax -C specs
	make nss-lax -C code

nss-verify:
	make nss-verify -C specs
	make nss-verify -C code

nss-extract:
	make nss-extract -C specs
	make nss-extract -C code

nss-test:
	make test -C nss


clean:
	rm -rf *~ nss


include code/Makefile.include

.PHONY: snapshot snapshot-gcc snapshot-ccomp snapshot-msvc snapshot-gcc-unrolled

HAS_CL=$(shell which cl.exe >/dev/null 2>&1 && echo true || echo false)
HAS_CCOMP=$(shell which ccomp >/dev/null 2>&1 && echo true || echo false)

GFIND=$(shell which gfind >/dev/null 2>&1 && echo gfind || echo find)

# These cannot benefit from parallelism, tests C extraction for available compilers
extract-all-c:
	if $(HAS_CCOMP); then $(MAKE) clean ; USE_CCOMP=true $(MAKE) extract-c ; fi
	if $(HAS_CL); then $(MAKE) clean ; USE_CL=true $(MAKE) extract-c ; fi
	$(MAKE) clean ; $(MAKE) extract-c


SNAPSHOT_FILES= ./c/* \
	$(addprefix code/poly1305/poly-c/, Poly1305_64.* AEAD_Poly1305_64.*) \
	code/curve25519/x25519-c/Curve25519.* \
	code/salsa-family/chacha-c/Chacha20.* \
	code/salsa-family/salsa-c/Salsa20.* \
	$(addprefix code/api/aead-c/, Chacha20Poly1305.*) \
	$(addprefix code/api/box-c/, NaCl.*) \
	$(addprefix code/api/policies-c/,  Hacl_Policies.*) \
	$(addprefix code/ed25519/ed25519-c/, Ed25519.*) \
	$(addprefix code/hash/sha2-c/, SHA2_256.*) \
	$(addprefix code/hash/sha2-c/, SHA2_384.*) \
	$(addprefix code/hash/sha2-c/, SHA2_512.*) \
	$(addprefix code/hmac/hmac-c/, HMAC_SHA2_256.*) \
	$(addprefix code/salsa-family/chacha-vec128-c/, Chacha20_Vec128.* ../vec128.h)


build-snapshot:
	mkdir -p $(SNAPSHOT_DIR)
	cp $(SNAPSHOT_FILES) $(SNAPSHOT_DIR)/
	$(MAKE) -C $(SNAPSHOT_DIR) clean


GCC=$(shell which gcc-7 >/dev/null 2>&1 && echo gcc-7 || (which gcc-6 >/dev/null 2>&1 && echo gcc-6 || echo gcc))
GCC_OPTS=-flto -std=c11 -D_GNU_SOURCE

test-gcc:
	$(MAKE) -C snapshot-gcc CC="$(GCC) -fno-tree-vectorize -flto" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test

test-gcc-unrolled:
	$(MAKE) -C snapshot-gcc-unrolled CC="$(GCC) -fno-tree-vectorize -flto" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test

snapshot:
	$(MAKE) extract-c-code extract-c-code-experimental
	$(MAKE) build-snapshot

snapshot-gcc:
	$(MAKE) -B extract-c-code extract-c-code-experimental KOPS+="-fparentheses"
	$(MAKE) -B build-snapshot SNAPSHOT_DIR=snapshot-gcc

snapshot-gcc-unrolled:
	$(MAKE) -B extract-c-code extract-c-code-experimental KOPTS+="-funroll-loops 5 -fparentheses"
	$(MAKE) -B build-snapshot SNAPSHOT_DIR=snapshot-gcc-unrolled

nss2:
	$(MAKE) snapshot-gcc
	$(MAKE) -C code clean
	$(MAKE) snapshot-gcc-unrolled
	$(MAKE) -C code clean
	$(MAKE) -C snapshot-gcc-unrolled clean
	$(MAKE) -C snapshot-gcc clean
	mkdir -p nss
	cp $(addprefix snapshot-gcc-unrolled/, Curve25519*) nss
	cp $(addprefix c-nss/, kremlib.h FStar.h Makefile)  nss
	$(MAKE) -C nss unit-tests
	$(MAKE) -C nss unit-tests-32
	$(MAKE) -C nss clean
