HACL_HOME?=../..
KREMLIN_HOME?=$(HACL_HOME)/kremlin
FSTAR_HOME?=$(HACL_HOME)/kremlin

.PHONY: snapshot

all:
	$(MAKE) ct
	$(MAKE) verify

travis:
	$(MAKE) extract-c
	$(MAKE) ct
	$(MAKE) -C .. world

extract-c-code:
	$(MAKE) -C ../code extract-c


extract-c: extract-c-code

ct:
	$(MAKE) -C ../code ct

verify-code:
	$(MAKE) -C ../code ci

hints-code:
	$(MAKE) -C ../code hints

hints: hints-code

verify: verify-code

build-snapshot:
	mkdir -p snapshot
	cp ../code/poly1305/poly-c/Poly1305_64.* ../code/curve25519/x25519-c/Curve25519.* \
		../code/salsa-family/chacha-c/Chacha20.* ../code/salsa-family/loops.h ../code/salsa-family/salsa-c/Salsa20.* \
		../code/salsa-family/hsalsa-c/Hacl_Symmetric_HSalsa20.* snapshot
	cp $(addprefix ../code/api/aead-c/, Hacl_AEAD_Chacha20Poly1305.*) snapshot
	cp $(addprefix ../code/api/box-c/, Hacl_Policies.* NaCl.*) snapshot
	mv snapshot/Hacl_Symmetric_HSalsa20.c snapshot/HSalsa20.c
	mv snapshot/Hacl_AEAD_Chacha20Poly1305.c snapshot/Chacha20Poly1305.c
	cp ./c/* snapshot/

CCOMP=gcc-6 -flto -std=c11 -D_GNU_SOURCE

test-snapshot:
	$(MAKE) -C snapshot CC="$(CCOMP)" test

snapshot:
	$(MAKE) extract-c-code
	$(MAKE) build-snapshot
	$(MAKE) test-snapshot

update-snapshot:
	$(build-snapshot)
	$(MAKE) -C snapshot clean
	cp snapshot/*.c snapshot/*.h ../snapshots/hacl-c

clean:
	$(MAKE) -C ../code clean
	$(MAKE) -C ../specs clean
	rm -rf snapshot *.o *.exe *~
