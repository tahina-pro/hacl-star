all: extract-c ct verify

DIRECTORIES=salsa-family bignum poly1305 curve25519 api hmac ed25519 hash
NSS_DIRECTORIES=curve25519

%-c: %
	$(MAKE) -C $< extract-c

%-test: %
	$(MAKE) -C $< test

%-lax: %
	$(MAKE) -C $< all-lax

%-ver: %
	$(MAKE) -C $< all-ver

%-ct: %
	$(MAKE) -C $< all-ct

%-ci: %
	$(MAKE) -C $< all-ci

%-hints: %
	$(MAKE) -C $< hints

%-clean: %
	$(MAKE) -C $< clean

lax: $(addsuffix -lax, $(DIRECTORIES))
verify: $(addsuffix -ver, $(DIRECTORIES))
test: $(addsuffix -test, $(DIRECTORIES))
ct: $(addsuffix -ct, $(DIRECTORIES))
extract-c: $(addsuffix -c, $(filter-out bignum, $(DIRECTORIES)))
hints: $(addsuffix -hints, $(DIRECTORIES))
ci: $(addsuffix -ci,$(DIRECTORIES))

nss-lax: $(addsuffix -lax, $(NSS_DIRECTORIES))
nss-verify: $(addsuffix -ver, $(NSS_DIRECTORIES))
nss-test: $(addsuffix -test, $(NSS_DIRECTORIES))
nss-ct: $(addsuffix -ct, $(NSS_DIRECTORIES))
nss-extract-c: $(addsuffix -c, $(filter-out bignum, $(NSS_DIRECTORIES)))
nss-hints: $(addsuffix -hints, $(NSS_DIRECTORIES))
nss-ci: $(addsuffix -ci, $(NSS_DIRECTORIES))

all-lax: lax
all-verify: verify
all-hints: hints
all-ci: ci
all-ct: ct
all-test: test

clean: $(addsuffix -clean, $(DIRECTORIES) experimental)
	rm -rf *~ *.exe *.out
