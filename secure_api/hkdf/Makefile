HACL_HOME?=../..
FSTAR_HOME?=../../../FStar
KREMLIN_HOME?=../../../kremlin
include ../Makefile

KRML_ARGS=$(FPIC) -ccopt -maes -fnouint128 \
  $(KREMLIN_HOME)/test/../kremlib/testlib.c \
  -drop Hacl.Spe.*,Spec,Hacl.Spec,Spec.*,Hacl.Spec.* \
  -add-include '"testlib.h"' -bundle Hacl.* $(KOPTS)

tmp/out.krml: Crypto.Test.HMAC.fst
	$(KRML) ../test/test_hacl/Crypto.Indexing.fst Crypto.Test.HMAC.fst \
	  -tmpdir tmp -skip-translation

test-hmac.exe: tmp/out.krml
	$(KRML) $< -tmpdir tmp -o $@ -no-prefix Crypto.Test.HMAC
	./$@	

include $(FSTAR_HOME)/src/gmake/z3.mk
include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

test-ocaml.exe: Crypto.Test.HMAC.fst 
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir tmp --codegen OCaml $<
	$(OCAMLOPT) -I tmp tmp/$(subst .,_,$(basename $<)).ml -o $@
	./$@


NOEXTRACT=$(FSTAR_DEFAULT_ARGS) $(addprefix --no_extract Hacl., UInt64 UInt32 UInt8)

spec_hmac_sha2_512.exe: Spec.Test.HMAC.SHA2_512.fst
	mkdir -p tmp
	$(FSTAR) --codegen OCaml --lax $(NOEXTRACT) --odir tmp $^
	$(OCAMLOPT) -I tmp $(OCAML_INCLUDES) -package fstarlib \
	tmp/FStar_Seq.ml \
	tmp/FStar_Endianness.ml \
	tmp/Spec_Loops.ml \
	tmp/Spec_Lib.ml \
	tmp/Seq_Create.ml \
	tmp/Spec_SHA2_512.ml \
	tmp/Spec_HMAC_SHA2_512.ml \
	TestLib.ml \
	tmp/Spec_Test_HMAC_SHA2_512.ml \
	-o spec_hmac_sha2_512.exe
	./spec_hmac_sha2_512.exe
