FSTAR_HOME?=../../../dependencies/FStar
HACL_HOME?=../..

include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

FSTAR_ARGS=$(OTHERFLAGS)

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10

all: poly1305.exe chacha20.exe salsa20.exe

EXTRACTED= FStar_Seq_Base.ml FStar_Seq.ml FStar_Seq_Properties.ml FStar_Math_Lib.ml FStar_BitVector.ml FStar_UInt.ml  FStar_Endianness.ml

NOEXTRACT=$(addprefix --no_extract FStar., Classical Ghost Int16 Int32 Int64 Int63 Int16 Int8 Int.Cast Int List.Tot.Base List.Tot List.Tot.Properties Math.Lemmas Mul StrongExcludedMiddle UInt128 UInt16 UInt32 UInt63 UInt64 UInt8) $(addprefix --no_extract Hacl., UInt64 UInt32 UInt8)

ARGS=--codegen OCaml --lax --include generic --include ../code/lib/kremlin $(NOEXTRACT) --include experimental --include $(FSTAR_HOME)/ulib/hyperstack

OCAML_INCLUDES=-I ../code/lib/ml -I $(FSTAR_HOME)/ulib/ml/hyperstack ../code/lib/ml/hacllib.cmxa 

%.fst-ver: %.fst
	$(FSTAR) --include generic --include ../code/lib/kremlin --include experimental --include $(FSTAR_HOME)/ulib/hyperstack $*.fst

poly1305.exe: Spec.Poly1305.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p poly-spec
	$(FSTAR) $(ARGS) --odir poly-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> poly-spec/Spec_Poly1305.ml
	$(OCAMLOPT) -I poly-spec $(OCAML_INCLUDES) $(addprefix poly-spec/, $(EXTRACTED)) poly-spec/Spec_Poly1305.ml -o poly1305.exe
	./poly1305.exe

chacha20.exe: Spec.Chacha20.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p chacha-spec
	$(FSTAR) $(ARGS) --odir chacha-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> chacha-spec/Spec_Chacha20.ml
	$(OCAMLOPT) -I chacha-spec $(OCAML_INCLUDES) $(addprefix chacha-spec/, $(EXTRACTED)) chacha-spec/Combinators.ml chacha-spec/Spec_Lib.ml chacha-spec/Spec_CTR.ml chacha-spec/Spec_Chacha20.ml -o chacha20.exe
	./chacha20.exe

salsa20.exe: Spec.Salsa20.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p salsa-spec
	$(FSTAR) $(ARGS) --odir salsa-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> salsa-spec/Spec_Salsa20.ml
	$(OCAMLOPT) -I salsa-spec $(OCAML_INCLUDES) $(addprefix salsa-spec/, $(EXTRACTED)) salsa-spec/Combinators.ml salsa-spec/Spec_Lib.ml salsa-spec/Spec_CTR.ml salsa-spec/Spec_Salsa20.ml -o salsa20.exe
	./salsa20.exe


clean:
	$(MAKE) -C ../code/lib/ml clean
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe poly-spec chacha-spec  salsa-spec
