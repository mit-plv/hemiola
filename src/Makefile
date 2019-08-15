VS:=$(shell find . -type f -name '*.v')

.PHONY: lib ex msisv clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

DEPS=-R . Top

Makefile.coq: Makefile $(VS)
	$(COQBIN)coq_makefile $(VS) $(DEPS) -o Makefile.coq

LIB_REPR_VO=RqRsLang.vo RqRsCorrect.vo
EX_SPEC_REPR_VO=Ex/SpecSv.vo
EX_MSISV_REPR_VO=Ex/MsiSv/MsiSvSim.vo
EX_MESI_REPR_VO=Ex/Mesi/MesiSim.vo
EX_MOSI_REPR_VO=Ex/Mosi/Mosi.vo

lib: Makefile.coq
	$(MAKE) -f Makefile.coq $(LIB_REPR_VO)

spec: Makefile.coq
	$(MAKE) -f Makefile.coq $(EX_SPEC_REPR_VO)

msisv: Makefile.coq
	$(MAKE) -f Makefile.coq $(EX_MSISV_REPR_VO)

mesi: Makefile.coq
	$(MAKE) -f Makefile.coq $(EX_MESI_REPR_VO)

mosi: Makefile.coq
	$(MAKE) -f Makefile.coq $(EX_MOSI_REPR_VO)

clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq
	rm -f .*.aux *.v.d *.glob *.vo *~
	rm -f */.*.aux */*.v.d */*.glob */*.vo */*~
	rm -f .coqdeps.d .lia.cache
	rm -f */.coqdeps.d */.lia.cache
