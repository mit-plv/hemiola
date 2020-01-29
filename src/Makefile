VS:=$(shell find . -type f -name '*.v')

.PHONY: lib spec msi mesi clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(COQBIN)coq_makefile -f _CoqProject $(VS) -o Makefile.coq

LIB_REPR_VO=RqRsLang.vo RqRsCorrect.vo
EX_SPEC_REPR_VO=Ex/SpecSv.vo
EX_MSI_REPR_VO=Ex/Msi/MsiSim.vo
EX_MESI_REPR_VO=Ex/Mesi/MesiSim.vo

lib: Makefile.coq
	$(MAKE) -f Makefile.coq $(LIB_REPR_VO)

spec: Makefile.coq
	$(MAKE) -f Makefile.coq $(EX_SPEC_REPR_VO)

msi: Makefile.coq
	$(MAKE) -f Makefile.coq $(EX_MSI_REPR_VO)

mesi: Makefile.coq
	$(MAKE) -f Makefile.coq $(EX_MESI_REPR_VO)

clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq
	rm -f .*.aux *.v.d *.glob *.vo *~
	rm -f */.*.aux */*.v.d */*.glob */*.vo */*~
	rm -f .coqdeps.d .lia.cache
	rm -f */.coqdeps.d */.lia.cache

clean_hard: clean
	git clean -dfx
