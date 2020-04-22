VS:=$(shell find . -type f -name '*.v')

.PHONY: clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(COQBIN)coq_makefile -f _CoqProject $(VS) -o Makefile.coq

MESI_EXT_VO=ex/Mesi/MesiExt.vo

mesi_comp: Makefile.coq
	$(MAKE) -f Makefile.coq $(MESI_EXT_VO)

BSV_EXT ?= kami/Kami/Ext/Ocaml
MESI_EXT_BSV_NAME ?= Mem.bsv

mesi_bsv: mesi_comp
	mv Target.ml* $(BSV_EXT)
	$(MAKE) -C $(BSV_EXT)
	cd $(BSV_EXT); ./Main.native -d -top Mem $(MESI_EXT_BSV_NAME)
	mv $(BSV_EXT)/$(MESI_EXT_BSV_NAME) .

clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq Makefile.coq.conf
	rm -f .*.aux *.v.d *.glob *.vo *.vos *.vok *~
	rm -f .coqdeps.d .lia.cache

