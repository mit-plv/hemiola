VS:=$(shell find . -type f -name '*.v')

.PHONY: clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(COQBIN)coq_makefile -f _CoqProject $(VS) -o Makefile.coq

MSI_EXT_VO=ex/Msi/MsiExt.vo

# MESI_EXT_VO=ex/Mesi/MesiL1L2LLExt.vo
MESI_EXT_VO=ex/Mesi/MesiL1LL4Ext.vo
# BSV_EXT_HEADER=HeaderL1L2LL4.bsv
BSV_EXT_HEADER=HeaderL1LL4.bsv
# BSV_EXT_INIT=ImplL1L2LL4.bsv
BSV_EXT_INIT=ImplL1LL4.bsv

msi_comp: Makefile.coq
	$(MAKE) -f Makefile.coq $(MSI_EXT_VO)

mesi_comp: Makefile.coq
	$(MAKE) -f Makefile.coq $(MESI_EXT_VO)

BSV_EXT ?= kami/Kami/Ext/Ocaml
BSV_EXT_FLAGS ?=
BSV_TOP_NAME ?= CC
MSI_EXT_BSV_NAME ?= $(BSV_TOP_NAME).bsv
MESI_EXT_BSV_NAME ?= $(BSV_TOP_NAME).bsv

msi_bsv: msi_comp
	mv Target.ml* $(BSV_EXT)
	$(MAKE) -C $(BSV_EXT)
	cd $(BSV_EXT); ./Main.native $(BSV_EXT_FLAGS) \
	-header $(BSV_EXT_HEADER) -top $(BSV_TOP_NAME) -top-impl $(BSV_EXT_INIT) \
	$(MSI_EXT_BSV_NAME)
	mv $(BSV_EXT)/$(MSI_EXT_BSV_NAME) ./

mesi_bsv: mesi_comp
	mv Target.ml* $(BSV_EXT)
	$(MAKE) -C $(BSV_EXT)
	cd $(BSV_EXT); ./Main.native $(BSV_EXT_FLAGS) \
	-header $(BSV_EXT_HEADER) -top $(BSV_TOP_NAME) -top-impl $(BSV_EXT_INIT) \
	$(MESI_EXT_BSV_NAME)
	mv $(BSV_EXT)/$(MESI_EXT_BSV_NAME) ./

clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq Makefile.coq.conf
	rm -f */.*.aux */*.v.d */*.glob */*.vo */*.vos */*.vok */*~
	rm -f .coqdeps.d .lia.cache

