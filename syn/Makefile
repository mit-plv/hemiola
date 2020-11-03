VS:=$(shell find . -type f -name '*.v')

.PHONY: clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(COQBIN)coq_makefile -f _CoqProject $(VS) -o Makefile.coq

MSI_EXT=ex/Msi/MsiExt
MSI_EXT_V=$(MSI_EXT).v
MSI_EXT_VO=$(MSI_EXT).vo

MESI_EXT=ex/Mesi/MesiL1LL2Ext
MESI_EXT_V=$(MESI_EXT).v
MESI_EXT_VO=$(MESI_EXT).vo

BSV_EXT_HEADER_REL=./predefs/Header.bsv

BSV_EXT_IMPL_REL=./predefs/ImplL1LL2.bsv
BSV_EXT_IFC_REL=./predefs/Ifc.bsv

BSV_EXT_HEADER=$(realpath $(BSV_EXT_HEADER_REL))
BSV_EXT_IMPL=$(realpath $(BSV_EXT_IMPL_REL))
BSV_EXT_IFC=$(realpath $(BSV_EXT_IFC_REL))

msi_comp: Makefile.coq
	touch $(MSI_EXT_V)
	$(MAKE) -f Makefile.coq $(MSI_EXT_VO)

mesi_comp: Makefile.coq
	touch $(MESI_EXT_V)
	$(MAKE) -f Makefile.coq $(MESI_EXT_VO)

BSV_EXT ?= kami/Kami/Ext/Ocaml
BSV_EXT_FLAGS ?= -d
BSV_TOP_NAME ?= CC
MSI_EXT_BSV_NAME ?= $(BSV_TOP_NAME).bsv
MESI_EXT_BSV_NAME ?= $(BSV_TOP_NAME).bsv

msi_bsv: msi_comp
	mv Target.ml* $(BSV_EXT)
	$(MAKE) -C $(BSV_EXT)
	cd $(BSV_EXT); ./Main.native $(BSV_EXT_FLAGS) \
	-header $(BSV_EXT_HEADER) -top $(BSV_TOP_NAME) -top-ifc $(BSV_EXT_IFC) -top-impl $(BSV_EXT_IMPL) \
	$(MSI_EXT_BSV_NAME)
	mv $(BSV_EXT)/$(MSI_EXT_BSV_NAME) ./

mesi_bsv: mesi_comp
	mv Target.ml* $(BSV_EXT)
	$(MAKE) -C $(BSV_EXT)
	cd $(BSV_EXT); ./Main.native $(BSV_EXT_FLAGS) \
	-header $(BSV_EXT_HEADER) -top $(BSV_TOP_NAME) -top-ifc $(BSV_EXT_IFC) -top-impl $(BSV_EXT_IMPL) \
	$(MESI_EXT_BSV_NAME)
	mv $(BSV_EXT)/$(MESI_EXT_BSV_NAME) ./

clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq Makefile.coq.conf
	rm -f */.*.aux */*.v.d */*.glob */*.vo */*.vos */*.vok */*~
	rm -f .coqdeps.d .lia.cache

