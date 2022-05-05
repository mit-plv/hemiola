COMPILE_VS:=$(wildcard compiler/*.v)
EX_MESI_VS:=$(wildcard ex/Mesi/*.v)

.PHONY: clean

Makefile.coq: Makefile $(COMPILE_VS) $(EX_MESI_VS)
	$(COQBIN)coq_makefile -f _CoqProject $(COMPILE_VS) $(EX_MESI_VS) -o Makefile.coq

MESI_L2_EXT=ex/Mesi/MesiL1LL4Ext
MESI_L2_EXT_V=$(MESI_L2_EXT).v
MESI_L2_EXT_VO=$(MESI_L2_EXT).vo
MESI_L2_BSV_EXT_HEADER_REL=./predefs/HeaderL1LL4.bsv
MESI_L2_BSV_EXT_IMPL_REL=./predefs/ImplL1LL4.bsv
MESI_L2_BSV_EXT_HEADER=$(realpath $(MESI_L2_BSV_EXT_HEADER_REL))
MESI_L2_BSV_EXT_IMPL=$(realpath $(MESI_L2_BSV_EXT_IMPL_REL))

MESI_L3_EXT=ex/Mesi/MesiL1L2LLExt
MESI_L3_EXT_V=$(MESI_L3_EXT).v
MESI_L3_EXT_VO=$(MESI_L3_EXT).vo
MESI_L3_BSV_EXT_HEADER_REL=./predefs/HeaderL1L2LL.bsv
MESI_L3_BSV_EXT_IMPL_REL=./predefs/ImplL1L2LL.bsv
MESI_L3_BSV_EXT_HEADER=$(realpath $(MESI_L3_BSV_EXT_HEADER_REL))
MESI_L3_BSV_EXT_IMPL=$(realpath $(MESI_L3_BSV_EXT_IMPL_REL))

BSV_EXT_IFC_REL=./predefs/Ifc.bsv
BSV_EXT_IFC=$(realpath $(BSV_EXT_IFC_REL))

mesi_l2_comp: Makefile.coq
	touch $(MESI_L2_EXT_V)
	$(MAKE) -f Makefile.coq $(MESI_L2_EXT_VO)

mesi_l3_comp: Makefile.coq
	touch $(MESI_L3_EXT_V)
	$(MAKE) -f Makefile.coq $(MESI_L3_EXT_VO)

BSV_EXT ?= kami/Kami/Ext/Ocaml
BSV_EXT_FLAGS ?=
BSV_TOP_NAME ?= CC
MESI_EXT_BSV_NAME ?= $(BSV_TOP_NAME).bsv

mesi_l2_bsv: mesi_l2_comp
	mv Target.ml* $(BSV_EXT)
	$(MAKE) -C $(BSV_EXT)
	cd $(BSV_EXT); ./Main.native $(BSV_EXT_FLAGS) \
	-header $(MESI_L2_BSV_EXT_HEADER) -top $(BSV_TOP_NAME) -top-ifc $(BSV_EXT_IFC) -top-impl $(MESI_L2_BSV_EXT_IMPL) \
	$(MESI_EXT_BSV_NAME)
	mv $(BSV_EXT)/$(MESI_EXT_BSV_NAME) ./

mesi_l3_bsv: mesi_l3_comp
	mv Target.ml* $(BSV_EXT)
	$(MAKE) -C $(BSV_EXT)
	cd $(BSV_EXT); ./Main.native $(BSV_EXT_FLAGS) \
	-header $(MESI_L3_BSV_EXT_HEADER) -top $(BSV_TOP_NAME) -top-ifc $(BSV_EXT_IFC) -top-impl $(MESI_L3_BSV_EXT_IMPL) \
	$(MESI_EXT_BSV_NAME)
	mv $(BSV_EXT)/$(MESI_EXT_BSV_NAME) ./

clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq Makefile.coq.conf
	rm -f */.*.aux */*.v.d */*.glob */*.vo */*.vos */*.vok */*~
	rm -f .coqdeps.d .lia.cache

