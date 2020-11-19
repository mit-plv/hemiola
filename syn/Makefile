COMPILE_VS:=$(wildcard compiler/*.v)
EX_MESI_VS:=$(wildcard ex/Mesi/*.v)

.PHONY: clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(COMPILE_VS) $(EX_MESI_VS)
	$(COQBIN)coq_makefile -f _CoqProject $(COMPILE_VS) $(EX_MESI_VS) -o Makefile.coq

# MESI_EXT=ex/Mesi/MesiL1LL2Ext
# MESI_EXT=ex/Mesi/MesiL1LL4Ext
MESI_EXT=ex/Mesi/MesiL1L2LLExt
MESI_EXT_V=$(MESI_EXT).v
MESI_EXT_VO=$(MESI_EXT).vo

# BSV_EXT_HEADER_REL=./predefs/HeaderL1LL2.bsv
# BSV_EXT_HEADER_REL=./predefs/HeaderL1LL4.bsv
BSV_EXT_HEADER_REL=./predefs/HeaderL1L2LL.bsv

# BSV_EXT_IMPL_REL=./predefs/ImplL1LL2.bsv
# BSV_EXT_IMPL_REL=./predefs/ImplL1LL4.bsv
BSV_EXT_IMPL_REL=./predefs/ImplL1L2LL.bsv

BSV_EXT_IFC_REL=./predefs/Ifc.bsv

BSV_EXT_HEADER=$(realpath $(BSV_EXT_HEADER_REL))
BSV_EXT_IMPL=$(realpath $(BSV_EXT_IMPL_REL))
BSV_EXT_IFC=$(realpath $(BSV_EXT_IFC_REL))

mesi_comp: Makefile.coq
	touch $(MESI_EXT_V)
	$(MAKE) -f Makefile.coq $(MESI_EXT_VO)

BSV_EXT ?= kami/Kami/Ext/Ocaml
# BSV_EXT_FLAGS ?= -d
BSV_EXT_FLAGS ?=
BSV_TOP_NAME ?= CC
MESI_EXT_BSV_NAME ?= $(BSV_TOP_NAME).bsv

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

