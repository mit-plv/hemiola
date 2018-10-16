LIBS:=$(wildcard *.v)
EXS:=$(wildcard Ex/*.v)

.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(LIBS) $(EXS)
	$(COQBIN)coq_makefile $(LIBS) $(EXS) -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f .*.aux *.v.d *.glob *.vo *~
	rm -f */.*.aux */*.v.d */*.glob */*.vo */*~
	rm -f Makefile.coq .coqdeps.d
