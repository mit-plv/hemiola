LIB:=$(wildcard *.v)
EX:=$(wildcard Ex/*.v)
MSISV:=$(wildcard Ex/MsiSv/*.v)

.PHONY: lib ex msisv clean

lib: Makefile.coq.lib
	$(MAKE) -f Makefile.coq.lib

Makefile.coq.lib: Makefile $(LIB)
	$(COQBIN)coq_makefile $(LIB) -o Makefile.coq.lib

ex: Makefile.coq.ex
	$(MAKE) -f Makefile.coq.ex

Makefile.coq.ex: Makefile $(LIB) $(EX)
	$(COQBIN)coq_makefile $(LIB) $(EX) -o Makefile.coq.ex

msisv: Makefile.coq.msisv
	$(MAKE) -f Makefile.coq.msisv

Makefile.coq.msisv: Makefile $(LIB) $(EX) $(MSISV)
	$(COQBIN)coq_makefile $(LIB) $(EX) $(MSISV) -o Makefile.coq.msisv

clean:
	$(MAKE) -f Makefile.coq.msisv clean || $(MAKE) -f Makefile.coq.ex clean || $(MAKE) -f Makefile.coq.lib clean
	rm -f .*.aux *.v.d *.glob *.vo *~
	rm -f */.*.aux */*.v.d */*.glob */*.vo */*~
	rm -f Makefile.coq.*
	rm -f .coqdeps.d
