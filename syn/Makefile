VS:=$(shell find . -type f -name '*.v')

.PHONY: clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(COQBIN)coq_makefile -f _CoqProject $(VS) -o Makefile.coq

clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq Makefile.coq.conf
	rm -f .*.aux *.v.d *.glob *.vo *.vos *.vok *~
	rm -f .coqdeps.d .lia.cache

