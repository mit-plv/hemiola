FILES:=$(wildcard *.v)

.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(FILES)
	$(COQBIN)coq_makefile $(ARGS) $(FILES) -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f .*.aux *.v.d *.glob *.vo *~
	rm -f Makefile.coq .coqdeps.d
