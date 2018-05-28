.PHONY: build test

build: Makefile.coq
	make -f $<

test: build
	coqc -Q src/ Pseudorandom test/test.v

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@
