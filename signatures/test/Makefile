all: headers
	echo `-R . AutosubstTestSuite` > _CoqProject
	ls -1a *.v >> _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
	$(MAKE) -f Makefile.coq

headers:
	cp ../../headers/*.v .


