MFCOQ := Makefile.coq

build: $(MFCOQ)
	make -f $(MFCOQ)

$(MFCOQ): _CoqProject
	coq_makefile -f _CoqProject -o $@
