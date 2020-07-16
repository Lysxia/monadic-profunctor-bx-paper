MFCOQ := Makefile.coq

.PHONY: build clean

build: $(MFCOQ)
	make -f $(MFCOQ)

clean:
	if [ -f $(MFCOQ) ] ; then make -f $(MFCOQ) cleanall ; rm -f $(MFCOQ) $(MFCOQ).conf ; fi

$(MFCOQ): _CoqProject
	coq_makefile -f _CoqProject -o $@
