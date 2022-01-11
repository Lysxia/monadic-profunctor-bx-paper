MFCOQ := Makefile.coq

.PHONY: build clean doc html

build: $(MFCOQ)
	$(MAKE) -f $(MFCOQ)

doc: html

clean:
	if [ -f $(MFCOQ) ] ; then $(MAKE) -f $(MFCOQ) cleanall ; rm -f $(MFCOQ) $(MFCOQ).conf ; fi

$(MFCOQ): _CoqProject
	coq_makefile -f _CoqProject -o $@

## coqdoc
TITLE:="Profmonads"
COQDOCFLAGS:= \
  -t $(TITLE) \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments

COQDOCJS_DIR=$(wildcard coqdocjs)

ifneq ($(COQDOCJS_DIR),)
COQDOCFLAGS+=--with-header $(COQDOCJS_DIR)/extra/header.html --with-footer $(COQDOCJS_DIR)/extra/footer.html

html: html-raw
	cp $(COQDOCJS_DIR)/extra/resources/* html/
else
html: html-raw
endif

export COQDOCFLAGS

html-raw:
	$(MAKE) -f $(MFCOQ) html
