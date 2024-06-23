MAKEFLAGS += --no-builtin-rules --no-builtin-variables

.SUFFIXES :

.PHONY : all clean deepclean

MI_HTML := $(patsubst src/mi/%.lagda.md,docs/mi.%.html,$(wildcard src/mi/*.lagda.md))
MI_CSS := $(patsubst src/mi/%.css,docs/%.css,$(wildcard src/mi/*.css))
AGDA := $(shell find src -type f -name '*.agda')

all : docs/CNAME docs/index.html $(MI_HTML) $(MI_CSS) $(HTML)

docs :
	mkdir docs

docs/CNAME : CNAME | docs
	cp $< $@

docs/%.css : src/mi/%.css | docs
	cp $< $@

docs/mi.%.html : docs/mi.%.md src/mi/mi-header.html src/mi/mi-footer.html
	pandoc -B src/mi/mi-header.html -A src/mi/mi-footer.html --katex --standalone --css=mi-common.css --css=mi-layout.css -o $@ $<

docs/mi.%.md : src/mi/%.lagda.md
	agda -i src --html --html-dir=docs --html-highlight=auto --css=mi-common.css $<

docs/index.html : $(AGDA)
	agda -i src --html --html-dir=docs --html-highlight=auto --css=mi-common.css src/index.agda

clean :
	-rm -r docs

deepclean : clean
	find src -type f -name '*.agdai' -delete
