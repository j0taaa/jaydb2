ROOT := $(abspath ..)
OUT := $(ROOT)/.build/tcc
export BIBINPUTS := $(CURDIR):
export BSTINPUTS := $(CURDIR):
.PHONY: all evidence article slides slides-html reader-assets clean
all: article slides
evidence:
	python3 -B evidence.py
	mkdir -p $(OUT)/output
article: evidence
	pdflatex -halt-on-error -interaction=nonstopmode -output-directory=$(OUT) main.tex
	cd $(OUT) && bibtex main
	pdflatex -halt-on-error -interaction=nonstopmode -output-directory=$(OUT) main.tex
	pdflatex -halt-on-error -interaction=nonstopmode -output-directory=$(OUT) main.tex
	pdflatex -halt-on-error -interaction=nonstopmode -output-directory=$(OUT) main.tex
	cp $(OUT)/main.pdf $(OUT)/output/jaydb2-tcc.pdf
slides: evidence
	python3 -B build_presentation.py
slides-html: evidence
	python3 -B build_presentation.py --html-only
reader-assets: all
	python3 -B build_reader_assets.py
clean:
	rm -f $(OUT)/*.aux $(OUT)/*.bbl $(OUT)/*.blg $(OUT)/*.log $(OUT)/*.nav $(OUT)/*.out $(OUT)/*.snm $(OUT)/*.toc
