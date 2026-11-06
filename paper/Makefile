ROOT := $(abspath ..)
OUT := $(ROOT)/.build/tcc
.PHONY: all evidence article slides clean
all: article slides
evidence:
	python3 -B evidence.py
	mkdir -p $(OUT)/output
article: evidence
	pdflatex -halt-on-error -interaction=nonstopmode -output-directory=$(OUT) main.tex
	pdflatex -halt-on-error -interaction=nonstopmode -output-directory=$(OUT) main.tex
	cp $(OUT)/main.pdf $(OUT)/output/jaydb2-tcc.pdf
slides: evidence
	pdflatex -halt-on-error -interaction=nonstopmode -output-directory=$(OUT) slides.tex
	pdflatex -halt-on-error -interaction=nonstopmode -output-directory=$(OUT) slides.tex
	cp $(OUT)/slides.pdf $(OUT)/output/jaydb2-defense.pdf
clean:
	rm -f $(OUT)/*.aux $(OUT)/*.log $(OUT)/*.nav $(OUT)/*.out $(OUT)/*.snm $(OUT)/*.toc
