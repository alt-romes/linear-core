INCLUDES = /Users/romes/Developer/beamer-theme/includes

slides.pdf: slides.tex
	TEXINPUTS=$(INCLUDES):.: pdflatex $< -o $@

%.tex: %.lhs
	LHS2TEXINPUTS=$(INCLUDES) /Users/romes/.local/bin/lhs2TeX -P$(INCLUDES): $< -o $@


.PHONY: clean
clean:
	rm *.aux *.nav *.log *.out *.snm *.toc *.ptb rm slides.tex
