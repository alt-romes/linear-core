DOCNAME=report

all: $(DOCNAME).pdf

.PHONY: clean

# $(DOCNAME).pdf: $(DOCNAME).tex
# 	pdflatex $(DOCNAME).tex

$(DOCNAME).pdf: $(DOCNAME).tex
	pdflatex $(DOCNAME).tex
	bibtex 	 $(DOCNAME).aux
	pdflatex $(DOCNAME).tex
	pdflatex $(DOCNAME).tex

$(DOCNAME).tex: $(DOCNAME).lhs
	lhs2TeX $(DOCNAME).lhs -o $(DOCNAME).tex

clean:
	rm -f *.out *.blg *.bbl *.aux *.log *.toc *.ptb report.tex
