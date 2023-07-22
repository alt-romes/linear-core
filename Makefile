DOCNAME=report

all: $(DOCNAME).pdf

.PHONY: clean final

DEPS=lwnovathesis.cls chapters/c2.tex chapters/c3.tex chapters/c4.tex chapters/c5.tex chapters/c6.tex proof.tex language/* language/proofs/* language-v2/* language-v2/proofs/*

$(DOCNAME).pdf: $(DOCNAME).tex $(DEPS)
	pdflatex $(DOCNAME).tex

final: $(DOCNAME).tex $(DEPS)
	pdflatex $(DOCNAME).tex
	makeglossaries $(DOCNAME)
	bibtex 	 $(DOCNAME).aux
	pdflatex $(DOCNAME).tex
	pdflatex $(DOCNAME).tex

%.tex: %.lhs
	lhs2TeX $< -o $@

clean:
	rm -f *.out *.blg *.bbl *.aux *.log *.toc *.ptb *.glg *.glo *.gls *.ist *.lof *.lot chapters/*.aux report.tex chapters/c2.tex chapters/c3.tex chapters/c4.tex chapters/c5.tex chapters/c6.tex
