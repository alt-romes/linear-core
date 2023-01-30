DOCNAME=report

all: $(DOCNAME).pdf

.PHONY: clean final

$(DOCNAME).pdf: $(DOCNAME).tex lwnovathesis.cls
	pdflatex $(DOCNAME).tex

final: $(DOCNAME).tex lwnovathesis.cls
	pdflatex $(DOCNAME).tex
	makeglossaries $(DOCNAME)
	bibtex 	 $(DOCNAME).aux
	pdflatex $(DOCNAME).tex
	pdflatex $(DOCNAME).tex

$(DOCNAME).tex: $(DOCNAME).lhs
	lhs2TeX $(DOCNAME).lhs -o $(DOCNAME).tex

clean:
	rm -f *.out *.blg *.bbl *.aux *.log *.toc *.ptb *.glg *.glo *.gls *.ist *.lof *.lot report.tex
