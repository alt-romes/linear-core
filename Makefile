DOCNAME=report

all: simple

.PHONY: clean

simple:
	pdflatex $(DOCNAME).tex

report:
	pdflatex $(DOCNAME).tex
	bibtex 	 $(DOCNAME).aux
	pdflatex $(DOCNAME).tex
	pdflatex $(DOCNAME).tex

clean:
	rm *.blg *.bbl *.aux *.log
