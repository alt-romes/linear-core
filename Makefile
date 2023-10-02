DOCNAME=report

all: $(DOCNAME).pdf

.PHONY: clean final

DEPS=lwnovathesis.cls references.bib chapters/c2.tex chapters/c3.tex chapters/c4.tex chapters/c5.tex chapters/c6.tex chapters/c7.tex chapters/c8.tex proof.tex language/* language/proofs/* language-v2/* language-v3/* language-v4/* language-v4/proofs/* language-v4/proofs/optimizations/* prototype/core-plugin-results.tex

# and all_proofs.tex

all_proofs.tex: language-v3/Proofs.hs
	./$<

$(DOCNAME).pdf: $(DOCNAME).tex $(DEPS)
	pdflatex $(DOCNAME).tex

final: $(DOCNAME).tex $(DEPS)
	pdflatex $(DOCNAME).tex
	# makeglossaries $(DOCNAME)
	bibtex 	 $(DOCNAME).aux
	pdflatex $(DOCNAME).tex
	pdflatex $(DOCNAME).tex
	@echo
	@echo "-----WARNING-------------------------------------------------------"
	@echo "Be sure to include the cover pdf and remove from draft mode, etc..."
	@echo "-------------------------------------------------------------------"

%.tex: %.lhs
	lhs2TeX $< -o $@

clean:
	rm -f *.out *.blg *.bbl *.aux *.log *.toc *.ptb *.glg *.glo *.gls *.ist *.lof *.lot chapters/*.aux report.tex chapters/c2.tex chapters/c3.tex chapters/c4.tex chapters/c5.tex chapters/c6.tex chapters/c7.tex chapters/c8.tex
