slides.pdf: slides.tex
	pdflatex $< -o $@

%.tex: %.lhs
	lhs2TeX $< -o $@


.PHONY: clean
clean:
	rm *.aux *.nav *.log *.out *.snm *.toc *.ptb rm slides.tex
