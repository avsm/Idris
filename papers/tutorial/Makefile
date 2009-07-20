all: tutorial.pdf

SOURCES = tutorial.tex literature.bib intro.tex firstex.tex features.tex example.tex

tutorial.pdf: ${SOURCES}
#	dvipdf tutorial.dvi
	pdflatex tutorial
	-bibtex tutorial
	-pdflatex tutorial

tutorial.ps: tutorial.dvi
	dvips -o tutorial.ps tutorial

tutorial.dvi: $(SOURCES)
	-latex tutorial
	-bibtex tutorial
	-latex tutorial
	-latex tutorial

#package: tutorial.tar

#tutorial.tar: tutorial.dvi tutorial.ps tutorial.pdf .PHONY
#	mkdir -p tutorial
#	cp ../bib/*.bib *.tex *.ltx *.bib *.ps *.pdf *.dvi *.cls tutorial
#	tar cvf tutorial.tar tutorial

.PHONY:
