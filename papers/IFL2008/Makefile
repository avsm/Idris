all: ifl08.pdf

SOURCES = ifl08.tex literature.bib intro.tex examples.tex interactive.tex \
  casestudy.tex ioforeign.tex conclusion.tex

ifl08.pdf: ${SOURCES}
#	dvipdf ifl08.dvi
	pdflatex ifl08
	-bibtex ifl08
	-pdflatex ifl08

ifl08.ps: ifl08.dvi
	dvips -o ifl08.ps ifl08

ifl08.dvi: $(SOURCES)
	-latex ifl08
	-bibtex ifl08
	-latex ifl08
	-latex ifl08

#package: ifl08.tar

#ifl08.tar: ifl08.dvi ifl08.ps ifl08.pdf .PHONY
#	mkdir -p ifl08
#	cp ../bib/*.bib *.tex *.ltx *.bib *.ps *.pdf *.dvi *.cls ifl08
#	tar cvf ifl08.tar ifl08

.PHONY:
