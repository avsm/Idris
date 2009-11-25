EXAMPLES = first.html primitives.html datafun.html
SRCS = first.idr primitives.idr datafun.idr

site: $(EXAMPLES) tutorial.html 

install: site
	scp $(EXAMPLES) $(SRCS) tutorial.html tutorial.css eb@home-staff:public_html/Idris

%.html: %.idr
	idris $< --cmd ':H $< $@ tutorial.css'

%.tex: %.idr
	idris $< --cmd ':L $< $@ tutorial.css'

%.pdf: %.tex
	pdflatex $<


