EXAMPLES = first.html primitives.html datafun.html interp.html iofns.html \
           stdlib.html views.html theorems.html provisional.html donotation.html \
           specialise.html foreign.html
SRCS = first.idr primitives.idr datafun.idr interp.idr iofns.idr \
       stdlib.idr views.idr theorems.idr provisional.idr donotation.idr \
       specialise.idr foreign.idr

site: $(EXAMPLES) tutorial.html 

install: site
	scp $(EXAMPLES) $(SRCS) tutorial.html tutorial.css eb@home-staff.cs.st-and.ac.uk:public_html/Idris

clean: .PHONY
	rm -f $(EXAMPLES)

%.html: %.idr
	idris $< --cmd ':H $< $@ tutorial.css'

%.tex: %.idr
	idris $< --cmd ':L $< $@ tutorial.css'

%.pdf: %.tex
	pdflatex $<

.PHONY: