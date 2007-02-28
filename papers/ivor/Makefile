all: ivor.pdf

SOURCES = ivor.tex intro.tex corett.tex tactics.tex code.tex \
          examples.tex conclusions.tex ../bib/literature.bib

ivor.pdf: $(SOURCES)
	pdflatex ivor
	-bibtex ivor
	-pdflatex ivor

ivor.ps: ivor.dvi
	dvips -o ivor.ps ivor

ivor.dvi: $(SOURCES)
	-latex ivor
	-bibtex ivor
	-latex ivor
	-latex ivor

package: ifl06.tar

ifl06.tar: ivor.dvi ivor.ps ivor.pdf .PHONY
	mkdir -p ifl06
	cp ../bib/*.bib *.tex *.ltx *.bib *.ps *.pdf *.dvi *.cls ifl06
	tar cvf ivor06.tar ifl06

.PHONY:
