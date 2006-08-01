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

.PHONY:
