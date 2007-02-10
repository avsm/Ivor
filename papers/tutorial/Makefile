all: tutorial.pdf

SOURCES = tutorial.tex introduction.tex programming.tex theoremproving.tex \
          hslibrary.tex

tutorial.pdf: $(SOURCES)
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

.PHONY:
