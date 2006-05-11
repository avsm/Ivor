all: humett.pdf

SOURCES = humett.tex dtp.bib macros.ltx library.ltx local.ltx \
          intro.tex tt.tex interface.tex shell.tex tactics.tex \
          combinators.tex conclusion.tex

humett.pdf: $(SOURCES)
	pdflatex humett
	-bibtex humett
	-pdflatex humett

humett.ps: humett.dvi
	dvips -o humett.ps humett

humett.dvi: $(SOURCES)
	-latex humett
	-bibtex humett
	-latex humett
	-latex humett

clean:
	rm -f *.dvi *.pdf *.aux *.bbl *.blg *.log