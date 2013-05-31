all: 
	lhs2TeX --agda -o C.tex Report.tex
#	#C.pdf
	pdflatex C.tex

ref:	
	lhs2TeX --agda -o C.tex Report.tex
	pdflatex C.tex
	bibtex C
	pdflatex C.tex
	pdflatex C.tex

C.pdf: C.tex
#	pdflatex C.tex
	latexmk -pdf C.tex

C.tex: 
	lhs2TeX --agda -o C.tex Report.tex


#52 repetitions...
#dvipdf C.dvi
#	bibtex C
#	pdflatex C.tex
#	pdflatex C.tex
# \newcommand{\anonymous}{\kern0.06em \vbox to -1 pt {\hrule\@width.5em}}

clean:
	rm -f C.*
	rm -f `cat .gitignore`

