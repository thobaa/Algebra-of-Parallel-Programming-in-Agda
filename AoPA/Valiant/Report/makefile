all: 
	lhs2TeX --agda -o C.tex Report.tex
	pdflatex C.tex
	bibtex C
	pdflatex C.tex
	pdflatex C.tex
clean:
	rm -f C.*