# change this to your main tex file
FILENAME = description

all: main

main: *.tex
	pdflatex $(FILENAME).tex
	pdflatex $(FILENAME).tex
#	cp $(FILENAME).pdf /home/manuel/Dropbox/Public/ba_slides.pdf

#handout: *.tex
#	sed "s/%handout/handout/" $(FILENAME).tex > $(FILENAME)_handout.tex
#	pdflatex $(FILENAME)_handout.tex
#	pdflatex $(FILENAME)_handout.tex
#	rm -fv $(FILENAME)_handout.tex


clean:
	rm -fv $(FILENAME).dvi
	rm -fv $(FILENAME).ps
	rm -fv *.aux
	rm -fv $(FILENAME).log
	rm -fv *.toc
	rm -fv *.bbl
	rm -fv *.blg
	rm -fv *.glo
	rm -fv *.out
	rm -fv *.nav
	rm -fv *.snm
	rm -fv *.log
	rm -fv *.vrb
	rm -fv *~
