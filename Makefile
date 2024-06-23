all:
	agda --html --html-highlight=code MartinLof2006.lagda.md
	pandoc -B mi-header.html -A mi-footer.html --katex --standalone --css=mi-common.css -o MartinLof2006.html html/MartinLof2006.md
