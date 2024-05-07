all:
	find docs -type f -name '*.html' -delete
	agda -i src --html --html-dir=docs --css=AgdaPP.css src/index.agda

clean:
	find src -type f -name '*.agdai' -delete
