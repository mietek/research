all:
	agda -i src --html --html-dir=docs --css=AgdaPP.css src/README.agda

clean:
	find src -type f -name '*.agdai' -delete
