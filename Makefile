all:
	agda -i . -i /usr/local/lib/agda/src --html Everything.agda
	cp Agda.css html/Agda.css

clean:
	find . -type f -name '*.agdai' -delete
	rm -rf html
