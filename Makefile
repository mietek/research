all:
	agda -i src -i /usr/local/lib/agda/src --html src/Everything.agda
	cp Agda.css html/Agda.css

clean:
	find src -type f -name '*.agdai' -delete
	rm -rf html
