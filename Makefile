all:
	agda -i . -i /usr/local/lib/agda/src --html README.agda

clean:
	find . -type f -name '*.agdai' -delete
	rm -rf html
