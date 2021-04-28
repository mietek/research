all:
	agda -i src --html src/README.agda
	cp Agda.css html/Agda.css

pub: all
	mv html html-new
	git checkout gh-pages
	git rm -rf html
	mv html-new html
	git add html
	git commit -m "Update HTML"
	git push --all
	git checkout master

clean:
	find src -type f -name '*.agdai' -delete
	rm -rf html
