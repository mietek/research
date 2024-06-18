all:
	agda --html --html-highlight=code AC.lagda.md && pandoc html/AC.md -f markdown+tex_math_dollars+yaml_metadata_block -o AC.html --standalone --katex --css=AC.css -B AC-before.html -A AC-after.html
