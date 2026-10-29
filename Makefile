.PHONY: pdf clean test

pdf:
	cd manuscript && pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
	cd manuscript && pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex

test:
	python3 -m unittest scripts/test_scaling.py

clean:
	rm -f manuscript/*.aux manuscript/*.log manuscript/*.out manuscript/*.toc \
	      manuscript/*.fls manuscript/*.fdb_latexmk manuscript/*.synctex.gz
