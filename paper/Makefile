# Build the paper.  Either tectonic (self-contained) or latexmk with a TeX Live installation.
PAPER = recaman

pdf:
	@if command -v tectonic >/dev/null; then tectonic -X compile $(PAPER).tex; \
	else latexmk -pdf $(PAPER).tex; fi

clean:
	rm -f $(PAPER).aux $(PAPER).log $(PAPER).out $(PAPER).blg $(PAPER).toc

.PHONY: pdf clean
