source = src/*.agda src/Basics/*.agda src/TwoPassMerge/*.agda src/SinglePassMerge/*.agda
paper = paper/*.tex paper/llncs.cls paper/references.bib paper/splncs.bst
other = Makefile LICENSE README.md paper/dep-typed-wbl-heaps.pdf.md5sum

dist: dep-typed-wbl-heaps.tar.gz

pdf: paper/dep-typed-wbl-heaps.pdf

paper/dep-typed-wbl-heaps.pdf.md5sum: paper/dep-typed-wbl-heaps.pdf
	md5sum paper/dep-typed-wbl-heaps.pdf > paper/dep-typed-wbl-heaps.pdf.md5sum

paper/dep-typed-wbl-heaps.pdf: $(paper)
	cd paper && \
	pdflatex dep-typed-wbl-heaps.tex && \
	bibtex dep-typed-wbl-heaps.aux && \
	sed -i -e 's/\\_media/_media/' dep-typed-wbl-heaps.bbl && \
	pdflatex dep-typed-wbl-heaps.tex && \
	pdflatex dep-typed-wbl-heaps.tex

dep-typed-wbl-heaps.tar.gz: paper/dep-typed-wbl-heaps.pdf $(source) $(other)
	tar czf dep-typed-wbl-heaps.tar.gz $(source) $(paper) $(other) paper/dep-typed-wbl-heaps.pdf

clean:
	find src -name "*.agdai" | xargs rm -f
	rm -f dep-typed-wbl-heaps.tar.gz
	find paper -name "*.backup" | xargs rm -f
	find paper -name "*.tex~" | xargs rm -f
	rm -f paper/dep-typed-wbl-heaps.aux
	rm -f paper/dep-typed-wbl-heaps.bbl
	rm -f paper/dep-typed-wbl-heaps.blg
	rm -f paper/dep-typed-wbl-heaps.log
	rm -f paper/dep-typed-wbl-heaps.pdf
	rm -f paper/dep-typed-wbl-heaps.pdf.md5sum

upload: paper/dep-typed-wbl-heaps.pdf dep-typed-wbl-heaps.tar.gz
	scp dep-typed-wbl-heaps.tar.gz stolarek@ics:public_html/data/media/pl/research
	scp paper/dep-typed-wbl-heaps.pdf stolarek@ics:public_html/data/media/pl/research
