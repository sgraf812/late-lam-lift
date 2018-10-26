BUILD=build
BASE=paper

default: $(BASE).pdf

$(BUILD)/references.bib: references.bib
	mkdir -p $(BUILD)
	cp references.bib $(BUILD)/references.bib

$(BUILD)/$(BASE).tex: $(BASE).lhs custom.fmt
	mkdir -p $(BUILD)
	lhs2TeX --poly $< > $@

$(BUILD)/$(BASE).pdf: $(BUILD)/$(BASE).tex $(BUILD)/references.bib tables/ll-nofib-table.tex
	mkdir -p $(BUILD)
	(TEXINPUTS=$(TEXINPUTS):style latexmk -f -pdf -jobname=build/$(BASE) -interaction=nonstopmode $< > /dev/null 2>&1) || (echo "Error! running rubber" && rubber -I`pwd` --pdf --into $(BUILD) $<)

$(BASE).pdf: $(BUILD)/$(BASE).pdf
	mv $< $@ # atomic update
	cp $@ $<

.PHONY: clean

clean:
	rm -rf build
