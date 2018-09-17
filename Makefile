BUILD=build
BASE=paper

default: $(BASE).pdf

$(BUILD)/references.bib: references.bib
	mkdir -p $(BUILD)
	cp references.bib $(BUILD)/references.bib

$(BUILD)/$(BASE).tex: $(BASE).lhs custom.fmt
	mkdir -p $(BUILD)
	lhs2TeX --poly $< > $@

$(BUILD)/$(BASE).pdf: $(BUILD)/$(BASE).tex references.bib $(BUILD)/references.bib
	mkdir -p $(BUILD)
	TEXINPUTS=$(TEXINPUTS):style latexmk -f -pdf -jobname=build/$(BASE) -interaction=nonstopmode $< # Add -xelatex when using the Biber backend

$(BASE).pdf: $(BUILD)/$(BASE).pdf
	mv $< $@ # atomic update
	cp $@ $<

.PHONY: show clean

show: $(BASE).pdf
	xdg-open $< || open $<

clean:
	rm -rf build
