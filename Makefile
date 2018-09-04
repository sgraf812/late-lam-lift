BUILD=build
BASE=paper
DEPS=$(shell find . -name "*.tex") $(shell find . -name "*.sty")

default: $(BASE).pdf

$(BUILD)/$(BASE).tex: $(BASE).lhs
	mkdir -p $(BUILD)
	lhs2TeX --poly $< > $@

$(BUILD)/$(BASE).pdf: $(BUILD)/$(BASE).tex $(DEPS)
	mkdir -p $(BUILD)
	TEXINPUTS=$(TEXINPUTS):style latexmk -f -pdf -jobname=build/$(BASE) $<

$(BASE).pdf: $(BUILD)/$(BASE).pdf
	mv $< $@ # atomic update
	cp $@ $<

.PHONY: show clean

show: $(BASE).pdf
	gnome-open $< || open $<

clean:
	rm -rf build
