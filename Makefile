BUILD=build
BASE=paper
TO_COPY=references.bib ACM-Reference-Format.bst acmart.cls
COPIED=$(addprefix $(BUILD)/,$(TO_COPY))

default: $(BASE).pdf

$(COPIED): $(BUILD)/% : %
	@mkdir -p $(BUILD)
	@echo "Copying $<..."
	@cp -pr $< $@

$(BUILD)/$(BASE).tex: $(BASE).lhs custom.fmt
	@mkdir -p $(BUILD)
	@echo "Generating $@..."
	@lhs2TeX --poly $< > $@

$(BUILD)/$(BASE).pdf: $(BUILD)/$(BASE).tex $(COPIED) tables/*.tex
	@mkdir -p $(BUILD)
	@echo "Rebuilding $@..."
	@(TEXINPUTS=$(TEXINPUTS):style latexmk -f -pdf -jobname=build/$(BASE) -interaction=nonstopmode $< > /dev/null 2>&1) || (echo "Error! running rubber" && rubber -I`pwd` --pdf --into $(BUILD) $<)

$(BASE).pdf: $(BUILD)/$(BASE).pdf
	@mv $< $@ # atomic update
	@cp $@ $<
	@echo "Successfully built the paper"

.PHONY: clean

arxiv: $(BUILD)/$(BASE).tex $(BUILD)/$(BASE).bbl tables/base.tex tables/c2.tex tables/c3.tex tables/c4.tex
	@rm -rf arxiv.zip
	@mkdir -p arxiv/tables
	cp $(BUILD)/$(BASE).tex $(BUILD)/$(BASE).bbl arxiv
	cp tables/base.tex tables/c2.tex tables/c3.tex tables/c4.tex arxiv/tables
	cd arxiv && zip -r ../arxiv.zip .; cd ..
	@rm -rf arxiv

clean:
	rm -rf build
	rm -rf arxiv
	rm -f arxiv.zip
