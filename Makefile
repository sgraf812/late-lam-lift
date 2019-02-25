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

clean:
	rm -rf build
