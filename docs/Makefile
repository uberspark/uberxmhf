#
# uberXMHF documentation makefile 
# author: Amit Vasudevan (amitvasudevan@acm.org)
#

UBERXMHF_DOC_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
SPHINXBUILD   ?= sphinx-build
UBERXMHF_DOC_SOURCEDIR     = $(UBERXMHF_DOC_PATH).
UBERXMHF_DOC_BUILDDIR      = $(UBERXMHF_DOC_PATH)_build

###### targets

### common documentation build prep
.PHONY: docs_build_prep
docs_build_prep:
	mkdir -p $(UBERXMHF_DOC_PATH)/_temp
	mkdir -p $(UBERXMHF_DOC_PATH)/_build
	mkdir -p $(UBERXMHF_DOC_PATH)/_themes
	cd $(UBERXMHF_DOC_PATH)/_temp && git clone https://github.com/uberspark/uberspark-htmlcss-themes.git uberspark-htmlcss-themes.git
	cd $(UBERXMHF_DOC_PATH)/_themes && ln -sf ../_temp/uberspark-htmlcss-themes.git/rtd_uberspark/sphinx_rtd_theme/ rtd_uberspark

.PHONY: docs_pdf
docs_pdf: docs_build_prep
	@$(SPHINXBUILD) -b latex "$(UBERXMHF_DOC_SOURCEDIR)" "$(UBERXMHF_DOC_BUILDDIR)"
	@cd $(UBERXMHF_DOC_BUILDDIR) && make 

.PHONY: docs_html
docs_html: docs_build_prep
	@$(SPHINXBUILD) -b html "$(UBERXMHF_DOC_SOURCEDIR)" "$(UBERXMHF_DOC_BUILDDIR)"

.PHONY: clean
clean:
	rm -rf $(UBERXMHF_DOC_PATH)_build
	rm -rf $(UBERXMHF_DOC_PATH)_themes
	rm -rf $(UBERXMHF_DOC_PATH)_temp