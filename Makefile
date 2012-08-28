all: doc

doc:
	tools/docgen/render-doc.sh

deploy-doc:
	tools/docgen/deploy.sh

.PHONY: doc all deploy-doc
