all:
	@echo "Please specify a build target."

docs:
	-ls build/doc | \
		grep -v -E 'Init|Lean|Mathlib' | \
		xargs -I {} rm -r "build/doc/{}"
	-./scripts/run_pdflatex.sh build > /dev/null
	lake build Bookshelf:docs

docs!:
	-rm -r build/doc
	-./scripts/run_pdflatex.sh build > /dev/null
	lake build Bookshelf:docs
