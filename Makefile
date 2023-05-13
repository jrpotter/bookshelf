all:
	@echo "Please specify a build target."

docs:
	-rm -r build/doc
	-./scripts/run_pdflatex.sh build > /dev/null
	lake build Bookshelf:docs
