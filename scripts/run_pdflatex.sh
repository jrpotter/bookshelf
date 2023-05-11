#!/usr/bin/env bash

if ! command -v pdflatex > /dev/null; then
  >&2 echo 'pdflatex was not found in the current $PATH.'
  exit 1
fi

BUILD_DIR="$1"

function process_file () {
  REL_DIR=$(dirname "$1")
  REL_BASE=$(basename -s ".tex" "$1")
  mkdir -p "$BUILD_DIR/doc/$REL_DIR"
  (cd "$REL_DIR" && pdflatex "$REL_BASE.tex")
  cp "$REL_DIR/$REL_BASE.pdf" "$BUILD_DIR/doc/$REL_DIR/"
}

export BUILD_DIR
export -f process_file

# We run this command twice to allow any cross-references to resolve correctly.
# https://tex.stackexchange.com/questions/41539/does-hyperref-work-between-two-files
for _ in {1..2}; do
  find ./* \( -path build -o -path lake-packages \) -prune -o -name "*.tex" -print0 \
    | xargs -0 -I{} bash -c "process_file {}"
done
