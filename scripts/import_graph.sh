#!/bin/bash

# The first pass of this was LLM generated for expediency

# scan the src directory for *.newt files
# match lines like `import Foo.Bar.Baz`
# use graphviz to create a dependency graph in a pdf file

SRC_DIR="/Users/dunham/prj/newt/src"
OUTPUT_FILE="/Users/dunham/prj/newt/dependency_graph.pdf"

TEMP_FILE=$(mktemp)
trap 'rm -f "$TEMP_FILE"' EXIT

echo "digraph dependencies {" > "$TEMP_FILE"

# GPT4 did the first version of this, I wasn't familiar with "read"
find "$SRC_DIR" -name "*.newt" | while read -r file; do
  grep -Eo '^import [A-Za-z0-9.]+' "$file" | egrep -v 'Prelude|Data' | while read -r line; do
    module=$(echo "$file" | sed "s|$SRC_DIR/||; s|/|.|g; s|.newt$||")
    imported_module=$(echo "$line" | awk '{print $2}')
    echo "  \"$module\" -> \"$imported_module\";" >> "$TEMP_FILE"
  done
done

# End the graphviz dot file
echo "}" >> "$TEMP_FILE"

# Generate the PDF using dot
dot -Tpdf "$TEMP_FILE" -o "$OUTPUT_FILE"

echo "Dependency graph created at $OUTPUT_FILE"
