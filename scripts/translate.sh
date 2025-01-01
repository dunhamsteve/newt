#!/bin/zsh

# script to translate a file from idris to newt
# this is just a first pass, hopefully
mkdir -p port

find src -type f -name '*.idr' | while read -r file; do
  output_file="port/${file#src/}"
  output_file="${output_file%.idr}.newt"
  mkdir -p "$(dirname "$output_file")"
  if [[ ! -f "$output_file" ]]; then
    echo "$file -> $output_file"
    perl -pe '
      s/^%.*//;
      s/\bType\b/U/g;
      s/\binterface\b/class/g;
      s/import public/import/g;
      s/^\s*covering//g;
      s/^export//g;
      s/pure \(\)/pure MkUnit/;
      s/M \(\)/M Unit/;
      s/Parser \(\)/Parser Unit/;
      s/OK \(\)/OK MkUnit/;
      s/toks,\s*com,\s*ops,\s*col/toks com ops col/;
      s/\bNat\b/Int/g;
      s/(\s+when [^\$]+\$)(.*)/\1 \\ _ =>\2/;
      s/^public export//g;
      s/\(([A-Z]\w+), ?([^)]+)\)/(\1 × \2)/g;
      s/\|\|\|/--/;
      # maybe break down an add the sugar?
      # patterns would be another option, but
      # we would need to handle overlapping ones
      s/\[\]/Nil/g;
      s/ \. / ∘ /g;
      s/\(([<>\/+]+)\)/_\1_/g;
      s/\{-/\/-/g;
      s/-\}/-\//g;
      s/\[<\]/Lin/g;
      s/\[<([^\],]+)\]/(Lin :< \1)/g;
      s/\[([^\],]+)\]/(\1 :: Nil)/g;
      s/^([A-Z].*where)/instance \1/g;
      s/^data (.*:\s*\w+)$/\1/g;
    ' "$file" > "$output_file"
  fi
done
