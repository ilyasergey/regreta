#!/bin/sh
# Check that every `file#Lnnn` link in the markdown points at a line that exists, and
# print the line it points at, so that links can be re-checked after the sources move.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
status=0
for md in README.md docs/*.md; do
  grep -o '](\(Greta\|scripts\|test\|ocaml-ref\)[^)]*#L[0-9]*)' "$md" 2>/dev/null |
  sed 's/^](//; s/)$//' |
  while IFS= read -r link; do
    file=${link%#L*}
    line=${link##*#L}
    if [ ! -f "$file" ]; then
      echo "$md: $link — no such file"; status=1; continue
    fi
    total=$(wc -l < "$file")
    if [ "$line" -gt "$total" ]; then
      echo "$md: $link — file has only $total lines"; status=1; continue
    fi
    printf '%-24s %-28s %s\n' "$md" "$link" "$(sed -n "${line}p" "$file" | cut -c1-60)"
  done
done
exit $status
