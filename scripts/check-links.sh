#!/bin/sh
# Check that every `file#Lnnn` link in the markdown points at a line that exists, and
# print the line it points at, so links can be re-checked after the sources move.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
tmp=$(mktemp)
for md in README.md docs/*.md; do
  dir=$(dirname "$md")
  grep -o '](\.\{0,2\}[./A-Za-z0-9_-]*#L[0-9]*)' "$md" 2>/dev/null |
    sed 's/^](//; s/)$//' |
    while IFS= read -r link; do
      printf '%s\t%s\t%s\n' "$md" "$dir" "$link"
    done
done > "$tmp"
status=0
while IFS="$(printf '\t')" read -r md dir link; do
  file=${link%#L*}
  line=${link##*#L}
  case $file in /*) path=$file ;; *) path="$dir/$file" ;; esac
  if [ ! -f "$path" ]; then
    echo "$md: $link — no such file ($path)"; status=1; continue
  fi
  total=$(wc -l < "$path")
  if [ "$line" -gt "$total" ]; then
    echo "$md: $link — file has only $total lines"; status=1; continue
  fi
  printf '%-24s %-34s %s\n' "$md" "$link" "$(sed -n "${line}p" "$path" | cut -c1-56)"
done < "$tmp"
rm -f "$tmp"
exit $status
