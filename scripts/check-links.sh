#!/bin/sh
# Check every `[`Name`](file#Lnnn)` link in the markdown: the file must exist, the line
# must exist, and the line must declare the identifier named in the link text (its last
# dot-separated component).  Prints each link with the line it points at.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
tmp=$(mktemp)
for md in README.md docs/*.md; do
  dir=$(dirname "$md")
  # link text (may be empty for bare links), path, line
  grep -o '\[[^]]*\](\.\{0,2\}[./A-Za-z0-9_-]*#L[0-9]*)' "$md" 2>/dev/null |
    sed 's/^\[\(.*\)\](\(.*\)#L\([0-9]*\))$/\1\t\2\t\3/' |
    while IFS="$(printf '\t')" read -r text link line; do
      printf '%s\t%s\t%s\t%s\t%s\n' "$md" "$dir" "$text" "$link" "$line"
    done
done > "$tmp"
status=0
while IFS="$(printf '\t')" read -r md dir text file line; do
  case $file in /*) path=$file ;; *) path="$dir/$file" ;; esac
  if [ ! -f "$path" ]; then
    echo "$md: $file#L$line — no such file ($path)"; status=1; continue
  fi
  total=$(wc -l < "$path")
  if [ "$line" -gt "$total" ]; then
    echo "$md: $file#L$line — file has only $total lines"; status=1; continue
  fi
  target=$(sed -n "${line}p" "$path")
  # The identifier: strip backticks, take the last dot-separated component.
  ident=$(printf '%s' "$text" | tr -d '`' | sed 's/.*\.//')
  if [ -n "$ident" ] && ! printf '%s' "$target" | grep -q -F -- "$ident"; then
    echo "$md: $file#L$line — line does not mention '$ident': $(printf '%s' "$target" | cut -c1-60)"
    status=1; continue
  fi
  printf '%-24s %-36s %s\n' "$md" "$file#L$line" "$(printf '%s' "$target" | cut -c1-56)"
done < "$tmp"
rm -f "$tmp"
exit $status
