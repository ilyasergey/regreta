#!/bin/sh
# Stage the Greta reference implementation for the differential-testing driver.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
repo=https://github.com/verse-lab/greta.git
commit=a62d6b68a92178eb2f1bd57b620386e5a2cdc1b6

if [ ! -d "$here/.greta/.git" ]; then
  echo "cloning $repo"
  git clone --quiet "$repo" "$here/.greta"
fi
git -C "$here/.greta" fetch --quiet origin
git -C "$here/.greta" checkout --quiet "$commit"

mkdir -p "$here/src"
for m in ta.ml cfg.ml cfgutils.ml utils.ml treeutils.ml pp.ml learner.ml operation.ml converter.ml; do
  cp "$here/.greta/lib/$m" "$here/src/$m"
done

cat > "$here/src/dune" <<'DUNE'
; The staged upstream modules.  Warnings are disabled: this is third-party code that we
; build out of its original dune context, and we do not want to patch it.
(library
 (name gretacore)
 (libraries str)
 (flags (:standard -rectypes -w -a)))
DUNE

echo "staged $(ls "$here/src"/*.ml | wc -l | tr -d ' ') modules in src/"
