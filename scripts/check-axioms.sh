#!/bin/sh
# Print the axioms the main theorems depend on.  Anything beyond Lean's own `propext`,
# `Classical.choice` and `Quot.sound` — in particular `sorryAx` — is a problem.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -t greta-axioms.XXXXXX).lean
cat > "$tmp" <<'LEAN'
import Greta
#print axioms Greta.TA.isEpsClosure_epsTable
#print axioms Greta.CFG.toTA_correct
#print axioms Greta.prodTA_lang
#print axioms Greta.greta_correct
#print axioms Greta.genTA_sound
#print axioms Greta.greta_correct_of_spec
#print axioms Greta.accepts_mono
LEAN
cd "$root" && lake env lean "$tmp"
rm -f "$tmp"
