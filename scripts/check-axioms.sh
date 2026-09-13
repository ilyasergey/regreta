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
#print axioms Greta.intersectTA_lang
#print axioms Greta.intersectTA_lang_prodTA
#print axioms Greta.intersectTA_lang_default
#print axioms Greta.repairOnce_lang
#print axioms Greta.repairOnce_correct
#print axioms Greta.topoSort_before
#print axioms Greta.relayerOrder_ordersOf_above
#print axioms Greta.relayerOrder_replicates
#print axioms Greta.foldl_relayer_strat
#print axioms Greta.foldl_relayer_single
#print axioms Greta.learnedSpec_of_check
#print axioms Greta.fits_of_check
#print axioms Greta.genTA_sound₂_pipeline
#print axioms Greta.repairOnceSpec_correct_pipeline
#print axioms Greta.refRelayerFold_no_inversion
#print axioms Greta.refLearnOaOp_specDominated
#print axioms Greta.refGenTA_specReach
LEAN
cd "$root" && lake env lean "$tmp"
rm -f "$tmp"
