#!/bin/sh
# Differential test: run the Lean formalisation and the OCaml reference implementation on
# the same inputs and compare.  See docs/testing.md and docs/divergences.md.
#
#   scripts/difftest.sh             run every check
#   GRETA_REF_TIMEOUT=60 ...        change the watchdog on the reference implementation
#
# Cases listed in test/expected-divergences.txt are reported as "known" rather than as
# failures; the script exits non-zero only when something diverges that we did not expect.
set -u

root=$(cd "$(dirname "$0")/.." && pwd)
lean="$root/.lake/build/bin/greta"
ref="$root/ocaml-ref/_build/default/driver/main.exe"
out="$root/test/out"
expected="$root/test/expected-divergences.txt"
: "${GRETA_REF_TIMEOUT:=30}"
export GRETA_REF_TIMEOUT

pass=0; fail=0; known=0

ok()   { pass=$((pass+1)); printf '  ok       %s\n' "$*"; }
bad()  { fail=$((fail+1)); printf '  FAIL     %s\n' "$*"; }
note() { known=$((known+1)); printf '  known    %s\n' "$*"; }

# A case is "known" when its label appears in the expectations file.
is_expected() {
  [ -f "$expected" ] || return 1
  grep -q -x -F -- "$1" "$expected"
}

report() {  # report LABEL OK_MESSAGE FAIL_MESSAGE
  if [ "$2" = "ok" ]; then
    if is_expected "$1"; then
      bad "$1: expected a divergence, but the two agree — update $expected"
    else
      ok "$1${3:+: $3}"
    fi
  else
    if is_expected "$1"; then
      note "$1${3:+: $3}"
    else
      bad "$1${3:+: $3}"
    fi
  fi
}

[ -x "$lean" ] || { echo "missing $lean — run 'lake build' first" >&2; exit 2; }
[ -x "$ref" ]  || { echo "missing $ref — run 'cd ocaml-ref && ./fetch.sh && dune build'" >&2; exit 2; }

mkdir -p "$out"

# ---------------------------------------------------------------- CFG -> TA, and O_bp

echo "CFG to tree automaton (Definition A.9) and base precedence order"
for g in "$root"/test/grammars/*.cfg; do
  name=$(basename "$g" .cfg)

  "$lean" cfg2ta "$g" > "$out/$name.lean.ta" 2> "$out/$name.lean.err"
  "$ref"  cfg2ta "$g" > "$out/$name.ref.ta"  2> "$out/$name.ref.err"

  if [ -s "$out/$name.ref.err" ]; then
    report "$name: cfg2ta" fail "the reference fails: $(tr -d '\n' < "$out/$name.ref.err")"
  elif cmp -s "$out/$name.lean.ta" "$out/$name.ref.ta"; then
    report "$name: cfg2ta" ok "byte-for-byte agreement"
  else
    report "$name: cfg2ta" fail "outputs differ"
    diff "$out/$name.ref.ta" "$out/$name.lean.ta" | head -10
  fi

  # The reference does not implement the trivial-symbol optimisation of Section 3.1.1,
  # so we compare against the Lean version with that optimisation switched off.
  "$lean" obp "$g" --keep-trivial > "$out/$name.lean.obp" 2>/dev/null
  "$ref"  obp "$g"                > "$out/$name.ref.obp"  2>/dev/null
  if [ ! -s "$out/$name.ref.obp" ]; then
    report "$name: obp" fail "the reference produced nothing"
  elif cmp -s "$out/$name.lean.obp" "$out/$name.ref.obp"; then
    report "$name: obp" ok "byte-for-byte agreement"
  else
    report "$name: obp" fail "orders differ"
    diff "$out/$name.ref.obp" "$out/$name.lean.obp" | head -10
  fi
done

# ---------------------------------------------------------------- intersection

echo
echo "tree automata intersection (Algorithm 3.3)"

# Runs the reference intersection and checks its result against the verified product.
check_intersection() {
  label=$1; a=$2; b=$3
  slug=$(echo "$label" | tr -c 'A-Za-z0-9._-' '_')
  "$ref" intersect "$a" "$b" > "$out/$slug.ref.ta" 2> "$out/$slug.ref.err"
  rc=$?
  if [ $rc -eq 124 ]; then
    report "$label" fail "the reference implementation does not terminate"
  elif [ $rc -ne 0 ]; then
    report "$label" fail "the reference implementation fails: $(tr -d '\n' < "$out/$slug.ref.err")"
  elif "$lean" checkinter "$a" "$b" "$out/$slug.ref.ta" 5 > "$out/$slug.check" 2>&1; then
    report "$label" ok "$(head -1 "$out/$slug.check"), all agree with the verified product"
  else
    report "$label" fail "the result disagrees with the verified product"
    sed -n '2,4p' "$out/$slug.check"
  fi
}

# The learned automaton against A_g, per grammar.  `bin/main.ml` of the reference calls
# `O.intersect ta_initial ta_learned`, so A_g first is the pipeline's own argument order.
for g in "$root"/test/grammars/*.cfg; do
  name=$(basename "$g" .cfg)
  ex="$root/test/examples/$name.ex"
  [ -f "$ex" ] || continue
  "$lean" cfg2ta "$g" > "$out/$name.ag.ta" 2>/dev/null || continue
  "$lean" genta  "$g" "$ex" --keep-trivial > "$out/$name.ar.ta" 2>/dev/null || continue
  check_intersection "$name: A_g with A_r" "$out/$name.ag.ta" "$out/$name.ar.ta"
  check_intersection "$name: A_r with A_g" "$out/$name.ar.ta" "$out/$name.ag.ta"
done

# Hand-written automaton pairs, in both argument orders: the reference is not symmetric.
for a in "$root"/test/automata/*-a.ta; do
  [ -f "$a" ] || continue
  b=$(echo "$a" | sed 's/-a\.ta$/-b.ta/')
  [ -f "$b" ] || continue
  name=$(basename "$a" -a.ta)
  check_intersection "$name: A with B" "$a" "$b"
  check_intersection "$name: B with A" "$b" "$a"
done

echo
echo "$pass passed, $fail unexpected, $known known divergences"
[ "$fail" -eq 0 ]
