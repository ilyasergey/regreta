# Reproducing the comparison with the reference implementation

How to run the Lean tool and Greta's OCaml code on the same inputs, what the comparison
checks, and what it prints. Findings are written up in
[`reference-defects.md`](reference-defects.md).

## Prerequisites

* The Lean build: `lake build` at the repository root (Lean 4.33.1 via `elan`; `lake exe
  cache get` first fetches prebuilt Mathlib).
* OCaml and dune. The reference builds with OCaml 4.14 and dune 3; it needs the `str`
  library, which ships with the compiler, and the driver needs `unix`.
* Network access once, to clone the reference.

## Building the reference driver

```
cd ocaml-ref
./fetch.sh
dune build
cd ..
```

`fetch.sh` clones <https://github.com/verse-lab/greta> into `ocaml-ref/.greta`, checks out
commit `a62d6b68a92178eb2f1bd57b620386e5a2cdc1b6`, and copies the nine library modules the
driver needs (`ta`, `cfg`, `cfgutils`, `utils`, `treeutils`, `pp`, `learner`, `operation`,
`converter`) into `ocaml-ref/src/`, unmodified. Both directories are ignored by git. The
driver, `ocaml-ref/driver/main.ml`, reads the text format of
[`testing.md`](testing.md#the-text-format) and calls the reference's own functions:

```
greta-ref cfg2ta GRAMMAR       A_g, as Converter.cfg_to_ta builds it
greta-ref obp GRAMMAR          the base precedence order it computes
greta-ref intersect TA1 TA2    Operation.intersect
greta-ref intersect-debug ...  the same with the reference's tracing on
```

The reference can loop forever on some inputs. With `GRETA_REF_TIMEOUT` set (seconds), the
driver installs a watchdog that flushes whatever has been printed and exits with status 124.

## Running the comparison

```
./scripts/difftest.sh                     # default watchdog: 30 s per reference call
GRETA_REF_TIMEOUT=10 ./scripts/difftest.sh
```

The script runs three comparisons and writes every intermediate file to `test/out/`.

1. **Grammar to automaton.** For each `test/grammars/*.cfg`, both tools print `A_g`; the
   outputs are compared byte for byte. Both print a canonical form: states, final states and
   terminals sorted and duplicate-free, transition lines sorted.
2. **Base precedence order.** For each grammar, both tools print `O_bp`. The reference does
   not implement the trivial-symbol exclusion of Section 3.1.1, so the Lean tool is run with
   `--keep-trivial`. Byte for byte again.
3. **Intersection.** For each grammar with a `test/examples/<name>.ex`, the Lean tool
   produces `A_g` and `A_r`, and the reference intersects them in both argument orders (it is
   not symmetric; `bin/main.ml` of the reference passes `A_g` first). The hand-written pairs
   in `test/automata/<name>-a.ta`, `<name>-b.ta` are intersected in both orders too. The
   reference renames product states, so its result is compared **by language**:
   `lake exe greta checkinter A B RESULT 5` enumerates trees of depth at most 5 from `A`, `B`
   and `RESULT` and checks that `RESULT` accepts a tree exactly when the verified product
   `prodTA A B` does. Because `prodTA_lang` is proved, a disagreement is a defect in the
   reference.

Cases listed in `test/expected-divergences.txt` are reported as `known`; the script exits
non-zero only if an unlisted case diverges or a listed case starts agreeing.

## Expected output

At commit `a62d6b6`, with the inputs in `test/`:

```
CFG to tree automaton (Definition A.9) and base precedence order
  ok       arith: cfg2ta: byte-for-byte agreement
  ok       arith: obp: byte-for-byte agreement
  ok       cycle: cfg2ta: byte-for-byte agreement
  ok       cycle: obp: byte-for-byte agreement
  ok       dangling-else: cfg2ta: byte-for-byte agreement
  ok       dangling-else: obp: byte-for-byte agreement
  ok       list: cfg2ta: byte-for-byte agreement
  ok       list: obp: byte-for-byte agreement
  ok       running-example: cfg2ta: byte-for-byte agreement
  ok       running-example: obp: byte-for-byte agreement
  known    unreachable: cfg2ta: the reference fails: Fatal error: exception Not_found
  known    unreachable: obp: the reference produced nothing

tree automata intersection (Algorithm 3.3)
  known    arith: A_g with A_r: the reference implementation does not terminate
  known    arith: A_r with A_g: the result disagrees with the verified product
  known    cycle: A_g with A_r: the reference implementation does not terminate
  known    cycle: A_r with A_g: the reference implementation fails: Fatal error: exception Gretacore.Ta.Invalid_transitions
  known    dangling-else: A_g with A_r: the result disagrees with the verified product
  known    dangling-else: A_r with A_g: the reference implementation does not terminate
  known    running-example: A_g with A_r: the result disagrees with the verified product
  known    running-example: A_r with A_g: the reference implementation does not terminate
  known    eps: A with B: the result disagrees with the verified product
  known    eps: B with A: the result disagrees with the verified product
  known    finals: A with B: the reference implementation does not terminate
  ok       finals: B with A: checked 5 trees, all agree with the verified product
  known    paper: A with B: the reference implementation does not terminate
  known    paper: B with A: the result disagrees with the verified product

11 passed, 0 unexpected, 15 known divergences
```

Each `disagrees` line is followed by up to three trees the reference rejects although both
inputs accept them. Which of `does not terminate` and `disagrees` a pair produces depends
on the argument order; the mapping to defects is: `Not_found` is
[D3](reference-defects.md#d3-convertercfg_to_ta-raises-not_found-on-unreachable-nonterminals),
`disagrees` is [D1](reference-defects.md#d1-the-intersection-drops-transitions-reachable-only-through-an-ε-transition),
`does not terminate` is [D2](reference-defects.md#d2-the-intersection-can-fail-to-terminate),
`Invalid_transitions` is [D4](reference-defects.md#d4-ta-invalid_transitions-escapes-from-the-intersection).

## Reproducing one case by hand

The paper's own running example, with the automata of Figures 6 and 7 as the reference's
pipeline passes them:

```
$ ocaml-ref/_build/default/driver/main.exe intersect test/automata/paper-b.ta test/automata/paper-a.ta > /tmp/ref.ta
$ lake exe greta checkinter test/automata/paper-b.ta test/automata/paper-a.ta /tmp/ref.ta 5
checked 113 trees
MISSING (in A ∩ B, rejected by the result): (2 IF 6 #IF ...
```

The other argument order hangs; `GRETA_REF_TIMEOUT=10` in the environment makes it stop.
The two-state automaton `test/automata/eps-a.ta` intersected with itself is the smallest
input that shows D1. `lake exe greta accepts TA GRAMMAR D` lists the trees an automaton
accepts, to see what a result contains.

## Adding a case

A grammar in `test/grammars/`, optionally with the rejected examples in
`test/examples/<name>.ex`, is picked up by every stage. A pair of automata goes in
`test/automata/` as `<name>-a.ta` and `<name>-b.ta`. If the reference is expected to
diverge on the new case, add the label the script prints to
`test/expected-divergences.txt`.
