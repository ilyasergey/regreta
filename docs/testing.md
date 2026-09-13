# Testing

Two suites. The Lean suite runs inside `lake exe greta selftest` and needs nothing but the
build. The differential suite compares the Lean tool with the OCaml reference
implementation and is described in [`reproducing.md`](reproducing.md).

## The Lean suite

```
lake exe greta selftest
```

**The running example.** The grammar of Figure 1 is encoded in `Greta/Test.lean`. The
suite checks that `CFG.toTA` reproduces Figure 6, that the base precedence order
reproduces the `O_bp` of Section 2.3.1, that `IDENT` is the only trivial symbol, that
`LearnOaOp` reproduces the `O_p` of Section 2.3.2 from the rejected tree examples of
Figure 3, and that `GenTA` reproduces Figure 7 transition for transition, with the `(TINT,4)`
row at `e2` corrected as [`divergences.md`](divergences.md#7-figure-7-has-a-typo) explains.
It also checks the translation theorem, [`CFG.toTA_correct`](../Greta/CFG.lean#L318), on concrete parse trees.

**The witnesses of `divergences.md`.** [`testAssocOnly`](../Greta/Test.lean#L247) checks
that a symbol whose only conflict is with itself is still re-layered ([§2](divergences.md#d2));
[`testCycle`](../Greta/Test.lean#L282) the cycle grammar against Theorem 3.1(2) ([§1](divergences.md#d1));
[`testBrackets`](../Greta/Test.lean#L448) that `x * (y + z)` is kept by neither the published
learner nor `Fits`, and is kept by the shipped one ([§8](divergences.md#d8));
[`testTopoSort`](../Greta/Test.lean#L498) that the four-operator grammar's long-range
constraint survives the linearisation ([§9](divergences.md#d9));
[`testPipelineChecked`](../Greta/Test.lean#L582) that the checked side conditions reject the
cycle witness; [`testShippedSound`](../Greta/Test.lean#L526) that Theorem 3.1(1) *does* hold
for the construction `learner.ml` builds, on the grammar where the published one fails
([§8](divergences.md#d8)); and [`testTotalOrder`](../Greta/Test.lean#L555) that a conflict
group the examples order only partially breaks Theorem 3.1(1), and that supplying the four
missing examples restores it ([§10](divergences.md#d10)). The `I¹` witness of [§5](divergences.md#d5) is not a test but a `#guard` in
`Greta/IntersectSpec.lean`, evaluated when the file is compiled.

**The learner as shipped.** [`testRefLearner`](../Greta/Test.lean#L348) compares
`refLearnOaOp` with what `Learner.learn_op` prints, as described
[below](#running-the-shipped-learner), and [`testRefBackEdge`](../Greta/Test.lean#L380)
checks that `refGenTA` carries the back-edges of `learn_ta`.

**The optimised intersection against the verified one.** For each of the five
configurations of Table 1 (`I^def`, `I^1`, `I^2`, `I^3`, `I^123`), the suite runs
[`intersectTA`](../Greta/Intersect.lean#L177) (Algorithm 3.3) and compares its language with
[`prodTA`](../Greta/Product.lean#L63) (Section 2.4) on a corpus of trees enumerated from
both inputs and from the result, so both over- and under-acceptance are visible. The same
comparison is run on grammars from a deterministic pseudo-random generator, so a failure
reproduces from its seed. The equality is proved ([`intersectTA_lang`](../Greta/IntersectSpec.lean#L1756));
the test remains as a check that the definitions the proof is about are the ones that
execute, and because the random grammars happen not to exercise the `I¹` defect.

## The text format

Shared by `lake exe greta` and the OCaml driver. Line-based, whitespace-separated, `#`
starts a comment. A name that would be empty is written `-`.

A **ranked symbol** is three tokens: identifier, name, rank. The identifier is the index
of the production the symbol comes from, counting from 0 in grammar order; `(ε,1)` is
`-1 ε 1`.

A **right-hand-side entry** is `T:<terminal>` or `S:<state>`.

A **tree automaton**:

```
states  q0 q1 ...
finals  q0
terminals  A B ...
trans <target> <id> <name> <rank> <entry> ...
```

A **grammar**:

```
nonterms  expr stmt ...
terms     PLUS INT ...
starts    stmt
prod <lhs> <entry> ...          # entries are T:<terminal> or N:<nonterminal>
```

A **tree example** is `example <top-id> <bottom-id> <child-index>`, the `Eg(α, β, i)` of
Section 3: the production `top-id` with the production `bottom-id` nested at child position
`i`. The file lists the examples the user did *not* select. The child index counts every
right-hand-side element, terminals included.

Trees, which only appear in diagnostic output, are printed as `#<terminal>` for a leaf
and `(<id> <name> <rank> <child> ...)` for a node.

## Running the shipped learner

`Greta/RefLearn.lean` is `Learner.update_op_per_ord_amb_symsls` and `Learner.learn_op` as
the OCaml ships them, and `lake exe greta selftest` compares it against what those
functions actually print.  The expectations in `Greta/Test.lean` (`expectedRefOp`,
`expectedRefSpecs`) were obtained by running the vendored code directly, since upstream's
own entry point is interactive and `ocaml-ref/driver` has no `learn` command.

Stage the sources outside the read-only tree, build a driver beside them that supplies
`M_to` on the command line, and call `Learner.learn_op`:

```
cp -r ocaml-ref/src /tmp/oref/src           # the modules `fetch.sh` staged
echo '(lang dune 3.0)' > /tmp/oref/dune-project
# /tmp/oref/learn/main.ml: parse the .cfg as ocaml-ref/driver/main.ml does, then
#   let (_, _, obp_tbl, _, _, _) = Converter.cfg_to_ta false g in
#   let op, specs = Learner.learn_op obp_tbl [] mto false in
#   ... print `op` and `specs` ...
dune build && ./_build/default/learn/main.exe test/grammars/running-example.cfg 0:1,2 1:5,6
```

where `0:1,2 1:5,6` is `M_to` by production identifier — order 0 holds the conflict group
`(IF,4) < (IF,6)` and order 1 holds `(PLUS,3) < (STAR,3)` — printed by `refLearnOaOp`'s
own `toMapOf`, so that the two implementations are given the same input.  OCaml 5.1 or
later is needed; the staged modules use `List.is_empty`.

On the four grammars in `test/grammars` that have example files, the `O_p` and the
`special_loop_symbols` the two produce agree exactly.  The comparison is not part of
`scripts/difftest.sh`, because the driver it needs is not in `ocaml-ref/`.
