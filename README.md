# greta-lean

A Lean 4 formalisation of *Grammar Repair with Examples and Tree Automata* (Yunjeong Lee,
Gokul Rajiv, Ilya Sergey, OOPSLA 2026), together with a differential-testing harness that
runs the formalised algorithms against the [Greta](https://github.com/verse-lab/greta)
reference implementation in OCaml.

Section and figure numbers below are those of the main body of the paper. The formal
definitions of tree automata and of the CFG-to-TA translation live in the paper's
supplementary material; where a statement only exists there it is noted.

The development has two halves.

* The **definitions and theorems** of Sections 2 and 3, formalised and proved from
  scratch: context-free grammars, the variant of bottom-up tree automata the paper uses,
  the translation from grammars to automata, and the intersection of tree automata.
* The **algorithms** of Section 3 — `LearnOaOp`, `GenTA`, `IntersectTA` and
  `FindDupStates` — as executable Lean definitions. These compile to a command-line tool
  that runs on the same inputs as the OCaml tool and can be compared with it.

There are no `sorry`s and no axioms beyond Lean's own `propext`, `Classical.choice` and
`Quot.sound` (`scripts/check-axioms.sh`). Both halves of Theorem 3.1 and all of Theorem
3.2 are proved; Theorem 3.1 carries five decidable side conditions, which
[`docs/divergences.md`](docs/divergences.md) explains.

## What is formalised

| Paper | Lean | Status |
| --- | --- | --- |
| §2.1, CFGs, parse trees, ambiguity | [`CFG`](Greta/CFG.lean#L25), [`isParseTree`](Greta/CFG.lean#L113), [`Ambiguous`](Greta/CFG.lean#L117) | definitions |
| §2.2, ranked symbols, tree automata, ε-transitions | [`Sym`](Greta/Basic.lean#L27), [`TA`](Greta/Basic.lean#L130), [`epsSym`](Greta/Basic.lean#L40) | definitions |
| §2.2, runs and acceptance | [`TA.evalT`](Greta/Semantics.lean#L31), [`TA.accepts`](Greta/Semantics.lean#L55), [`TA.Lang`](Greta/Semantics.lean#L59) | definitions |
| §2.2, the ε-closure is computed correctly | [`TA.isEpsClosure_epsTable`](Greta/Closure.lean#L248) | **proved** |
| §2.2, acceptance does not depend on which ε-closure is used | [`TA.accepts_congr`](Greta/Semantics.lean#L105) | **proved** |
| §2.2, translating a CFG into `A_g` | [`CFG.toTA`](Greta/CFG.lean#L79) | definition |
| §2.2, `L(A_G) = L_G` (supplementary material, Thm. A.10) | [`CFG.toTA_correct`](Greta/CFG.lean#L227) | **proved** |
| §2.4, intersecting two tree automata | [`prodTA`](Greta/Product.lean#L63), [`compatAll`](Greta/Product.lean#L33) | definition |
| §2.4, `L(A ⊗ B) = L(A) ∩ L(B)` | [`prodTA_lang`](Greta/Product.lean#L377) | **proved** |
| §3, tree examples, `ParseTrees`, `P⁻`, `L⁻` | [`TreeExample`](Greta/Examples.lean#L17), [`parseTreesOf`](Greta/Examples.lean#L67), [`excludedBy`](Greta/Examples.lean#L75), [`excludedLang`](Greta/Examples.lean#L80) | definitions |
| §3.1.1, `O_bp`, trivial symbols, `HighToLow` | [`baseOrder`](Greta/Order.lean#L108), [`trivialSyms`](Greta/Order.lean#L90), [`highToLow`](Greta/Order.lean#L134) | executable definitions |
| Algorithm 3.1, `LearnOaOp` | [`learnOaOp`](Greta/Learn.lean#L57), [`relayerOrder`](Greta/Learn.lean#L38) | executable definition |
| Algorithm 3.2, `GenTA` | [`genTA`](Greta/GenTA.lean#L38), [`fillRhs`](Greta/GenTA.lean#L22) | executable definition |
| Algorithm 3.3, `IntersectTA`, ablations of Table 1 | [`intersectTA`](Greta/Intersect.lean#L168), [`IntersectOpts`](Greta/Intersect.lean#L151) | executable definition; agreement with `prodTA` is **tested, not proved** |
| Algorithm 3.3, a sub-automaton accepts no more | [`accepts_mono`](Greta/Intersect.lean#L249), [`evalT_mono`](Greta/Intersect.lean#L231) | **proved**; the soundness half of the reachability restriction |
| Algorithm 3.4, `FindDupStates` | [`findDupStates`](Greta/Intersect.lean#L99) | executable definition |
| §2.2, the shape of `A_r`: ε-reachability is `≤` on levels | [`epsReach_lvl`](Greta/GenTASpec.lean#L161), [`evalT_genTA_inv`](Greta/GenTASpec.lean#L179) | **proved**; this is Lemma B.1's content |
| §3.1.4, Theorem 3.1(2), `L_r ∩ L⁻ = ∅` | [`genTA_sound₂`](Greta/GenTASpec.lean#L343) | **proved** under `LearnedSpec` and acyclicity |
| §3.1.4, Theorem 3.1(1), `L_r ⊇ L_g \ L⁻` | [`genTA_sound₁`](Greta/GenTASpec.lean#L634) | **proved** under `Fits`, `Covers` and acyclicity |
| §3.2, Theorem 3.2, correctness of Greta | [`greta_correct_of_spec`](Greta/GenTASpec.lean#L677) | **proved**, from the two above and `prodTA_lang` |
| Lemma B.2 (supplementary material) | [`shift_mono`](Greta/Soundness.lean#L31) | its arithmetic core **proved**; superseded by [`Fits`](Greta/GenTASpec.lean#L470) |

Every entry marked **proved** is a complete Lean proof. Entries marked *definition* are
formalised but carry no theorem of their own; *executable* means the definition also runs,
via `lake exe greta`.

## Status of the proofs

Four results carry the development.

[`CFG.toTA_correct`](Greta/CFG.lean#L227) says the automaton built from a grammar accepts
exactly that grammar's complete parse trees, which is what makes the approach of §2.2
legitimate. The supplementary material proves it in one line ("Follows directly from the
construction"); here it is an induction over trees that has to line up the automaton's
children-matching with the grammar's right-hand sides.

[`prodTA_lang`](Greta/Product.lean#L377) says the product of two tree automata recognises
the intersection of their languages — the mathematical content of Theorem 3.2. Handling
ε-transitions is the delicate part: the ε-closure of a product state has to be shown to be
the product of the component closures before the evaluation lemma can be proved.

[`genTA_sound`](Greta/GenTASpec.lean#L667) is Theorem 3.1, both halves. The proof does not
reason about languages directly: it pins down the transitions `GenTA` emits, shows the
ε-graph is the chain `e₀ ←ε e₁ ←ε … ←ε eₘ`, and deduces that ε-reachability between
ordered states is `≤` on levels. After that every argument is arithmetic. Statement (2)
follows by induction over the tree; statement (1) builds a run by assigning levels
top-down.

[`greta_correct_of_spec`](Greta/GenTASpec.lean#L677) is Theorem 3.2, assembled from the
three. No hypothesis about languages remains: what is left are five decidable conditions
on the learned order — [`LearnedSpec`](Greta/GenTASpec.lean#L235),
[`Fits`](Greta/GenTASpec.lean#L470), [`Covers`](Greta/GenTASpec.lean#L598), that no start
nonterminal is trivial, and that `HighToLow` reports nothing.

That last one is a real restriction rather than a technicality, and it is the case the
paper's own proof of Lemma B.1 sets aside: *"Cases of symbols at adjacent levels which are
involved in a conflict … are explicitly not handled by the algorithm."*
[`docs/divergences.md`](docs/divergences.md) goes through every place the statements here
differ from the paper's.

What is **not** proved is that Algorithm 3.3 — the optimised intersection Greta actually
runs — has the same language as the product construction.
[`evalT_mono`](Greta/Intersect.lean#L231) and [`accepts_mono`](Greta/Intersect.lean#L249)
give the soundness half of the reachability restriction; the rest is covered by testing
against the verified product, and `docs/proof-plan.md` sets out what proving it would take.

## Building

Lean 4.33.1 and Mathlib; `elan` picks the toolchain up from `lean-toolchain`.

```
lake exe cache get      # prebuilt Mathlib, optional but much faster
lake build
```

## Running

```
$ lake exe greta
greta — Lean formalisation of Grammar Repair with Examples and Tree Automata

  greta cfg2ta GRAMMAR                  print A_g, the tree automaton of a CFG
  greta obp GRAMMAR [--keep-trivial]    print the base precedence order O_bp
  greta op GRAMMAR EXAMPLES             print the learned precedence order O_p
  greta genta GRAMMAR EXAMPLES          print A_r, the automaton learned from examples
  greta intersect TA1 TA2 [FLAGS]       run Algorithm 3.3 (IntersectTA)
  greta product TA1 TA2                 run the verified textbook product
  greta repair GRAMMAR EXAMPLES [FLAGS] one round of repair, printed as a grammar
  greta checkinter TA1 TA2 RESULT [D]   check L(RESULT) = L(TA1) ∩ L(TA2) on a corpus
  greta accepts TA GRAMMAR [D]          list the corpus trees TA accepts
  greta selftest                        run the built-in test suite
```

The running example of Section 2 is `test/grammars/running-example.cfg`, with the tree
examples of Figure 3 that the user did *not* select in
`test/examples/running-example.ex`:

```
lake exe greta cfg2ta test/grammars/running-example.cfg    # Figure 6
lake exe greta op     test/grammars/running-example.cfg \
                      test/examples/running-example.ex     # the O_p of §2.3.2
lake exe greta genta  test/grammars/running-example.cfg \
                      test/examples/running-example.ex     # Figure 7
lake exe greta repair test/grammars/running-example.cfg \
                      test/examples/running-example.ex     # the repaired grammar
```

`lake exe greta selftest` checks the formalisation against the paper's own worked example:
that `CFG.toTA` reproduces Figure 6, that `baseOrder` reproduces the `O_bp` of §2.3.1,
that `learnOaOp` reproduces the `O_p` of §2.3.2, and that `genTA` reproduces Figure 7
transition for transition. It then compares `intersectTA`, under all five ablation
settings of Table 1, with the verified product on the running example and on randomly
generated grammars.

## Testing against the OCaml implementation

`ocaml-ref/` builds a driver on top of the reference implementation's own modules, so both
implementations can be run on the same inputs. The Greta sources are not vendored:
`ocaml-ref/fetch.sh` clones the upstream repository at a pinned commit.

```
cd ocaml-ref && ./fetch.sh && dune build && cd ..
./scripts/difftest.sh
```

Where both implementations produce an automaton, the outputs are compared byte for byte.
Where the reference renames states — the intersection does — the comparison is by
language: the reference's result is read back into Lean and checked against the verified
product construction on a corpus of trees enumerated from both inputs and from the result.
Because `prodTA_lang` is proved, a disagreement is a defect in the reference, not in the
comparison.

`docs/testing.md` describes the harness and the text format; `docs/structure.md` describes
the Lean development.

## What the testing found

The translation from grammars to tree automata (§2.2) and the base precedence order
(§3.1.1) agree byte for byte between the two implementations on every well-formed grammar
tested. The intersection of Algorithm 3.3 does not: on the paper's own running example it
silently drops every `if … then … else` statement, and with its arguments in the other
order it does not terminate.

[`docs/reference-defects.md`](docs/reference-defects.md) is the write-up: each defect with
a reproducer, a diagnosis and a suggested fix.

## Layout

```
Greta/            the formalisation (see docs/structure.md)
Main.lean         the command-line driver
ocaml-ref/        driver for the OCaml reference implementation
scripts/          differential-testing harness and the axiom check
test/             grammars, tree examples and automata used by the tests
docs/             design notes, testing, divergences from the paper, defects found
                  in the reference implementation, and a plan for the last gap
```

## References

* Yunjeong Lee, Gokul Rajiv, Ilya Sergey. *Grammar Repair with Examples and Tree
  Automata*. Proc. ACM Program. Lang. 10, OOPSLA1, Article 134 (April 2026).
  [doi:10.1145/3798242](https://doi.org/10.1145/3798242).
  The supplementary material, which contains the formal definitions of tree automata and
  the proofs, is also available as [arXiv:2602.18166](https://arxiv.org/abs/2602.18166).
* The Greta tool: <https://github.com/verse-lab/greta> (MIT licensed).
