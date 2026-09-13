# How Dare You!

A Lean 4 formalisation of *Grammar Repair with Examples and Tree Automata* (Yunjeong Lee,
Gokul Rajiv, Ilya Sergey, OOPSLA 2026), and a differential test of the formalised
algorithms against Greta, the paper's OCaml implementation.

* The paper: [ACM DL, 10.1145/3798242](https://dl.acm.org/doi/10.1145/3798242).
* The extended version, with the supplementary material:
  [arXiv:2602.18166](https://arxiv.org/abs/2602.18166).
* The implementation: [Greta](https://github.com/verse-lab/greta) at commit
  [`a62d6b6`](https://github.com/verse-lab/greta/tree/a62d6b68a92178eb2f1bd57b620386e5a2cdc1b6),
  the head of its `main` branch on 5 March 2026.

## Overview

* The theory of Sections 2 and 3 is machine-checked: grammars, tree automata with
  ε-transitions, the grammar-to-automaton translation, the product construction, and the
  correctness theorems (Theorem A.10, the product theorem, Theorems 3.1 and 3.2). No `sorry`;
  only Lean's standard axioms.
* The algorithms of Section 3 are executable Lean definitions, compiled to a command-line tool
  that reproduces the paper's running example (Figures 6 and 7, Section 2.3).
* The tool is compared against the reference OCaml implementation on the same inputs.

What was found, in brief; [`docs/divergences.md`](docs/divergences.md) has the details.

* Theorem 3.2 holds as stated, for the product construction of Section 2.4.
* Theorem 3.1(2) holds once the grammar's symbol order has no cycle, the case the paper's
  own proof declares out of scope; a five-production grammar shows the condition is
  necessary. It is proved, and the side conditions are checked on the input.
* Theorem 3.1(1) is false for the published algorithms. On the grammar of Section 1, with
  the paper's own rejected examples, the repair loses `x * (y + z)`: Algorithm 3.1 as
  printed copies the non-conflicting symbols to every new order, so a bracketing production
  keeps its contents at its own precedence level. Greta's own learner, which uses a
  back-edge instead, is not affected.
* Building `M_to` needs a topological sort. A comparison sort can drop a constraint it
  never tests, and the repaired grammar then still admits a rejected nesting.
* Algorithm 3.3, the optimised intersection, is proved to recognise the intersection, so
  the last link in the paper's chain of correctness no longer rests on testing. One of its
  ablations is wrong: with reachability off, duplicate merging can elect a non-accepting
  representative and lose trees. A two-transition witness is checked at build time.
* Two of the defects found in the OCaml implementation are in code the paper does not
  describe.

Where the paper and the OCaml code disagree, the formalisation follows the paper. Symbol
naming follows the code so that printed automata can be compared byte for byte. Section,
figure, algorithm and theorem numbers below are those of the paper's main body; Definitions
A.n and Lemmas B.n are in its supplementary material.

## Documents

* [`docs/divergences.md`](docs/divergences.md): where the theorems proved here differ from
  the paper's, and what each difference means.
* [`docs/structure.md`](docs/structure.md): how the Lean development is laid out and why.
* [`docs/testing.md`](docs/testing.md): the Lean test suite and the text format shared with
  the OCaml driver.
* [`docs/reproducing.md`](docs/reproducing.md): how to run the comparison with the
  reference implementation.
* [`docs/reference-defects.md`](docs/reference-defects.md): defects found in the OCaml
  implementation, and what a fix would look like.
* [`docs/complexity.md`](docs/complexity.md): the paper's complexity claims, which are
  not formalised, and what proving them would need.

## What is formalised

*Proved* is a complete Lean proof. *Proved under assumptions* links to the section of
[`docs/divergences.md`](docs/divergences.md) that states the assumptions. *Checked* means
the tool decides the condition on its input, and the theorem applies when the check passes.
*Executable* definitions also run, through `lake exe greta`. Definitions A.n, Theorem A.10
and Lemmas B.n are in the paper's supplementary material, part of the extended version at
[arXiv:2602.18166](https://arxiv.org/abs/2602.18166).

| Paper | Lean | Status |
| --- | --- | --- |
| §2.1 grammars, parse trees, ambiguity | [`CFG`](Greta/CFG.lean#L25), [`isParseTree`](Greta/CFG.lean#L204), [`Ambiguous`](Greta/CFG.lean#L208) | definitions |
| §2.2 ranked symbols, tree automata, ε-transitions | [`Sym`](Greta/Basic.lean#L27), [`TA`](Greta/Basic.lean#L130), [`epsSym`](Greta/Basic.lean#L40) | definitions |
| §2.2 runs and acceptance | [`TA.evalT`](Greta/Semantics.lean#L31), [`TA.accepts`](Greta/Semantics.lean#L55), [`TA.Lang`](Greta/Semantics.lean#L59) | definitions, decidable |
| §2.2 the ε-closure is computed correctly | [`TA.isEpsClosure_epsTable`](Greta/Closure.lean#L248) | proved |
| §2.2 translating a grammar to `A_g` | [`CFG.toTA`](Greta/CFG.lean#L117) | executable |
| Theorem A.10, `L(A_g) = L_g` | [`CFG.toTA_correct`](Greta/CFG.lean#L318) | proved |
| §2.4 the product of two tree automata | [`prodTA`](Greta/Product.lean#L63) | executable |
| §2.4 `L(A ⊗ B) = L(A) ∩ L(B)` | [`prodTA_lang`](Greta/Product.lean#L377) | proved |
| §3 tree examples, `ParseTrees`, `P⁻`, `L⁻` | [`TreeExample`](Greta/Examples.lean#L17), [`parseTreesOf`](Greta/Examples.lean#L117), [`excludedLang`](Greta/Examples.lean#L130) | definitions |
| §3.1.1 `O_bp`, trivial symbols, `HighToLow` | [`baseOrder`](Greta/Order.lean#L124), [`trivialSyms`](Greta/Order.lean#L106), [`highToLow`](Greta/Order.lean#L150) | executable |
| Algorithm 3.1, `LearnOaOp`, as printed | [`learnOaOp`](Greta/Learn.lean#L62) | executable ([§8](docs/divergences.md#d8), [§9](docs/divergences.md#d9)) |
| Algorithm 3.1 as `learner.ml` ships it | [`refLearnOaOp`](Greta/RefLearn.lean#L131), [`refGenTA`](Greta/RefLearn.lean#L560) | executable; matches the OCaml ([D7](docs/reference-defects.md#d7-algorithm-31-as-printed-is-not-what-learnerml-does)) |
| Algorithm 3.2, `GenTA` | [`genTA`](Greta/GenTA.lean#L140) | executable ([§6](docs/divergences.md#d6), [§7](docs/divergences.md#d7)) |
| Algorithm 3.3, `IntersectTA`, with the ablations of Table 1 | [`intersectTA`](Greta/Intersect.lean#L177), [`intersectTA_lang`](Greta/IntersectSpec.lean#L1756) | executable; proved equal to `prodTA` ([§5](docs/divergences.md#d5)) |
| Algorithm 3.4, `FindDupStates` | [`findDupStates`](Greta/Intersect.lean#L101), [`merge_lang`](Greta/IntersectSpec.lean#L1384) | executable; merging proved language-preserving |
| Lemma B.1, `O_p` against `L_r` | [`epsReach_lvl`](Greta/GenTASpec.lean#L160), [`evalT_genTA_inv`](Greta/GenTASpec.lean#L178) | proved, restated ([§3](docs/divergences.md#d3)) |
| Lemma B.2, as printed | [`relayerOrder_ordersOf_above`](Greta/LearnSpec.lean#L370), [`relayerOrder_replicates`](Greta/LearnSpec.lean#L475) | proved, both halves ([§4](docs/divergences.md#d4)) |
| Lemma B.2, for the learner Greta ships | [`refGenTA_specReach`](Greta/RefLearn.lean#L708), [`refRelayerFold_no_inversion`](Greta/RefLearn.lean#L312) | proved ([§4](docs/divergences.md#d4)) |
| Theorem 3.1(1), `L_r ⊇ L_g \ L⁻` | [`genTA_sound₁`](Greta/GenTASpec.lean#L646) | proved under assumptions; false as stated ([§8](docs/divergences.md#d8)) |
| Theorem 3.1(2), `L_r ∩ L⁻ = ∅` | [`genTA_sound₂`](Greta/GenTASpec.lean#L342) | proved under assumptions ([§1](docs/divergences.md#d1), [§2](docs/divergences.md#d2)) |
| Theorem 3.2, for the product construction | [`greta_correct_of_spec`](Greta/GenTASpec.lean#L689) | proved ([§5](docs/divergences.md#d5)) |
| The assumptions of Theorem 3.1, of the pair Algorithm 3.1 learns | [`learnedSpec_of_check`](Greta/LearnSpec.lean#L923), [`fits_of_check`](Greta/LearnSpec.lean#L1023) | checked; `Fits` fails on brackets ([§2](docs/divergences.md#d2), [§8](docs/divergences.md#d8)) |
| Theorem 3.1(2), for the pipeline of Figure 4 | [`genTA_sound₂_pipeline`](Greta/LearnSpec.lean#L1106) | proved, assumptions checked |
| Theorem 3.2, for the pipeline of Figure 4 | [`repairOnceSpec_correct_pipeline`](Greta/LearnSpec.lean#L1144) | proved, assumptions checked |
| One round of repair as run equals the verified round | [`repairOnce_lang`](Greta/Soundness.lean#L157) | proved, given distinct start nonterminals |

## Building and running

Lean 4.33.1 and Mathlib; `elan` picks the toolchain up from `lean-toolchain`.

```
lake exe cache get        # prebuilt Mathlib, optional
lake build
lake exe greta selftest   # the paper's worked example and randomised checks
```

`lake exe greta` with no arguments lists the commands. The running example of Section 2 is
`test/grammars/running-example.cfg`; the tree examples of Figure 3 that the user did not
select are `test/examples/running-example.ex`.

```
lake exe greta cfg2ta test/grammars/running-example.cfg                                   # Figure 6
lake exe greta op     test/grammars/running-example.cfg test/examples/running-example.ex  # O_p of §2.3.2
lake exe greta genta  test/grammars/running-example.cfg test/examples/running-example.ex  # Figure 7
lake exe greta repair test/grammars/running-example.cfg test/examples/running-example.ex  # the repaired grammar
```

[`docs/structure.md`](docs/structure.md) describes the Lean development;
[`docs/testing.md`](docs/testing.md) the self-test and the text format.

## Testing against the OCaml implementation

Requires OCaml and dune. [`docs/reproducing.md`](docs/reproducing.md) has the full
procedure and the expected output.

```
cd ocaml-ref && ./fetch.sh && dune build && cd ..
./scripts/difftest.sh
```

Where the reference renames nothing, outputs are compared byte for byte. Where it does,
in the intersection, its output is read back into Lean and compared by language with the
verified product on a corpus of enumerated trees. Since `prodTA_lang` is proved, a
disagreement there is a defect in the reference.

| Stage | Outcome |
| --- | --- |
| Grammar to `A_g` (§2.2) | Agree byte for byte on every well-formed grammar. The reference crashes on a grammar with an unreachable nonterminal. |
| `O_bp` (§3.1.1) | Agree byte for byte, with the trivial-symbol optimisation switched off on the Lean side: the reference does not implement it. |
| `LearnOaOp`, `GenTA` (§3.1) | Not compared directly: the reference implements a different re-layering than Algorithm 3.1 prints. The Lean side reproduces the paper's `O_p` and Figure 7. |
| Intersection (Algorithm 3.3) | The reference disagrees with the verified product on every automaton pair tested. It drops the transitions of the accepting state that are reachable only through an ε-transition, so on the running example the repaired grammar loses `if … then … else`. With the arguments in the other order it does not terminate. |

Both intersection defects are in the OCaml code, not in Algorithm 3.3 as printed: the Lean
`intersectTA`, which follows the pseudocode, is proved to recognise the same language as
the verified product ([`intersectTA_lang`](Greta/IntersectSpec.lean#L1756)) in the
configuration Greta runs. Each defect has a reproducer, a diagnosis and a suggested fix in
[`docs/reference-defects.md`](docs/reference-defects.md).

## Layout

```
Greta/            the formalisation
Main.lean         the command-line tool
ocaml-ref/        driver over the reference implementation's own modules
scripts/          differential test, axiom check, link check
test/             grammars, tree examples and automata used by both test suites
docs/             divergences from the paper, defects in the reference, structure,
                  testing, how to reproduce the comparison, complexity claims
```

## References

* Yunjeong Lee, Gokul Rajiv, Ilya Sergey. *Grammar Repair with Examples and Tree
  Automata*. Proc. ACM Program. Lang. 10, OOPSLA1, Article 134 (April 2026).
  [doi:10.1145/3798242](https://doi.org/10.1145/3798242). The version with the
  supplementary material is [arXiv:2602.18166](https://arxiv.org/abs/2602.18166).
* Greta, the reference implementation: <https://github.com/verse-lab/greta>, MIT licence.
