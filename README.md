# greta-lean

A Lean 4 formalisation of *Grammar Repair with Examples and Tree Automata* (Yunjeong Lee,
Gokul Rajiv, Ilya Sergey, OOPSLA 2026), together with a differential-testing harness that
runs the formalised algorithms against the [Greta](https://github.com/verse-lab/greta)
reference implementation in OCaml.

The development has two halves.

* The **definitions and theorems** of the paper, formalised in Lean and proved from
  scratch: context-free grammars, the variant of bottom-up tree automata the paper uses,
  the translation from grammars to automata, and the intersection of tree automata.
* The **algorithms**, `LearnOaOp`, `GenTA`, `IntersectTA` and `FindDupStates`, as
  executable Lean definitions. These compile to a command-line tool that can be run on
  the same inputs as the OCaml tool and compared with it.

Every theorem below is proved; there are no `sorry`s and no added axioms beyond Lean's
own `propext`, `Classical.choice` and `Quot.sound`. Where the paper's proof is not
formalised, the statement appears as an explicit hypothesis rather than as an assumption
hidden inside a proof — see [Status of the proofs](#status-of-the-proofs).

## What is formalised

| Paper | Lean | Status |
| --- | --- | --- |
| Def. A.1–A.3, CFGs, parse trees, ambiguity | `Greta/CFG.lean` | definitions |
| Def. A.4–A.6, ranked alphabets, tree automata, ε-transitions | `Greta/Basic.lean`, `Greta/Closure.lean` | definitions, ε-closure proved correct |
| Def. A.7–A.8, runs and acceptance | `Greta/Semantics.lean` | definitions, independent of the closure table |
| Def. A.9, CFG → TA translation | `CFG.toTA` | definition |
| **Thm. A.10**, the translation is language-preserving | `CFG.toTA_correct` | **proved** |
| §2.4, product of tree automata | `Greta/Product.lean` | definition |
| **Intersection**, `L(A ⊗ B) = L(A) ∩ L(B)` | `prodTA_lang` | **proved** |
| §3, tree examples, `ParseTrees`, `P⁻`, `L⁺`, `L⁻` | `Greta/Examples.lean` | definitions |
| §3.1.1, base precedence order `O_bp`, trivial symbols, `HighToLow` | `Greta/Order.lean` | executable |
| Alg. 3.1, `LearnOaOp` | `Greta/Learn.lean` | executable |
| Alg. 3.2, `GenTA` | `Greta/GenTA.lean` | executable |
| Alg. 3.3/3.4, `IntersectTA`, `FindDupStates` | `Greta/Intersect.lean` | executable, ablations as flags |
| Lemma B.2, order preservation | `shift_mono` | arithmetic core proved |
| Thm. 3.1, soundness of `GenTA` | `GenTASound₁`, `GenTASound₂` | stated, not proved |
| **Thm. 3.2**, correctness of Greta | `greta_correct` | **proved from Thm. 3.1** |

## Status of the proofs

Three results carry the development.

`CFG.toTA_correct` (Theorem A.10) says that the automaton built from a grammar accepts
exactly that grammar's complete parse trees. The paper's proof is one line ("Follows
directly from the construction"); here it is an induction over trees that has to line up
the automaton's children-matching with the grammar's right-hand sides.

`prodTA_lang` says that the product of two tree automata recognises the intersection of
their languages. This is the mathematical content of Theorem 3.2. Handling
ε-transitions is the delicate part: the ε-closure of a product state is the product of
the component closures, and that has to be established before the evaluation lemma can be
proved by induction.

`greta_correct` (Theorem 3.2) reproduces the paper's own derivation. Given the two halves
of Theorem 3.1 as hypotheses, it concludes that intersecting the learned automaton with
the grammar's automaton recognises exactly `L_g \ L⁻`.

Theorem 3.1 itself is not proved. Its published argument reasons informally about the
shape of the automaton `GenTA` produces and it excludes some cases outright ("Cases of
symbols at adjacent levels which are involved in a conflict … are explicitly not handled
by the algorithm"). Rather than encode a proof the paper does not give, the two halves
are stated as `GenTASound₁` and `GenTASound₂` and used as hypotheses, so it is visible
exactly what the formalised part of Theorem 3.2 rests on.

The three optimisations of Algorithm 3.3 are likewise not proved language-preserving.
`evalT_mono` and `accepts_mono` in `Greta/Intersect.lean` prove that shrinking an
automaton shrinks its language, which is the soundness half of the reachability
restriction; the rest is covered by testing against the verified product construction.

## Building

Lean 4.33.1 and Mathlib are required; `elan` will pick the toolchain up from
`lean-toolchain`.

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
  greta genta GRAMMAR EXAMPLES          print A_r, the automaton learned from examples
  greta intersect TA1 TA2 [FLAGS]       run Algorithm 3.3 (IntersectTA)
  greta product TA1 TA2                 run the verified textbook product
  greta repair GRAMMAR EXAMPLES [FLAGS] one round of repair, printed as a grammar
  greta checkinter TA1 TA2 RESULT [D]   check L(RESULT) = L(TA1) ∩ L(TA2) on a corpus
  greta accepts TA GRAMMAR [D]          list the corpus trees TA accepts
  greta selftest                        run the built-in test suite
```

The running example of the paper is in `test/grammars/running-example.cfg` with the
rejected tree examples in `test/examples/running-example.ex`:

```
lake exe greta cfg2ta test/grammars/running-example.cfg    # Figure 6
lake exe greta genta  test/grammars/running-example.cfg \
                      test/examples/running-example.ex     # Figure 7
lake exe greta repair test/grammars/running-example.cfg \
                      test/examples/running-example.ex     # the repaired grammar
```

`lake exe greta selftest` checks the formalisation against the paper's figures and then
compares `IntersectTA`, under all five ablation settings of Table 1, with the verified
product construction on the running example and on randomly generated grammars.

## Testing against the OCaml implementation

`ocaml-ref/` builds a driver on top of the reference implementation's own modules, so
that both implementations can be run on the same inputs. The Greta sources are not
vendored: `ocaml-ref/fetch.sh` clones the upstream repository at a pinned commit.

```
cd ocaml-ref && ./fetch.sh && dune build && cd ..
./scripts/difftest.sh
```

The harness compares the two implementations in two ways. Where both produce an
automaton in the shared text format, the outputs are compared byte for byte. Where the
reference renames states (the intersection does), the comparison is by language: the
reference's result is read back into Lean and checked against the verified product
construction on a corpus of trees enumerated from both inputs and from the result.

`docs/testing.md` describes the harness and the text format; `docs/structure.md`
describes the Lean development.

## What the testing found

The translation from grammars to tree automata and the base precedence order agree
byte for byte between the two implementations on every well-formed grammar tested. The
intersection does not. In summary, and with reproducers and diagnoses in
`docs/divergences.md`:

* **The intersection drops transitions that are reachable only through an ε-transition.**
  On the paper's own running example — Figure 6 intersected with Figure 7, in the
  argument order the tool itself uses — the result has no `(IF,6)` transition at all, so
  every `if … then … else` statement is lost from the repaired grammar. Figure 9 of the
  paper does contain that transition, so the published figure cannot be reproduced by the
  current implementation. A two-state automaton reproduces the bug.
* **The intersection can loop forever.** With the arguments in the other order the same
  example does not terminate. The loop is in
  `Operation.collect_eps_connected_states_from_states_pair`, which walks ε-transitions
  without recording the states it has visited.
* **`Converter.cfg_to_ta` raises `Not_found`** on any grammar with a nonterminal that is
  not reachable from the start symbol.
* Three smaller discrepancies between the paper and the code: Algorithm 3.1 as printed
  differs from what `learner.ml` does, the trivial-symbol optimisation of Section 3.1.1
  is not implemented, and `Treeutils.cartesian` does not check that paired terminals are
  equal.

## Layout

```
Greta/            the formalisation (see docs/structure.md)
Main.lean         the command-line driver
ocaml-ref/        driver for the OCaml reference implementation
scripts/          differential-testing harness
test/             grammars, tree examples and automata used by the tests
docs/             design and testing notes, and the list of divergences
```

## References

* Yunjeong Lee, Gokul Rajiv, Ilya Sergey. *Grammar Repair with Examples and Tree
  Automata*. Proc. ACM Program. Lang. 10, OOPSLA1, Article 134 (April 2026).
  [doi:10.1145/3798242](https://doi.org/10.1145/3798242),
  [extended version](https://arxiv.org/abs/2602.18166).
* The Greta tool: <https://github.com/verse-lab/greta> (MIT licensed).
