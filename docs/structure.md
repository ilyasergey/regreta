# The Lean development

How the formalisation is laid out and why it is built the way it is. It assumes Sections 2
and 3 of the paper and some familiarity with Lean 4.

Section numbers refer to the paper's main body. The formal definitions of tree automata,
runs, acceptance and the CFG-to-TA translation are in the supplementary material as
Definitions A.1 to A.10; the Lean source cites them by that numbering.

## Module map

| Module | Contents |
| --- | --- |
| `Greta/Basic.lean` | ranked symbols, `Beta`, transitions, trees, `TA`, the strong induction principle `Tree.rec'` |
| `Greta/Closure.lean` | `EpsReach`, the saturation procedure, `TA.epsTable` and its correctness |
| `Greta/Semantics.lean` | the bottom-up evaluator `TA.evalT`, acceptance, `TA.Lang` |
| `Greta/CFG.lean` | grammars, parse trees, ambiguity, `CFG.toTA`, Theorem A.10 ([`CFG.toTA_correct`](../Greta/CFG.lean#L318)) |
| `Greta/Product.lean` | the product construction and [`prodTA_lang`](../Greta/Product.lean#L377) |
| `Greta/Order.lean` | levels of nonterminals, trivial symbols, `O_bp`, `HighToLow` |
| `Greta/Examples.lean` | tree examples, `ParseTrees`, `P⁻`, `L⁻` |
| `Greta/Learn.lean` | Algorithm 3.1 |
| `Greta/GenTA.lean` | Algorithm 3.2 |
| `Greta/Intersect.lean` | Algorithms 3.3 and 3.4, and the monotonicity lemmas |
| `Greta/Soundness.lean` | Theorem 3.1 as two statements ([`GenTASound₁`](../Greta/Soundness.lean#L46), [`GenTASound₂`](../Greta/Soundness.lean#L54)), Theorem 3.2 derived from them ([`greta_correct`](../Greta/Soundness.lean#L69)), the repair pipeline |
| `Greta/GenTASpec.lean` | the shape of `A_r`; Theorem 3.1 proved ([`genTA_sound`](../Greta/GenTASpec.lean#L663)); Theorem 3.2 with Theorem 3.1 discharged ([`greta_correct_of_spec`](../Greta/GenTASpec.lean#L673)) |
| `Greta/Serialize.lean` | the text format shared with the OCaml driver |
| `Greta/Enumerate.lean` | bounded enumeration of accepted trees, used for language comparison |
| `Greta/Test.lean` | the `selftest` suite |

`Greta/Soundness.lean` also defines [`repairOnce`](../Greta/Soundness.lean#L107), one round
of the repair loop of Figure 4 with Algorithm 3.3 as the intersection, and
[`repairOnceSpec`](../Greta/Soundness.lean#L116), the same round with the product
construction; [`repairOnceSpec_correct`](../Greta/Soundness.lean#L128) is Theorem 3.2
applied to it.

## Design decisions

### Acceptance is a computable function, not an inductive relation

A run is defined (§2.2; Definition A.7) as a map from a tree's nodes to states. Encoding
that directly gives a relation that is mutually inductive with a relation on lists of
children, and Lean's induction principles for mutual inductives are awkward to use.

Instead, `TA.evalT A tbl t` computes the list of states a run may assign to the root of
`t`, by structural recursion, with `TA.matchAll` handling the children. Acceptance is then
a `Bool`, the semantics is decidable by construction, and every proof about it is an
ordinary induction over trees using `Tree.rec'`. `TA.Lang` wraps it as a `Prop` and comes
with a `Decidable` instance.

`TA.evalT` uses `TA.realTrans`, the transitions whose symbol is not `(ε,1)`. An
ε-transition never consumes a node (§2.2; Definition A.6), so it may not match a node's
constructor; only the closure may use it.

### The ε-closure is a parameter, and is proved correct

The evaluator takes a closure table `tbl : σ → List σ`. This matters twice.

[`TA.evalT_congr`](../Greta/Semantics.lean#L204) proves that the evaluator does not depend on which correct table is
supplied, so `TA.Lang` is well defined and can be computed with whichever table is
convenient. For the product construction the convenient table is the product of the two
component tables, which is what makes the evaluation lemma go through.

`TA.epsTable` is the canonical table, computed by saturation. It is proved to compute
`EpsReach` exactly ([`TA.isEpsClosure_epsTable`](../Greta/Closure.lean#L248)). The termination argument is the usual
finite-closure one, and it is spelled out: [`saturate_closed`](../Greta/Closure.lean#L178) shows that a budget exceeding
the size of the state universe suffices, because each step that changes anything strictly
increases the length of a duplicate-free list bounded by that universe.

### States are a type parameter

`TA σ` is parameterised by its state type. The reference implementation fixes states to be
strings and encodes a product state by concatenating the two names, which is not
injective. Here the product construction works at `σ₁ × σ₂` and only the printer turns a
pair into a string. `GenTA` produces states of the datatype `GState`, from which the proofs
read a level back; the printer names them `e0`, `e1`, … as the reference does.

### Two intersections

`Greta/Product.lean` defines the product of §2.4 and proves it correct.
`Greta/Intersect.lean` defines the algorithm Greta runs, with the three optimisations of
Algorithm 3.3 as flags so that the ablations of Table 1 can be reproduced. The two are
related by testing: `lake exe greta selftest` checks, on the running example and on random
grammars, that all five settings agree with the verified product on a corpus of trees.

The soundness half of the reachability optimisation is proved: [`evalT_mono`](../Greta/Intersect.lean#L231) and
[`accepts_mono`](../Greta/Intersect.lean#L249) say that removing transitions, shrinking the closure, or removing final
states can only shrink the language.

### Symbol names

A ranked symbol is `(id, name, rank)` (§2.2, Figure 5). Only `id` matters semantically, it
identifies the production the symbol came from, but `name` is part of symbol equality in
the reference implementation, so the formalisation reproduces the reference's choice of
names (the first terminal of the right-hand side, or the empty string) rather than the
paper's `δ`. This keeps the generated automata comparable byte for byte.

## Reading the main theorems

[`CFG.toTA_correct`](../Greta/CFG.lean#L318) is Theorem A.10, [`prodTA_lang`](../Greta/Product.lean#L377) the
product theorem, [`genTA_sound`](../Greta/GenTASpec.lean#L663) Theorem 3.1 and
[`greta_correct_of_spec`](../Greta/GenTASpec.lean#L673) Theorem 3.2.

```lean
theorem CFG.toTA_correct (g : CFG) (t : Tree) :
    (g.toTA).Lang t ↔ g.isParseTree t = true

theorem prodTA_lang (A : TA σ₁) (B : TA σ₂) (t : Tree) :
    (prodTA A B).Lang t ↔ A.Lang t ∧ B.Lang t

theorem genTA_sound (hspec : LearnedSpec g neg b oa op) (hfits : Fits g neg b oa op)
    (hcov : Covers g b op) (hstart : ∀ A ∈ g.starts, A ∉ trivNts g b)
    (hAc : g.highToLow (g.baseOrder b) op = []) :
    GenTASound₁ g neg (genTA g oa op b) ∧ GenTASound₂ g neg (genTA g oa op b)

theorem greta_correct_of_spec (hspec : LearnedSpec g neg b oa op) (hfits : Fits g neg b oa op)
    (hcov : Covers g b op) (hstart : ∀ A ∈ g.starts, A ∉ trivNts g b)
    (hAc : g.highToLow (g.baseOrder b) op = []) (t : Tree) :
    (prodTA (genTA g oa op b) g.toTA).Lang t ↔ g.repairedLang neg t = true
```

`g.repairedLang neg` is `L_g \ L⁻`: a complete parse tree of `g` that no unselected tree
example rules out. [`GenTASound₁`](../Greta/Soundness.lean#L46) and [`GenTASound₂`](../Greta/Soundness.lean#L54) are the two statements of Theorem 3.1,
`L_r ⊇ L_g \ L⁻` and `L_r ∩ L⁻ = ∅`. The hypotheses are explained in
[`divergences.md`](divergences.md).

`scripts/check-axioms.sh` prints the axioms these theorems depend on:

```
'Greta.CFG.toTA_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Greta.prodTA_lang' depends on axioms: [propext, Classical.choice, Quot.sound]
'Greta.genTA_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Greta.greta_correct_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
```
