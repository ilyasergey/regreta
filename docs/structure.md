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
| `Greta/IntersectSpec.lean` | Algorithm 3.3 proved equal to the product ([`intersectTA_lang`](../Greta/IntersectSpec.lean#L1756)), one optimisation at a time; the `I¹` witness |
| `Greta/Soundness.lean` | Theorem 3.1 as two statements ([`GenTASound₁`](../Greta/Soundness.lean#L52), [`GenTASound₂`](../Greta/Soundness.lean#L60)), Theorem 3.2 derived from them ([`greta_correct`](../Greta/Soundness.lean#L75)), the repair pipeline as run and as verified ([`repairOnce_lang`](../Greta/Soundness.lean#L157)) |
| `Greta/GenTASpec.lean` | the shape of `A_r`; Theorem 3.1 proved ([`genTA_sound`](../Greta/GenTASpec.lean#L679)); Theorem 3.2 with Theorem 3.1 discharged ([`greta_correct_of_spec`](../Greta/GenTASpec.lean#L689)) |
| `Greta/LearnSpec.lean` | Lemma B.2 ([`relayerOrder_ordersOf_above`](../Greta/LearnSpec.lean#L370), [`relayerOrder_replicates`](../Greta/LearnSpec.lean#L475)); the learner against `LearnedSpec`, `Fits` and `Covers`; Theorem 3.2 for the pipeline ([`repairOnceSpec_correct_pipeline`](../Greta/LearnSpec.lean#L1144)) |
| `Greta/RefLearn.lean` | Algorithm 3.1 *as shipped*, the back-edges of `learn_ta`, and the restated Lemma B.2 ([`refGenTA_specReach`](../Greta/RefLearn.lean)) |
| `Greta/Serialize.lean` | the text format shared with the OCaml driver |
| `Greta/Enumerate.lean` | bounded enumeration of accepted trees, used for language comparison |
| `Greta/Test.lean` | the `selftest` suite |

`Greta/Soundness.lean` also defines [`repairOnce`](../Greta/Soundness.lean#L113), one round
of the repair loop of Figure 4 with Algorithm 3.3 as the intersection, and
[`repairOnceSpec`](../Greta/Soundness.lean#L122), the same round with the product
construction. [`repairOnce_lang`](../Greta/Soundness.lean#L157) shows the two recognise the same
language, given distinct start nonterminals, so Theorem 3.2 applies to either
([`repairOnceSpec_correct`](../Greta/Soundness.lean#L134), [`repairOnce_correct`](../Greta/Soundness.lean#L171)).

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
Algorithm 3.3 as flags so that the ablations of Table 1 can be reproduced.
`Greta/IntersectSpec.lean` proves the two equal ([`intersectTA_lang`](../Greta/IntersectSpec.lean#L1756)),
one optimisation at a time: the worklist loop by an ε-elimination lemma and a fuel
argument in the style of `saturate_closed`, duplicate merging as a quotient by a
language-preserving equivalence, ε-introduction by a subsumption lemma that needs no
invariant over the loop. Two decidable side conditions remain; the default setting
discharges both, and one of the ablations does not ([`divergences.md` §5](divergences.md#d5)).
`lake exe greta selftest` still compares all five settings with the product on enumerated
trees, as a check that the definitions the proof is about are the ones that execute.

[`evalT_mono`](../Greta/Intersect.lean#L240) and [`accepts_mono`](../Greta/Intersect.lean#L258)
are the easy half, kept because the proof of the reachability stage uses them: removing
transitions, shrinking the closure, or removing final states can only shrink the language.

### Symbol names

A ranked symbol is `(id, name, rank)` (§2.2, Figure 5). Only `id` matters semantically, it
identifies the production the symbol came from, but `name` is part of symbol equality in
the reference implementation, so the formalisation reproduces the reference's choice of
names (the first terminal of the right-hand side, or the empty string) rather than the
paper's `δ`. This keeps the generated automata comparable byte for byte.

## Reading the main theorems

[`CFG.toTA_correct`](../Greta/CFG.lean#L318) is Theorem A.10, [`prodTA_lang`](../Greta/Product.lean#L377) the
product theorem, [`genTA_sound`](../Greta/GenTASpec.lean#L679) Theorem 3.1,
[`greta_correct_of_spec`](../Greta/GenTASpec.lean#L689) Theorem 3.2, and
[`intersectTA_lang`](../Greta/IntersectSpec.lean#L1756) the correctness of Algorithm 3.3.

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

theorem intersectTA_lang (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts)
    (hnd : opts.reachability = true → (pairs A.finals B.finals).Nodup)
    (hkeep : DedupKeepsFinals A B opts) (t : Tree) :
    (intersectTA A B opts).Lang t ↔ A.Lang t ∧ B.Lang t
```

`g.repairedLang neg` is `L_g \ L⁻`: a complete parse tree of `g` that no unselected tree
example rules out. [`GenTASound₁`](../Greta/Soundness.lean#L52) and [`GenTASound₂`](../Greta/Soundness.lean#L60) are the two statements of Theorem 3.1,
`L_r ⊇ L_g \ L⁻` and `L_r ∩ L⁻ = ∅`. The hypotheses are explained in
[`divergences.md`](divergences.md); `Fits` is false whenever a production brackets its own
nonterminal, so `genTA_sound₁` says nothing about such grammars ([§8](divergences.md#d8)).
`Greta/LearnSpec.lean` decides `LearnedSpec` and the other conditions on the input, and
[`repairOnceSpec_correct_pipeline`](../Greta/LearnSpec.lean#L1144) is Theorem 3.2 for the
pipeline of Figure 4 with them all discharged by the check.

`scripts/check-axioms.sh` prints the axioms these theorems depend on:

```
'Greta.CFG.toTA_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Greta.prodTA_lang' depends on axioms: [propext, Classical.choice, Quot.sound]
'Greta.genTA_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Greta.greta_correct_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Greta.intersectTA_lang' depends on axioms: [propext, Classical.choice, Quot.sound]
```

together with the rest of the theorems named in this document and in the README.
