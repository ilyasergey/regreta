# The Lean development

This note describes how the formalisation is laid out and why it is built the way it is.
It assumes Sections 2 and 3 of the paper and some familiarity with Lean 4.

Section numbers refer to the main body. The formal definitions of tree automata, of runs
and acceptance, and of the CFG-to-TA translation are only in the paper's supplementary
material, where they are Definitions A.1–A.10; the Lean source cites them by that
numbering, and this note gives the corresponding section of the main body alongside.

## Module map

| Module | Contents |
| --- | --- |
| `Greta/Basic.lean` | ranked symbols, `Beta`, transitions, trees, `TA`, the strong induction principle `Tree.rec'` |
| `Greta/Closure.lean` | `EpsReach`, the saturation procedure, `TA.epsTable` and its correctness |
| `Greta/Semantics.lean` | the bottom-up evaluator `TA.evalT`, acceptance, `TA.Lang` |
| `Greta/CFG.lean` | grammars, parse trees, ambiguity, `CFG.toTA`, Theorem A.10 |
| `Greta/Product.lean` | the product construction and `prodTA_lang` |
| `Greta/Order.lean` | levels of nonterminals, trivial symbols, `O_bp`, `HighToLow` |
| `Greta/Examples.lean` | tree examples, `ParseTrees`, `P⁻`, `L⁺`, `L⁻` |
| `Greta/Learn.lean` | Algorithm 3.1 |
| `Greta/GenTA.lean` | Algorithm 3.2 |
| `Greta/Intersect.lean` | Algorithms 3.3 and 3.4, and the monotonicity lemmas |
| `Greta/Soundness.lean` | Theorem 3.1 as statements, Theorem 3.2 proved from them, the repair pipeline |
| `Greta/Serialize.lean` | the text format shared with the OCaml driver |
| `Greta/Enumerate.lean` | bounded enumeration of accepted trees, used for language comparison |
| `Greta/Test.lean` | the `selftest` suite |

What is proved and what is not is set out in the README; `proof-plan.md` is a plan for
closing the gaps.

`Greta/Soundness.lean` also defines [`repairOnce`](../Greta/Soundness.lean#L122), one round
of the repair loop of Figure 4, and `repairOnceSpec`, the same round with the verified
product in place of Algorithm 3.3; `repairOnceSpec_correct` is Theorem 3.2 applied to it.

## Design decisions

### Acceptance is a computable function, not an inductive relation

A run is defined (§2.2; Definition A.7) as a map from a tree's nodes to states. Encoding that directly gives
a relation that is mutually inductive with a relation on lists of children, and Lean's
induction principles for mutual inductives are awkward to use.

Instead, `TA.evalT A tbl t` computes the list of states a run may assign to the root of
`t`, by structural recursion, with `TA.matchAll` handling the children. Acceptance is
then a `Bool`, the semantics is decidable by construction, and every proof about it is an
ordinary induction over trees using `Tree.rec'`. `TA.Lang` wraps it as a `Prop` and comes
with a `Decidable` instance.

`TA.evalT` uses `TA.realTrans`, the transitions whose symbol is not `(ε,1)`. An
ε-transition never consumes a node (§2.2; Definition A.6), so it may not be used to match
a node's constructor; only the closure may use it.

### The ε-closure is a parameter, and is proved correct

The evaluator takes a closure table `tbl : σ → List σ`. This matters twice.

`TA.evalT_congr` proves that the evaluator does not depend on *which* correct table is
supplied, so `TA.Lang` is well defined and can be computed with whichever table is
convenient. For the product construction the convenient table is the product of the two
component tables, which is what makes the evaluation lemma go through.

`TA.epsTable` is the canonical table, computed by saturation. It is proved to compute
`EpsReach` exactly (`TA.isEpsClosure_epsTable`). The termination argument is the usual
finite-closure one, and it is spelled out: `saturate_closed` shows that a budget
exceeding the size of the state universe suffices, because each step that changes
anything strictly increases the length of a duplicate-free list bounded by that universe.

### States are a type parameter

`TA σ` is parameterised by its state type. The reference implementation fixes states to
be strings and encodes a product state by concatenating the two names, which is not
injective. Here the product construction works at `σ₁ × σ₂` and only the printer turns a
pair into a string. Executable algorithms are instantiated at `σ := String` so that they
line up with the reference implementation.

### Two intersections

`Greta/Product.lean` defines the product of §2.4 and proves it correct.
`Greta/Intersect.lean` defines the algorithm Greta actually runs, with the three
optimisations of Algorithm 3.3 as flags so that the ablations of Table 1 can be
reproduced. The two are related by testing: `lake exe greta selftest` checks, on the
running example and on random grammars, that all five settings agree with the verified
product on a corpus of trees.

The soundness half of the reachability optimisation is proved: `evalT_mono` and
`accepts_mono` say that removing transitions, shrinking the closure, or removing final
states can only shrink the language.

### Symbol names

A ranked symbol is `(id, name, rank)` (§2.2, Figure 5). Only `id` matters semantically —
it identifies the production the symbol came from — but `name` is part of symbol equality
in the reference implementation, so the formalisation reproduces the reference's choice of
names (the first terminal of the right-hand side, or the empty string) rather than the
paper's `δ`. This keeps the generated automata comparable byte for byte.

## Reading the main theorems

```lean
theorem CFG.toTA_correct (g : CFG) (t : Tree) :
    (g.toTA).Lang t ↔ g.isParseTree t = true

theorem prodTA_lang (A : TA σ₁) (B : TA σ₂) (t : Tree) :
    (prodTA A B).Lang t ↔ A.Lang t ∧ B.Lang t

theorem greta_correct (g : CFG) (neg : List TreeExample) (Ar : TA String)
    (h₁ : GenTASound₁ g neg Ar) (h₂ : GenTASound₂ g neg Ar) (t : Tree) :
    (prodTA Ar g.toTA).Lang t ↔ g.repairedLang neg t = true
```

`g.repairedLang neg` is `L_g \ L⁻`: a complete parse tree of `g` that no unselected tree
example rules out. `GenTASound₁` and `GenTASound₂` are the two statements of Theorem 3.1,
`L_r ⊇ L_g \ L⁻` and `L_r ∩ L⁻ = ∅`.

To see what the theorems depend on, put

```lean
import Greta
#print axioms Greta.CFG.toTA_correct
#print axioms Greta.prodTA_lang
#print axioms Greta.greta_correct
```

in a file and run `lake env lean` on it:

```
'Greta.CFG.toTA_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Greta.prodTA_lang' depends on axioms: [propext, Classical.choice, Quot.sound]
'Greta.greta_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`scripts/check-axioms.sh` does this.
