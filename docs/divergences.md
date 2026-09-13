# Theory, implementation, and what is proved

The paper makes three kinds of claim: theorems (3.1, 3.2, A.10 and Lemmas B.1, B.2),
algorithms (3.1 to 3.4), and an implementation that is said to realise them. This note
records where the Lean statements differ from the paper's, why, and what each difference
means in practice. Defects found in the OCaml code are catalogued separately in
[`reference-defects.md`](reference-defects.md).

It is written in three layers. [The verdict](#the-verdict) says in a line each what the
nine differences are and what it would take to settle them; [the table](#the-nine-differences)
puts each one beside the paper's claim and this development's; and the numbered sections
after it give the detail, the witness, and the Lean. Every layer links to the next.

Section, algorithm and theorem numbers are those of the paper's main body; Definitions A.n
and the proofs of Lemmas B.1 and B.2 are in the supplementary material.

## The verdict

Nine differences, in the order the paper builds the pipeline. Three ask for a change to an
algorithm, one of them a single line. The rest are prose.

**Do they invalidate the paper's general claims?** The approach is sound and the evaluation
stands: the tool that was evaluated has neither serious defect in the form the paper prints,
because it is Algorithm 3.1 *as printed* that loses bracketed parses, not the code that was
run. What does not survive is the statement of Theorem 3.1. Part (1) is false for any
grammar that brackets its own nonterminal, and the theorem as a whole holds only under the
acyclicity restriction its own proof already sets aside. Neither is a matter of wording,
and both are repairable: adopt the construction the code already uses, and state the
restriction. Table 1's `I¹` ablation also measures a construction that is not
language-preserving, though the default configuration it is compared against is.

* **Ordering a conflict group.** The paper says each group is totally ordered, but never
  says how to order it, and a comparison sort silently drops constraints. [→ 9](#d9)
  * *Here:* Kahn's algorithm, every constraint proved respected, cyclic examples reported.
  * *Paper:* should specify the construction, and say contradictory examples are rejected.
  * *Code:* no change; it detects the case and exits.

* **What Algorithm 3.1 owes Algorithm 3.2.** The stages are never separated, so the
  conditions the second relies on are never written down. [→ 2](#d2)
  * *Here:* four decidable conditions, checked on the input by the tool.
  * *Paper:* should state them with Algorithm 3.1, including that `M_to` keeps the
    singleton conflict groups.
  * *Code:* no change; it builds the singletons.

* **Brackets — needs an algorithm changed.** Algorithm 3.1 copies a bracketing production
  to every precedence level and keeps its contents at that level, so `x * (y + z)` is lost.
  Theorem 3.1(1) is false on the paper's own Section 1 grammar. [→ 8](#d8)
  * *Here:* the witness is in the self-test, `Fits` is reported false on exactly these
    grammars, and the shipped learner is formalised and shown to keep the parse.
  * *Paper:* should replace the replication step with the back-edge construction the code
    already uses, and reprove Lemma B.2 and Theorem 3.1(1) for it.
  * *Code:* no change; it is already right, and should not be moved towards the paper.

* **Lemma B.2** is about Algorithm 3.1 as printed, not the learner that ships. [→ 4](#d4)
  * *Here:* stated and proved for both, in the form each algorithm calls for.
  * *Paper:* should restate it for the back-edge algorithm, with the bracket fix above.
  * *Code:* no change.

* **Lemma B.1** mentions no child position, so it cannot cover the associativity case its
  own use in the proof of Theorem 3.1(2) needs. [→ 3](#d3)
  * *Here:* split into two statements, both proved, with the position supplied.
  * *Paper:* should add the child position.
  * *Code:* no change.

* **Algorithm 3.2** applies one associativity restriction where a symbol may carry two, and
  dropping one makes Theorem 3.1(2) fail for it. [→ 6](#d6)
  * *Here:* every restriction is applied.
  * *Paper:* should write "for all `p`" instead of "if there exists `p`".
  * *Code:* no change; it already folds over all of them.

* **Figure 7** contradicts its own footnote 3 in one row. [→ 7](#d7)
  * *Here:* the footnote is implemented and the corrected figure reproduced exactly.
  * *Paper:* should fix the row.
  * *Code:* no change.

* **Cycles in the symbol order — needs an algorithm changed.** Theorem 3.1 is printed
  without hypotheses, but its proof sets this case aside and the theorem is false there.
  [→ 1](#d1)
  * *Here:* the hypothesis is explicit and decidable, the tool checks it, and the witness
    is in the self-test.
  * *Paper:* should state the restriction, or change Algorithm 3.2's cycle rule to give
    each nonterminal of a production its own level.
  * *Code:* follows whichever the paper chooses.

* **Algorithm 3.3.** Its agreement with the textbook product was the one step taken on
  trust. [→ 5](#d5)
  * *Here:* proved, for all five settings of Table 1, under two decidable side conditions
    that the configuration Greta runs discharges by itself.
  * *Paper:* should filter the *images* of the accepting pairs, not the accepting pairs
    themselves; as printed, the `I¹` ablation of Table 1 can lose trees.
  * *Code:* the same one-line change; the default configuration is unaffected.

The OCaml has two further defects of its own, in code the paper does not describe; they
touch none of the theorems and are catalogued in
[`reference-defects.md`](reference-defects.md).

## The nine differences

Each row links to the section that gives the detail.

| | Paper | Here | In practice |
| --- | --- | --- | --- |
| <a id="d1"></a>[1](#1-theorem-31-needs-acyclicity) | Theorem 3.1 holds unconditionally | it holds when `HighToLow` reports nothing | **real restriction.** On a grammar with a cycle, one round of repair can leave a rejected tree in the language. The paper's proof excludes the case. |
| <a id="d2"></a>[2](#2-algorithm-31s-inputs-get-a-specification) | `O_a`, `O_p` are whatever the earlier stages produce | [`LearnedSpec`](../Greta/GenTASpec.lean#L234), [`Fits`](../Greta/GenTASpec.lean#L482), [`Covers`](../Greta/GenTASpec.lean#L610) say what they must satisfy | bookkeeping. Implied by the definitions; one clause is easy to lose in an implementation. |
| <a id="d3"></a>[3](#3-lemma-b1-gains-a-child-position) | Lemma B.1 relates two symbols | it relates two symbols at a child position | the published lemma cannot cover associativity examples; the restated one does. |
| <a id="d4"></a>[4](#4-lemma-b2-is-about-the-published-algorithm-31) | Lemma B.2 is about Greta | it is about Algorithm 3.1 as printed; the shipped learner gets a separate, reachability-flavoured restatement | the shipped learner is a different algorithm, formalised in [`Greta/RefLearn.lean`](../Greta/RefLearn.lean); on `arith` the two repair to different languages. |
| <a id="d5"></a>[5](#5-theorem-32-is-about-the-product-construction) | Theorem 3.2 is about Algorithm 3.3's output | it is about the product construction, and Algorithm 3.3 is separately proved equal to it | resolved for the configuration Greta runs, which needs no side condition beyond duplicate-free final states. **Real defect in the `I¹` ablation:** with reachability off, merging can elect a non-accepting representative and the intersection loses trees. |
| <a id="d6"></a>[6](#6-algorithm-32-applies-every-associativity-restriction) | `if ∃p, (s,p) ∈ O_a` | every such `p` is applied | pseudocode clarification; the reference already does this. |
| <a id="d7"></a>[7](#7-figure-7-has-a-typo) | Figure 7's `(TINT,4)` row at `e2` | `TINT ident EQ e2` | typo. |
| <a id="d8"></a>[8](#8-theorem-311-is-false-for-grammars-with-brackets) | Theorem 3.1(1) holds | it fails whenever a production brackets its own nonterminal | **real defect.** On the grammar of Section 1 the repaired grammar loses `x * (y + z)`. The shipped learner is not affected. |
| <a id="d9"></a>[9](#9-linearising-a-conflict-group-needs-a-topological-sort) | `M_to`'s groups are "totally ordered" | they are linearised by Kahn's algorithm, which reports contradictory examples | **real defect if sorted by comparison.** A merge sort can drop a constraint it never tests; the reference detects the case and exits. |

## What is proved

Five results carry the development, all in Lean with no `sorry` and no axioms beyond
`propext`, `Classical.choice` and `Quot.sound`.

[`CFG.toTA_correct`](../Greta/CFG.lean#L318) is Theorem A.10: the automaton built from a
grammar accepts exactly that grammar's complete parse trees. The paper proves it in one
line; here it is an induction over trees that lines up the automaton's child matching with
the grammar's right-hand sides.

[`prodTA_lang`](../Greta/Product.lean#L377) says the product of two tree automata
recognises the intersection of their languages. The ε-closure of a product state has to be
shown to be the product of the component closures before the evaluation lemma goes through.

[`genTA_sound`](../Greta/GenTASpec.lean#L679) is Theorem 3.1, both halves. The proof pins
down the four groups of transitions `GenTA` emits, shows the ε-graph is the chain
`e₀ ←ε e₁ ←ε … ←ε eₘ`, and deduces that ε-reachability between ordered states is `≤` on
levels. After that every argument is arithmetic: statement (2) by induction over the tree,
statement (1) by building a run top-down.

[`greta_correct_of_spec`](../Greta/GenTASpec.lean#L689) is Theorem 3.2 assembled from the
three, with the product construction as the intersection. Its hypotheses are five decidable
conditions on the learned order: [`LearnedSpec`](../Greta/GenTASpec.lean#L234),
[`Fits`](../Greta/GenTASpec.lean#L482), [`Covers`](../Greta/GenTASpec.lean#L610), that no
start nonterminal is trivial, and that `HighToLow` reports nothing. Sections 1 and 2 below
say where each comes from.

[`intersectTA_lang`](../Greta/IntersectSpec.lean#L1756) proves that Algorithm 3.3, the
optimised intersection Greta runs, recognises the same language as the product
construction, so the paper's chain of correctness no longer has a link that rests on
testing (Section 5). [`repairOnce_correct`](../Greta/Soundness.lean#L171) carries Theorem
3.2 over to one round of repair as the tool actually runs it.

## 1. Theorem 3.1 needs acyclicity

[`genTA_sound`](../Greta/GenTASpec.lean#L679) carries the hypothesis

```lean
(hAc : g.highToLow (g.baseOrder b) op = [])
```

`HighToLow` (§3.1.3) finds a production whose head sits at a higher order than one of its
nonterminal children, and Algorithm 3.2's last loop adds `δ_F(e_{o_h}, ē_{o_l}, s_h)` for
it: a transition from a high order back to a low one. That is exactly the parent-above-child
shape the level argument otherwise rules out. If `s_h` is the top symbol of a rejected
example, the cycle transition re-permits the pattern `O_p` was arranged to forbid; and
because it is built with every child at `e_{o_l}`, it ignores `O_a` as well.

The paper's proof of Lemma B.1 ends:

> Cases of symbols at adjacent levels which are involved in a conflict (i.e. they are
> involved in a cycle) are explicitly not handled by the algorithm.

and Section 3.1.1 motivates the order with "In the absence of cycles, a symbol at a higher
order always appears deeper in the parse tree than a symbol at a lower order." So the
unconditional statement was never supported by its proof.

**The witness.** `test/grammars/cycle.cfg` is `S → S + S | T | x`, `T → S * S | y`. `T` is
at level 1, `S` at level 0, and `T → S * S` nests `S` again, so `HighToLow` reports
`(STAR,3)`. The one rejected example is `Eg((STAR,3), (PLUS,3), 0)`. `O_p` already puts
`STAR` above `PLUS`, so the ordinary transitions forbid the nesting, but `GenTA` also emits
`e1 ←(STAR,3) e0 STAR e0`, and

```
S → T → (S + S) * S
```

is accepted by `A_r`, is a parse tree of the grammar, and contains the rejected pattern.
[`testCycle`](../Greta/Test.lean#L281) checks all three facts. The repaired grammar
`lake exe greta repair` prints keeps the production `(e0,T) → (e0,S) STAR (e0,S)`, so one
round of repair does not remove the ambiguity the user pointed at. What the outer loop of
Figure 4 does next is outside the formalisation.

**Where it bites.** A cycle in the order needs a nonterminal at a deeper level to take a
shallower one as a direct child. The running example has none; neither does any grammar
of `test/` except the witness. The hypothesis is decidable, and `greta` computes it, so a
tool can check it on its input rather than have the theorem silently not apply.

Statement (1) needs acyclicity for the opposite reason. Without the cycle transitions the
level assignment has nowhere to go when a child's nonterminal sits above its parent's;
with them, `δ_F(e_{o_h}, ē_{o_l}, s_h)` sends every nonterminal of the production to one
level, so a production with two nonterminal children needing different levels is not
covered. Relaxing `hAc` would mean giving each nonterminal its own level in that rule,
which is a change to Algorithm 3.2.

## 2. Algorithm 3.1's inputs get a specification

Algorithms 3.1 and 3.2 take `M_to`, `O_a` and `O_p` as arguments, so a theorem about them
has to say what those arguments satisfy. Four hypotheses, all decidable, and — this is the
point of [8](#d8) — not all of them true:

* [`LearnedSpec`](../Greta/GenTASpec.lean#L234): `O_p` mentions only symbols of `g`; no
  symbol of a tree example is trivial (§3.1.1 excludes those from conflicts); a rejected
  precedence example puts its top strictly above its bottom; a rejected associativity
  example is recorded in `O_a`; a symbol in an associativity conflict sits at exactly one
  order.
* [`Fits`](../Greta/GenTASpec.lean#L482): a symbol that may legitimately sit at child
  position `k` of an `s`-node at level `i` has a level at or above the one the transition
  demands. This is what makes the level assignment of statement (1) succeed.
* [`Covers`](../Greta/GenTASpec.lean#L610): every non-trivial symbol has a level.
* No start nonterminal is trivial.

The paper leaves these implicit because it never separates the stages. One of them is
easy to lose when implementing: `M_to` must range over all of `S_E`, singletons included.
`S_C` is the symbols in a precedence **or an associativity** conflict, so a symbol whose
only conflict is with itself is a singleton member of `S_E`, and Algorithm 3.1's last
clause only fires for symbols that are in a group. Build `M_to` from the orders with two or
more conflicting symbols and Theorem 3.1(1) is false: on
`S → S + S | S * S | (S) | x | y | z` with the single example `Eg((PLUS,3),(PLUS,3),2)`,
`O_p` stays `{0 ↦ everything}` and `GenTA` emits a transition naming a state `e₁` that does
not exist, so every tree containing a `+` is rejected, `x + y` included. The reference
implementation constructs the singletons deliberately (`assoc_only` in
`Examples.form_total_order_among_op_symbols_from_same_group`);
[`toMapOf`](../Greta/Learn.lean#L223) keeps them, and `testAssocOnly` checks the case.

**The tool checks them.** [`learnedSpecB`](../Greta/LearnSpec.lean#L913) decides `LearnedSpec`,
[`fitsB`](../Greta/LearnSpec.lean#L1011) is a sufficient condition for `Fits`,
[`coversB`](../Greta/LearnSpec.lean#L1061) for `Covers`, and
[`pipelineFullOK`](../Greta/LearnSpec.lean#L1132) bundles all four with acyclicity, so
[`repairOnceSpec_correct_pipeline`](../Greta/LearnSpec.lean#L1144) states Theorem 3.2 for the
pipeline of Figure 4 with every side condition discharged by computation rather than
assumed. Two of the four also hold outright:
[`ofGrammar_learnOaOp`](../Greta/LearnSpec.lean#L249) and
[`assocRecorded_learnOaOp`](../Greta/LearnSpec.lean#L60).

`Fits` is the one that fails, and it fails for a reason rather than by accident: it is what
statement (1) needs of the learned order, and [8](#d8) shows statement (1) itself is false
for grammars with brackets. The check reports `false` on the paper's running example and on
`arith`, and `true` on `dangling-else`, which has no bracketing production.

`Fits` was also too strong as first written. It quantified over every pair of grammar
symbols, including pairs no parse tree can put in a parent/child relation, which made it
false even where statement (1) is fine. It is now guarded by
[`ChildAt`](../Greta/GenTASpec.lean#L474), which is what the proof of `genTA_sound₁`
actually appeals to.

## 3. Lemma B.1 gains a child position

The paper's Lemma B.1 is

> for `(s₁,o₁), (s₂,o₂) ∈ O_p` where `s₁` and `s₂` are involved in a precedence conflict,
> `o₁ ≤ o₂ ⟺ L_r includes trees with s₁ directly above s₂`

which mentions no child position, so it cannot cover associativity examples, where the
restriction is at one position only. Yet the proof of Theorem 3.1(2) appeals to it for
exactly those.

Here the content of B.1 is split in two and both parts are proved:
[`epsReach_lvl`](../Greta/GenTASpec.lean#L160), ε-reachability between ordered states is
`≤` on levels, and [`evalT_genTA_inv`](../Greta/GenTASpec.lean#L178), every state assigned
to a node is the level of that node's symbol. The position enters through `oaFill`, and
`matchesHere_false` does the work B.1 was meant to do, for precedence and associativity
examples alike.

## 4. Lemma B.2 is about the published Algorithm 3.1

B.2's proof appeals to "the construction of `O_p`, which copies the non-conflicting symbols
to each newly inserted order". That is what Algorithm 3.1 prints, and it is not what
`learner.ml` does; see
[D7](reference-defects.md#d7-algorithm-31-as-printed-is-not-what-learnerml-does).
[`relayerOrder`](../Greta/Learn.lean#L43) implements the published version. A proof about
the shipped one needs a different, reachability-flavoured invariant; both are given below.

[`shift_mono`](../Greta/Soundness.lean#L31) is B.2's arithmetic core. For the published
algorithm the lemma is stated and proved in two halves:
[`relayerOrder_ordersOf_above`](../Greta/LearnSpec.lean#L370), that one re-layering moves
every order strictly above its band by a single offset, so relative order is preserved
exactly rather than merely weakly; and
[`relayerOrder_replicates`](../Greta/LearnSpec.lean#L475), the replication step B.2's proof
appeals to. What statement (1) needs on top of them is
[`Fits`](../Greta/GenTASpec.lean#L482), the same idea localised to one parent/child pair.

For the shipped algorithm it *is* stated, in [`Greta/RefLearn.lean`](../Greta/RefLearn.lean).
`refRelayerOrder` and `refLearnOaOp` there are `Learner.update_op_per_ord_amb_symsls` and
`Learner.learn_op`, `refGenTA` is `Learner.learn_ta` with the back-edges the special loop
symbols get, and the two halves of the restated lemma are

* [`refGenTA_specReach`](../Greta/RefLearn.lean): a non-conflicting symbol set aside from
  order `d` ends at an order `l ≥ d`, its transition carries `e_d` at every unrestricted
  right-hand-side position, and `e_l` is ε-promoted to `e_d` — *reachable from* the
  original order where the published algorithm is *present at* it;
* [`refRelayerFold_no_inversion`](../Greta/RefLearn.lean): re-layering never inverts the
  relative order of two symbols no conflict group mentions.

The first rests on [`refLearnOaOp_specDominated`](../Greta/RefLearn.lean), which proves
`d ≤ l` for the loop, under the discipline `Learner.learn_op` runs it with (orders visited
downwards, groups drawn from the order they are attached to); that the concrete
`toMapOf ∘ baseOrder` input satisfies the discipline is checked by `lake exe greta
selftest`, not proved.

The two algorithms do not agree. On `test/grammars/arith.cfg` with a single rejected
right-associative `PLUS`, the published one loses `x + ((x + x) * x)` — at `e1` the copy
of `(STAR,3)` sends its children to `e1`, where `(PLUS,3)` does not live — while the
back-edge of the shipped one keeps it. Theorem 3.1(1) requires it to be kept, so on that
input it is the *published* algorithm that is wrong. The self-test pins the witness down.
[8](#8-theorem-311-is-false-for-grammars-with-brackets) gives the general statement: the
replication step is wrong for any production that brackets its own nonterminal, and the
grammar of Section 1 is already a counterexample.

## 5. Theorem 3.2 is about the product construction

The paper's Theorem 3.2 is about the output of Algorithm 3.3.
[`greta_correct_of_spec`](../Greta/GenTASpec.lean#L689) is about
[`prodTA`](../Greta/Product.lean#L63), the product of Section 2.4, which
[`prodTA_lang`](../Greta/Product.lean#L377) proves recognises the intersection.

The two are now identified by proof rather than by testing.
[`intersectTA_lang`](../Greta/IntersectSpec.lean#L1756) shows that Algorithm 3.3 recognises
`L(A) ∩ L(B)`, and [`intersectTA_lang_prodTA`](../Greta/IntersectSpec.lean#L1764) states it
as agreement with the product; [`repairOnce_correct`](../Greta/Soundness.lean#L171) carries
Theorem 3.2 over to one round of repair as the tool runs it. Each of the three
optimisations needs its own argument, and each is proved separately in
[`Greta/IntersectSpec.lean`](../Greta/IntersectSpec.lean):

* **Reachability** ([`stage0_lang`](../Greta/IntersectSpec.lean#L772)). The loop is not a
  sub-automaton of the product: `transAt` looks *through* the ε-transitions of the two
  inputs and `crossTrans` retargets the result at the pair it came from, so both
  ε-closures are inlined and the output has none of its own. That needs an ε-elimination
  lemma ([`mem_epsDown_iff`](../Greta/IntersectSpec.lean#L236), the mirror image of
  `TA.closeFrom` for the reversed ε-graph) and a fuel-adequacy argument
  ([`reachLoop_spec`](../Greta/IntersectSpec.lean#L426)): the potential
  `|worklist| + (|Q_A × Q_B| − |explored|)` drops by exactly one per iteration, so the
  printed budget does reach a fixed point.
* **Duplicate merging** ([`merge_lang`](../Greta/IntersectSpec.lean#L1384)) is a quotient by
  a language-preserving equivalence. Its key lemma is
  [`sigEq_evalT`](../Greta/IntersectSpec.lean#L926): two states whose incoming transitions
  agree once each is replaced by the placeholder of `betaSubst` accept the same trees, by
  induction on the size of the tree — the placeholder positions are exactly where the twin
  transition names the other state, and the children there are strictly smaller.
* **ε-introduction** ([`introEpsAll_lang`](../Greta/IntersectSpec.lean#L1374)) needs no loop
  invariant in the end, because each step justifies itself: by
  [`shapes_ev`](../Greta/IntersectSpec.lean#L1171), when every transition shape of `e_i` is
  also a shape of `e_j` then everything `e_i` accepts `e_j` accepts, so the new ε-edge adds
  nothing while the transitions the step deletes are recovered through `e_i`. In
  particular **no acyclicity hypothesis is needed**: the argument never looks at the
  ε-graph as a whole, so a cycle would be harmless here, even though one makes the
  reference implementation diverge
  ([D2](reference-defects.md#d2-the-intersection-can-fail-to-terminate)).

Two decidable side conditions remain, and
[`intersectTA_lang_default`](../Greta/IntersectSpec.lean#L1772) discharges both for the
configuration Greta actually runs.

**The accepting pairs must be listed once each.** The fuel of Algorithm 3.3 is
`|Q_A| · |Q_B| + 1`, one iteration per product state, so a pair queued twice leaves the
budget one short. In the pipeline `A_r` has the single accepting state `e₀`, so this asks
only that the grammar list each start nonterminal once
([`repairOnce_lang`](../Greta/Soundness.lean#L157)). It is vacuous when
`reachability := false`.

**Merging must not elect a non-accepting representative**
([`DedupKeepsFinals`](../Greta/IntersectSpec.lean#L1625)). Algorithm 3.4 rewrites every
state to a representative of its class, and Algorithm 3.3 keeps as final exactly those
accepting pairs that *survive* the rewriting; nothing in the pseudocode makes the
representative of a class containing an accepting pair accepting. With
`reachability := true` it cannot go wrong
([`dedupKeepsFinals_of_reachability`](../Greta/IntersectSpec.lean#L1640)): the worklist
starts from the accepting pairs, so they form a prefix of the state list, `findDupStates`
emits `(e_i, e_j)` before `(e_j, e_i)` when `e_i` comes first, and the guard in the fold
then blocks the reversed pair — every state is merged into an earlier one, and an
accepting pair can only be merged into another accepting pair.

**With reachability off it does go wrong.** `DedupWitness`, at the end of
[`Greta/IntersectSpec.lean`](../Greta/IntersectSpec.lean) and checked at build time, is two
automata over the single symbol `(a,1)`: `A` has one accepting state with `qA ←(a,1) a`,
and `B` has `rB ←(a,1) a` and `qB ←(a,1) a` with `qB` accepting and `rB` listed first. Both
accept the one-node tree, `prodTA` accepts it, `intersectTA` with the default flags accepts
it, and `intersectTA A B {reachability := false}` has no final states at all: without the
worklist the pairs are enumerated as `Q_A × Q_B`, `(qA,rB)` comes first, it is elected
representative of `(qA,qB)`, and the accepting pair does not survive. So the `I¹` ablation
of Table 1 is not language-preserving as printed, while the `I^def` that is measured is.
Filtering the *images* of the accepting pairs instead of the accepting pairs themselves
would remove the side condition.

## 6. Algorithm 3.2 applies every associativity restriction

Algorithm 3.2 reads `if ∃p, (s, p) ∈ O_a then …`, which picks one `p`. A symbol can carry
two restrictions, when the user rejected `Eg(s,s,0)` and `Eg(s,s,2)`, and then one is
dropped and Theorem 3.1(2) fails for it. [`oaFill`](../Greta/GenTA.lean#L104) tests
membership instead. The reference implementation folds over all of `oa_neg`, so this is a
clarification of the pseudocode rather than a change to the algorithm.

## 7. Figure 7 has a typo

Figure 7 lists `e2 ←(TINT,4) TINT e2 EQ e2`, replacing the `ident` nonterminal by `e2`,
while the rows at `e3` and `e4` keep it. Footnote 3 of §3.1.3 says the δ-generator
replaces "each old state (excluding the states associated with trivial symbols)", which
makes the `e3` and `e4` rows the correct ones. [`fillRhs`](../Greta/GenTA.lean#L67)
implements the footnote, and with that row corrected `lake exe greta genta` reproduces
Figure 7 transition for transition, which the self-test checks.

## 8. Theorem 3.1(1) is false for grammars with brackets

Statement (1) of Theorem 3.1 is `L_r ⊇ L_g \ L⁻`: repair keeps every parse tree the user
did not exclude. On the grammar of Section 1,

```
S → S + S | S * S | ( S ) | x | y | z
```

with the rejected examples of [`test/examples/arith.ex`](../test/examples/arith.ex) — `+`
and `*` are not right-associative, and `*` does not sit directly above `+` — the tree for
`x * (y + z)` is a complete parse tree, no rejected example excludes it, and the automaton
`GenTA` produces rejects it. So does the repaired grammar. `(y + z) * x` goes the same way.

The learned automaton is

```
e0 ←ε e1            e1 ←ε e2
e0 ← e0 + e1        e1 ← e1 * e2
e0 ← ( e0 )         e1 ← ( e1 )        e2 ← ( e2 )
e0 ← x | y | z      e1 ← x | y | z     e2 ← x | y | z
```

The ε-chain promotes a deeper state to a shallower one, so a state `e_i` accepts children
at levels `≥ i` only. `*` demands its right child at `e2`, and the only bracketing
transition at `e2` is `e2 ← ( e2 )`, which demands the bracketed expression at `e2` as
well; but `+` lives at `e0`. The parse is lost.

The cause is the replication half of Lemma B.2: Algorithm 3.1 as printed copies the
non-conflicting symbols `S` of a band to *every* newly inserted order, and Algorithm 3.2
then fills each copy's right-hand side with that copy's own state. A bracketing production
is exactly the case where the right-hand side has to be filled with the *lowest* state
instead, since brackets reset precedence.

`Learner.learn_ta` in the reference does that. For a symbol in `special_loop_symbols` — the
non-conflicting symbols, which the shipped learner places once rather than replicating —
it fills the right-hand side with the symbol's *original* order:

```ocaml
let _rhs_st = match List.assoc_opt sym special_loop_symbols with
  | Some s -> "e" ^ string_of_int s
  | None -> curr_state
```

The difference is visible in the learned order itself. On this grammar the published
algorithm replicates the four non-conflicting symbols across all three orders, while the
shipped one places them once and remembers where they came from:

```
published   order 0  +  ( x y z          shipped   order 0  +
            order 1  *  ( x y z                    order 1  *
            order 2     ( x y z                    order 2     ( x y z   (back-edge to 0)
```

So the shipped tool emits `e_i ← ( e_0 )` and keeps the parse.  `lake exe greta selftest`
checks both halves: the published automaton rejects `x * (y + z)` and `(y + z) * x`, the
shipped one accepts them, and both are in `L_g \ L⁻`. This reverses the reading of
[D7](reference-defects.md#d7-algorithm-31-as-printed-is-not-what-learnerml-does): the
divergence between the code and the paper is not cosmetic, and the fix suggested there —
change the code to replicate, as the paper does — would introduce this defect into the
tool. The paper's Algorithm 3.1 should be restated to match the code instead.

Because `Fits` is what statement (1) needs of the learned order, and `Fits` is exactly what
fails here, [`fitsB`](../Greta/LearnSpec.lean#L1011) reports `false` on this grammar and on the
paper's running example, and `true` on `dangling-else`, which has no bracketing production.

`Fits` was also *too strong* as first stated: it quantified over every pair of grammar
symbols, including pairs no parse tree can put in a parent/child relation. It is now
guarded by [`ChildAt`](../Greta/GenTASpec.lean#L474), which is what the proof of
`genTA_sound₁` actually uses.

## 9. Linearising a conflict group needs a topological sort

Algorithm 3.1 takes `M_to` with each conflict group already "totally ordered from lowest to
highest precedence". Building that order from the rejected examples is left to Section 3's
prose. It cannot be done by a comparison sort: "`a` before `b` unless an example says
otherwise" is not transitive, so a merge sort can fail to compare two symbols that an
example relates, and silently drop the constraint.

[`test/grammars/four-ops.cfg`](../test/grammars/four-ops.cfg) is the smallest witness: four
operators at one base order, with one example relating the first and the last and one
relating the two in the middle. A merge sort never compares the first with the last, leaves
them in base order, and the repaired grammar still admits the rejected nesting, with
`HighToLow` empty — so this is not the acyclicity case of [1](#1-theorem-31-needs-acyclicity).

[`topoSort`](../Greta/Learn.lean#L110) is Kahn's algorithm instead, and
[`topoSort_before`](../Greta/Learn.lean#L167) proves that every constraint is respected. It
returns `none` when the constraints are cyclic, which is the case the reference detects in
`Examples.form_total_order_among_op_symbols_from_same_group`, where an insertion sort checks
each placement with `ensure_consistent` and exits on failure.

## Representation choices

Not divergences, but places where the formalisation deliberately does not copy the paper.

* **States of `A_r` are a datatype**, `GState.lvl i` and `GState.triv A`, printed as `e0`,
  `e1`, … and the nonterminal. The proofs read a level back off a state, which strings do
  not support well.
* **Product states are pairs**, not concatenated names. `Treeutils.state_pair_append` is
  not injective; [`TA`](../Greta/Basic.lean#L130) is parameterised by its state type.
* **The δ symbol is named `""`**, as `Cfg.first_terminal_of` names it, not `δ`. Symbol
  names carry no meaning, production identifiers tell symbols apart, but they take part in
  symbol equality in the reference implementation, so following it keeps the printed
  automata comparable byte for byte.
* **Associativity positions index the whole right-hand side.** `t_idx` in §3 says
  `0 ≤ i < Rank(t_T)`, which counts terminals too, and
  `Treeutils.find_index_subt_with_same_sym` agrees; §3.1.2's prose ("as a right child
  (position 1)") counts only nonterminals. The two readings agree on the paper's example.
* **`HighToLow` compares against `O_bp`**, as §3.1.3 says, and reports orders from `O_p`.
  Comparing against `O_p` would report every ordinary nesting as a cycle.
* **ε-introduction is guarded** by `Δ_i ≠ ∅`; Algorithm 3.3's `RHS of Δ_i ⊆ RHS of Δ_j` is
  vacuously true for an empty `Δ_i`. See
  [D2](reference-defects.md#d2-the-intersection-can-fail-to-terminate).
