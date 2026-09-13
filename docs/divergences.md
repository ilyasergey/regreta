# Theory, implementation, and what is proved

The paper makes three kinds of claim: theorems (3.1, 3.2, A.10 and Lemmas B.1, B.2),
algorithms (3.1 to 3.4), and an implementation that is said to realise them. This note
records where the Lean statements differ from the paper's, why, and what each difference
means in practice. Defects found in the OCaml code are catalogued separately in
[`reference-defects.md`](reference-defects.md).

Section, algorithm and theorem numbers are those of the paper's main body; Definitions A.n
and the proofs of Lemmas B.1 and B.2 are in the supplementary material.

## The verdict

**Theorem 3.2 holds as stated**, for the product construction of Section 2.4. Its proof in
the paper is "Follows from Theorem 3.1 and set intersection", and that is the proof here.

**Theorem 3.1 does not hold as stated.** It is printed without hypotheses, but its proof
(through Lemma B.1) ends by declaring one case out of scope: symbols "involved in a cycle"
in the symbol order. On a grammar with such a cycle the statement is false. The grammar
`S → S + S | T | x`, `T → S * S | y`, with the single rejected example "a `+` directly
under a `*`", makes `GenTA` emit a cycle transition that accepts exactly that nesting, and
the repaired grammar still admits it. `lake exe greta selftest` checks this witness, and
`lake exe greta repair test/grammars/cycle.cfg test/examples/cycle.ex` prints the grammar.

**With acyclicity assumed, Theorem 3.1 holds**, and both halves are proved. Four further
hypotheses are needed to state the theorem about Algorithms 3.1 and 3.2 in isolation; the
paper's definitions imply them, and they are decidable.

**The algorithms are correct as printed**, on acyclic inputs, with two clarifications to
the pseudocode that the reference implementation already observes: Algorithm 3.2 must apply
every associativity restriction of a symbol, and Algorithm 3.1's input `M_to` must include
the singleton conflict groups.

**The reference implementation diverges from the paper in two places and has two defects
that the paper's algorithms do not.** Neither defect touches the theorems: both are in the
OCaml intersection, and Algorithm 3.3 as printed, implemented in Lean, agrees with the
verified product in every test.

| | Paper | Here | In practice |
| --- | --- | --- | --- |
| [1](#1-theorem-31-needs-acyclicity) | Theorem 3.1 holds unconditionally | it holds when `HighToLow` reports nothing | **real restriction.** On a grammar with a cycle, one round of repair can leave a rejected tree in the language. The paper's proof excludes the case. |
| [2](#2-algorithm-31s-inputs-get-a-specification) | `O_a`, `O_p` are whatever the earlier stages produce | `LearnedSpec`, `Fits`, `Covers` say what they must satisfy | bookkeeping. Implied by the definitions; one clause is easy to lose in an implementation. |
| [3](#3-lemma-b1-gains-a-child-position) | Lemma B.1 relates two symbols | it relates two symbols at a child position | the published lemma cannot cover associativity examples; the restated one does. |
| [4](#4-lemma-b2-is-about-the-published-algorithm-31) | Lemma B.2 is about Greta | it is about Algorithm 3.1 as printed, not as shipped | the shipped learner is a different algorithm; its correctness is not established here. |
| [5](#5-theorem-32-is-about-the-product-construction) | Theorem 3.2 is about Algorithm 3.3's output | it is about the product construction | Algorithm 3.3 agrees with the product in every test; not proved. |
| [6](#6-algorithm-32-applies-every-associativity-restriction) | `if ∃p, (s,p) ∈ O_a` | every such `p` is applied | pseudocode clarification; the reference already does this. |
| [7](#7-figure-7-has-a-typo) | Figure 7's `(TINT,4)` row at `e2` | `TINT ident EQ e2` | typo. |

## What is proved

Four results carry the development, all in Lean with no `sorry` and no axioms beyond
`propext`, `Classical.choice` and `Quot.sound`.

[`CFG.toTA_correct`](../Greta/CFG.lean#L318) is Theorem A.10: the automaton built from a
grammar accepts exactly that grammar's complete parse trees. The paper proves it in one
line; here it is an induction over trees that lines up the automaton's child matching with
the grammar's right-hand sides.

[`prodTA_lang`](../Greta/Product.lean#L377) says the product of two tree automata
recognises the intersection of their languages. The ε-closure of a product state has to be
shown to be the product of the component closures before the evaluation lemma goes through.

[`genTA_sound`](../Greta/GenTASpec.lean#L663) is Theorem 3.1, both halves. The proof pins
down the four groups of transitions `GenTA` emits, shows the ε-graph is the chain
`e₀ ←ε e₁ ←ε … ←ε eₘ`, and deduces that ε-reachability between ordered states is `≤` on
levels. After that every argument is arithmetic: statement (2) by induction over the tree,
statement (1) by building a run top-down.

[`greta_correct_of_spec`](../Greta/GenTASpec.lean#L673) is Theorem 3.2 assembled from the
three, with the product construction as the intersection. Its hypotheses are five decidable
conditions on the learned order: [`LearnedSpec`](../Greta/GenTASpec.lean#L233),
[`Fits`](../Greta/GenTASpec.lean#L467), [`Covers`](../Greta/GenTASpec.lean#L594), that no
start nonterminal is trivial, and that `HighToLow` reports nothing. Sections 1 and 2 below
say where each comes from.

Not proved: that Algorithm 3.3, the optimised intersection Greta runs, has the same
language as the product construction (Section 5).

## 1. Theorem 3.1 needs acyclicity

[`genTA_sound`](../Greta/GenTASpec.lean#L663) carries the hypothesis

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
`testCycle` in `Greta/Test.lean` checks all three facts. The repaired grammar
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
has to say what those arguments satisfy. Four hypotheses, all decidable, all true of the
pipeline:

* [`LearnedSpec`](../Greta/GenTASpec.lean#L233): `O_p` mentions only symbols of `g`; no
  symbol of a tree example is trivial (§3.1.1 excludes those from conflicts); a rejected
  precedence example puts its top strictly above its bottom; a rejected associativity
  example is recorded in `O_a`; a symbol in an associativity conflict sits at exactly one
  order.
* [`Fits`](../Greta/GenTASpec.lean#L467): a symbol that may legitimately sit at child
  position `k` of an `s`-node at level `i` has a level at or above the one the transition
  demands. This is what makes the level assignment of statement (1) succeed.
* [`Covers`](../Greta/GenTASpec.lean#L594): every non-trivial symbol has a level.
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
[`toMapOf`](../Greta/Learn.lean#L102) keeps them, and `testAssocOnly` checks the case.

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
[`relayerOrder`](../Greta/Learn.lean#L38) implements the published version, so every
statement here is about the paper's algorithm. A proof about the shipped one would need a
different, reachability-flavoured invariant, and none is given here.

[`shift_mono`](../Greta/Soundness.lean#L25) is B.2's arithmetic core. B.2 itself is not
separately stated: what statement (1) needs is `Fits`, the same idea localised to one
parent/child pair.

## 5. Theorem 3.2 is about the product construction

The paper's Theorem 3.2 is about the output of Algorithm 3.3.
[`greta_correct_of_spec`](../Greta/GenTASpec.lean#L673) is about
[`prodTA`](../Greta/Product.lean#L63), the product of Section 2.4, which
[`prodTA_lang`](../Greta/Product.lean#L377) proves recognises the intersection.

Algorithm 3.3 is implemented ([`intersectTA`](../Greta/Intersect.lean#L168)) and compared
with `prodTA` by testing, under all five ablation settings of Table 1, on the running
example and on random grammars, with no disagreement. Identifying the two is the one link
in the paper's chain that is tested rather than proved. [`accepts_mono`](../Greta/Intersect.lean#L249)
gives the easy half of the reachability restriction, that a sub-automaton accepts no more;
the rest needs a simulation argument for reachability and bisimulations for duplicate
merging and ε-introduction.

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
