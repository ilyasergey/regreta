# Divergences from the paper

The formalisation proves the paper's theorems, but not always the paper's *statements*.
This note lists every place the two differ and why.

Section, algorithm and theorem numbers are those of the main body; `Definition A.n` and
the proofs of Lemmas B.1 and B.2 are in the supplementary material.  Defects found in the
OCaml tool are separate, in [`reference-defects.md`](reference-defects.md).

## The short version

Theorem 3.2 is proved exactly as stated. Theorem 3.1 is proved with five side conditions
attached, all decidable. Four of them are facts the paper's own definitions already give;
the fifth, acyclicity, is a real restriction — and it is the case the paper's own proof of
Lemma B.1 sets aside in one sentence.

| | Paper | Here |
| --- | --- | --- |
| [1](#1-theorem-31-needs-acyclicity) | Theorem 3.1 holds unconditionally | it holds when `HighToLow` reports nothing |
| [2](#2-algorithm-31s-inputs-get-a-specification) | `O_a`, `O_p` are "whatever the earlier stages produce" | `LearnedSpec`, `Fits`, `Covers` say what they must satisfy |
| [3](#3-lemma-b1-gains-a-child-position) | Lemma B.1 relates two symbols | it relates two symbols *at a position* |
| [4](#4-lemma-b2-is-about-the-published-algorithm-31) | Lemma B.2 is about Greta | it is about Algorithm 3.1 as printed, not as shipped |
| [5](#5-theorem-32-is-about-a-different-intersection) | Theorem 3.2 is about Algorithm 3.3's output | it is about the verified product |
| [6](#6-algorithm-32-applies-every-associativity-restriction) | Algorithm 3.2 reads `if ∃p, (s,p) ∈ O_a` | every such `p` is applied |
| [7](#7-figure-7-has-a-typo) | Figure 7's `(TINT,4)` row at `e2` | `TINT ident EQ e2` |

## 1. Theorem 3.1 needs acyclicity

[`genTA_sound`](../Greta/GenTASpec.lean#L667) carries the hypothesis

```lean
(hAc : g.highToLow (g.baseOrder b) op = [])
```

The cycle transitions of Algorithm 3.2's last loop go from a *high* order back to a *low*
one, which is precisely the parent-above-child shape the level argument otherwise rules
out.  If the head of such a pair is the top symbol of a rejected example, the transition
re-permits the pattern `O_p` was arranged to forbid; and because the cycle rule is built
with `fun _ => e_{o_l}`, it ignores `O_a` entirely.

This is not a restriction we invented.  Lemma B.1's published proof ends:

> Cases of symbols at adjacent levels which are involved in a conflict (i.e. they are
> involved in a cycle) are explicitly not handled by the algorithm.

So the unconditional statement of Theorem 3.1 was never supported by its own proof.  Making
it a hypothesis turns a silent gap into something the tool can check: `hAc` is decidable,
and it holds for the paper's running example and for every grammar in `test/`.

Statement (1) needs acyclicity for the opposite reason.  Without the cycle transitions the
level assignment has nowhere to go when a child's nonterminal sits *above* its parent's;
with them, `δ_F(e_{o_h}, ē_{o_l}, s_h)` sends **all** of a production's nonterminals to one
level, so a production with two nonterminal children needing different levels is not
covered.  Relaxing `hAc` means giving each nonterminal its own level in that rule.

## 2. Algorithm 3.1's inputs get a specification

Algorithms 3.1 and 3.2 take `M_to`, `O_a` and `O_p` as arguments, so a theorem about them
has to say what those arguments satisfy.  Four hypotheses, all decidable, all true of the
pipeline:

* [`LearnedSpec`](../Greta/GenTASpec.lean#L235) — `O_p` mentions only symbols of `g`; no
  symbol of a tree example is trivial (§3.1.1 excludes those from conflicts); a rejected
  precedence example puts its top strictly above its bottom; a rejected associativity
  example is recorded in `O_a`; a symbol in an associativity conflict sits at exactly one
  order.
* [`Fits`](../Greta/GenTASpec.lean#L470) — a symbol that may legitimately sit at child
  position `k` of an `s`-node at level `i` has a level at or above the one the transition
  demands.  This is what makes the level assignment of statement (1) succeed.
* [`Covers`](../Greta/GenTASpec.lean#L598) — every non-trivial symbol has a level.
* No start nonterminal is trivial.

The paper leaves these implicit because it never separates the stages.  One of them is
easy to lose when implementing: `M_to` must range over *all* of `S_E`, singletons
included.  `S_C` is the symbols in a precedence **or an associativity** conflict, so a
symbol whose only conflict is with itself is a singleton member of `S_E`, and Algorithm
3.1's last clause only fires for symbols that are in a group.  Build `M_to` from the orders
with two or more conflicting symbols and Theorem 3.1(1) is false: on
`S → S + S | S * S | (S) | x | y | z` with the single example `Eg((PLUS,3),(PLUS,3),2)`,
`O_p` stays `{0 ↦ everything}` and `GenTA` emits a transition naming a state `e₁` that does
not exist, so every tree containing a `+` is rejected — `x + y` included.  The reference
implementation constructs the singletons deliberately (`assoc_only` in
`Examples.form_total_order_among_op_symbols_from_same_group`); this repository did not,
until `testAssocOnly` was added.

## 3. Lemma B.1 gains a child position

The paper's Lemma B.1 is

> for `(s₁,o₁), (s₂,o₂) ∈ O_p` where `s₁` and `s₂` are involved in a precedence conflict,
> `o₁ ≤ o₂ ⟺ L_r includes trees with s₁ directly above s₂`

which mentions no child position — so it cannot cover associativity examples, where the
restriction is *at one position only*.  Yet the proof of Theorem 3.1(2) appeals to it for
exactly those.

Here the content of B.1 is split in two and both parts are proved:
[`epsReach_lvl`](../Greta/GenTASpec.lean#L161) — ε-reachability between ordered states is
`≤` on levels — and [`evalT_genTA_inv`](../Greta/GenTASpec.lean#L179), which says every
state assigned to a node is the level of that node's symbol.  The position enters through
`oaFill`, and `matchesHere_false` does the work B.1 was meant to do, for precedence and
associativity examples alike.

## 4. Lemma B.2 is about the published Algorithm 3.1

B.2's proof appeals to "the construction of `O_p`, which copies the non-conflicting symbols
to each newly inserted order".  That is what Algorithm 3.1 prints, and it is not what
`learner.ml` does — see [D7](reference-defects.md#d7-algorithm-31-as-printed-is-not-what-learnerml-does).
[`relayerOrder`](../Greta/Learn.lean#L38) implements the published version, so the
statements here are about the paper's algorithm.  A proof about the shipped one would need
a different, reachability-flavoured invariant.

`shift_mono` is B.2's arithmetic core.  B.2 itself is not separately stated: what statement
(1) actually needs is `Fits`, which is the same idea localised to one parent/child pair.

## 5. Theorem 3.2 is about a different intersection

The paper's Theorem 3.2 is about the output of Algorithm 3.3.
[`greta_correct_of_spec`](../Greta/GenTASpec.lean#L677) is about
[`prodTA`](../Greta/Product.lean#L63), the textbook product, which
[`prodTA_lang`](../Greta/Product.lean#L377) proves recognises the intersection.

Algorithm 3.3 is implemented ([`intersectTA`](../Greta/Intersect.lean#L168)) and checked
against `prodTA` by testing, under all five ablation settings of Table 1, on the running
example and on random grammars.  Identifying the two is the one piece of the paper's chain
that is tested rather than proved: it needs a simulation argument for the reachability
restriction and bisimulations for duplicate merging and ε-introduction.

## 6. Algorithm 3.2 applies every associativity restriction

Algorithm 3.2 reads `if ∃p, (s, p) ∈ O_a then …`, which picks one `p`.  A symbol can carry
two restrictions — the user rejected `Eg(s,s,0)` *and* `Eg(s,s,2)` — and then one is
dropped and Theorem 3.1(2) fails for it.  [`oaFill`](../Greta/GenTA.lean#L104) tests
membership instead.  The reference implementation folds over all of `oa_neg`, so this is a
clarification of the pseudocode rather than a change to the algorithm.

## 7. Figure 7 has a typo

Figure 7 lists `e2 ←(TINT,4) TINT e2 EQ e2`, replacing the `ident` nonterminal by `e2`,
while the rows at `e3` and `e4` keep it.  Footnote 3 of §3.1.3 says the δ-generator
replaces "each old state (excluding the states associated with trivial symbols)", which
makes the `e3`/`e4` rows the correct ones.  [`fillRhs`](../Greta/GenTA.lean#L67) implements
the footnote, and with that row corrected `lake exe greta genta` reproduces Figure 7
transition for transition — which the self-test checks.

## Representation choices

Not divergences, but places where the formalisation deliberately does not copy the paper.

* **States of `A_r` are a datatype**, `GState.lvl i` and `GState.triv A`, printed as `e0`,
  `e1`, … and the nonterminal.  The proofs read a level back off a state, and `Nat`'s
  `toString` has no injectivity lemma to hand.
* **Product states are pairs**, not concatenated names.  `Treeutils.state_pair_append` is
  not injective; [`TA`](../Greta/Basic.lean#L130) is parameterised by its state type.
* **The δ symbol is named `""`**, as `Cfg.first_terminal_of` names it, not `δ`.  Symbol
  names carry no meaning — production identifiers tell symbols apart — but they take part
  in symbol equality in the reference implementation, so following it keeps the printed
  automata comparable byte for byte.
* **Associativity positions index the whole right-hand side.**  `t_idx` in §3 says
  `0 ≤ i < Rank(t_T)`, which counts terminals too, and
  `Treeutils.find_index_subt_with_same_sym` agrees; §3.1.2's prose ("as a right child
  (position 1)") counts only nonterminals.  The two readings agree on the paper's example.
* **`HighToLow` compares against `O_bp`**, as §3.1.3 says, and reports orders from `O_p`.
  Comparing against `O_p` would report every ordinary nesting as a cycle.
* **ε-introduction is guarded** by `Δ_i ≠ ∅`; Algorithm 3.3's `RHS of Δ_i ⊆ RHS of Δ_j` is
  vacuously true for an empty `Δ_i`.  See [D2](reference-defects.md#d2-the-intersection-can-fail-to-terminate).
