# Proof plan

**Status.** Steps 1–6 below are done: `Greta/GenTASpec.lean` carries them out and
[`genTA_sound`](../Greta/GenTASpec.lean#L667) proves both halves of Theorem 3.1, so
[`greta_correct_of_spec`](../Greta/GenTASpec.lean#L677) derives Theorem 3.2 with no
language-level hypothesis left. What the plan called side conditions became the explicit
hypotheses of those theorems; [`divergences.md`](divergences.md) lists them.

What remains open is the last section of this note: that Algorithm 3.3, the optimised
intersection, has the same language as the product construction. That is still covered by
testing only.

The rest of this note is the plan as written before the proofs, kept because it explains
why the proofs are shaped the way they are.

It also records the six side conditions and clarifications that Theorem 3.1 turns out to
need. Most of them are hypotheses that the paper's own definitions already supply and that
the reference implementation already establishes; two are genuine gaps, both about the
cycle transitions, and the paper says as much about one of them. See
[What Theorem 3.1 needs](#what-theorem-31-needs).

## Theorem 3.1

> Let `A_r` be the automaton `GenTA` returns and `A_g` the automaton derived from `G`, and
> `T⁻` the unselected tree examples. With `L_r = L(A_r)`, `L_g = L(A_g)` and
> `L⁻ = ⋃_{t ∈ T⁻} P⁻(t)`:
> (1) `L_r ⊇ L_g \ L⁻` and (2) `L_r ∩ L⁻ = ∅`.

In Lean these are [`GenTASound₁`](../Greta/Soundness.lean#L66) and
[`GenTASound₂`](../Greta/Soundness.lean#L73).

Both are statements about the *language* of a machine assembled by four stages: levels →
`O_bp` → `LearnOaOp` → `GenTA`. Proving them directly means reasoning about runs of that
machine, which is hopeless without first pinning down its shape. The plan below does that
first, and the language statements then fall out.

### The shape of `A_r`

`GenTA` produces a very regular automaton, and that regularity is the invariant to carry
through the whole proof.

**Step 1 — inversion (`genTA_trans_shape`).** Every transition of
[`genTA g oa op`](../Greta/GenTA.lean#L38) has one of four shapes:

* `e_i ←_s δ_F(e_i, …, e_i)` for `(s, i) ∈ O_p` with `s` not in `O_a`;
* `e_i ←_s δ_F(…, e_{i+1} at position p, …)` for `(s, i) ∈ O_p` and `(s, p) ∈ O_a`;
* `A ←_s δ_F(A, …)` for a trivial symbol `s` whose production has left-hand side `A`;
* `e_i ←(ε,1) e_{i+1}` for `i < m`, and the cycle transitions from `HighToLow`.

The proof is computation: `genTA`'s transition list is an append of four `filterMap`s, so
this is `List.mem_append` and `List.mem_filterMap` four times. Tedious, not deep. It is
the lemma everything else rests on, so it is worth stating in the positive direction as
well (each shape *is* present), since Theorem 3.1(1) needs that.

**Step 2 — the ε-graph is a chain (`genTA_epsEdges`).**

```lean
theorem genTA_epsEdges (g : CFG) (oa : Oa) (op : OrderMap) (b : Bool) :
    (genTA g oa op b).epsEdges =
      (List.range op.maxOrder).map fun i => (stateName (i + 1), stateName i)
```

Only the third bullet of Step 1 produces an ε-symbol, so this follows from inversion plus
`stateName` being injective (`"e" ++ toString i`, so injectivity is
`String.toNat`-flavoured but routine).

**Step 3 — ε-reachability is `≤` on levels (`epsReach_genTA`).**

```lean
theorem epsReach_genTA {i j : Nat} (hi : i ≤ m) (hj : j ≤ m) :
    EpsReach (genTA g oa op b) (stateName j) (stateName i) ↔ i ≤ j
```

`←` chains `EpsReach.step` down from `e_j` to `e_i`; `→` is an induction on the derivation
using Step 2. **This is Lemma B.1 in its usable form** — the informal "epsilon transitions
are only introduced from higher-leveled states to lower-leveled states" becomes a decidable
arithmetic statement.

**Step 4 — runs of `A_r` (`evalT_genTA_iff`).**

```lean
theorem evalT_genTA_iff (t : Tree) (q : String) :
    q ∈ (genTA g oa op b).evalT (genTA g oa op b).epsTable t ↔ …
```

with the right-hand side spelling out: `t = .node s ts`, `(s, i) ∈ O_p`, `q = e_i`, and
each child `ts[k]` evaluates to a state whose level is `≥ i` (`≥ i + 1` at the position
`O_a` forbids), or is the trivial state the production names. By `Tree.rec'` from Steps 1
and 3. After this, nothing in the rest of the proof mentions transitions at all — only
levels.

### Lemma B.1, formally

With Step 4 in hand, Lemma B.1 becomes a statement about levels and is provable in both
directions:

```lean
theorem lemmaB1 {s₁ s₂ : Sym} {o₁ o₂ k : Nat}
    (h₁ : o₁ ∈ op.ordersOf s₁) (h₂ : o₂ ∈ op.ordersOf s₂) (hk : (s₁, k) ∉ oa) :
    (∃ t, (genTA g oa op b).Lang t ∧ (TreeExample.mk s₁ s₂ k).matchesHere t) ↔ o₁ ≤ o₂
```

`←` builds a witness tree bottom-up from the transitions Step 1 guarantees are present;
`→` reads the levels off the run given by Step 4 and applies Step 3.

### Theorem 3.1(2)

This is the easier half. `L⁻ = ⋃ P⁻(t)`, and
[`excludedBy`](../Greta/Examples.lean#L75) splits on the kind of example:

* *Precedence-related* `t_p` with top `s₁`, bottom `s₂`. `LearnOaOp` places them at
  `o₁ > o₂` — that is the content of Step 5 below — so `lemmaB1` gives that no tree of
  `L_r` has `s₁` directly above `s₂` at any child position, and `P⁻(t_p)` is exactly the
  set of parse trees containing that pattern at some position. Disjointness follows by
  induction over the tree, since `occursIn` is a disjunction over subtrees and Step 4
  applies at each.
* *Associativity-related* `t_a` with symbol `s` at position `idx`. `(s, idx) ∈ O_a`, so
  by Step 1 the only `s`-transition at level `i` demands `e_{i+1}` at position `idx`, and
  by Step 3 a subtree rooted at `s` evaluates to some `e_j` with `j ≤ i` — never `i + 1`
  or more. So the nested occurrence is impossible.

### Theorem 3.1(1)

The harder half, and the one that needs `LearnOaOp` characterised.

**Step 5 — the specification of `LearnOaOp` (`learnOaOp_spec`).** Two properties of the
`O_p` that [`learnOaOp`](../Greta/Learn.lean#L57) returns, both by induction over the fold
of [`relayerOrder`](../Greta/Learn.lean#L38) over the conflict groups:

* *(a) Conflicting symbols are stratified.* If `s` and `s'` are in the same group of
  `M_to` with `s` before `s'`, then every order of `s` is strictly below every order of
  `s'`. This is what Theorem 3.1(2) used above.
* *(b) Everything else is preserved.* If `s` is not in any conflict, and `o₁ ≤ o₂` in
  `O_bp` for `s` and some `s'`, then `o₁' ≤ o₂'` for some orders in `O_p` — Lemma B.2.
  [`shift_mono`](../Greta/Soundness.lean#L31) is its arithmetic core; what remains is to
  show that `relayerOrder` only ever moves an order by a `shift`, and that the
  non-conflicting symbols of the order being re-layered are re-inserted at *every* order
  it creates. That second clause is exactly the line of Algorithm 3.1 that the reference
  implementation does not implement — see [D7](reference-defects.md#d7-algorithm-31-as-printed-is-not-what-learnerml-does).

**Step 6 — the level assignment.** Given `t ∈ L_g \ L⁻`, construct a run of `A_r` on `t`
top-down: assign the root the smallest order its symbol has in `O_p`, and each child the
smallest order of its symbol that is `≥` the parent's (`≥ parent + 1` at an `O_a`
position). Two obligations:

* *the assignment exists* — every symbol of `t` occurs in `O_p`, because `t ∈ L_g` means
  every node is labelled by a production of `g` and `O_p` covers every non-trivial symbol
  of `g` (Step 5, plus `baseOrder` covering the reachable symbols);
* *the assignment is monotone* — if it were not, the parent/child pair would be one that
  `LearnOaOp` had inverted, which by Step 5(a) only happens for pairs named by `T⁻`, and
  `t ∉ L⁻` rules those out; for pairs not in any conflict, Step 5(b) gives monotonicity.

Then Step 4 turns the assignment into `t ∈ L_r`.

## What Theorem 3.1 needs

Working through the plan turns up six conditions. None of them invalidates the algorithm:
four are hypotheses that Section 3's own definitions supply and that the reference
implementation establishes, and the remaining two are about the cycle transitions, where
the published proof of Lemma B.1 already concedes that the case is "explicitly not handled
by the algorithm".

They are listed here because a proof has to state them, and because four of them are easy
to lose when implementing — two of them were lost in this repository, and are now fixed.

### S1. Every associativity restriction of a symbol must be applied

Algorithm 3.2 reads

> **if** `∃p, (s, p) ∈ O_a` **then** `Δ ← Δ ∪ {δ_F(e_i, [e_i; …; e_{i+1}; …; e_i], s)}`

which, taken literally, picks one `p`. A symbol can carry two restrictions — the user
rejected `Eg(s,s,0)` *and* `Eg(s,s,2)`, so `s` may nest on neither side — and then one of
them is dropped and Theorem 3.1(2) fails for it.

The reference implementation gets this right: `Learner.learn_ta` folds
`update_oa_sym_prod_for_index` over every element of `oa_neg`, and the rewrites compose.
So this is a clarification of the pseudocode, not a change to the algorithm. This
repository took only the first position until recently;
[`genTA`](../Greta/GenTA.lean#L38) now tests membership:

```lean
let forbidden := oa.positionsOf s
deltaGen g trivNts (stateName i)
  (fun k => if forbidden.contains k then stateName (i + 1) else stateName i) s
```

### S2. `M_to` must cover all of `S_E`, singletons included

`S_C` in Section 3 is the set of symbols involved in a precedence **or an associativity**
related conflict, and `S_E` is its partition into maximal pairwise-conflicting subsets. A
symbol whose only conflict is with itself is a *singleton* member of `S_E`, and Algorithm
3.1 needs it there: its last clause —

> **if** `i = size − 1 ∧ ∃ s ∈ ithSymbols, (s, _) ∈ O_a` **then** `O_tmp ← pushN(O_tmp, o+i+1, 1)` …

— only fires for symbols that are in a group, and it is what leaves an order *above* the
symbol for `GenTA` to send the forbidden child to.

The reference implementation constructs the singletons explicitly.
`Examples.form_total_order_among_op_symbols_from_same_group` collects the symbols whose
only conflict is associativity —

```ocaml
let assoc_only = learned_trees
  |> filter (fun (_, _, (oa_pos, _, _), _) -> oa_pos)
  |> map (fun (_, _, _, rls) -> match rls with Assoc (s, _) :: _ -> s | _ -> …)
  |> filter (fun s -> not s_is_contained_in_precedence_tree)
```

— and adds each as a one-element group: `Hashtbl.replace prec_restrictions order ((s :: []) :: prev)`.

**Why the hypothesis is not vacuous.** Build `M_to` from the orders that contain *two or
more* conflicting symbols, as one naturally might, and Theorem 3.1(1) becomes false. On
`S → S + S | S * S | (S) | x | y | z` with the single rejected example
`Eg((PLUS,3), (PLUS,3), 2)`, `O_p` stays `{0 ↦ everything}`, so `m = 0`, and `GenTA` emits

```
states e0
finals e0
trans e0 0 PLUS 3 S:e0 T:PLUS S:e1
```

naming a state `e₁` that does not exist. Nothing satisfies it, so every tree containing a
`+` is rejected: 7 of the grammar's 15 trees at depth 3 survive, and `x + y`, which the
user never excluded, is among the losses.

This repository built `M_to` that way until recently.
[`toMapOf`](../Greta/Learn.lean#L96) now keeps the singletons: `O_p` becomes
`{0 ↦ everything, 1 ↦ everything but PLUS}`, 13 of the 15 trees survive, and the two that
do not are exactly the right-associative nestings. `testAssocOnly` in `Greta/Test.lean` is
the regression test.

With the hypothesis in place,

> `(s, i) ∈ O_p ∧ (s, p) ∈ O_a ⟹ i < m`

is a **lemma** about `learnOaOp` rather than an assumption, which is what Step 4 of the
plan needs.

### S3. `O_a` positions must name a non-trivial nonterminal

`fillRhs` leaves terminals alone, and leaves the nonterminals of trivial symbols at their
own state, so an `O_a` position pointing at either is silently dropped. The condition

> for every `(s, p) ∈ O_a`, `Prod(s).rhs[p]` is a nonterminal that is not the left-hand
> side of a trivial symbol

is *derivable* when `O_a` comes from well-formed tree examples — the nested node of
`Eg(s,s,p)` is an `s`-rooted subtree, hence a nonterminal, and a trivial nonterminal
produces a single terminal so it cannot root one. It still has to be stated, because
Algorithm 3.2 takes `O_a` as an arbitrary input.

### S4. `M_to` must be well formed

Likewise for Algorithm 3.1's other input:

* each symbol occurs in at most one group;
* each group is duplicate-free;
* every symbol of a group at order `o` has `o` as its order in `O_bp`.

These follow from `S_E` being a partition of `S_C` and from each symbol having a single
level. They are what makes "a conflicting symbol has exactly one order in `O_p`" true,
which Theorem 3.1(2) uses to conclude that *all* orders of `s₂` lie below *all* orders of
`s₁`.

### S5. Cycles, for statement (2)

The first of the two genuine gaps, and the one the paper flags: Lemma B.1's proof ends
"Cases of symbols at adjacent levels which are involved in a conflict (i.e. they are
involved in a cycle) are explicitly not handled by the algorithm."

`HighToLow` emits `e_{o_h} ←_{s_h} … e_{o_l} …` with `o_l < o_h`, which is exactly the
parent-above-child shape that Step 3 of the plan otherwise rules out. If `s_h` is the top
symbol of a rejected example, the cycle transition re-permits the pattern `O_p` was
arranged to forbid: with `s₁ = s_h` at order 5, `o_l = 0`, and `s₂` at order 3, the child
needs only `0 ≤ 3`. The associativity case is worse, because `GenTA` builds the cycle
transition with `fun _ => stateName o_l` and so ignores `O_a` altogether.

The condition a proof needs:

> for every `((s_l, o_l), (s_h, o_h)) ∈ HighToLow(G, O_p)` and every rejected example with
> top symbol `s_h` and bottom symbol `s₂`, every order of `s₂` is strictly below `o_l`.

Simpler, decidable and strictly stronger: no symbol reported as `s_h` by `HighToLow` is
the top symbol of a rejected example. Simplest of all, and what we would assume first:
`HighToLow(G, O_bp) = ∅` — no production of `G` takes a nonterminal at level `a` to a
nonterminal at a level below `a`. That holds for the paper's own running example and for
every grammar in `test/`, which is why `GenTA` emits no cycle transitions for any of them.
It is decidable, so `greta` can check it and say so when it does not hold, rather than the
theorem quietly not applying.

### S6. Cycles, for statement (1)

The converse problem, and the second genuine gap. Dropping the cycle transitions makes (2)
safe but breaks (1) on any grammar whose level graph is not monotone, because the level
assignment of Step 6 has nowhere to go when a child's nonterminal sits *above* its
parent's.

Keeping them is not enough either, as published: `δ_F(e_{o_h}, ē_{o_l}, s_h)` sends **all**
of the production's nonterminals to the single level `o_l`, so a production with two
nonterminal children needing different levels is not covered. Giving each nonterminal `B`
its own state — the lowest order of any symbol of `B` — is still one transition per pair
and is what the level assignment needs.

Under `HighToLow(G, O_bp) = ∅` the question does not arise, which is the other reason to
take that as the first assumption and relax it later.

### Summary

| | Condition | Kind | Needed for | Status |
| --- | --- | --- | --- | --- |
| S1 | apply every `O_a` position, not one | pseudocode clarification | 3.1(2) | reference is right; fixed here |
| S2 | `M_to` covers all of `S_E` | hypothesis on the input | 3.1(1) | reference is right; fixed here |
| S3 | `O_a` positions name non-trivial nonterminals | hypothesis on the input | 3.1(2) | to state |
| S4 | `M_to` well formed | hypothesis on the input | 3.1(2) | to state |
| S5 | no cycle head is a conflict top | genuine gap; decidable side condition | 3.1(2) | to state |
| S6 | per-child levels in the cycle rule | genuine gap; change to Algorithm 3.2 | 3.1(1) | to do, or assume acyclicity |

With S1–S5 in place and `HighToLow(G, O_bp) = ∅` standing in for S6, both halves of
Theorem 3.1 are, as far as this analysis goes, provable by the plan above, and the only
remaining work is the eight lemmas.

## Two statements that have to change first

**Cycles.** Lemma B.1's (⇐) direction ends with "Cases of symbols at adjacent levels which
are involved in a conflict (i.e. they are involved in a cycle) are explicitly not handled
by the algorithm." The cycle transitions that
[`highToLow`](../Greta/Order.lean#L134) feeds into `GenTA` go from a *high* order back to a
*low* one, which is precisely what Step 3 forbids for ordinary transitions. So Theorem
3.1(2) as published is not true of an automaton with cycle transitions between conflicting
symbols, and the Lean statement needs a side condition — something like

```lean
def NoConflictingCycle (g : CFG) (oa : Oa) (obp op : OrderMap) : Prop :=
  ∀ pr ∈ g.highToLow obp op, pr.1.1 ∉ op.symbols ∨ pr.2.1 ∉ op.symbols ∨ …
```

The condition is decidable, so `greta` can check it on the actual input and report when it
does not hold, rather than the theorem quietly not applying. Deciding what the weakest
usable condition is, is part of the work: the honest first version is "no symbol reported
by `HighToLow` takes part in a conflict", which is true of every grammar in `test/`.

**`L_r` contains non-parse-trees.** `L⁻` is defined in terms of parse trees of `g`
([`parseTreesOf`](../Greta/Examples.lean#L67) conjoins `isParseTree`), so statement (2) is
about `L_r ∩ L⁻` where `L⁻ ⊆ L_g`. That is fine, but the proof must not assume that every
tree of `L_r` is a parse tree of `g` — `A_r` is deliberately more permissive, which is why
the intersection with `A_g` exists at all. The `occursIn` induction in Theorem 3.1(2)
should therefore be done on arbitrary trees, not on parse trees.

## The optimisations of Algorithm 3.3

[`intersectTA`](../Greta/Intersect.lean#L168) is checked against
[`prodTA`](../Greta/Product.lean#L63) by testing. Proving it means three separate lemmas,
in increasing order of difficulty.

**Reachability.** The pruned automaton is not literally a sub-automaton of `prodTA`,
because [`transitionsAtPair`](../Greta/Intersect.lean#L58) targets the pair it started from
and looks the constituents up through the ε-closure, where `prodTA` uses explicit ε-edges.
The two are related by a simulation: `(q₁,q₂)` in the pruned automaton simulates the set
`{(p₁,p₂) | p₁ ∈ cl(q₁), p₂ ∈ cl(q₂)}` in the product. Stating that simulation and proving
it a bisimulation on accepted trees is the bulk of the work;
[`accepts_mono`](../Greta/Intersect.lean#L249) already gives the easy inclusion once the
simulation is in place.

**Duplicate merging.** `mergeDups` quotients the state set by "same incoming transitions up
to renaming yourself". That relation is a bisimulation — two states with the same
signature accept the same trees — so language preservation is the standard quotient
argument. The catch is that `findDupStates` computes the relation on a *single* pass rather
than to a fixed point, so it merges a sound but not necessarily complete set of pairs;
soundness is all that is needed here, and it is the direction that is provable.

**ε-introduction.** `introEpsStep` replaces the transitions of `e_j` that duplicate those
of `e_i` by `e_j ←ε e_i`. Language preservation needs: (a) every tree that reached `e_j`
by a removed transition still reaches `e_i` and is promoted, and (b) no new tree reaches
`e_j`, which needs `shapesOf δ e_i ⊆ shapesOf δ e_j` — the guard the step tests. Both are
one induction each, but they have to be done against the transition set *as it is being
rewritten*, since `introEpsAll` folds the step over all pairs; the invariant is that each
step preserves the language, which composes.

## Effort

Steps 1–4 and Lemma B.1 are mechanical: a few hundred lines, no new ideas, and they are
worth doing first because they make every subsequent statement a statement about natural
numbers. Step 5 is where the difficulty is, and it is where
[D7](reference-defects.md#d7-algorithm-31-as-printed-is-not-what-learnerml-does) bites: the
published Algorithm 3.1 has the invariant that Lemma B.2 needs, the implemented one
replaces it with back-edges, so a proof about the code as written needs a different,
reachability-flavoured invariant. Fixing the code to match the paper makes the proof
easier and is the smaller change.
