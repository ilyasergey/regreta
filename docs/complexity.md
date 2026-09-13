# The paper's complexity claims

The paper states asymptotic bounds for three of its four algorithms. None of them is
formalised here: the Lean definitions mirror the pseudocode and are list-based, and no cost
model is attached to them. This note records the claims, where they are made, and what a
proof would involve.

## The claims

`|F|` is the number of ranked symbols, `r_max` the largest rank, `|O_p|` and `|O_a|` the sizes
of the learned orders, `|Q_g|, |Δ_g|` and `|Q_r|, |Δ_r|` the states and transitions of the two
automata being intersected. The bounds for `GenTA` and `IntersectTA` treat `r_max` as a
constant.

| Algorithm | Lean | Claim | Where |
| --- | --- | --- | --- |
| 3.1 `LearnOaOp` | [`learnOaOp`](../Greta/Learn.lean#L57) | `O(\|F\|²)` time, `O(\|F\|)` additional space | §3.1.2, last paragraph before the final `O_p` of the example; Appendix C.1 |
| 3.2 `GenTA` | [`genTA`](../Greta/GenTA.lean#L140) | `O(\|F\|)` time and space | §3.1.3, after the `HighToLow` paragraph; Appendix C.2 |
| 3.3 `IntersectTA` | [`intersectTA`](../Greta/Intersect.lean#L168) | `O((\|Q_g\|·\|Q_r\|)² · \|Δ_g\|·\|Δ_r\|)` time, `O((\|Q_g\|·\|Q_r\|)² + \|Δ_g\|·\|Δ_r\|)` space | §3.2, before Theorem 3.2; Appendix C.3 |
| 3.4 `FindDupStates` | [`findDupStates`](../Greta/Intersect.lean#L99) | `O(\|Q\|²·\|Δ\|)` time, `O(\|Q\|² + \|Δ\|)` space, as a step of Algorithm 3.3 | Appendix C.3 |

Appendix C is in the extended version, [arXiv:2602.18166](https://arxiv.org/abs/2602.18166);
the main body refers to it as the supplementary material.

## A gap in the `GenTA` bound

Appendix C.2 costs the main loop of Algorithm 3.2 at `O(r_max · |O_p|)` and concludes
`O(|F|)`, which needs `|O_p| ∈ O(|F|)`. `O_p` is a set of symbol-and-order pairs, and
Algorithm 3.1 as printed copies the non-conflicting symbols of an order to every order it
creates ([`relayerOrder`](../Greta/Learn.lean#L38)), so one symbol can occur at many
orders. The paper's own example shows it: the `O_p` of §2.3.2 has 18 pairs for 10 symbols,
and Figure 7 has 23 transitions, one per pair plus the ε-chain and the trivial symbol.
Since the number of orders is itself bounded only by `|F|`, the output of `GenTA` can be
quadratic in `|F|`, and the stated bound holds with `|O_p|` as the size parameter, not `|F|`.
The shipped `learner.ml` avoids the copying with back-edges
([D7](reference-defects.md#d7-algorithm-31-as-printed-is-not-what-learnerml-does)), so the
tool may be closer to the bound than the published algorithm is.

## What a proof would need

* **A cost model.** The Lean definitions compute results, not costs. Proving a bound means
  either instrumenting them with a step counter (a `StateM Nat` or a fuel argument) and
  proving a bound on the count, or proving bounds on output sizes and reading the time
  bound off the structure of the loops. The second is enough for `GenTA`, whose cost is
  proportional to its output.
* **Size bounds on the intermediate objects.** `|O_p|` in terms of `|F|` and the number of
  conflict groups, for Algorithm 3.1; `|Q| ≤ |Q_g|·|Q_r|` and `|Δ| ≤ |Δ_g|·|Δ_r|` after the
  worklist loop, for Algorithm 3.3. The second pair is where the claimed bound comes from
  and is the only part with real content.
* **Data structures matching the analysis.** Appendix C assumes constant-time membership
  tests in `O_a` and a precomputed production map. The Lean definitions use lists, so a
  bound proved about them as written would be weaker by a factor of `|F|` in places. Either
  the definitions change or the theorem is stated for an abstract structure with the
  assumed operation costs.

None of this affects the correctness results: Theorems 3.1 and 3.2 are about languages,
and the complexity claims are independent of them.
