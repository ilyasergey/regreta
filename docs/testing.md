# Testing

Two suites. The Lean suite runs inside `lake exe greta selftest` and needs nothing but the
build. The differential suite compares the Lean tool with the OCaml reference
implementation and is described in [`reproducing.md`](reproducing.md).

## The Lean suite

```
lake exe greta selftest
```

**The running example.** The grammar of Figure 1 is encoded in `Greta/Test.lean`. The
suite checks that `CFG.toTA` reproduces Figure 6, that the base precedence order
reproduces the `O_bp` of Section 2.3.1, that `IDENT` is the only trivial symbol, that
`LearnOaOp` reproduces the `O_p` of Section 2.3.2 from the rejected tree examples of
Figure 3, and that `GenTA` reproduces Figure 7 transition for transition, with the `(TINT,4)`
row at `e2` corrected as [`divergences.md`](divergences.md#7-figure-7-has-a-typo) explains.
It also checks the translation theorem on concrete parse trees.

**Two edge cases of the learner.** `testAssocOnly` checks that a symbol whose only conflict
is with itself is still re-layered ([divergences §2](divergences.md#2-algorithm-31s-inputs-get-a-specification));
`testCycle` checks the witness against Theorem 3.1(2) as printed
([divergences §1](divergences.md#1-theorem-31-needs-acyclicity)).

**The optimised intersection against the verified one.** For each of the five
configurations of Table 1 (`I^def`, `I^1`, `I^2`, `I^3`, `I^123`), the suite runs
`intersectTA` (Algorithm 3.3) and compares its language with `prodTA` (Section 2.4), which
is proved to recognise the intersection. The comparison is on a corpus of trees enumerated
from both inputs and from the result, so both over- and under-acceptance are visible. The
same comparison is run on grammars from a deterministic pseudo-random generator, so a
failure reproduces from its seed.

## The text format

Shared by `lake exe greta` and the OCaml driver. Line-based, whitespace-separated, `#`
starts a comment. A name that would be empty is written `-`.

A **ranked symbol** is three tokens: identifier, name, rank. The identifier is the index
of the production the symbol comes from, counting from 0 in grammar order; `(ε,1)` is
`-1 ε 1`.

A **right-hand-side entry** is `T:<terminal>` or `S:<state>`.

A **tree automaton**:

```
states  q0 q1 ...
finals  q0
terminals  A B ...
trans <target> <id> <name> <rank> <entry> ...
```

A **grammar**:

```
nonterms  expr stmt ...
terms     PLUS INT ...
starts    stmt
prod <lhs> <entry> ...          # entries are T:<terminal> or N:<nonterminal>
```

A **tree example** is `example <top-id> <bottom-id> <child-index>`, the `Eg(α, β, i)` of
Section 3: the production `top-id` with the production `bottom-id` nested at child position
`i`. The file lists the examples the user did *not* select. The child index counts every
right-hand-side element, terminals included.

Trees, which only appear in diagnostic output, are printed as `#<terminal>` for a leaf
and `(<id> <name> <rank> <child> ...)` for a node.
