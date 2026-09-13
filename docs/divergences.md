# Divergences

Three things are being compared: the paper (`ilyasergey.net/assets/pdf/papers/greta-oopsla26.pdf`
and its extended version, arXiv:2602.18166), the reference implementation
(<https://github.com/verse-lab/greta>, commit `a62d6b6`), and this formalisation. This
note records where they disagree.

Each defect below has a reproducer in the repository. `scripts/difftest.sh` runs them and
reports them as `known`; `test/expected-divergences.txt` lists the labels.

## Defects in the reference implementation

### D1. The intersection drops transitions reachable only through an ε-transition

*Severity: the repaired grammar loses productions.*

`Operation.intersect` handles the accepting state pair differently from every other pair.
For the accepting pair it calls `cartesian_product_trans_from` (`lib/operation.ml:57`),
which computes

```ocaml
let interm_sts1 = find_intermediate_states st1 trans_tbl1 debug in
...
let symbols_reachable_from_sts1 = reachable_symbols_from_states (st1::interm_sts1) trans_tbl1 in
```

so the *symbols* are collected from `st1` and everything ε-reachable below it, but the
transitions for those symbols are then looked up at `st1` alone:

```ocaml
let rhs_blsls1 = find_corr_trans_in_tbl sym st1 trans_tbl1 in
```

For every other state pair the sibling function `cartesian_product_trans_from_for_sym`
(`lib/operation.ml:101`) uses `reachable_beta_lsls_from_state_symbol`, which does look
through ε-transitions. So a transition of the accepting state that is only reachable
through an ε-transition contributes a symbol to the common alphabet, finds no matching
transition, and is silently dropped.

This is exactly the shape that `GenTA` produces: the accepting state is `e₀` and the
levels below it are reached by the ε-chain `e_i ←(ε,1) e_{i+1}`.

**On the paper's own running example.** `test/automata/paper-a.ta` is `A_r` of Figure 7
and `test/automata/paper-b.ta` is `A_g` of Figure 6. `bin/main.ml:273` of the reference
calls `O.intersect ta_initial ta_learned`, so `A_g` comes first:

```
$ ocaml-ref/_build/default/driver/main.exe intersect \
      test/automata/paper-b.ta test/automata/paper-a.ta
states decl4 expr1 expr2 expr3 iden5 stmt1
finals stmt1
...
trans stmt1 0 SEMI 2 S:decl4 T:SEMI
trans stmt1 1 IF 4 T:IF S:expr1 T:THEN S:stmt1
```

There is no `(IF,6)` transition: `if … then … else` has disappeared from the repaired
grammar. Figure 9 of the paper does contain `stmt1 ←(IF,6) IF expr0 THEN stmt1 ELSE
stmt1`, so the published figure cannot be reproduced by the implementation as it stands.
`greta checkinter` confirms the loss against the verified product:

```
$ lake exe greta checkinter test/automata/paper-b.ta test/automata/paper-a.ta REF 5
checked 113 trees
MISSING (in A ∩ B, rejected by the result): (2 IF 6 #IF ... )
```

**Smallest reproducer.** `test/automata/eps-a.ta` (and `eps-b.ta`, the same automaton):

```
states q0 q1
finals q0
trans q0 0 a 1 T:a
trans q0 -1 ε 1 S:q1
trans q1 1 b 1 T:b
```

`L(A) = { a, b }`, so `L(A ∩ A) = { a, b }`. The reference returns a single state with
only the `a` transition; the tree `b` is lost.

The same defect shows up on `test/grammars/dangling-else.cfg`, where every `if … then`
without an `else` is lost.

### D2. The intersection can fail to terminate

*Severity: the tool hangs.*

`Operation.collect_eps_connected_states_from_states_pair` (`lib/operation.ml:247`) walks
the ε-transitions of the product recursively and keeps no record of the states it has
already visited, so any cycle among them diverges. A stack sample of a hung run shows the
whole stack inside that function.

```
$ GRETA_REF_TIMEOUT=25 ocaml-ref/_build/default/driver/main.exe intersect \
      test/automata/paper-a.ta test/automata/paper-b.ta
greta-ref: timed out
```

The same inputs in the other argument order terminate (with the loss described in D1), so
whether the tool hangs depends on the order of its arguments. `test/automata/finals-a.ta`
with `finals-b.ta` is a four-transition reproducer.

A likely source of the cycles is `Treeutils.st1_transblock_subset_of_st2_transblock`:
its inner `traverse_rhs` returns `true` on the empty list, so a product state with *no*
transitions counts as a subset of every other state and gets ε-linked from all of them.
Algorithm 3.3 as printed has the same gap — `if RHS of Δ_i ⊆ RHS of Δ_j` is vacuously
true when `Δ_i` is empty — and this formalisation guards against it explicitly
(`introEpsStep` in `Greta/Intersect.lean` requires `Δ_i ≠ ∅`). We confirmed the loop's
location and the vacuous-subset behaviour, but not that this is the cycle in any
particular run.

### D3. `Converter.cfg_to_ta` raises `Not_found` on unreachable nonterminals

*Severity: the tool crashes on a legal grammar.*

`collect_nonterm_orders` (`lib/converter.ml:150`) assigns a level only to nonterminals
reachable from a start nonterminal, and `collect_sym_orders_wrt_nonterm_order` then looks
every nonterminal up with `List.assoc`.

```
$ ocaml-ref/_build/default/driver/main.exe cfg2ta test/grammars/unreachable.cfg
Fatal error: exception Not_found
```

The grammar is `A → x`, `B → A y`, `U → y` with start `A`.

### D4. `Ta.Invalid_transitions` escapes from the intersection

`find_trans_block_for_states_pair` (`lib/treeutils.ml:780`) raises `Invalid_transitions`
when it is asked for the transition block of a state pair that has none. This escapes on
`test/grammars/arith.cfg` when the learned automaton is the first argument.

### D5. `Treeutils.cartesian` does not implement the paper's matching condition

Section 2.4 requires two transitions to match when their right-hand sides have the same
length and, at each position, hold either two states or *the same* terminal.
`Treeutils.cartesian` (`lib/treeutils.ml:604`) pairs `T _, T _` without comparing the
terminals, and uses `List.map2`, which raises `Invalid_argument` on a length mismatch
rather than treating the pair as non-matching.

Neither is observable in a normal run: ranked symbols are keyed by production identifier,
and two transitions carrying the same symbol come from the same production, hence agree on
both length and terminals. The function is exported and the invariant is undocumented, so
the guards are worth having. `compatAll` in `Greta/Product.lean` implements the condition
as stated.

### D6. `Pp` disables the tracing that `intersect`'s `debug` argument selects

`lib/pp.ml` begins with `let debug = false`, and all `Pp.pp_*` printers are gated on it.
Passing `debug:true` to `Operation.intersect` therefore prints the step banners but none of
the automata, which makes the trace hard to use. (This is how the `-- hack fix because
there are too many such uses to fix... --` comment above it describes itself.)

## Differences between the paper and the reference implementation

### D7. Algorithm 3.1 as printed is not what `learner.ml` does

The published algorithm re-inserts the non-conflicting symbols `S` of an order at *every*
newly created order:

> **for** `i` in `[0, size)` **do** … `O_tmp ← O_tmp ∪ withOrder(S ∪ ithSymbols, o + i)`

preceded by `O_tmp ← pushN(O_tmp, o + 1, size − 1)`. The worked example in Section 3.1.2
follows this: `{(SEMI,2),0), ((PLUS,3),0), ((STAR,3),0)}` becomes
`{((SEMI,2),0), ((STAR,3),0), ((SEMI,2),1), ((PLUS,3),1)}`, with `(SEMI,2)` at both orders.

`Learner.update_op_per_ord_amb_symsls` (`lib/learner.ml:40`) instead pushes by `size`
(not `size − 1`) when `S` is non-empty, inserts only `ithSymbols` at each new order, and
places `S` once, below everything, at order `o + size`. It then records `S` in
`special_loop_symbols`, and `Learner.learn_ta` gives those symbols transitions whose
right-hand side points back at the *original* order, restoring by a back-edge what the
published algorithm achieves by replication.

This matters for Lemma B.2, whose proof appeals to "the construction of `O_p`, which
copies the non-conflicting symbols to each newly inserted order". That is an argument
about the published algorithm, not about the code.

This formalisation implements the published algorithm (`relayerOrder` in
`Greta/Learn.lean`).

### D8. The trivial-symbol optimisation of Section 3.1.1 is not implemented

`lib/converter.ml:255` reads `(* 3. Find trivial symbol and nontrminal - Ignore for now *)`,
and `collect_sym_orders_wrt_nonterm_order` gives every symbol an order. So `F_tr` is
empty in the tool and `O_bp` contains `((IDENT,1), 2)`, whereas Section 2.3 prints `O_bp`
for the running example without it:

```
$ ocaml-ref/_build/default/driver/main.exe obp test/grammars/running-example.cfg
order 0 0 1 2
order 1 3 5 6 7 8 9
order 2 4              # (IDENT,1), which the paper excludes
```

Section 3.1.1 says the exclusion is an optimisation that does not affect correctness, so
both are sound. The formalisation implements the exclusion and takes `--keep-trivial` to
switch it off; with that flag the two implementations agree byte for byte, which is how
`scripts/difftest.sh` compares them.

### D9. Figure 7 is internally inconsistent

Figure 7 lists `e2 ←(TINT,4) TINT e2 EQ e2`, replacing the `ident` nonterminal by `e2`,
while the corresponding rows at `e3` and `e4` keep it: `e3 ←(TINT,4) TINT ident EQ e3`.
Footnote 3 of Section 3.1.3 says the δ-generator replaces "each old state (excluding the
states associated with trivial symbols)", which makes the `e3` and `e4` rows the correct
ones. `test/automata/paper-a.ta` uses `TINT ident EQ e2` and says so in a comment.

`fillRhs` in `Greta/GenTA.lean` implements the footnote.

## Choices made in the formalisation

These are deliberate, and are not defects in either the paper or the tool.

* **The δ symbol is named `""`.** The paper writes `δ` for the ranked symbol of a
  production with no terminal on its right-hand side; `Cfg.first_terminal_of` uses the
  empty string. Symbol names carry no meaning — symbols are told apart by their
  production identifier — but they take part in symbol equality in the reference
  implementation, so the formalisation follows the reference to keep the printed automata
  comparable.
* **ε-introduction is guarded.** See D2.
* **Product states are pairs.** The reference encodes a product state by concatenating the
  two names (`Treeutils.state_pair_append`), which is not injective. `TA` is
  parameterised by its state type so that the product construction can use real pairs; the
  printer turns them into `(q1,q2)`.
* **Associativity positions index the whole right-hand side.** Definition of `t_idx` in
  Section 3 says `0 ≤ i < Rank(t_T)`, which counts terminals as well as nonterminals, and
  `Treeutils.find_index_subt_with_same_sym` agrees. Section 3.1.2's prose ("as a right
  child (position 1)") counts only nonterminals. The two readings agree on the paper's
  example; the formalisation follows the formal definition and the code.
