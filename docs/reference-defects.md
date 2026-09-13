# Defects in the reference implementation

What the differential testing found in [Greta](https://github.com/verse-lab/greta) at
commit [`a62d6b6`](https://github.com/verse-lab/greta/tree/a62d6b68a92178eb2f1bd57b620386e5a2cdc1b6),
and what a fix would look like.  Where the paper and the tool disagree is here too; where
the paper's statements and this formalisation's differ is in
[`divergences.md`](divergences.md).  [`reproducing.md`](reproducing.md) says how to run
the comparison.

Section, figure and algorithm numbers are those of the main body of the paper. Numbered
definitions (`Definition A.n`) and the proofs of Lemmas B.1 and B.2 are in the paper's
supplementary material.

Every defect below has a reproducer in the repository. `scripts/difftest.sh`
runs them and reports them as `known`; `test/expected-divergences.txt` lists the labels, so
that anything new that diverges is reported as a failure.

None of D1 to D6 affects the paper's theorems: they are in code the paper does not
describe, or in code paths the paper's algorithms do not take.  D1 and D2 do affect the
tool: on the paper's own running example the repaired grammar loses `if … then … else`,
and with the automata in the other order the tool hangs.

## Summary

| | What | Where | Severity |
| --- | --- | --- | --- |
| [D1](#d1-the-intersection-drops-transitions-reachable-only-through-an-ε-transition) | The intersection drops transitions reachable only through an ε-transition | `lib/operation.ml` | the repaired grammar silently loses productions |
| [D2](#d2-the-intersection-can-fail-to-terminate) | The intersection can fail to terminate | `lib/operation.ml` | the tool hangs |
| [D3](#d3-convertercfg_to_ta-raises-not_found-on-unreachable-nonterminals) | `cfg_to_ta` raises `Not_found` on unreachable nonterminals | `lib/converter.ml` | the tool crashes on a legal grammar |
| [D4](#d4-ta-invalid_transitions-escapes-from-the-intersection) | `Invalid_transitions` escapes from the intersection | `lib/treeutils.ml` | the tool crashes |
| [D5](#d5-treeutilscartesian-does-not-implement-the-papers-matching-condition) | `cartesian` does not check that paired terminals are equal | `lib/treeutils.ml` | latent |
| [D6](#d6-pp-disables-the-tracing-that-intersects-debug-argument-selects) | `Pp` disables the tracing the `debug` flag selects | `lib/pp.ml` | debugging |
| [D7](#d7-algorithm-31-as-printed-is-not-what-learnerml-does) | Algorithm 3.1 as printed is not what `learner.ml` does | paper vs. code | Lemma B.2's proof does not apply to the code |
| [D8](#d8-the-trivial-symbol-optimisation-of-311-is-not-implemented) | The trivial-symbol optimisation of §3.1.1 is not implemented | paper vs. code | the paper's `O_bp` is not what the tool computes |
| [D9](#d9-figure-7-is-internally-inconsistent) | Figure 7 is internally inconsistent | paper | typo |

## Defects in the reference implementation

### D1. The intersection drops transitions reachable only through an ε-transition

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
transition, and is dropped without a warning.

This is exactly the shape `GenTA` produces: the accepting state is `e₀`, and the levels
below it are reached by the ε-chain `e_i ←(ε,1) e_{i+1}`.

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
grammar. Figure 9 does contain `stmt1 ←(IF,6) IF expr0 THEN stmt1 ELSE stmt1`, so the
published figure is not what the implementation produces. `greta checkinter` confirms the
loss against the verified product:

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

**Suggested fix.** Look transitions up through the ε-closure at the accepting pair too.
The one-line version is to replace, in `cartesian_product_trans_from`,

```ocaml
let rhs_blsls1 = find_corr_trans_in_tbl sym st1 trans_tbl1 in
let rhs_blsls2 = find_corr_trans_in_tbl sym st2 trans_tbl2 in
```

by the ε-aware lookup that the rest of the algorithm already uses:

```ocaml
let rhs_blsls1 = reachable_beta_lsls_from_state_symbol st1 sym trans_tbl1 debug in
let rhs_blsls2 = reachable_beta_lsls_from_state_symbol st2 sym trans_tbl2 debug in
```

`cartesian_product_trans_from` then does the same thing as
`cartesian_product_trans_from_for_sym` and can be dropped in favour of it: Step 1 becomes
the first iteration of the Step 3 worklist. That is how the formalisation is structured:
[`transitionsAtPair`](../Greta/Intersect.lean#L59) is used for the accepting pair and for
every other pair alike, and [`TA.transAt`](../Greta/Intersect.lean#L41) always looks
through [`TA.epsDown`](../Greta/Intersect.lean#L32).

A regression test for it: `L(A ⊗ A) = L(A)` for any `A` with an ε-transition out of its
accepting state, which `test/automata/eps-a.ta` is.

### D2. The intersection can fail to terminate

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

A likely source of the cycles is `Treeutils.st1_transblock_subset_of_st2_transblock`: its
inner `traverse_rhs` returns `true` on the empty list, so a product state with *no*
transitions counts as a subset of every other state and gets ε-linked from all of them.
Algorithm 3.3 as printed has the same gap: `if RHS of Δ_i ⊆ RHS of Δ_j` is vacuously true
when `Δ_i` is empty. The loop's location and the vacuous-subset behaviour are confirmed;
that this is the cycle in any particular run is not.

**Suggested fix**, in two parts.

*Make the walk total.* Thread a visited set through the recursion:

```ocaml
let rec collect_eps_connected (from_states : state * state) (seen : (state * state) list)
    (raw_trans : ...) : (state * state) list =
  if List.mem from_states seen then [] else
  let seen = from_states :: seen in
  ...  (* recurse with `seen` instead of starting over *)
```

The walk then terminates on any input, cycles included, and the result is the ε-closure of
the pair rather than an unfolding of it.

*Stop creating the spurious links.* Require the subset to be non-empty, both in the code
and in Algorithm 3.3:

```ocaml
let res_bool =
  st1_trans_rhs_lst <> []                       (* added *)
  && List.length st1_trans_rhs_lst <= List.length st2_trans_rhs_lst
  && traverse_rhs st1_trans_rhs_lst
```

and correspondingly `if ∅ ≠ RHS of Δ_i ⊆ RHS of Δ_j` in the pseudocode. A state with no
transitions is a dead state, which Step 12 already removes; it should not be ε-linked from
anything first. [`introEpsStep`](../Greta/Intersect.lean#L134) carries that guard.

### D3. `Converter.cfg_to_ta` raises `Not_found` on unreachable nonterminals

`collect_nonterm_orders` (`lib/converter.ml:150`) assigns a level only to nonterminals
reachable from a start nonterminal, and `collect_sym_orders_wrt_nonterm_order` then looks
every nonterminal up with `List.assoc`.

```
$ ocaml-ref/_build/default/driver/main.exe cfg2ta test/grammars/unreachable.cfg
Fatal error: exception Not_found
```

The grammar is `A → x`, `B → A y`, `U → y` with start `A` (`test/grammars/unreachable.cfg`).

**Suggested fix.** An unreachable nonterminal cannot occur in any complete parse tree, so
dropping it changes nothing about the language. Prune before converting:

```ocaml
let reachable = nonterms_reachable_from g.starts g.productions in
let g = { g with nonterms   = List.filter (fun nt -> List.mem nt reachable) g.nonterms;
                 productions = List.filter (fun (lhs, _) -> List.mem lhs reachable) g.productions }
```

and warn, since an unreachable nonterminal in a grammar the user wrote is usually a
mistake. Failing with a diagnostic that names the nonterminal would also be an
improvement on `Not_found`. The formalisation takes the third route:
[`levelOf`](../Greta/Order.lean#L91) returns an `Option`, and
[`baseOrder`](../Greta/Order.lean#L124) skips the symbols with no level.

### D4. `Ta.Invalid_transitions` escapes from the intersection

`find_trans_block_for_states_pair` (`lib/treeutils.ml:777`) raises `Invalid_transitions`
when asked for the transition block of a state pair that has none:

```ocaml
match List.assoc_opt st_pair trans_blocks with
| None -> raise Invalid_transitions
| Some ls -> ls
```

Its only caller is `st1_transblock_subset_of_st2_transblock`, which
`simplify_trans_blocks_with_epsilon_transitions` (Step 10) applies to every pair in
`state_pairs_renamed`. So the raise fires whenever the renamed state list and the renamed
transition blocks get out of step, which the duplicate-state removal of Steps 5–8 can do.

`test/grammars/cycle.cfg` with `test/examples/cycle.ex` reaches it: `A_r` there has two
`(STAR,3)` transitions at `e1`, one of them the cycle transition of Section 3.1.3, and
intersecting `A_r` with `A_g` in that order ends with

```
$ ocaml-ref/_build/default/driver/main.exe intersect test/out/cycle.ar.ta test/out/cycle.ag.ta
Fatal error: exception Gretacore.Ta.Invalid_transitions
```

(`scripts/difftest.sh` writes the two automata to `test/out/`). In the other argument
order the same inputs do not terminate (D2).

**Suggested fix.** Return `[]`. A product state with no transitions is a dead state, and
the algorithm already has that notion, since Step 12 of `intersect` computes `dead_states`
exactly as the pairs with an empty block. Raising here turns a normal intermediate state
of the construction into an error. This interacts with D2: once the empty block is a legal
value, `st1_transblock_subset_of_st2_transblock` has to reject it explicitly rather than
treat it as a subset of everything.

### D5. `Treeutils.cartesian` does not implement the paper's matching condition

Section 2.4 requires two transitions to match when their right-hand sides have the same
length and, at each position, hold either two states or *the same* terminal.
`Treeutils.cartesian` (`lib/treeutils.ml:604`) pairs `T _, T _` without comparing the
terminals, and uses `List.map2`, which raises `Invalid_argument` on a length mismatch
rather than treating the pair as non-matching.

Neither is observable in a normal run: ranked symbols are keyed by production identifier,
and two transitions carrying the same symbol come from the same production, hence agree on
both length and terminals. The function is exported and the invariant is undocumented, so
the guards are worth having.

**Suggested fix.** Make the function partial in the intended sense rather than in the
exception sense: return the matched pairs as an option and let the caller drop a
non-match:

```ocaml
let rec cartesian (xs : beta list) (ys : beta list) : (beta * beta) list option =
  match xs, ys with
  | [], [] -> Some []
  | T a :: xs, T b :: ys when String.equal a b ->
      Option.map (fun r -> (T a, T b) :: r) (cartesian xs ys)
  | (S _ as x) :: xs, (S _ as y) :: ys ->
      Option.map (fun r -> (x, y) :: r) (cartesian xs ys)
  | _ -> None
```

`cross_buckets` then uses `List.filter_map` instead of `List.map`.
[`compatAll`](../Greta/Product.lean#L33) and [`zipBetas`](../Greta/Product.lean#L39)
implement the condition as stated, and
[`compatAll_of_match`](../Greta/Product.lean#L217) proves that it is exactly the condition
under which the two automata can accept the same tree, so the guard costs nothing.

### D6. `Pp` disables the tracing that `intersect`'s `debug` argument selects

`lib/pp.ml` begins with

```ocaml
(* hack fix because there are too many such uses to fix... *)
let debug = false
let noprintf fmt = if debug then printf fmt else ifprintf stdout fmt
```

and every `Pp.pp_*` printer is gated on it. Passing `debug:true` to `Operation.intersect`
therefore prints the step banners but none of the automata, which makes the trace hard to
use; D2 was located by stack sampling rather than by reading a trace.

**Suggested fix.** Give the printers a `debug` parameter, as the rest of the library
already does, and pass the caller's flag through; or, less invasively, replace the
module-level `let debug = false` with a mutable flag that `intersect` and the other
entry points set on the way in.

## Differences between the paper and the reference implementation

### D7. Algorithm 3.1 as printed is not what `learner.ml` does

The published algorithm re-inserts the non-conflicting symbols `S` of an order at *every*
newly created order:

> **for** `i` in `[0, size)` **do** … `O_tmp ← O_tmp ∪ withOrder(S ∪ ithSymbols, o + i)`

preceded by `O_tmp ← pushN(O_tmp, o + 1, size − 1)`. The worked example in §3.1.2 follows
this: `{((SEMI,2),0), ((PLUS,3),0), ((STAR,3),0)}` becomes
`{((SEMI,2),0), ((STAR,3),0), ((SEMI,2),1), ((PLUS,3),1)}`, with `(SEMI,2)` at both orders.

`Learner.update_op_per_ord_amb_symsls` (`lib/learner.ml:40`) instead pushes by `size` (not
`size − 1`) when `S` is non-empty, inserts only `ithSymbols` at each new order, and places
`S` once, below everything, at order `o + size`. It then records `S` in
`special_loop_symbols`, and `Learner.learn_ta` gives those symbols transitions whose
right-hand side points back at the *original* order, restoring by a back-edge what the
published algorithm achieves by replication.

This matters for Lemma B.2, whose proof appeals to "the construction of `O_p`, which
copies the non-conflicting symbols to each newly inserted order". That is an argument
about the published algorithm, not about the code.

**Suggested fix.** The smaller change is to the code: make the loop insert
`S ∪ ithSymbols` at each new order and push by `size − 1`, which is what
[`relayerOrder`](../Greta/Learn.lean#L38) does, and drop `special_loop_symbols` and the
back-edges in `learn_ta` that compensate for its absence. Lemma B.2 then applies to the
code as written.

If the back-edge construction is preferred, since it produces fewer states, then Algorithm 3.1
in the paper should be restated to match it, and Lemma B.2 reproved: the back-edge makes
the non-conflicting symbols reachable from the original order rather than present at it,
so the lemma's conclusion has to be about reachability in the generated automaton rather
than about membership in `O_p`.

### D8. The trivial-symbol optimisation of §3.1.1 is not implemented

`lib/converter.ml:255` reads `(* 3. Find trivial symbol and nontrminal - Ignore for now *)`,
and `collect_sym_orders_wrt_nonterm_order` gives every symbol an order. So `F_tr` is empty
in the tool and `O_bp` contains `((IDENT,1), 2)`, whereas §2.3.1 prints `O_bp` for the
running example without it:

```
$ ocaml-ref/_build/default/driver/main.exe obp test/grammars/running-example.cfg
order 0 0 1 2
order 1 3 5 6 7 8 9
order 2 4              # (IDENT,1), which the paper excludes
```

§3.1.1 says the exclusion is an optimisation that does not affect correctness, so both are
sound.

**Suggested fix.** `F_tr` is a two-line predicate, a rank-1 symbol whose production is
`A → a` and all of whose left-hand side's productions have that shape, so implementing it
is cheap; [`trivialSyms`](../Greta/Order.lean#L106) is the whole of it. Filtering `O_bp`
through it makes the tool produce the `O_bp` and the `A_r` the paper prints. Failing that,
§3.1.1 should say that the optimisation is described but not implemented, since a reader
checking Figure 7 against the artefact will otherwise get a different automaton.

The formalisation implements the exclusion and takes `--keep-trivial` to switch it off;
with that flag the two implementations agree byte for byte, which is how
`scripts/difftest.sh` compares them.

### D9. Figure 7 is internally inconsistent

Figure 7 lists `e2 ←(TINT,4) TINT e2 EQ e2`, replacing the `ident` nonterminal by `e2`,
while the corresponding rows at `e3` and `e4` keep it: `e3 ←(TINT,4) TINT ident EQ e3`.
Footnote 3 of §3.1.3 says the δ-generator replaces "each old state (excluding the states
associated with trivial symbols)", which makes the `e3` and `e4` rows the correct ones.

**Suggested fix.** Print `e2 ←(TINT,4) TINT ident EQ e2`.
[`fillRhs`](../Greta/GenTA.lean#L67) implements the footnote, and with that row corrected
`lake exe greta genta` reproduces Figure 7 transition for transition; the self-test checks
it.
