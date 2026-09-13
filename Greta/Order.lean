/-
The base precedence order `O_bp` of Section 3.1.1, trivial symbols `F_tr` of Section
3.1.1, and the `HighToLow` relation used by Algorithm 3.2 to reintroduce cycles.
-/
import Greta.CFG

namespace Greta

/-- A precedence order: a map from order (level) to the symbols sitting at that order. -/
abbrev OrderMap := List (Nat × List Sym)

namespace OrderMap

/-- Symbols at a given order. -/
def ofOrder (m : OrderMap) (o : Nat) : List Sym :=
  (m.filter fun p => p.1 == o).flatMap Prod.snd

/-- Orders at which a symbol occurs. -/
def ordersOf (m : OrderMap) (s : Sym) : List Nat :=
  (m.filter fun p => p.2.contains s).map Prod.fst

/-- Largest order occurring in the map. -/
def maxOrder (m : OrderMap) : Nat := m.foldl (fun acc p => max acc p.1) 0

private theorem le_foldl_self : ∀ (l : List (Nat × List Sym)) (a : Nat),
    a ≤ l.foldl (fun acc q => max acc q.1) a
  | [],      a => Nat.le_refl a
  | q :: qs, a => Nat.le_trans (Nat.le_max_left a q.1) (le_foldl_self qs (max a q.1))

private theorem le_foldl_of_mem : ∀ (l : List (Nat × List Sym)) (a i : Nat) (ss : List Sym),
    (i, ss) ∈ l → i ≤ l.foldl (fun acc q => max acc q.1) a
  | [],      _, _, _,  h => absurd h (by simp)
  | q :: qs, a, i, ss, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_trans (Nat.le_max_right a i) (le_foldl_self qs (max a i))
      · exact le_foldl_of_mem qs (max a q.1) i ss h

theorem le_maxOrder {m : OrderMap} {i : Nat} {ss : List Sym} (h : (i, ss) ∈ m) :
    i ≤ m.maxOrder := le_foldl_of_mem m 0 i ss h

/-- All symbols mentioned. -/
def symbols (m : OrderMap) : List Sym := (m.flatMap Prod.snd).dedup

/-- Normal form: one entry per order, ordered by increasing order, duplicates removed. -/
def normalise (m : OrderMap) : OrderMap :=
  (List.range (m.maxOrder + 1)).filterMap fun o =>
    let ss := (m.ofOrder o).dedup
    if ss.isEmpty then none else some (o, ss)

/-- Shift every order `≥ o` up by `n` (`pushN` of Algorithm 3.1). -/
def pushN (m : OrderMap) (o n : Nat) : OrderMap :=
  m.map fun p => if o ≤ p.1 then (p.1 + n, p.2) else p

/-- Drop everything at order `o`. -/
def removeOrder (m : OrderMap) (o : Nat) : OrderMap := m.filter fun p => p.1 != o

/-- `withOrder S o`: place the symbols `S` at order `o`. -/
def withOrder (ss : List Sym) (o : Nat) : OrderMap := if ss.isEmpty then [] else [(o, ss)]

end OrderMap

namespace CFG

/-! ### Levels of nonterminals -/

/-- Nonterminals occurring on the right-hand side of some production of `A`. -/
def succNts (g : CFG) (A : Nonterminal) : List Nonterminal :=
  ((g.prods.filter fun p => p.1 == A).flatMap fun p =>
    p.2.filterMap fun
      | .nt B => some B
      | .term _ => none).dedup

/-- One layer of breadth-first search from `frontier`. -/
def levelStep (g : CFG) : Nat → List Nonterminal → List (Nonterminal × Nat) → Nat →
    List (Nonterminal × Nat)
  | 0,        _,        acc, _ => acc
  | fuel + 1, frontier, acc, d =>
      let seen := acc.map Prod.fst
      let next := ((frontier.flatMap (g.succNts ·)).dedup).filter fun B => !seen.contains B
      if next.isEmpty then acc
      else levelStep g fuel next (acc ++ next.map fun B => (B, d + 1)) (d + 1)

/--
`d(e)`, the distance of each nonterminal from a start nonterminal (Section 3.1.1).
Nonterminals unreachable from a start nonterminal get no level.
-/
def levels (g : CFG) : List (Nonterminal × Nat) :=
  levelStep g (g.nonterms.length + 1) g.starts (g.starts.map fun s => (s, 0)) 0

/-- Level of a nonterminal, `0` for start nonterminals. -/
def levelOf (g : CFG) (A : Nonterminal) : Option Nat := g.levels.lookup A

/-! ### Trivial symbols -/

/-- A production whose right-hand side is a single terminal. -/
def isSingleTerminalProd (p : Production) : Bool :=
  match p.2 with
  | [.term _] => true
  | _         => false

/--
`F_tr` (Section 3.1.1): rank-1 symbols whose production maps a nonterminal to a single
terminal, and *all* of whose left-hand side's productions do the same.  Such symbols
cannot take part in an associativity or precedence conflict.
-/
def trivialSyms (g : CFG) : List Sym :=
  g.rankedProds.filterMap fun sp =>
    if isSingleTerminalProd sp.2 ∧ ((g.prods.filter fun p => p.1 == sp.2.1).all isSingleTerminalProd)
    then some sp.1 else none

/-! ### The base precedence order -/

/-- `ô(s) = d(Lhs(Prod(s)))`, the order of a ranked symbol (Section 3.1.1). -/
def symOrder (g : CFG) (sp : Sym × Production) : Option Nat := g.levelOf sp.2.1

/--
`O_bp = {(s, ô(s)) | s ∈ F \ F_tr}` (Section 3.1.1), presented as a map from order to
the symbols at that order.

Note.  The reference implementation does not exclude trivial symbols here; see
`docs/divergences.md`.  Section 3.1.1 states that this exclusion is an optimisation that
does not affect correctness, so both choices are sound.
-/
def baseOrder (g : CFG) (excludeTrivial : Bool := true) : OrderMap :=
  let triv := g.trivialSyms
  let pairs := g.rankedProds.filterMap fun sp =>
    if excludeTrivial ∧ triv.contains sp.1 then none
    else (g.symOrder sp).map fun o => (sp.1, o)
  (OrderMap.normalise (pairs.map fun so => (so.2, [so.1])))

/-! ### Cycles in the symbol order -/

/--
`HighToLow(G, O_p)` (Section 3.1.3).  A pair of symbols `(s_l, s_h)` is reported when

* `s_h` sits at a strictly higher order than `s_l` in the *base* precedence order `O_bp`,
  and
* the production of `s_h` mentions the left-hand side nonterminal of `s_l` on its
  right-hand side,

so that `s_l` can appear deeper in a parse tree than `s_h` even though the order places it
above.  Such a cycle in the symbol order has to be reintroduced into the learned
automaton.  The orders reported alongside the symbols are the *highest* order of `s_h` and
the *lowest* order of `s_l` in the learned order `O_p`.

Note that the comparison is against `O_bp` and the reported orders come from `O_p`; using
`O_p` for the comparison as well would report every ordinary nesting of one symbol under
another, not just the cycles.
-/
def highToLow (g : CFG) (obp op : OrderMap) : List ((Sym × Nat) × (Sym × Nat)) :=
  g.rankedProds.flatMap fun sh =>
    g.rankedProds.filterMap fun sl =>
      match (obp.ordersOf sh.1).min?, (obp.ordersOf sl.1).min?,
            (op.ordersOf sh.1).max?, (op.ordersOf sl.1).min? with
      | some bh, some bl, some oh, some ol =>
          if bl < bh ∧ sh.2.2.contains (.nt sl.2.1) then some ((sl.1, ol), (sh.1, oh))
          else none
      | _, _, _, _ => none

end CFG

end Greta
