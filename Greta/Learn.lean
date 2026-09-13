/-
**Algorithm 3.1 (LearnOaOp)**: learning associativity and precedence orderings from the
tree examples the user did *not* select.

The algorithm rewrites the base precedence order `O_bp` of the input grammar so that the
symbols involved in each conflict are stratified into consecutive orders, while the
relative order of all other symbols is preserved.
-/
import Greta.Examples

namespace Greta

/-- `O_a`: associativity restrictions, a symbol together with a forbidden child position. -/
abbrev Oa := List (Sym × Nat)

/--
`M_to` of Algorithm 3.1: for each order, the groups of conflicting symbols at that order,
each group totally ordered from lowest to highest precedence.
-/
abbrev ToMap := List (Nat × List (List Sym))

namespace Oa

/-- The forbidden child positions recorded for a symbol. -/
def positionsOf (oa : Oa) (s : Sym) : List Nat :=
  (oa.filter fun p => p.1 == s).map Prod.snd

/-- Whether the symbol takes part in an associativity restriction. -/
def mem (oa : Oa) (s : Sym) : Bool := oa.any fun p => p.1 == s

end Oa

/--
One iteration of the second loop of Algorithm 3.1: re-insert the conflicting symbol
groups `grp` found at order `o`, stratified over the orders `o, …, o + size - 1`, keeping
the non-conflicting symbols `S` of that order alongside them.
-/
def relayerOrder (oa : Oa) (otmp : OrderMap) (o : Nat) (grp : List (List Sym)) : OrderMap :=
  let size := grp.foldl (fun a gl => max a gl.length) 0
  if size = 0 then otmp else
  let ambs := grp.flatten
  let S := (otmp.ofOrder o).filter fun s => !ambs.contains s
  let m0 := (otmp.removeOrder o).pushN (o + 1) (size - 1)
  let m1 := (List.range size).foldl (fun m i =>
      let ith := grp.filterMap fun gl => gl[i]?
      m ++ OrderMap.withOrder ((S ++ ith).dedup) (o + i)) m0
  let lastIth := grp.filterMap fun gl => gl[size - 1]?
  if lastIth.any (fun s => oa.mem s) then
    (m1.pushN (o + size) 1) ++ OrderMap.withOrder S (o + size)
  else m1

/--
**Algorithm 3.1 (LearnOaOp).**  Returns the associativity restrictions `O_a` inferred
from the unselected examples and the precedence order `O_p` obtained by stratifying the
base precedence order of `g` according to `mto`.
-/
def learnOaOp (g : CFG) (neg : List TreeExample) (mto : ToMap)
    (excludeTrivial : Bool := true) : Oa × OrderMap :=
  let obp := g.baseOrder excludeTrivial
  let oa : Oa := neg.filterMap fun e => if e.isAssoc then some (e.top, e.idx) else none
  -- descending in the order
  let groups := mto.filter (fun p => !p.2.isEmpty)
                   |>.mergeSort (fun a b => b.1 ≤ a.1)
  let otmp := groups.foldl (fun m og => relayerOrder oa m og.1 og.2) obp
  (oa, otmp.normalise)

/-!
### Deriving `M_to` from the unselected examples

A precedence-related example `Eg(α, β, i)` that the user rejected says that `α` must
*not* sit directly above `β`, i.e. that `β` has the lower precedence of the two, so in
the learned hierarchy `β` must be strictly *shallower* (lower order) than `α`.
-/

/-- The ordering constraints `β < α` carried by the unselected precedence examples. -/
def precPairs (neg : List TreeExample) : List (Sym × Sym) :=
  neg.filterMap fun e => if e.isPrec then some (e.bot, e.top) else none

/--
Topologically sort a set of symbols according to `lt` (lowest precedence first),
falling back on the given order for symbols the constraints do not relate.  The result is
the `G` component of `M_to` for one conflict group.
-/
def orderGroup (lt : List (Sym × Sym)) (ss : List Sym) : List Sym :=
  ss.mergeSort fun a b =>
    -- `a` comes first when `a < b` is required, or when nothing forces the opposite
    if lt.contains (a, b) then true
    else if lt.contains (b, a) then false
    else true

/--
Build `M_to` from a base precedence order and the unselected examples: every order of
`obp` that contains at least two symbols mentioned in a precedence conflict yields one
totally ordered group.
-/
def toMapOf (obp : OrderMap) (neg : List TreeExample) : ToMap :=
  let lt := precPairs neg
  let involved := (lt.flatMap fun p => [p.1, p.2]).dedup
  obp.filterMap fun p =>
    let here : List Sym := p.2.filter fun s => involved.contains s
    if 2 ≤ here.length then some (p.1, [orderGroup lt here]) else none

end Greta
