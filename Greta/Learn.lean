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

/-!
### Linearising a conflict group

The symbols of one conflict group are laid out from lowest to highest precedence.  The
layout has to respect every constraint the rejected examples impose, and to leave symbols
the constraints do not relate in their original order.

A comparison sort cannot do this.  The comparison "`a` before `b` unless the examples say
otherwise" is not transitive, so a merge sort can fail to compare two symbols that a
constraint relates and silently drop that constraint.  Kahn's algorithm is used instead.
-/

/-- Nothing still to be placed is required to come before `a`. -/
def topoReady (lt : List (Sym × Sym)) (rest : List Sym) (a : Sym) : Bool :=
  rest.all fun b => b == a || !(lt.contains (b, a))

/--
Kahn's algorithm with "first available" selection: repeatedly take the first symbol of
`rest` that nothing remaining has to precede, so that symbols the constraints leave
unrelated keep their original relative order.

`none` means the constraints have a cycle inside `rest`, so the rejected examples are
contradictory and no linearisation exists.  The reference implementation detects the same
situation in `Examples.form_total_order_among_op_symbols_from_same_group`, where an
insertion sort checks each placement with `ensure_consistent` and exits on failure.
-/
def topoSort (lt : List (Sym × Sym)) : Nat → List Sym → Option (List Sym)
  | 0,        rest => if rest.isEmpty then some [] else none
  | fuel + 1, rest =>
      if rest.isEmpty then some []
      else
        match rest.find? (topoReady lt rest) with
        | some a => (topoSort lt fuel (rest.erase a)).map (a :: ·)
        | none   => none

/-- The linearisation of one conflict group, or `none` when the constraints are cyclic. -/
def orderGroup? (lt : List (Sym × Sym)) (ss : List Sym) : Option (List Sym) :=
  topoSort lt ss.length ss

/--
Order a conflict group from lowest to highest precedence, keeping the given order for
symbols the constraints do not relate.  The result is the `G` component of `M_to` for one
conflict group.  On contradictory examples the input order is kept unchanged;
`orderGroup?` reports that case, and the soundness theorems assume it does not arise.
-/
def orderGroup (lt : List (Sym × Sym)) (ss : List Sym) : List Sym :=
  (orderGroup? lt ss).getD ss

/-! #### Correctness of the linearisation -/

theorem topoSort_perm (lt : List (Sym × Sym)) :
    ∀ (fuel : Nat) (rest l : List Sym), topoSort lt fuel rest = some l → l.Perm rest := by
  intro fuel
  induction fuel with
  | zero =>
      intro rest l h
      rw [topoSort] at h
      split at h
      · next he =>
          cases h; rw [List.isEmpty_iff] at he; subst he; exact List.Perm.refl _
      · exact absurd h (by simp)
  | succ fuel ih =>
      intro rest l h
      rw [topoSort] at h
      split at h
      · next he =>
          cases h; rw [List.isEmpty_iff] at he; subst he; exact List.Perm.refl _
      · next =>
          cases hf : rest.find? (topoReady lt rest) with
          | none => rw [hf] at h; exact absurd h (by simp)
          | some c =>
              rw [hf] at h
              simp only [Option.map_eq_some_iff] at h
              obtain ⟨l', hl', rfl⟩ := h
              exact ((ih _ _ hl').cons c).trans (List.perm_cons_erase
                (List.mem_of_find?_eq_some hf)).symm

/--
Every constraint the examples impose is respected: if the group's symbols `a` and `b` are
distinct and the examples require `a` to come before `b`, then it does.  This is what
makes `LearnedSpec.strat` hold of the pipeline, and it is exactly what the merge sort this
replaces failed to deliver.
-/
theorem topoSort_before (lt : List (Sym × Sym)) :
    ∀ (fuel : Nat) (rest l : List Sym), topoSort lt fuel rest = some l →
      ∀ a b, a ∈ rest → b ∈ rest → a ≠ b → (a, b) ∈ lt → l.idxOf a < l.idxOf b := by
  intro fuel
  induction fuel with
  | zero =>
      intro rest l h a b ha _ _ _
      rw [topoSort] at h
      split at h
      · next he => rw [List.isEmpty_iff] at he; subst he; exact absurd ha (by simp)
      · exact absurd h (by simp)
  | succ fuel ih =>
      intro rest l h a b ha hb hne hlt
      rw [topoSort] at h
      split at h
      · next he => rw [List.isEmpty_iff] at he; subst he; exact absurd ha (by simp)
      · next =>
          cases hf : rest.find? (topoReady lt rest) with
          | none => rw [hf] at h; exact absurd h (by simp)
          | some c =>
              rw [hf] at h
              simp only [Option.map_eq_some_iff] at h
              obtain ⟨l', hl', rfl⟩ := h
              have hready : topoReady lt rest c = true := List.find?_some hf
              -- nothing still to be placed may be required to precede the symbol taken
              have key : ∀ x ∈ rest, x ≠ c → (x, c) ∉ lt := by
                intro x hx hxc hmem
                have h1 : (x == c || !(lt.contains (x, c))) = true :=
                  (List.all_eq_true.mp hready) x hx
                rcases Bool.or_eq_true _ _ |>.mp h1 with h2 | h2
                · exact hxc (by simpa using h2)
                · have h3 : lt.contains (x, c) = true := List.elem_eq_true_of_mem hmem
                  rw [h3] at h2
                  exact Bool.noConfusion h2
              have hcb : c ≠ b := fun hcb => key a ha (hcb ▸ hne) (hcb ▸ hlt)
              by_cases hac : a = c
              · subst hac
                rw [List.idxOf_cons_self, List.idxOf_cons_ne _ hcb]
                exact Nat.succ_pos _
              · have ha' : a ∈ rest.erase c := (List.mem_erase_of_ne hac).mpr ha
                have hb' : b ∈ rest.erase c :=
                  (List.mem_erase_of_ne (Ne.symm hcb)).mpr hb
                rw [List.idxOf_cons_ne _ (Ne.symm hac), List.idxOf_cons_ne _ hcb]
                exact Nat.succ_lt_succ (ih _ _ hl' a b ha' hb' hne hlt)

/--
Build `M_to` from a base precedence order and the unselected examples.

`S_C` of Section 3 is the set of symbols involved in a precedence *or an associativity*
related conflict, and `S_E` is its partition into maximal pairwise-conflicting subsets, so
a symbol whose only conflict is with itself — an associativity restriction and no
precedence partner — forms a singleton group.  Those singletons matter: they are what
makes the last clause of Algorithm 3.1 fire, which is what leaves an order above the
symbol for `GenTA` to send the forbidden child to.  Dropping them leaves the symbol at the
top order, `e_{i+1}` does not exist, and every tree using the symbol is rejected.
-/
def toMapOf (obp : OrderMap) (neg : List TreeExample) : ToMap :=
  let lt := precPairs neg
  let involved := (neg.flatMap fun e => [e.top, e.bot]).dedup
  obp.filterMap fun p =>
    let here : List Sym := p.2.filter fun s => involved.contains s
    if here.isEmpty then none else some (p.1, [orderGroup lt here])

end Greta
