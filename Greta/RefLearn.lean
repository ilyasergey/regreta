/-
**The learner Greta actually ships**, and the analogue of Lemma B.2 for it.

`Greta.Learn` implements Algorithm 3.1 *as printed*: the non-conflicting symbols `S` of a
re-layered order are copied to every newly created order.  `Learner.update_op_per_ord_amb_symsls`
(`ocaml-ref/.greta/lib/learner.ml:40`) does something else:

* it pushes the orders above `o` by `size` rather than by `size - 1` whenever `S` is
  non-empty, so that one extra order is made;
* each new order `o + i` receives *only* the `i`-th conflicting symbols, not `S ∪ ithSymbols`;
* `S` is placed once, below all of them, at order `o + size`;
* `S` is recorded in `special_loop_symbols` together with the order `o` it came from, and
  `Learner.learn_ta` then gives each such symbol a transition whose right-hand side points
  back at `e_o`.

The published algorithm achieves by replication what the shipped one achieves by a
back-edge, so the conclusion of Lemma B.2 changes from "the symbol is *present at* the
original order in `O_p`" to "the symbol is *reachable from* the original order in the
generated automaton"; see `docs/reference-defects.md`, D7.  That restatement is
`refGenTA_specReach` below.

### Where the OCaml leaves a choice implicit

1. `Hashtbl.remove op_tbl curr_ord` removes only the most recent binding of `curr_ord`.
   `OrderMap.removeOrder` removes all of them.  The two agree on every run of the
   algorithm: the orders are visited strictly downwards and each step only ever adds keys
   `≥` the order it is visiting, so `curr_ord` has exactly one binding when it is removed.
2. `find_nth_ambs_from_symlsls` does not remove duplicates, and neither does the `for`
   loop that inserts its result, so `refRelayerOrder` does not `dedup` either — unlike
   `relayerOrder`, which has to, because there the conflicting symbols are inserted
   alongside `S`.
3. `specs` is shifted by `push_n` unconditionally, not only for the entries recorded at an
   order above the one being visited.  Since the orders are visited downwards, every entry
   already recorded does sit above `curr_ord`, so the unconditional shift is the same
   thing; it is transcribed as written.
4. `List.assoc` in `learn_ta` takes the *first* binding of a symbol, and new bindings are
   consed on the front, so the most recently recorded order wins.  `List.lookup` has the
   same behaviour, and `refOaFill` uses it.
5. `update_oa_sym_prod_for_index` rewrites position `ind` of an already-populated
   right-hand side to `increment_suffix lhs_st`, i.e. to the level *of the transition*
   plus one, overwriting the back-edge at that position.  `refOaFill` therefore tests the
   associativity restriction first and consults the special-loop table only otherwise.  No
   run can tell the two orders apart: a symbol of `S` takes part in no conflict, so it
   carries no associativity restriction.
6. The guard `size = 0` is not in the OCaml, where `push_n` would become `-1`;
   `Learner.learn_op` filters those groups out before the fold.  `relayerOrder` has the
   same guard.
7. `learn_ta` builds its states from the keys of the hash table and stops the ε-chain at
   `Hashtbl.length op_learned - 1`, a count of *bindings*.  `refGenTA` keeps `genTA`'s
   `op.maxOrder`, the largest order.  The two agree whenever every order from `0` to the
   largest carries exactly one binding, which is what the loop produces.

### What is assumed

The back-edge half of the restated lemma needs one fact about the loop — that a recorded
order never sits *below* the order its symbol ends at — and that fact needs the discipline
`Learner.learn_op` runs the loop under: orders visited strictly downwards, and conflict
groups drawn from the order they are attached to.  That is `Disciplined` below, a hypothesis
of `refLearnOaOp_specDominated`.  It is decidable and `lake exe greta selftest` checks it
on the paper's running example; `decide` cannot close it inside the kernel, because
`List.mergeSort`, which `sort_assoc_desc` becomes, is defined by well-founded recursion.
Proving it of `toMapOf (baseOrder g)` for every grammar is left open.
-/
import Greta.LearnSpec

namespace Greta

/--
`special_loop_symbols`: a non-conflicting symbol together with the order its back-edge
points at — the order it sat at before the re-layering that moved it.
-/
abbrev SpecMap := List (Sym × Nat)

/-! ### Algorithm 3.1 as shipped -/

/-- `max_len`: the size of the largest conflict group at the order being re-layered. -/
def relayerSize (grp : List (List Sym)) : Nat := grp.foldl (fun a gl => max a gl.length) 0

/-- `temp_others`, the `S` of Algorithm 3.1: the symbols of the order that no group holds. -/
def relayerOthers (m : OrderMap) (o : Nat) (grp : List (List Sym)) : List Sym :=
  (m.ofOrder o).filter fun s => !grp.flatten.contains s

/-- `push_n`: one order more than the published algorithm pushes, unless `S` is empty. -/
def relayerPush (m : OrderMap) (o : Nat) (grp : List (List Sym)) : Nat :=
  if (relayerOthers m o grp).isEmpty then relayerSize grp - 1 else relayerSize grp

/-- The `i`-th conflicting symbols, `find_nth_ambs_from_symlsls i`. -/
def nthAmbs (grp : List (List Sym)) (i : Nat) : List Sym := grp.filterMap fun gl => gl[i]?

/--
The order map one iteration of the loop of `update_op_per_ord_amb_symsls` produces: the
`i`-th conflicting symbols alone at order `o + i`, and `S` once at order `o + size`.
-/
def refRelayerMap (m : OrderMap) (o : Nat) (grp : List (List Sym)) : OrderMap :=
  if relayerSize grp = 0 then m else
  let m1 := (List.range (relayerSize grp)).foldl
      (fun acc i => acc ++ OrderMap.withOrder (nthAmbs grp i) (o + i))
      ((m.removeOrder o).pushN (o + 1) (relayerPush m o grp))
  if (relayerOthers m o grp).isEmpty then m1
  else m1 ++ OrderMap.withOrder (relayerOthers m o grp) (o + relayerSize grp)

/--
The `special_loop_symbols` the same iteration produces: every symbol of `S` remembers the
order `o` it is leaving, and every entry recorded earlier is pushed by `push_n`.
-/
def refRelayerSpecs (m : OrderMap) (specs : SpecMap) (o : Nat) (grp : List (List Sym)) :
    SpecMap :=
  if relayerSize grp = 0 then specs else
  (relayerOthers m o grp).map (fun s => (s, o))
    ++ specs.map (fun p => (p.1, p.2 + relayerPush m o grp))

/--
One iteration of the second loop of Algorithm 3.1 *as shipped*
(`Learner.update_op_per_ord_amb_symsls`).  Compare `relayerOrder`, which is the same loop
as printed in the paper.
-/
def refRelayerOrder (m : OrderMap) (specs : SpecMap) (o : Nat) (grp : List (List Sym)) :
    OrderMap × SpecMap :=
  (refRelayerMap m o grp, refRelayerSpecs m specs o grp)

/-- The conflict groups of `M_to`, in the order the shipped loop visits them. -/
def refGroups (mto : ToMap) : List (Nat × List (List Sym)) :=
  -- descending in the order, as `sort_assoc_desc` leaves it
  (mto.filter fun p => !p.2.isEmpty).mergeSort (fun a b => b.1 ≤ a.1)

/--
**Algorithm 3.1 as shipped** (`Learner.learn_op`).  Returns the associativity restrictions
`O_a`, the precedence order `O_p`, and the `special_loop_symbols` that `learn_ta` turns
into back-edges.
-/
def refLearnOaOp (g : CFG) (neg : List TreeExample) (mto : ToMap)
    (excludeTrivial : Bool := true) : Oa × OrderMap × SpecMap :=
  let obp := g.baseOrder excludeTrivial
  let oa : Oa := neg.filterMap fun e => if e.isAssoc then some (e.top, e.idx) else none
  let st := (refGroups mto).foldl (fun st og => refRelayerOrder st.1 st.2 og.1 og.2)
              (obp, ([] : SpecMap))
  (oa, st.1.normalise, st.2)

/-!
### Reading orders off the pieces an iteration is built from

`OrderMap` is a raw association list, so every re-layering step is an `++` of a `pushN`, a
`removeOrder` and a few `withOrder`s.  `Greta.LearnSpec` has the membership lemmas for
those pieces; all that is missing is that `ofOrder` and `ordersOf` are two readings of the
same table.
-/

theorem OrderMap.mem_ordersOf_iff_mem_ofOrder {m : OrderMap} {o : Nat} {s : Sym} :
    o ∈ m.ordersOf s ↔ s ∈ m.ofOrder o := by
  rw [OrderMap.mem_ordersOf, OrderMap.mem_ofOrder]
  constructor
  · rintro ⟨ss, hp, hs⟩; exact ⟨(o, ss), hp, rfl, hs⟩
  · rintro ⟨q, hq, rfl, hs⟩; exact ⟨q.2, by cases q; exact hq, hs⟩

/-! ### What one iteration does to the orders of a symbol -/

/-- The orders the `for` loop of `update_op_per_ord_amb_symsls` adds. -/
theorem ordersOf_foldl_nthAmbs (m₀ : OrderMap) (o : Nat) (grp : List (List Sym)) :
    ∀ (k : Nat) {s : Sym} {l : Nat},
      l ∈ ((List.range k).foldl
            (fun acc i => acc ++ OrderMap.withOrder (nthAmbs grp i) (o + i)) m₀).ordersOf s ↔
        l ∈ m₀.ordersOf s ∨ ∃ i, i < k ∧ s ∈ nthAmbs grp i ∧ l = o + i := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro s l
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, OrderMap.ordersOf_append, ih,
        OrderMap.ordersOf_withOrder]
      constructor
      · rintro ((h | ⟨i, hi, hs, rfl⟩) | ⟨rfl, hs⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, by omega, hs, rfl⟩
        · exact Or.inr ⟨k, by omega, hs, rfl⟩
      · rintro (h | ⟨i, hi, hs, rfl⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_or_ge i k with hik | hik
          · exact Or.inl (Or.inr ⟨i, hik, hs, rfl⟩)
          · have : i = k := by omega
            subst this
            exact Or.inr ⟨rfl, hs⟩

/--
The orders at which a symbol sits after one iteration: pushed up from where it was, or at
`o + i` if it is the `i`-th symbol of a conflict group, or at `o + size` if it is one of
the non-conflicting symbols `S`.
-/
theorem ordersOf_refRelayerMap {m : OrderMap} {o : Nat} {grp : List (List Sym)} {s : Sym}
    {l : Nat} (hsize : relayerSize grp ≠ 0) :
    l ∈ (refRelayerMap m o grp).ordersOf s ↔
      (∃ l', l' ∈ m.ordersOf s ∧ l' ≠ o ∧ l = shift (o + 1) (relayerPush m o grp) l')
        ∨ (∃ i, i < relayerSize grp ∧ s ∈ nthAmbs grp i ∧ l = o + i)
        ∨ (s ∈ relayerOthers m o grp ∧ l = o + relayerSize grp) := by
  rw [refRelayerMap, if_neg hsize]
  have base : ∀ {l : Nat},
      l ∈ (((List.range (relayerSize grp)).foldl
            (fun acc i => acc ++ OrderMap.withOrder (nthAmbs grp i) (o + i))
            ((m.removeOrder o).pushN (o + 1) (relayerPush m o grp))).ordersOf s) ↔
        (∃ l', l' ∈ m.ordersOf s ∧ l' ≠ o ∧ l = shift (o + 1) (relayerPush m o grp) l')
          ∨ (∃ i, i < relayerSize grp ∧ s ∈ nthAmbs grp i ∧ l = o + i) := by
    intro l
    rw [ordersOf_foldl_nthAmbs, OrderMap.ordersOf_pushN]
    simp only [OrderMap.ordersOf_removeOrder]
    constructor
    · rintro (⟨l', ⟨hl', hne⟩, rfl⟩ | h)
      · exact Or.inl ⟨l', hl', hne, rfl⟩
      · exact Or.inr h
    · rintro (⟨l', hl', hne, rfl⟩ | h)
      · exact Or.inl ⟨l', ⟨hl', hne⟩, rfl⟩
      · exact Or.inr h
  split
  · next hS =>
      rw [base]
      rw [List.isEmpty_iff] at hS
      simp [hS]
  · rw [OrderMap.ordersOf_append, base, OrderMap.ordersOf_withOrder, or_assoc]
    exact or_congr_right (or_congr_right (by constructor <;> (rintro ⟨a, b⟩; exact ⟨b, a⟩)))

/-!
### Lemma B.2, the relative-order half

Re-layering never inverts the relative order of two symbols that no example relates.
`shift_mono` is the arithmetic core; what has to be added is the one order the shipped
algorithm treats specially, the order `o` being re-layered, whose non-conflicting symbols
all move together to `o + size`.
-/

/-- Where one iteration sends the order of a symbol that takes part in no conflict group. -/
def relayerShift (m : OrderMap) (o : Nat) (grp : List (List Sym)) (l : Nat) : Nat :=
  if relayerSize grp = 0 then l
  else if l = o then o + relayerSize grp
  else shift (o + 1) (relayerPush m o grp) l

/-- A symbol in no conflict group keeps an order, namely the image of its old one. -/
theorem relayerShift_mem {m : OrderMap} {o : Nat} {grp : List (List Sym)} {s : Sym} {l : Nat}
    (hs : s ∉ grp.flatten) (hl : l ∈ m.ordersOf s) :
    relayerShift m o grp l ∈ (refRelayerMap m o grp).ordersOf s := by
  unfold relayerShift
  split
  · next h => rw [refRelayerMap, if_pos h]; exact hl
  · next hsize =>
      rw [ordersOf_refRelayerMap hsize]
      split
      · next hlo =>
          subst hlo
          refine Or.inr (Or.inr ⟨?_, rfl⟩)
          rw [relayerOthers, List.mem_filter]
          exact ⟨OrderMap.mem_ordersOf_iff_mem_ofOrder.mp hl, by simpa using hs⟩
      · next hlo => exact Or.inl ⟨l, hl, hlo, rfl⟩

/-- That image is monotone: two orders are never swapped. -/
theorem relayerShift_mono (m : OrderMap) (o : Nat) (grp : List (List Sym)) {i j : Nat}
    (hij : i ≤ j) : relayerShift m o grp i ≤ relayerShift m o grp j := by
  unfold relayerShift
  split
  · exact hij
  · next hsize =>
      have hs1 : 1 ≤ relayerSize grp := by omega
      have hpush : relayerPush m o grp = relayerSize grp ∨
          relayerPush m o grp = relayerSize grp - 1 := by
        unfold relayerPush; split
        · exact Or.inr rfl
        · exact Or.inl rfl
      split <;> split <;> rename_i hi hj
      · omega
      · -- i = o, j ≠ o, so o < j
        subst hi
        have : i + 1 ≤ j := by omega
        unfold shift
        rw [if_pos this]
        omega
      · -- j = o, i ≠ o, so i < o
        subst hj
        unfold shift
        rw [if_neg (by omega)]
        omega
      · exact shift_mono _ _ hij

/--
**Lemma B.2, relative-order half, for one iteration.**  If neither `x` nor `y` takes part
in a conflict group of the order being re-layered, and `x` sat at or above `y`, then it
still does.
-/
theorem refRelayerMap_no_inversion {m : OrderMap} {o : Nat} {grp : List (List Sym)}
    {x y : Sym} {i j : Nat} (hx : x ∉ grp.flatten) (hy : y ∉ grp.flatten)
    (hi : i ∈ m.ordersOf x) (hj : j ∈ m.ordersOf y) (hij : i ≤ j) :
    relayerShift m o grp i ∈ (refRelayerMap m o grp).ordersOf x ∧
      relayerShift m o grp j ∈ (refRelayerMap m o grp).ordersOf y ∧
      relayerShift m o grp i ≤ relayerShift m o grp j :=
  ⟨relayerShift_mem hx hi, relayerShift_mem hy hj, relayerShift_mono m o grp hij⟩

/-! ### The whole second loop -/

/-- The order map the second loop of Algorithm 3.1 produces, forgetting the spec map. -/
def refRelayerFold : OrderMap → List (Nat × List (List Sym)) → OrderMap
  | m, []          => m
  | m, og :: rest  => refRelayerFold (refRelayerMap m og.1 og.2) rest

theorem foldl_refRelayerOrder_fst :
    ∀ (gs : List (Nat × List (List Sym))) (m : OrderMap) (specs : SpecMap),
      (gs.foldl (fun st og => refRelayerOrder st.1 st.2 og.1 og.2) (m, specs)).1 =
        refRelayerFold m gs
  | [],       _, _ => rfl
  | _ :: gs, _, _ => foldl_refRelayerOrder_fst gs _ _

/--
**Lemma B.2, relative-order half.**  If no conflict group mentions `x` or `y` — which is
what "no example relates them" comes to, since `M_to` is built from the examples — then
the whole of the second loop of Algorithm 3.1 leaves their relative order alone.
-/
theorem refRelayerFold_no_inversion (gs : List (Nat × List (List Sym))) :
    ∀ {m : OrderMap} {x y : Sym} {i j : Nat},
      (∀ og ∈ gs, x ∉ og.2.flatten) → (∀ og ∈ gs, y ∉ og.2.flatten) →
      i ∈ m.ordersOf x → j ∈ m.ordersOf y → i ≤ j →
      ∃ i' ∈ (refRelayerFold m gs).ordersOf x,
        ∃ j' ∈ (refRelayerFold m gs).ordersOf y, i' ≤ j' := by
  induction gs with
  | nil => intro m x y i j _ _ hi hj hij; exact ⟨i, hi, j, hj, hij⟩
  | cons og gs ih =>
      intro m x y i j hx hy hi hj hij
      exact ih (fun p hp => hx p (List.mem_cons_of_mem _ hp))
        (fun p hp => hy p (List.mem_cons_of_mem _ hp))
        (relayerShift_mem (hx og List.mem_cons_self) hi)
        (relayerShift_mem (hy og List.mem_cons_self) hj)
        (relayerShift_mono _ _ _ hij)

/-!
### Lemma B.2, the back-edge half: the recorded order is never below the symbol

The published algorithm leaves a non-conflicting symbol *at* the order it was found at.
The shipped one moves it down to `o + size` and remembers `o`.  Everything the restated
lemma needs from the learner is that the remembered order is never *below* the order the
symbol ends up at, since that is what makes the ε-chain run from the remembered order to
the symbol's transition.
-/

/-- Every recorded back-edge points at an order at or above the symbol's own. -/
def SpecDominated (m : OrderMap) (specs : SpecMap) : Prop :=
  ∀ s d, (s, d) ∈ specs → ∀ l ∈ m.ordersOf s, d ≤ l

/--
The auxiliary invariant of the loop: everything already recorded, and every order its
symbols occupy, sits strictly above the order about to be visited.  This is what visiting
the orders downwards buys.
-/
def SpecAbove (o : Nat) (m : OrderMap) (specs : SpecMap) : Prop :=
  ∀ s d, (s, d) ∈ specs → o < d ∧ ∀ l ∈ m.ordersOf s, o < l

theorem mem_nthAmbs_flatten {grp : List (List Sym)} {i : Nat} {s : Sym}
    (h : s ∈ nthAmbs grp i) : s ∈ grp.flatten := by
  simp only [nthAmbs, List.mem_filterMap] at h
  obtain ⟨gl, hgl, hs⟩ := h
  exact List.mem_flatten.mpr ⟨gl, hgl, List.mem_of_getElem? hs⟩

theorem relayerOthers_subset {m : OrderMap} {o : Nat} {grp : List (List Sym)} {s : Sym}
    (h : s ∈ relayerOthers m o grp) : s ∈ m.ofOrder o :=
  (List.mem_filter.mp h).1

/--
The case analysis both invariants need: where a symbol can sit after one iteration, given
that the order being re-layered is a clean layer and that the conflict groups really sit
at it.
-/
private theorem ordersOf_step_cases {m : OrderMap} {o : Nat} {grp : List (List Sym)}
    {s : Sym} {l : Nat} (hsize : relayerSize grp ≠ 0)
    (hamb : grp.flatten ⊆ m.ofOrder o)
    (hlay : ∀ s ∈ m.ofOrder o, ∀ l ∈ m.ordersOf s, l = o)
    (hl : l ∈ (refRelayerMap m o grp).ordersOf s) :
    (∃ l', l' ∈ m.ordersOf s ∧ o < l' ∧ l = l' + relayerPush m o grp ∧ s ∉ grp.flatten ∧
        s ∉ relayerOthers m o grp)
      ∨ (∃ l', l' ∈ m.ordersOf s ∧ l' < o ∧ l = l' ∧ s ∉ grp.flatten ∧
          s ∉ relayerOthers m o grp)
      ∨ (o ≤ l ∧ s ∈ m.ofOrder o) := by
  rcases (ordersOf_refRelayerMap hsize).mp hl with ⟨l', hl', hne, rfl⟩ | ⟨i, hi, hs, rfl⟩ | ⟨hs, rfl⟩
  · -- pushed up from an old order; `s` cannot have been at `o`, which is a clean layer
    have hin : s ∉ m.ofOrder o := fun hin => hne (hlay s hin l' hl')
    · have hnf : s ∉ grp.flatten := fun h => hin (hamb h)
      have hno : s ∉ relayerOthers m o grp := fun h => hin (relayerOthers_subset h)
      rcases Nat.lt_or_ge l' o with hlt | hge
      · exact Or.inr (Or.inl ⟨l', hl', hlt, by unfold shift; rw [if_neg (by omega)], hnf, hno⟩)
      · exact Or.inl ⟨l', hl', by omega, by unfold shift; rw [if_pos (by omega)], hnf, hno⟩
  · exact Or.inr (Or.inr ⟨Nat.le_add_right _ _, hamb (mem_nthAmbs_flatten hs)⟩)
  · exact Or.inr (Or.inr ⟨Nat.le_add_right _ _, relayerOthers_subset hs⟩)

/-- One iteration keeps every back-edge pointing at or above its symbol. -/
theorem refRelayerSpecs_dominated {m : OrderMap} {specs : SpecMap} {o : Nat}
    {grp : List (List Sym)}
    (hamb : grp.flatten ⊆ m.ofOrder o)
    (hlay : ∀ s ∈ m.ofOrder o, ∀ l ∈ m.ordersOf s, l = o)
    (habove : SpecAbove o m specs) (hdom : SpecDominated m specs) :
    SpecDominated (refRelayerMap m o grp) (refRelayerSpecs m specs o grp) := by
  intro s d hd l hl
  unfold refRelayerSpecs at hd
  split at hd
  · next h => rw [refRelayerMap, if_pos h] at hl; exact hdom s d hd l hl
  · next hsize =>
      rcases List.mem_append.mp hd with hd | hd
      · -- a newly recorded symbol: it came from order `o`, which is all it had
        simp only [List.mem_map, Prod.mk.injEq] at hd
        obtain ⟨t, ht, rfl, rfl⟩ := hd
        rcases ordersOf_step_cases hsize hamb hlay hl with ⟨l', hl', hlt, -, -, hno⟩ | ⟨l', hl', -, -, -, hno⟩ | ⟨h, -⟩
        · exact absurd ht hno
        · exact absurd ht hno
        · exact h
      · -- an entry recorded earlier, pushed up together with its symbol
        simp only [List.mem_map, Prod.mk.injEq] at hd
        obtain ⟨⟨t, e⟩, hte, rfl, rfl⟩ := hd
        obtain ⟨hlt, hall⟩ := habove t e hte
        rcases ordersOf_step_cases hsize hamb hlay hl with ⟨l', hl', -, rfl, -, -⟩ | ⟨l', hl', hlt', -, -, -⟩ | ⟨-, hin⟩
        · exact Nat.add_le_add_right (hdom t e hte l' hl') _
        · exact absurd (hall l' hl') (by omega)
        · exact absurd (hall o (OrderMap.mem_ordersOf_iff_mem_ofOrder.mpr hin)) (by omega)

/-- And it re-establishes the auxiliary invariant for every order still to be visited. -/
theorem refRelayerSpecs_above {m : OrderMap} {specs : SpecMap} {o o' : Nat}
    {grp : List (List Sym)} (ho : o' < o)
    (hamb : grp.flatten ⊆ m.ofOrder o)
    (hlay : ∀ s ∈ m.ofOrder o, ∀ l ∈ m.ordersOf s, l = o)
    (habove : SpecAbove o m specs) :
    SpecAbove o' (refRelayerMap m o grp) (refRelayerSpecs m specs o grp) := by
  intro s d hd
  unfold refRelayerSpecs at hd
  split at hd
  · next h =>
      rw [refRelayerMap, if_pos h]
      obtain ⟨h1, h2⟩ := habove s d hd
      exact ⟨by omega, fun l hl => by have := h2 l hl; omega⟩
  · next hsize =>
      rcases List.mem_append.mp hd with hd | hd
      · simp only [List.mem_map, Prod.mk.injEq] at hd
        obtain ⟨t, ht, rfl, rfl⟩ := hd
        refine ⟨ho, fun l hl => ?_⟩
        rcases ordersOf_step_cases hsize hamb hlay hl with ⟨l', hl', -, -, -, hno⟩ | ⟨l', hl', -, -, -, hno⟩ | ⟨h, -⟩
        · exact absurd ht hno
        · exact absurd ht hno
        · omega
      · simp only [List.mem_map, Prod.mk.injEq] at hd
        obtain ⟨⟨t, e⟩, hte, rfl, rfl⟩ := hd
        obtain ⟨hlt, hall⟩ := habove t e hte
        refine ⟨by omega, fun l hl => ?_⟩
        rcases ordersOf_step_cases hsize hamb hlay hl with ⟨l', hl', hlt', rfl, -, -⟩ | ⟨l', hl', hlt', -, -, -⟩ | ⟨-, hin⟩
        · omega
        · exact absurd (hall l' hl') (by omega)
        · exact absurd (hall o (OrderMap.mem_ordersOf_iff_mem_ofOrder.mpr hin)) (by omega)

/-! ### The whole loop -/

/-- The `special_loop_symbols` the second loop of Algorithm 3.1 produces. -/
def refRelayerSpecsFold : OrderMap → SpecMap → List (Nat × List (List Sym)) → SpecMap
  | _, specs, []         => specs
  | m, specs, og :: rest =>
      refRelayerSpecsFold (refRelayerMap m og.1 og.2) (refRelayerSpecs m specs og.1 og.2) rest

theorem foldl_refRelayerOrder_snd :
    ∀ (gs : List (Nat × List (List Sym))) (m : OrderMap) (specs : SpecMap),
      (gs.foldl (fun st og => refRelayerOrder st.1 st.2 og.1 og.2) (m, specs)).2 =
        refRelayerSpecsFold m specs gs
  | [],       _, _ => rfl
  | _ :: gs, _, _ => foldl_refRelayerOrder_snd gs _ _

/--
The discipline `Learner.learn_op` runs its loop under: the orders are visited strictly
downwards (`sort_assoc_desc`), the conflict groups attached to an order really are symbols
of that order (`M_to` is read off `O_bp`), and each visited order is a clean layer — no
symbol of it also sits somewhere else.  All three are finite, checkable conditions on the
input, and `Disciplined` is decidable; `Greta.Test` checks it on the paper's running
example.
-/
def Disciplined : OrderMap → List (Nat × List (List Sym)) → Prop
  | _, []          => True
  | m, og :: rest  =>
      og.2.flatten ⊆ m.ofOrder og.1
        ∧ (∀ s ∈ m.ofOrder og.1, ∀ l ∈ m.ordersOf s, l = og.1)
        ∧ (∀ p ∈ rest, p.1 < og.1)
        ∧ Disciplined (refRelayerMap m og.1 og.2) rest

def decDisciplined : ∀ (m : OrderMap) (gs : List (Nat × List (List Sym))),
    Decidable (Disciplined m gs)
  | _, []         => .isTrue trivial
  | m, og :: rest =>
      have : Decidable (Disciplined (refRelayerMap m og.1 og.2) rest) :=
        decDisciplined (refRelayerMap m og.1 og.2) rest
      decidable_of_iff
        ((∀ s ∈ og.2.flatten, s ∈ m.ofOrder og.1)
          ∧ (∀ s ∈ m.ofOrder og.1, ∀ l ∈ m.ordersOf s, l = og.1)
          ∧ (∀ p ∈ rest, p.1 < og.1)
          ∧ Disciplined (refRelayerMap m og.1 og.2) rest) Iff.rfl

instance (m : OrderMap) (gs : List (Nat × List (List Sym))) : Decidable (Disciplined m gs) :=
  decDisciplined m gs

/--
**The invariant of the shipped loop.**  Run under the discipline of `Learner.learn_op`,
the second loop of Algorithm 3.1 never records a back-edge that points *below* the order
its symbol ends up at.
-/
theorem foldl_refRelayer_specDominated :
    ∀ (gs : List (Nat × List (List Sym))) (m : OrderMap) (specs : SpecMap),
      Disciplined m gs → SpecDominated m specs → (∀ og ∈ gs, SpecAbove og.1 m specs) →
      SpecDominated (refRelayerFold m gs) (refRelayerSpecsFold m specs gs)
  | [],          _, _,     _,     hdom, _      => hdom
  | og :: rest,  m, specs, hdisc, hdom, habove => by
      obtain ⟨hamb, hlay, hlt, hrest⟩ := hdisc
      refine foldl_refRelayer_specDominated rest _ _ hrest
        (refRelayerSpecs_dominated hamb hlay (habove og List.mem_cons_self) hdom) ?_
      intro og' hog'
      exact refRelayerSpecs_above (hlt og' hog') hamb hlay (habove og List.mem_cons_self)

/--
**Algorithm 3.1 as shipped records only downward back-edges.**  `refLearnOaOp` returns a
`special_loop_symbols` table in which every symbol sits at or below the order its
back-edge points at.
-/
theorem refLearnOaOp_snd_fst (g : CFG) (neg : List TreeExample) (mto : ToMap) (b : Bool) :
    (refLearnOaOp g neg mto b).2.1 = (refRelayerFold (g.baseOrder b) (refGroups mto)).normalise := by
  simp only [refLearnOaOp, foldl_refRelayerOrder_fst]

theorem refLearnOaOp_snd_snd (g : CFG) (neg : List TreeExample) (mto : ToMap) (b : Bool) :
    (refLearnOaOp g neg mto b).2.2 = refRelayerSpecsFold (g.baseOrder b) [] (refGroups mto) := by
  simp only [refLearnOaOp, foldl_refRelayerOrder_snd]

/--
**Algorithm 3.1 as shipped records only downward back-edges.**  `refLearnOaOp` returns a
`special_loop_symbols` table in which every symbol sits at or below the order its
back-edge points at.  This is what makes the restated Lemma B.2 below go through.
-/
theorem refLearnOaOp_specDominated (g : CFG) (neg : List TreeExample) (mto : ToMap)
    (b : Bool) (hdisc : Disciplined (g.baseOrder b) (refGroups mto)) :
    SpecDominated (refLearnOaOp g neg mto b).2.1 (refLearnOaOp g neg mto b).2.2 := by
  intro s d hd l hl
  rw [refLearnOaOp_snd_snd] at hd
  rw [refLearnOaOp_snd_fst, OrderMap.ordersOf_normalise] at hl
  exact foldl_refRelayer_specDominated _ _ _ hdisc (by intro _ _ h; exact absurd h (by simp))
    (by intro _ _ _ _ h; exact absurd h (by simp)) s d hd l hl

/-! ### Algorithm 3.2 with the back-edges of `learn_ta` -/

/--
The state a level-`i` transition for `s` puts at right-hand-side position `k`, as
`Learner.learn_ta` builds it: one level deeper at every position `O_a` forbids, and
otherwise the order recorded for `s` in `special_loop_symbols` — the *original* order of a
non-conflicting symbol — falling back to `i` for every other symbol.
-/
def refOaFill (oa : Oa) (specs : SpecMap) (s : Sym) (i k : Nat) : GState :=
  if (oa.positionsOf s).contains k then .lvl (i + 1)
  else .lvl ((specs.lookup s).getD i)

/-- Transitions for the non-trivial symbols, with the back-edges of `learn_ta`. -/
def refNonTrivTrans (g : CFG) (oa : Oa) (specs : SpecMap) (op : OrderMap)
    (tn : List Nonterminal) : List (Transition GState) :=
  op.flatMap fun oss =>
    oss.2.filterMap fun s => deltaGen g tn (.lvl oss.1) (refOaFill oa specs s oss.1) s

/--
**Algorithm 3.2 against the shipped learner.**  `genTA` with `refNonTrivTrans` in place of
`nonTrivTrans`; everything else — the trivial symbols, the ε-chain and the cycle
transitions — is unchanged, because `learn_ta` treats them the same way.
-/
def refGenTA (g : CFG) (oa : Oa) (specs : SpecMap) (op : OrderMap)
    (excludeTrivial : Bool := true) : TA GState where
  states    := ((List.range (op.maxOrder + 1)).map GState.lvl)
                 ++ (trivNts g excludeTrivial).map GState.triv
  alphabet  := (op.symbols ++ trivSyms g excludeTrivial ++ [epsSym]).dedup
  terminals := g.terms
  finals    := [.lvl 0]
  trans     := refNonTrivTrans g oa specs op (trivNts g excludeTrivial)
                 ++ trivialTrans g (trivSyms g excludeTrivial)
                 ++ epsChain op.maxOrder
                 ++ cycleTrans g (g.baseOrder excludeTrivial) op (trivNts g excludeTrivial)

@[simp] theorem refGenTA_finals (g : CFG) (oa : Oa) (specs : SpecMap) (op : OrderMap)
    (b : Bool) : (refGenTA g oa specs op b).finals = [.lvl 0] := rfl

@[simp] theorem refGenTA_trans (g : CFG) (oa : Oa) (specs : SpecMap) (op : OrderMap)
    (b : Bool) : (refGenTA g oa specs op b).trans =
      refNonTrivTrans g oa specs op (trivNts g b) ++ trivialTrans g (trivSyms g b)
        ++ epsChain op.maxOrder ++ cycleTrans g (g.baseOrder b) op (trivNts g b) := rfl

/-! ### The shape of the automaton the shipped learner produces -/

theorem mem_refNonTrivTrans {g : CFG} {oa : Oa} {specs : SpecMap} {op : OrderMap}
    {tn : List Nonterminal} {tr : Transition GState} :
    tr ∈ refNonTrivTrans g oa specs op tn ↔
      ∃ i ss, (i, ss) ∈ op ∧ ∃ s ∈ ss, ∃ p, g.prodOfSym s = some p ∧
        tr = ⟨.lvl i, s, fillRhs tn p.2 (refOaFill oa specs s i)⟩ := by
  simp only [refNonTrivTrans, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨oss, hoss, s, hs, hd⟩
    obtain ⟨p, hp, rfl⟩ := mem_deltaGen.mp hd
    exact ⟨oss.1, oss.2, hoss, s, hs, p, hp, rfl⟩
  · rintro ⟨i, ss, hp, s, hs, p, hpp, rfl⟩
    exact ⟨(i, ss), hp, s, hs, mem_deltaGen.mpr ⟨p, hpp, rfl⟩⟩

/-- The ε-chain of the shipped `A_r`, exactly as in `genTA`: `learn_ta` adds the same one. -/
theorem refGenTA_eps_mem {g : CFG} {oa : Oa} {specs : SpecMap} {op : OrderMap} {b : Bool}
    {i : Nat} (h : i < op.maxOrder) :
    (⟨.lvl i, epsSym, [.state (.lvl (i + 1))]⟩ : Transition GState)
      ∈ (refGenTA g oa specs op b).trans := by
  rw [refGenTA_trans]
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  exact List.mem_map_of_mem (List.mem_range.mpr h)

/--
The back-edges change no ε-transition: the ε-graph of the shipped `A_r` is the same chain
`e_0 ←ε e_1 ←ε ⋯ ←ε e_m` as `genTA`'s.
-/
theorem refGenTA_epsEdges_iff {g : CFG} {oa : Oa} {specs : SpecMap} {op : OrderMap}
    {b : Bool} (hog : OrderOfGrammar g op) {x y : GState} :
    (x, y) ∈ (refGenTA g oa specs op b).epsEdges ↔
      ∃ i < op.maxOrder, x = .lvl (i + 1) ∧ y = .lvl i := by
  rw [mem_epsEdges]
  constructor
  · rintro ⟨tr, htr, hsym, hrhs, htgt⟩
    rw [refGenTA_trans] at htr
    rcases List.mem_append.mp htr with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · obtain ⟨i, ss, hp, s, hs, p, _, rfl⟩ := mem_refNonTrivTrans.mp h
          exact absurd hsym (hog.sym_ne_eps (OrderMap.mem_symbols.mpr ⟨(i, ss), hp, hs⟩))
        · obtain ⟨s, hs, p, _, rfl⟩ := mem_trivialTrans.mp h
          exact absurd hsym (trivSyms_ne_eps hs)
      · obtain ⟨i, hi, rfl⟩ := mem_epsChain.mp h
        simp only [List.cons.injEq, Beta.state.injEq] at hrhs
        exact ⟨i, hi, hrhs.1.symm, htgt.symm ▸ rfl⟩
    · simp only [cycleTrans, List.mem_filterMap] at h
      obtain ⟨pr, hpr, hd⟩ := h
      obtain ⟨p, _, rfl⟩ := mem_deltaGen.mp hd
      exact absurd hsym (highToLow_sym_ne_eps hpr)
  · rintro ⟨i, hi, rfl, rfl⟩
    exact ⟨_, refGenTA_eps_mem hi, rfl, rfl, rfl⟩

private theorem refEpsReach_add {g : CFG} {oa : Oa} {specs : SpecMap} {op : OrderMap}
    {b : Bool} :
    ∀ (d l : Nat), l + d ≤ op.maxOrder →
      EpsReach (refGenTA g oa specs op b) (.lvl (l + d)) (.lvl l)
  | 0,     _, _ => .refl _
  | d + 1, l, h =>
      (EpsReach.step
        (mem_epsEdges.mpr ⟨_, refGenTA_eps_mem (i := l + d) (by omega), rfl, rfl, rfl⟩)
        (.refl _)).trans (refEpsReach_add d l (by omega))

/-- The ε-chain promotes any level to any shallower one. -/
theorem refEpsReach_of_le {g : CFG} {oa : Oa} {specs : SpecMap} {op : OrderMap} {b : Bool}
    {l j : Nat} (hlj : l ≤ j) (hj : j ≤ op.maxOrder) :
    EpsReach (refGenTA g oa specs op b) (.lvl j) (.lvl l) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = l + d := ⟨j - l, by omega⟩
  exact refEpsReach_add d l hj

/-- And nothing else: ε-reachability between ordered states is still `≤` on levels. -/
theorem refEpsReach_lvl {g : CFG} {oa : Oa} {specs : SpecMap} {op : OrderMap} {b : Bool}
    (hog : OrderOfGrammar g op) {i j : Nat}
    (h : EpsReach (refGenTA g oa specs op b) (.lvl j) (.lvl i)) : i ≤ j := by
  generalize hx : (GState.lvl j) = x at h
  generalize hy : (GState.lvl i) = y at h
  induction h generalizing i j with
  | refl => subst hx; simp only [GState.lvl.injEq] at hy; omega
  | @step x z y he _ ih =>
      obtain ⟨k, hk, hxz, rfl⟩ := (refGenTA_epsEdges_iff hog).mp he
      subst hx
      simp only [GState.lvl.injEq] at hxz
      exact Nat.le_trans (Nat.le_of_lt_succ (Nat.lt_succ_of_le (ih rfl hy))) (by omega)

/-!
### The restated Lemma B.2

The published Lemma B.2 concludes that a non-conflicting symbol of an order is *present
at* that order in `O_p`.  The shipped algorithm moves it below the conflicting symbols and
compensates with a back-edge, so the conclusion becomes: the transition `learn_ta` gives
the symbol carries the *original* order on its right-hand side, and the state it targets
is ε-promoted to the original order — the symbol is *reachable from* the original order in
the generated automaton.  See `docs/reference-defects.md`, D7.
-/

theorem mem_of_lookup_specs {specs : SpecMap} {s : Sym} {d : Nat}
    (h : specs.lookup s = some d) : (s, d) ∈ specs := by
  induction specs with
  | nil => simp [List.lookup] at h
  | cons q qs ih =>
      obtain ⟨k, v⟩ := q
      rw [List.lookup] at h
      split at h
      · next he =>
          have : s = k := by simpa using he
          subst this
          simp only [Option.some.injEq] at h
          subst h
          exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/--
**Lemma B.2 for the learner Greta ships.**  Let `s` be one of the non-conflicting symbols
that a re-layering set aside, `d` the order it was set aside from — its entry in
`special_loop_symbols` — and `l` the order the learner put it at.  Then

1. the transition `learn_ta` gives `s` sits at `e_l`;
2. every right-hand-side position that `O_a` does not restrict carries `e_d`, the state of
   the *original* order, which is the back-edge;
3. `d ≤ l`; and
4. `e_l` is ε-promoted to `e_d`, so everything the transition accepts is accepted at the
   original order.

Where the published algorithm puts `s` at order `d` outright, the shipped one makes it
reachable from `d`.  Statements (2) and (4) together are what the published proof gets
from "the construction of `O_p`, which copies the non-conflicting symbols to each newly
inserted order".
-/
theorem refGenTA_specReach {g : CFG} {oa : Oa} {specs : SpecMap} {op : OrderMap} {b : Bool}
    (hdom : SpecDominated op specs) {s : Sym} {d l : Nat} {p : Production}
    (hlk : specs.lookup s = some d) (hl : l ∈ op.ordersOf s) (hp : g.prodOfSym s = some p) :
    (⟨.lvl l, s, fillRhs (trivNts g b) p.2 (refOaFill oa specs s l)⟩ : Transition GState)
        ∈ (refGenTA g oa specs op b).trans
      ∧ (∀ k, (oa.positionsOf s).contains k = false → ∀ B, p.2[k]? = some (.nt B) →
          B ∉ trivNts g b →
          (fillRhs (trivNts g b) p.2 (refOaFill oa specs s l))[k]? = some (.state (.lvl d)))
      ∧ d ≤ l
      ∧ EpsReach (refGenTA g oa specs op b) (.lvl l) (.lvl d) := by
  obtain ⟨ss, hss, hsmem⟩ := OrderMap.mem_ordersOf.mp hl
  have hdl : d ≤ l := hdom s d (mem_of_lookup_specs hlk) l hl
  refine ⟨?_, ?_, hdl, refEpsReach_of_le hdl (OrderMap.le_maxOrder hss)⟩
  · rw [refGenTA_trans]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (mem_refNonTrivTrans.mpr ⟨l, ss, hss, s, hsmem, p, hp, rfl⟩)))
  · intro k hk B hB htn
    rw [getElem?_fillRhs, hB]
    simp only [Option.map_some, fillOne, Option.some.injEq]
    have hk' : ¬ ((oa.positionsOf s).contains k = true) := by rw [hk]; simp
    rw [if_neg (by simpa using htn), refOaFill, if_neg hk', hlk]
    rfl

end Greta
