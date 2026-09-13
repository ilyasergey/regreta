/-
**Lemma B.2, and the learner against its specification.**

`Greta.GenTASpec` proves Theorem 3.1 for an arbitrary pair `(O_a, O_p)` satisfying
`LearnedSpec`, `Fits` and `Covers`, and `docs/divergences.md` §2 explains why those were
hypotheses rather than facts.  This file does three things.

**Lemma B.2 is stated and proved**, in the two halves the paper's proof uses:

* `relayerOrder_ordersOf_above` — one re-layering step moves every order strictly above its
  band by a *single* offset, the same for every symbol, so relative order is preserved
  exactly rather than merely weakly.  `shift_mono` in `Greta.Soundness` is its arithmetic
  core; this is the statement that core was the core of.
* `relayerOrder_replicates` — the non-conflicting symbols of a band are copied to every
  order the band expands into.  This is the step B.2's proof appeals to, and the step
  Greta's own learner replaces by a back-edge; `docs/divergences.md` §8 shows that the
  replication is what makes Theorem 3.1(1) false for grammars with brackets.

**The fold is analysed band by band**, giving `foldl_relayer_strat` (two symbols of one
conflict group end strictly separated, in the order the examples demand) and
`foldl_relayer_single` (a symbol of a conflict group ends at exactly one order).  These are
the content of `LearnedSpec.strat` and `LearnedSpec.assocSingle`.

**The specification is discharged for the pipeline.**  `ofGrammar_learnOaOp` and
`assocRecorded_learnOaOp` hold unconditionally.  The rest is decidable: `learnedSpecB`
decides `LearnedSpec`, `fitsB` is a sufficient condition for `Fits`, `coversB` for
`Covers`, and `pipelineFullOK` bundles them, so `repairOnceSpec_correct_pipeline` gives
Theorem 3.2 for the pipeline of Figure 4 with every side condition checked on the input
rather than assumed.

Left open: that `toMapOf ∘ baseOrder` always presents the fold with the band structure
`foldl_relayer_strat` needs — bands visited strictly downwards, each conflicting symbol in
one group and at one band to begin with.  `List.pairwise_mergeSort'` gives the ordering
half; the rest is bookkeeping about `normalise` and has not been done.  Nothing depends on
it: `learnedSpecB` decides the same property by computation, and the self-test checks it on
the paper's running example.
-/
import Greta.GenTASpec

namespace Greta

/-! ### `O_a` records what the associativity examples say -/

theorem learnOaOp_fst (g : CFG) (neg : List TreeExample) (mto : ToMap) (b : Bool) :
    (learnOaOp g neg mto b).1 =
      neg.filterMap (fun e => if e.isAssoc then some (e.top, e.idx) else none) := rfl

theorem learnOaOp_snd (g : CFG) (neg : List TreeExample) (mto : ToMap) (b : Bool) :
    (learnOaOp g neg mto b).2 =
      (((mto.filter fun p => !p.2.isEmpty).mergeSort fun a b => b.1 ≤ a.1).foldl
        (fun m og => relayerOrder (learnOaOp g neg mto b).1 m og.1 og.2)
        (g.baseOrder b)).normalise := rfl

theorem mem_positionsOf {oa : Oa} {s : Sym} {k : Nat} (h : (s, k) ∈ oa) :
    k ∈ oa.positionsOf s := by
  simp only [Oa.positionsOf, List.mem_map, List.mem_filter, beq_iff_eq]
  exact ⟨(s, k), ⟨h, rfl⟩, rfl⟩

/-- Every rejected associativity example is recorded in the learned `O_a`. -/
theorem assocRecorded_learnOaOp (g : CFG) (neg : List TreeExample) (mto : ToMap) (b : Bool) :
    ∀ e ∈ neg, e.isAssoc = true → e.idx ∈ (learnOaOp g neg mto b).1.positionsOf e.top := by
  intro e he ha
  rw [learnOaOp_fst]
  refine mem_positionsOf ?_
  simp only [List.mem_filterMap]
  exact ⟨e, he, by simp [ha]⟩

/-! ### Which symbols an order map mentions -/

namespace OrderMap

theorem mem_ofOrder {m : OrderMap} {o : Nat} {s : Sym} :
    s ∈ m.ofOrder o ↔ ∃ p ∈ m, p.1 = o ∧ s ∈ p.2 := by
  simp only [ofOrder, List.mem_flatMap, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨p, ⟨hp, ho⟩, hs⟩; exact ⟨p, hp, ho, hs⟩
  · rintro ⟨p, hp, ho, hs⟩; exact ⟨p, ⟨hp, ho⟩, hs⟩

theorem mem_symbols_append {m₁ m₂ : OrderMap} {s : Sym} :
    s ∈ (m₁ ++ m₂).symbols ↔ s ∈ m₁.symbols ∨ s ∈ m₂.symbols := by
  simp only [mem_symbols, List.mem_append]
  constructor
  · rintro ⟨p, hp | hp, hs⟩
    · exact Or.inl ⟨p, hp, hs⟩
    · exact Or.inr ⟨p, hp, hs⟩
  · rintro (⟨p, hp, hs⟩ | ⟨p, hp, hs⟩)
    · exact ⟨p, Or.inl hp, hs⟩
    · exact ⟨p, Or.inr hp, hs⟩

theorem mem_symbols_pushN {m : OrderMap} {o n : Nat} {s : Sym} :
    s ∈ (m.pushN o n).symbols ↔ s ∈ m.symbols := by
  simp only [mem_symbols, pushN, List.mem_map]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hs⟩
    refine ⟨q, hq, ?_⟩
    by_cases h : o ≤ q.1 <;> simpa [h] using hs
  · rintro ⟨p, hp, hs⟩
    refine ⟨_, ⟨p, hp, rfl⟩, ?_⟩
    by_cases h : o ≤ p.1 <;> simp [h, hs]

theorem mem_symbols_removeOrder {m : OrderMap} {o : Nat} {s : Sym}
    (h : s ∈ (m.removeOrder o).symbols) : s ∈ m.symbols := by
  simp only [mem_symbols, removeOrder, List.mem_filter] at h ⊢
  obtain ⟨p, ⟨hp, -⟩, hs⟩ := h
  exact ⟨p, hp, hs⟩

theorem mem_symbols_withOrder {ss : List Sym} {o : Nat} {s : Sym} :
    s ∈ (withOrder ss o).symbols ↔ s ∈ ss := by
  unfold withOrder
  by_cases h : ss.isEmpty
  · rw [List.isEmpty_iff] at h; subst h; simp [mem_symbols]
  · simp [h, mem_symbols]

theorem mem_symbols_normalise {m : OrderMap} {s : Sym}
    (h : s ∈ m.normalise.symbols) : s ∈ m.symbols := by
  simp only [mem_symbols, normalise, List.mem_filterMap] at h
  obtain ⟨p, ⟨o, -, hif⟩, hs⟩ := h
  split at hif
  · exact absurd hif (by simp)
  · cases hif
    obtain ⟨q, hq, -, hq2⟩ := mem_ofOrder.mp (List.mem_dedup.mp hs)
    exact mem_symbols.mpr ⟨q, hq, hq2⟩

/-- Appending one layer per index can only add the symbols of those layers. -/
theorem mem_symbols_foldl_withOrder (ss : Nat → List Sym) (f : Nat → Nat) :
    ∀ (l : List Nat) (m : OrderMap) (s : Sym),
      s ∈ (l.foldl (fun m i => m ++ withOrder (ss i) (f i)) m).symbols →
      s ∈ m.symbols ∨ ∃ i ∈ l, s ∈ ss i := by
  intro l
  induction l with
  | nil => intro m s h; exact Or.inl h
  | cons i l ih =>
      intro m s h
      rcases ih _ _ h with h' | ⟨j, hj, hjs⟩
      · rcases mem_symbols_append.mp h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr ⟨i, List.mem_cons_self .., mem_symbols_withOrder.mp h''⟩
      · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hjs⟩

end OrderMap

/-! ### Re-layering moves symbols around but invents none -/

/-- The layers `relayerOrder` appends hold only `S` and the group members. -/
private theorem mem_symbols_layers {S : List Sym} {grp : List (List Sym)} {m0 : OrderMap}
    {o size : Nat} {s : Sym}
    (h : s ∈ ((List.range size).foldl (fun m' i =>
            m' ++ OrderMap.withOrder ((S ++ grp.filterMap fun gl => gl[i]?).dedup) (o + i))
          m0).symbols) :
    s ∈ m0.symbols ∨ s ∈ S ∨ s ∈ grp.flatten := by
  rcases OrderMap.mem_symbols_foldl_withOrder
      (fun i => (S ++ grp.filterMap fun gl => gl[i]?).dedup) (fun i => o + i)
      (List.range size) m0 s h with h' | ⟨i, -, hi⟩
  · exact Or.inl h'
  · rcases List.mem_append.mp (List.mem_dedup.mp hi) with hS | hith
    · exact Or.inr (Or.inl hS)
    · simp only [List.mem_filterMap] at hith
      obtain ⟨gl, hgl, hget⟩ := hith
      exact Or.inr (Or.inr (List.mem_flatten_of_mem hgl (List.mem_of_getElem? hget)))

/--
Re-layering an order introduces no new symbol: everything in the result was already in the
map, or is a member of the conflict groups being re-inserted.
-/
theorem mem_symbols_relayerOrder {oa : Oa} {m : OrderMap} {o : Nat} {grp : List (List Sym)}
    {s : Sym} (h : s ∈ (relayerOrder oa m o grp).symbols) :
    s ∈ m.symbols ∨ s ∈ grp.flatten := by
  have hS : ∀ x, x ∈ (m.ofOrder o).filter (fun y => !grp.flatten.contains y) →
      x ∈ m.symbols := by
    intro x hx
    obtain ⟨q, hq, -, hq2⟩ := OrderMap.mem_ofOrder.mp (List.mem_filter.mp hx).1
    exact OrderMap.mem_symbols.mpr ⟨q, hq, hq2⟩
  have hm0 : ∀ x, x ∈ ((m.removeOrder o).pushN (o + 1)
      ((grp.foldl (fun a gl => max a gl.length) 0) - 1)).symbols → x ∈ m.symbols :=
    fun x hx => OrderMap.mem_symbols_removeOrder (OrderMap.mem_symbols_pushN.mp hx)
  unfold relayerOrder at h
  simp only at h
  split at h
  · exact Or.inl h
  · split at h
    · rcases OrderMap.mem_symbols_append.mp h with h' | h'
      · rcases mem_symbols_layers (OrderMap.mem_symbols_pushN.mp h') with h'' | h'' | h''
        · exact Or.inl (hm0 _ h'')
        · exact Or.inl (hS _ h'')
        · exact Or.inr h''
      · exact Or.inl (hS _ (OrderMap.mem_symbols_withOrder.mp h'))
    · rcases mem_symbols_layers h with h'' | h'' | h''
      · exact Or.inl (hm0 _ h'')
      · exact Or.inl (hS _ h'')
      · exact Or.inr h''

/-! ### Every symbol of the learned order comes from the grammar -/

theorem mem_orderGroup {lt : List (Sym × Sym)} {ss : List Sym} {s : Sym}
    (h : s ∈ orderGroup lt ss) : s ∈ ss := by
  unfold orderGroup orderGroup? at h
  cases hts : topoSort lt ss.length ss with
  | none => rw [hts] at h; simpa using h
  | some l => rw [hts] at h; exact (topoSort_perm lt _ _ _ hts).subset h

theorem mem_flatten_toMapOf {obp : OrderMap} {neg : List TreeExample}
    {og : Nat × List (List Sym)} (hog : og ∈ toMapOf obp neg) {s : Sym}
    (hs : s ∈ og.2.flatten) : s ∈ obp.symbols := by
  simp only [toMapOf, List.mem_filterMap] at hog
  obtain ⟨p, hp, hif⟩ := hog
  split at hif
  · exact absurd hif (by simp)
  · cases hif
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hs
    exact OrderMap.mem_symbols.mpr ⟨p, hp, (List.mem_filter.mp (mem_orderGroup hs)).1⟩

/-- The re-layering fold never leaves the symbols it started with. -/
theorem mem_symbols_foldl_relayer (oa : Oa) (base : OrderMap) :
    ∀ (gs : List (Nat × List (List Sym))) (m : OrderMap),
      (∀ x ∈ m.symbols, x ∈ base.symbols) →
      (∀ og ∈ gs, ∀ x ∈ og.2.flatten, x ∈ base.symbols) →
      ∀ s ∈ (gs.foldl (fun m og => relayerOrder oa m og.1 og.2) m).symbols,
        s ∈ base.symbols := by
  intro gs
  induction gs with
  | nil => intro m hm _ s hs; exact hm s hs
  | cons og gs ih =>
      intro m hm hgs s hs
      refine ih _ (fun x hx => ?_) (fun og' hog' x hx =>
        hgs og' (List.mem_cons_of_mem _ hog') x hx) s hs
      rcases mem_symbols_relayerOrder hx with h | h
      · exact hm x h
      · exact hgs og (List.mem_cons_self ..) x h

theorem mem_symbols_baseOrder {g : CFG} {b : Bool} {s : Sym}
    (h : s ∈ (g.baseOrder b).symbols) : ∃ sp ∈ g.rankedProds, sp.1 = s := by
  unfold CFG.baseOrder at h
  simp only at h
  obtain ⟨p, hp, hs⟩ := OrderMap.mem_symbols.mp (OrderMap.mem_symbols_normalise h)
  simp only [List.mem_map, List.mem_filterMap] at hp
  obtain ⟨so, ⟨sp, hsp, hif⟩, rfl⟩ := hp
  refine ⟨sp, hsp, ?_⟩
  simp only [List.mem_singleton] at hs
  split at hif
  · exact absurd hif (by simp)
  · simp only [Option.map_eq_some_iff] at hif
    obtain ⟨o, -, hso⟩ := hif
    rw [hs, ← hso]

/--
**`LearnedSpec.ofGrammar` for the pipeline.**  Every symbol the learned order mentions is
a symbol of the grammar.
-/
theorem ofGrammar_learnOaOp (g : CFG) (neg : List TreeExample) (b : Bool) :
    OrderOfGrammar g (learnOaOp g neg (toMapOf (g.baseOrder b) neg) b).2 := by
  intro s hs
  rw [learnOaOp_snd] at hs
  refine mem_symbols_baseOrder (mem_symbols_foldl_relayer _ _ _ _ (fun x hx => hx)
    (fun og hog x hx => ?_) s (OrderMap.mem_symbols_normalise hs))
  exact mem_flatten_toMapOf
    (List.mem_filter.mp ((List.mergeSort_perm _ _).subset hog)).1 hx

/-! ### Which orders an order map assigns -/

namespace OrderMap

theorem ordersOf_append {m₁ m₂ : OrderMap} {s : Sym} {i : Nat} :
    i ∈ (m₁ ++ m₂).ordersOf s ↔ i ∈ m₁.ordersOf s ∨ i ∈ m₂.ordersOf s := by
  simp only [mem_ordersOf, List.mem_append]
  constructor
  · rintro ⟨ss, hp | hp, hs⟩
    · exact Or.inl ⟨ss, hp, hs⟩
    · exact Or.inr ⟨ss, hp, hs⟩
  · rintro (⟨ss, hp, hs⟩ | ⟨ss, hp, hs⟩)
    · exact ⟨ss, Or.inl hp, hs⟩
    · exact ⟨ss, Or.inr hp, hs⟩

theorem ordersOf_pushN {m : OrderMap} {o n : Nat} {s : Sym} {i : Nat} :
    i ∈ (m.pushN o n).ordersOf s ↔ ∃ x ∈ m.ordersOf s, i = shift o n x := by
  rw [pushN_eq_shift]
  simp only [mem_ordersOf, List.mem_map]
  constructor
  · rintro ⟨ss, ⟨p, hp, hpe⟩, hs⟩
    refine ⟨p.1, ⟨p.2, by simpa using hp, ?_⟩, ?_⟩
    · have : p.2 = ss := congrArg Prod.snd hpe
      exact this ▸ hs
    · exact (congrArg Prod.fst hpe).symm
  · rintro ⟨x, ⟨ss, hp, hs⟩, rfl⟩
    exact ⟨ss, ⟨(x, ss), hp, rfl⟩, hs⟩

theorem ordersOf_removeOrder {m : OrderMap} {o : Nat} {s : Sym} {i : Nat} :
    i ∈ (m.removeOrder o).ordersOf s ↔ i ∈ m.ordersOf s ∧ i ≠ o := by
  simp only [mem_ordersOf, removeOrder, List.mem_filter, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨ss, ⟨hp, hne⟩, hs⟩; exact ⟨⟨ss, hp, hs⟩, by simpa using hne⟩
  · rintro ⟨⟨ss, hp, hs⟩, hne⟩; exact ⟨ss, ⟨hp, by simpa using hne⟩, hs⟩

theorem ordersOf_withOrder {ss : List Sym} {o : Nat} {s : Sym} {i : Nat} :
    i ∈ (withOrder ss o).ordersOf s ↔ i = o ∧ s ∈ ss := by
  unfold withOrder
  by_cases h : ss.isEmpty = true
  · rw [List.isEmpty_iff] at h; subst h; simp [mem_ordersOf]
  · rw [if_neg h]
    constructor
    · intro hi
      obtain ⟨ss', hp, hs⟩ := mem_ordersOf.mp hi
      simp only [List.mem_singleton, Prod.mk.injEq] at hp
      exact ⟨hp.1, hp.2 ▸ hs⟩
    · rintro ⟨rfl, hs⟩
      exact mem_ordersOf.mpr ⟨ss, by simp, hs⟩

theorem ordersOf_normalise {m : OrderMap} {s : Sym} {i : Nat} :
    i ∈ m.normalise.ordersOf s ↔ i ∈ m.ordersOf s := by
  constructor
  · intro h
    obtain ⟨ss, hp, hs⟩ := mem_ordersOf.mp h
    simp only [normalise, List.mem_filterMap] at hp
    obtain ⟨o, -, hif⟩ := hp
    split at hif
    · exact absurd hif (by simp)
    · cases hif
      obtain ⟨q, hq, hq1, hq2⟩ := mem_ofOrder.mp (List.mem_dedup.mp hs)
      exact mem_ordersOf.mpr ⟨q.2, hq1 ▸ (by cases q; exact hq), hq2⟩
  · intro h
    obtain ⟨ss, hp, hs⟩ := mem_ordersOf.mp h
    have hmem : s ∈ (m.ofOrder i).dedup :=
      List.mem_dedup.mpr (mem_ofOrder.mpr ⟨(i, ss), hp, rfl, hs⟩)
    refine mem_ordersOf.mpr ⟨(m.ofOrder i).dedup, ?_, hmem⟩
    simp only [normalise, List.mem_filterMap]
    refine ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le (le_maxOrder hp)), ?_⟩
    rw [if_neg]
    intro hempty
    rw [List.isEmpty_iff] at hempty
    rw [hempty] at hmem
    exact absurd hmem (by simp)

end OrderMap

/-! ### Lemma B.2: re-layering never inverts the order

`shift_mono` in `Greta.Soundness` is the arithmetic core.  What the paper's Lemma B.2
needs on top of it is that a re-layering acts on everything above its band by *one and the
same* offset, so relative order is preserved exactly, not merely weakly.
-/

theorem shift_of_le {o n x : Nat} (h : o ≤ x) : shift o n x = x + n := by
  unfold shift; rw [if_pos h]

theorem shift_strictMono (o n : Nat) {x y : Nat} (h : x < y) : shift o n x < shift o n y := by
  unfold shift; split <;> split <;> omega

/-- A symbol absent from every appended layer keeps exactly the orders it had. -/
theorem ordersOf_foldl_withOrder (ss : Nat → List Sym) (f : Nat → Nat) (u : Sym)
    (hu : ∀ i, u ∉ ss i) :
    ∀ (l : List Nat) (m : OrderMap) (y : Nat),
      y ∈ (l.foldl (fun m i => m ++ OrderMap.withOrder (ss i) (f i)) m).ordersOf u ↔
        y ∈ m.ordersOf u := by
  intro l
  induction l with
  | nil => intro m y; exact Iff.rfl
  | cons i l ih =>
      intro m y
      rw [List.foldl_cons, ih, OrderMap.ordersOf_append]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd (OrderMap.ordersOf_withOrder.mp h).2 (hu i)
      · exact Or.inl

/--
**Lemma B.2, the exact form.**  One re-layering step moves every order strictly above its
band by a single offset `n`, the same for every symbol.  Relative order is therefore
preserved exactly: nothing is inverted, and nothing is collapsed.
-/
theorem relayerOrder_ordersOf_above (oa : Oa) (m : OrderMap) (o : Nat)
    (grp : List (List Sym)) :
    ∃ n : Nat, ∀ u : Sym, u ∉ grp.flatten → (∀ x ∈ m.ordersOf u, o < x) →
      ∀ y : Nat, (y ∈ (relayerOrder oa m o grp).ordersOf u ↔ ∃ x ∈ m.ordersOf u, y = x + n) := by
  unfold relayerOrder
  simp only
  split
  · -- the band is empty: nothing moves
    refine ⟨0, fun u _ _ y => ?_⟩
    constructor
    · exact fun h => ⟨y, h, rfl⟩
    · rintro ⟨x, hx, rfl⟩; simpa using hx
  · next hsize =>
      set size := grp.foldl (fun a gl => max a gl.length) 0 with hsz
      -- the layers the step appends never mention a symbol above the band
      have hlayers : ∀ (u : Sym), u ∉ grp.flatten → (∀ x ∈ m.ordersOf u, o < x) →
          ∀ i : Nat, u ∉ ((((m.ofOrder o).filter fun x => !grp.flatten.contains x)
            ++ grp.filterMap fun gl => gl[i]?).dedup) := by
        intro u hgrp habove i hmem
        rcases List.mem_append.mp (List.mem_dedup.mp hmem) with hS | hith
        · have := (List.mem_filter.mp hS).1
          obtain ⟨q, hq, hq1, hq2⟩ := OrderMap.mem_ofOrder.mp this
          exact absurd (habove o (OrderMap.mem_ordersOf.mpr ⟨q.2, hq1 ▸ (by cases q; exact hq), hq2⟩))
            (Nat.lt_irrefl o)
        · simp only [List.mem_filterMap] at hith
          obtain ⟨gl, hgl, hget⟩ := hith
          exact hgrp (List.mem_flatten_of_mem hgl (List.mem_of_getElem? hget))
      -- what the two `pushN`s do to an order strictly above the band
      have hm0 : ∀ (u : Sym), (∀ x ∈ m.ordersOf u, o < x) → ∀ y,
          (y ∈ ((m.removeOrder o).pushN (o + 1) (size - 1)).ordersOf u ↔
            ∃ x ∈ m.ordersOf u, y = x + (size - 1)) := by
        intro u habove y
        rw [OrderMap.ordersOf_pushN]
        constructor
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨hx', -⟩ := OrderMap.ordersOf_removeOrder.mp hx
          exact ⟨x, hx', shift_of_le (habove x hx')⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, OrderMap.ordersOf_removeOrder.mpr ⟨hx, Nat.ne_of_gt (habove x hx)⟩,
            (shift_of_le (habove x hx)).symm⟩
      split
      · -- an associativity restriction at the top of the band adds one more order
        refine ⟨size, fun u hgrp habove y => ?_⟩
        rw [OrderMap.ordersOf_append, OrderMap.ordersOf_pushN]
        have hS : y ∉ (OrderMap.withOrder
            ((m.ofOrder o).filter fun x => !grp.flatten.contains x) (o + size)).ordersOf u := by
          intro hy
          have := (OrderMap.ordersOf_withOrder.mp hy).2
          obtain ⟨q, hq, hq1, hq2⟩ := OrderMap.mem_ofOrder.mp (List.mem_filter.mp this).1
          exact absurd (habove o (OrderMap.mem_ordersOf.mpr ⟨q.2, hq1 ▸ (by cases q; exact hq), hq2⟩))
            (Nat.lt_irrefl o)
        constructor
        · rintro (⟨z, hz, rfl⟩ | hy)
          · rw [ordersOf_foldl_withOrder _ _ _ (hlayers u hgrp habove)] at hz
            obtain ⟨x, hx, rfl⟩ := (hm0 u habove z).mp hz
            refine ⟨x, hx, ?_⟩
            rw [shift_of_le (by have := habove x hx; omega)]
            have := habove x hx
            omega
          · exact absurd hy hS
        · rintro ⟨x, hx, rfl⟩
          refine Or.inl ⟨x + (size - 1), ?_, ?_⟩
          · rw [ordersOf_foldl_withOrder _ _ _ (hlayers u hgrp habove)]
            exact (hm0 u habove _).mpr ⟨x, hx, rfl⟩
          · rw [shift_of_le (by have := habove x hx; omega)]
            have := habove x hx
            omega
      · refine ⟨size - 1, fun u hgrp habove y => ?_⟩
        rw [ordersOf_foldl_withOrder _ _ _ (hlayers u hgrp habove)]
        exact hm0 u habove y

/-- Orders already present survive the appending of further layers. -/
theorem ordersOf_foldl_withOrder_mono (ss : Nat → List Sym) (f : Nat → Nat) (u : Sym) :
    ∀ (l : List Nat) (m : OrderMap) (y : Nat), y ∈ m.ordersOf u →
      y ∈ (l.foldl (fun m i => m ++ OrderMap.withOrder (ss i) (f i)) m).ordersOf u := by
  intro l
  induction l with
  | nil => intro m y h; exact h
  | cons i l ih =>
      intro m y h
      rw [List.foldl_cons]
      exact ih _ _ (OrderMap.ordersOf_append.mpr (Or.inl h))

/-- A symbol placed in the `j`-th appended layer acquires that layer's order. -/
theorem ordersOf_foldl_withOrder_mem (ss : Nat → List Sym) (f : Nat → Nat) (u : Sym) :
    ∀ (l : List Nat) (m : OrderMap) (j : Nat), j ∈ l → u ∈ ss j →
      f j ∈ (l.foldl (fun m i => m ++ OrderMap.withOrder (ss i) (f i)) m).ordersOf u := by
  intro l
  induction l with
  | nil => intro _ _ hj _; exact absurd hj (by simp)
  | cons i l ih =>
      intro m j hj hu
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ordersOf_foldl_withOrder_mono _ _ _ _ _ _
          (OrderMap.ordersOf_append.mpr (Or.inr (OrderMap.ordersOf_withOrder.mpr ⟨rfl, hu⟩)))
      · exact ih _ _ hj hu

/--
**Lemma B.2, replication half.**  The non-conflicting symbols of a band are copied to
every order the band expands into.  This is the step the paper's proof of B.2 appeals to,
"the construction of `O_p`, which copies the non-conflicting symbols to each newly
inserted order", and the step Greta's own learner replaces by a back-edge (see
`docs/reference-defects.md`, D7).
-/
theorem relayerOrder_replicates (oa : Oa) (m : OrderMap) (o : Nat) (grp : List (List Sym))
    (s : Sym) (hs : s ∈ (m.ofOrder o).filter fun x => !grp.flatten.contains x)
    (i : Nat) (hi : i < grp.foldl (fun a gl => max a gl.length) 0) :
    (o + i) ∈ (relayerOrder oa m o grp).ordersOf s := by
  unfold relayerOrder
  simp only
  split
  · next hz => exact absurd hi (by rw [hz]; exact Nat.not_lt_zero i)
  · next =>
      have hmem : (o + i) ∈ ((List.range (grp.foldl (fun a gl => max a gl.length) 0)).foldl
          (fun m' j => m' ++ OrderMap.withOrder
            ((((m.ofOrder o).filter fun x => !grp.flatten.contains x)
              ++ grp.filterMap fun gl => gl[j]?).dedup) (o + j))
          (((m.removeOrder o).pushN (o + 1)
            ((grp.foldl (fun a gl => max a gl.length) 0) - 1)))).ordersOf s :=
        ordersOf_foldl_withOrder_mem _ _ _ _ _ i (List.mem_range.mpr hi)
          (List.mem_dedup.mpr (List.mem_append_left _ hs))
      split
      · refine OrderMap.ordersOf_append.mpr (Or.inl ?_)
        refine OrderMap.ordersOf_pushN.mpr ⟨o + i, hmem, ?_⟩
        unfold shift
        rw [if_neg (by omega)]
      · exact hmem

/--
A re-layering leaves everything *below* its band alone.  Together with
`relayerOrder_ordersOf_above` this is what lets the fold be analysed one band at a time:
bands are processed from the highest down, so when a band is reached, the bands already
processed sit above it and the bands still to come sit below it.
-/
theorem relayerOrder_ordersOf_below (oa : Oa) (m : OrderMap) (o : Nat)
    (grp : List (List Sym)) (u : Sym) (hgrp : u ∉ grp.flatten)
    (hbelow : ∀ x ∈ m.ordersOf u, x < o) :
    ∀ y : Nat, (y ∈ (relayerOrder oa m o grp).ordersOf u ↔ y ∈ m.ordersOf u) := by
  have hlayers : ∀ i : Nat, u ∉ ((((m.ofOrder o).filter fun x => !grp.flatten.contains x)
      ++ grp.filterMap fun gl => gl[i]?).dedup) := by
    intro i hmem
    rcases List.mem_append.mp (List.mem_dedup.mp hmem) with hS | hith
    · obtain ⟨q, hq, hq1, hq2⟩ := OrderMap.mem_ofOrder.mp (List.mem_filter.mp hS).1
      exact absurd (hbelow o (OrderMap.mem_ordersOf.mpr
        ⟨q.2, hq1 ▸ (by cases q; exact hq), hq2⟩)) (Nat.lt_irrefl o)
    · simp only [List.mem_filterMap] at hith
      obtain ⟨gl, hgl, hget⟩ := hith
      exact hgrp (List.mem_flatten_of_mem hgl (List.mem_of_getElem? hget))
  have hS : ∀ (n : Nat) (y : Nat), y ∉ (OrderMap.withOrder
      ((m.ofOrder o).filter fun x => !grp.flatten.contains x) n).ordersOf u := by
    intro n y hy
    obtain ⟨q, hq, hq1, hq2⟩ :=
      OrderMap.mem_ofOrder.mp (List.mem_filter.mp (OrderMap.ordersOf_withOrder.mp hy).2).1
    exact absurd (hbelow o (OrderMap.mem_ordersOf.mpr
      ⟨q.2, hq1 ▸ (by cases q; exact hq), hq2⟩)) (Nat.lt_irrefl o)
  unfold relayerOrder
  simp only
  split
  · intro y; exact Iff.rfl
  · next =>
      set size := grp.foldl (fun a gl => max a gl.length) 0 with hsz
      have hm0 : ∀ y : Nat,
          (y ∈ ((m.removeOrder o).pushN (o + 1) (size - 1)).ordersOf u ↔ y ∈ m.ordersOf u) := by
        intro y
        rw [OrderMap.ordersOf_pushN]
        constructor
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨hx', -⟩ := OrderMap.ordersOf_removeOrder.mp hx
          rwa [show shift (o + 1) (size - 1) x = x by
            unfold shift; rw [if_neg (by have := hbelow x hx'; omega)]]
        · intro hy
          exact ⟨y, OrderMap.ordersOf_removeOrder.mpr ⟨hy, Nat.ne_of_lt (hbelow y hy)⟩,
            by unfold shift; rw [if_neg (by have := hbelow y hy; omega)]⟩
      split
      · intro y
        rw [OrderMap.ordersOf_append, OrderMap.ordersOf_pushN]
        constructor
        · rintro (⟨z, hz, rfl⟩ | hy)
          · rw [ordersOf_foldl_withOrder _ _ _ hlayers] at hz
            have hzm := (hm0 z).mp hz
            rwa [show shift (o + size) 1 z = z by
              unfold shift; rw [if_neg (by have := hbelow z hzm; omega)]]
          · exact absurd hy (hS _ _)
        · intro hy
          refine Or.inl ⟨y, ?_, ?_⟩
          · rw [ordersOf_foldl_withOrder _ _ _ hlayers]; exact (hm0 y).mpr hy
          · unfold shift; rw [if_neg (by have := hbelow y hy; omega)]
      · intro y
        rw [ordersOf_foldl_withOrder _ _ _ hlayers]
        exact hm0 y

/-- The orders a symbol has after appending layers, exactly. -/
theorem ordersOf_foldl_withOrder_iff (ss : Nat → List Sym) (f : Nat → Nat) (u : Sym) :
    ∀ (l : List Nat) (m : OrderMap) (y : Nat),
      y ∈ (l.foldl (fun m i => m ++ OrderMap.withOrder (ss i) (f i)) m).ordersOf u ↔
        (y ∈ m.ordersOf u ∨ ∃ i ∈ l, y = f i ∧ u ∈ ss i) := by
  intro l
  induction l with
  | nil => intro m y; simp
  | cons i l ih =>
      intro m y
      rw [List.foldl_cons, ih, OrderMap.ordersOf_append]
      constructor
      · rintro ((h | h) | ⟨j, hj, hy, hu⟩)
        · exact Or.inl h
        · obtain ⟨hy, hu⟩ := OrderMap.ordersOf_withOrder.mp h
          exact Or.inr ⟨i, List.mem_cons_self .., hy, hu⟩
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hy, hu⟩
      · rintro (h | ⟨j, hj, hy, hu⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact Or.inl (Or.inr (OrderMap.ordersOf_withOrder.mpr ⟨hy, hu⟩))
          · exact Or.inr ⟨j, hj, hy, hu⟩

/--
At its own band a conflicting symbol lands at exactly one order, the band's base plus the
symbol's position in the linearised group.  This is what turns `topoSort_before` into a
statement about orders.
-/
theorem relayerOrder_ordersOf_at_band (oa : Oa) (m : OrderMap) (o : Nat)
    (grp : List (List Sym)) (u : Sym) (p : Nat)
    (huniq : ∀ i : Nat, u ∈ grp.filterMap (fun g => g[i]?) ↔ i = p)
    (hp : p < grp.foldl (fun a g => max a g.length) 0)
    (hmem : u ∈ grp.flatten)
    (hm : ∀ x ∈ m.ordersOf u, x = o) :
    ∀ y : Nat, (y ∈ (relayerOrder oa m o grp).ordersOf u ↔ y = o + p) := by
  have hnotS : u ∉ (m.ofOrder o).filter fun x => !grp.flatten.contains x := by
    intro h
    have h2 := (List.mem_filter.mp h).2
    have h3 : grp.flatten.contains u = true := by simp [hmem]
    rw [h3] at h2
    exact Bool.noConfusion h2
  have hlayer : ∀ i : Nat, (u ∈ (((m.ofOrder o).filter fun x => !grp.flatten.contains x)
      ++ grp.filterMap fun g => g[i]?).dedup) ↔ i = p := by
    intro i
    rw [List.mem_dedup, List.mem_append]
    constructor
    · rintro (h | h)
      · exact absurd h hnotS
      · exact (huniq i).mp h
    · rintro rfl
      exact Or.inr ((huniq _).mpr rfl)
  unfold relayerOrder
  simp only
  split
  · next hz => exact absurd hp (by rw [hz]; exact Nat.not_lt_zero p)
  · next =>
      set size := grp.foldl (fun a g => max a g.length) 0 with hsz
      have hm0 : ∀ y : Nat, y ∉ ((m.removeOrder o).pushN (o + 1) (size - 1)).ordersOf u := by
        intro y hy
        obtain ⟨x, hx, -⟩ := OrderMap.ordersOf_pushN.mp hy
        obtain ⟨hx', hne⟩ := OrderMap.ordersOf_removeOrder.mp hx
        exact hne (hm x hx')
      have hm1 : ∀ y : Nat,
          (y ∈ ((List.range size).foldl (fun m' i => m' ++ OrderMap.withOrder
            ((((m.ofOrder o).filter fun x => !grp.flatten.contains x)
              ++ grp.filterMap fun g => g[i]?).dedup) (o + i))
            ((m.removeOrder o).pushN (o + 1) (size - 1))).ordersOf u ↔ y = o + p) := by
        intro y
        rw [ordersOf_foldl_withOrder_iff]
        constructor
        · rintro (h | ⟨i, -, rfl, hu⟩)
          · exact absurd h (hm0 y)
          · rw [(hlayer i).mp hu]
        · rintro rfl
          exact Or.inr ⟨p, List.mem_range.mpr hp, rfl, (hlayer p).mpr rfl⟩
      split
      · intro y
        rw [OrderMap.ordersOf_append, OrderMap.ordersOf_pushN]
        constructor
        · rintro (⟨z, hz, rfl⟩ | hy)
          · rw [hm1 z] at hz
            subst hz
            unfold shift; rw [if_neg (by omega)]
          · exact absurd (OrderMap.ordersOf_withOrder.mp hy).2 hnotS
        · rintro rfl
          exact Or.inl ⟨o + p, (hm1 _).mpr rfl, by unfold shift; rw [if_neg (by omega)]⟩
      · exact hm1

/-!
### Separation survives the rest of the fold

Once a band has been re-layered, the bands still to be processed all sit strictly below
it, so by `relayerOrder_ordersOf_above` each of them moves the two symbols by one and the
same offset.  Strict separation is therefore preserved to the end of the fold.
-/

theorem foldl_relayer_above (oa : Oa) :
    ∀ (gs : List (Nat × List (List Sym))) (m : OrderMap) (u : Sym) (bound : Nat),
      (∀ og ∈ gs, og.1 < bound) → (∀ og ∈ gs, u ∉ og.2.flatten) →
      (∀ x ∈ m.ordersOf u, bound ≤ x) →
      ∀ x ∈ (gs.foldl (fun m og => relayerOrder oa m og.1 og.2) m).ordersOf u, bound ≤ x := by
  intro gs
  induction gs with
  | nil => intro m u bound _ _ h x hx; exact h x hx
  | cons og gs ih =>
      intro m u bound hb hu hm x hx
      rw [List.foldl_cons] at hx
      refine ih _ _ _ (fun og' hog' => hb og' (List.mem_cons_of_mem _ hog'))
        (fun og' hog' => hu og' (List.mem_cons_of_mem _ hog')) (fun y hy => ?_) x hx
      obtain ⟨n, hn⟩ := relayerOrder_ordersOf_above oa m og.1 og.2
      obtain ⟨z, hz, rfl⟩ := (hn u (hu og (List.mem_cons_self ..))
        (fun w hw => Nat.lt_of_lt_of_le (hb og (List.mem_cons_self ..)) (hm w hw)) y).mp hy
      exact Nat.le_trans (hm z hz) (Nat.le_add_right _ _)

/--
Strict separation of two symbols is preserved by every later band.  This is the step that
turns the placement at one band into a statement about the learned order.
-/
theorem foldl_relayer_preserves_lt (oa : Oa) :
    ∀ (gs : List (Nat × List (List Sym))) (m : OrderMap) (u v : Sym) (bound : Nat),
      (∀ og ∈ gs, og.1 < bound) →
      (∀ og ∈ gs, u ∉ og.2.flatten) → (∀ og ∈ gs, v ∉ og.2.flatten) →
      (∀ x ∈ m.ordersOf u, bound ≤ x) → (∀ y ∈ m.ordersOf v, bound ≤ y) →
      (∀ x ∈ m.ordersOf u, ∀ y ∈ m.ordersOf v, x < y) →
      ∀ x ∈ (gs.foldl (fun m og => relayerOrder oa m og.1 og.2) m).ordersOf u,
      ∀ y ∈ (gs.foldl (fun m og => relayerOrder oa m og.1 og.2) m).ordersOf v, x < y := by
  intro gs
  induction gs with
  | nil => intro m u v _ _ _ _ _ _ h x hx y hy; exact h x hx y hy
  | cons og gs ih =>
      intro m u v bound hb hu hv hmu hmv hlt x hx y hy
      rw [List.foldl_cons] at hx hy
      obtain ⟨n, hn⟩ := relayerOrder_ordersOf_above oa m og.1 og.2
      have habu : ∀ w ∈ m.ordersOf u, og.1 < w := fun w hw =>
        Nat.lt_of_lt_of_le (hb og (List.mem_cons_self ..)) (hmu w hw)
      have habv : ∀ w ∈ m.ordersOf v, og.1 < w := fun w hw =>
        Nat.lt_of_lt_of_le (hb og (List.mem_cons_self ..)) (hmv w hw)
      have hnu := hn u (hu og (List.mem_cons_self ..)) habu
      have hnv := hn v (hv og (List.mem_cons_self ..)) habv
      refine ih _ _ _ bound (fun og' hog' => hb og' (List.mem_cons_of_mem _ hog'))
        (fun og' hog' => hu og' (List.mem_cons_of_mem _ hog'))
        (fun og' hog' => hv og' (List.mem_cons_of_mem _ hog'))
        (fun w hw => ?_) (fun w hw => ?_) (fun w hw w' hw' => ?_) x hx y hy
      · obtain ⟨z, hz, rfl⟩ := (hnu w).mp hw
        exact Nat.le_trans (hmu z hz) (Nat.le_add_right _ _)
      · obtain ⟨z, hz, rfl⟩ := (hnv w).mp hw
        exact Nat.le_trans (hmv z hz) (Nat.le_add_right _ _)
      · obtain ⟨z, hz, rfl⟩ := (hnu w).mp hw
        obtain ⟨z', hz', rfl⟩ := (hnv w').mp hw'
        exact Nat.add_lt_add_right (hlt z hz z' hz') n

/-- Bands strictly above a symbol's own order leave that order untouched. -/
theorem foldl_relayer_below (oa : Oa) :
    ∀ (gs : List (Nat × List (List Sym))) (m : OrderMap) (u : Sym) (bound : Nat),
      (∀ og ∈ gs, bound < og.1) → (∀ og ∈ gs, u ∉ og.2.flatten) →
      (∀ x ∈ m.ordersOf u, x ≤ bound) →
      ∀ y : Nat, (y ∈ (gs.foldl (fun m og => relayerOrder oa m og.1 og.2) m).ordersOf u ↔
        y ∈ m.ordersOf u) := by
  intro gs
  induction gs with
  | nil => intro m u bound _ _ _ y; exact Iff.rfl
  | cons og gs ih =>
      intro m u bound hb hu hm y
      have hstep := relayerOrder_ordersOf_below oa m og.1 og.2 u
        (hu og (List.mem_cons_self ..))
        (fun x hx => Nat.lt_of_le_of_lt (hm x hx) (hb og (List.mem_cons_self ..)))
      rw [List.foldl_cons,
        ih _ _ bound (fun og' hog' => hb og' (List.mem_cons_of_mem _ hog'))
          (fun og' hog' => hu og' (List.mem_cons_of_mem _ hog'))
          (fun x hx => hm x ((hstep x).mp hx)) y]
      exact hstep y

/--
**`LearnedSpec.strat`, as a theorem about the re-layering fold.**  Two symbols of one
conflict group, linearised at positions `p < q`, end the fold strictly separated, with the
one the examples put first sitting at the strictly lower order.

The hypotheses say exactly what `toMapOf` delivers: the bands are processed from the
highest down, each symbol belongs to only its own band's group, and each starts out at its
band.  `topoSort_before` is what supplies `p < q`.
-/
theorem foldl_relayer_strat (oa : Oa) (m : OrderMap)
    (before : List (Nat × List (List Sym))) (o : Nat) (grp : List (List Sym))
    (after : List (Nat × List (List Sym))) (u v : Sym) (p q : Nat)
    (hbefore : ∀ og ∈ before, o < og.1) (hafter : ∀ og ∈ after, og.1 < o)
    (hub : ∀ og ∈ before, u ∉ og.2.flatten) (hvb : ∀ og ∈ before, v ∉ og.2.flatten)
    (hua : ∀ og ∈ after, u ∉ og.2.flatten) (hva : ∀ og ∈ after, v ∉ og.2.flatten)
    (hmu : ∀ x ∈ m.ordersOf u, x = o) (hmv : ∀ x ∈ m.ordersOf v, x = o)
    (huniqU : ∀ i : Nat, u ∈ grp.filterMap (fun g => g[i]?) ↔ i = p)
    (huniqV : ∀ i : Nat, v ∈ grp.filterMap (fun g => g[i]?) ↔ i = q)
    (hpq : p < q)
    (hpsize : p < grp.foldl (fun a g => max a g.length) 0)
    (hqsize : q < grp.foldl (fun a g => max a g.length) 0)
    (humem : u ∈ grp.flatten) (hvmem : v ∈ grp.flatten) :
    ∀ x ∈ ((before ++ (o, grp) :: after).foldl
             (fun m og => relayerOrder oa m og.1 og.2) m).ordersOf u,
    ∀ y ∈ ((before ++ (o, grp) :: after).foldl
             (fun m og => relayerOrder oa m og.1 og.2) m).ordersOf v, x < y := by
  rw [List.foldl_append, List.foldl_cons]
  set m' := before.foldl (fun m og => relayerOrder oa m og.1 og.2) m with hm'
  -- the bands processed first sit above this one, so they leave it alone
  have hmu' : ∀ x ∈ m'.ordersOf u, x = o := fun x hx =>
    hmu x ((foldl_relayer_below oa before m u o hbefore hub
      (fun w hw => Nat.le_of_eq (hmu w hw)) x).mp hx)
  have hmv' : ∀ x ∈ m'.ordersOf v, x = o := fun x hx =>
    hmv x ((foldl_relayer_below oa before m v o hbefore hvb
      (fun w hw => Nat.le_of_eq (hmv w hw)) x).mp hx)
  -- at its own band each symbol lands at its position in the linearised group
  have hbandU := relayerOrder_ordersOf_at_band oa m' o grp u p huniqU hpsize humem hmu'
  have hbandV := relayerOrder_ordersOf_at_band oa m' o grp v q huniqV hqsize hvmem hmv'
  refine foldl_relayer_preserves_lt oa after _ u v o
    hafter hua hva (fun x hx => ?_) (fun y hy => ?_) (fun x hx y hy => ?_)
  · rw [hbandU x] at hx; omega
  · rw [hbandV y] at hy; omega
  · rw [hbandU x] at hx; rw [hbandV y] at hy; omega

/-!
### A symbol in an associativity conflict keeps a single order

`LearnedSpec.assocSingle` needs the symbol of an associativity example to sit at exactly
one order.  Its own band gives it one, by `relayerOrder_ordersOf_at_band`, and every later
band moves it by a single offset, so it can never be split.
-/

theorem foldl_relayer_singleton (oa : Oa) :
    ∀ (gs : List (Nat × List (List Sym))) (m : OrderMap) (u : Sym) (bound : Nat),
      (∀ og ∈ gs, og.1 < bound) → (∀ og ∈ gs, u ∉ og.2.flatten) →
      (∀ x ∈ m.ordersOf u, bound ≤ x) →
      (∀ x ∈ m.ordersOf u, ∀ y ∈ m.ordersOf u, x = y) →
      ∀ x ∈ (gs.foldl (fun m og => relayerOrder oa m og.1 og.2) m).ordersOf u,
      ∀ y ∈ (gs.foldl (fun m og => relayerOrder oa m og.1 og.2) m).ordersOf u, x = y := by
  intro gs
  induction gs with
  | nil => intro m u _ _ _ _ h x hx y hy; exact h x hx y hy
  | cons og gs ih =>
      intro m u bound hb hu hm hsing x hx y hy
      rw [List.foldl_cons] at hx hy
      obtain ⟨n, hn⟩ := relayerOrder_ordersOf_above oa m og.1 og.2
      have habu : ∀ w ∈ m.ordersOf u, og.1 < w := fun w hw =>
        Nat.lt_of_lt_of_le (hb og (List.mem_cons_self ..)) (hm w hw)
      have hnu := hn u (hu og (List.mem_cons_self ..)) habu
      refine ih _ _ bound (fun og' hog' => hb og' (List.mem_cons_of_mem _ hog'))
        (fun og' hog' => hu og' (List.mem_cons_of_mem _ hog'))
        (fun w hw => ?_) (fun w hw w' hw' => ?_) x hx y hy
      · obtain ⟨z, hz, rfl⟩ := (hnu w).mp hw
        exact Nat.le_trans (hm z hz) (Nat.le_add_right _ _)
      · obtain ⟨z, hz, rfl⟩ := (hnu w).mp hw
        obtain ⟨z', hz', rfl⟩ := (hnu w').mp hw'
        rw [hsing z hz z' hz']

/--
**`LearnedSpec.assocSingle`, as a theorem about the re-layering fold.**  A symbol that
belongs to a conflict group ends the fold at exactly one order.
-/
theorem foldl_relayer_single (oa : Oa) (m : OrderMap)
    (before : List (Nat × List (List Sym))) (o : Nat) (grp : List (List Sym))
    (after : List (Nat × List (List Sym))) (u : Sym) (p : Nat)
    (hbefore : ∀ og ∈ before, o < og.1) (hafter : ∀ og ∈ after, og.1 < o)
    (hub : ∀ og ∈ before, u ∉ og.2.flatten) (hua : ∀ og ∈ after, u ∉ og.2.flatten)
    (hmu : ∀ x ∈ m.ordersOf u, x = o)
    (huniqU : ∀ i : Nat, u ∈ grp.filterMap (fun g => g[i]?) ↔ i = p)
    (hpsize : p < grp.foldl (fun a g => max a g.length) 0)
    (humem : u ∈ grp.flatten) :
    ∀ x ∈ ((before ++ (o, grp) :: after).foldl
             (fun m og => relayerOrder oa m og.1 og.2) m).ordersOf u,
    ∀ y ∈ ((before ++ (o, grp) :: after).foldl
             (fun m og => relayerOrder oa m og.1 og.2) m).ordersOf u, x = y := by
  rw [List.foldl_append, List.foldl_cons]
  set m' := before.foldl (fun m og => relayerOrder oa m og.1 og.2) m with hm'
  have hmu' : ∀ x ∈ m'.ordersOf u, x = o := fun x hx =>
    hmu x ((foldl_relayer_below oa before m u o hbefore hub
      (fun w hw => Nat.le_of_eq (hmu w hw)) x).mp hx)
  have hband := relayerOrder_ordersOf_at_band oa m' o grp u p huniqU hpsize humem hmu'
  refine foldl_relayer_singleton oa after _ u o hafter hua (fun x hx => ?_)
    (fun x hx y hy => ?_)
  · rw [hband x] at hx; omega
  · rw [hband x] at hx; rw [hband y] at hy; omega

/-- An order already held survives every later band, which only shifts it. -/
theorem foldl_relayer_mono (oa : Oa) :
    ∀ (gs : List (Nat × List (List Sym))) (m : OrderMap) (u : Sym) (bound : Nat),
      (∀ og ∈ gs, og.1 < bound) → (∀ og ∈ gs, u ∉ og.2.flatten) →
      (∀ x ∈ m.ordersOf u, bound ≤ x) →
      ∀ x ∈ m.ordersOf u,
      ∃ y, y ∈ (gs.foldl (fun m og => relayerOrder oa m og.1 og.2) m).ordersOf u := by
  intro gs
  induction gs with
  | nil => intro m u _ _ _ _ x hx; exact ⟨x, hx⟩
  | cons og gs ih =>
      intro m u bound hb hu hm x hx
      rw [List.foldl_cons]
      obtain ⟨n, hn⟩ := relayerOrder_ordersOf_above oa m og.1 og.2
      have habu : ∀ w ∈ m.ordersOf u, og.1 < w := fun w hw =>
        Nat.lt_of_lt_of_le (hb og (List.mem_cons_self ..)) (hm w hw)
      have hnu := hn u (hu og (List.mem_cons_self ..)) habu
      refine ih _ _ bound (fun og' hog' => hb og' (List.mem_cons_of_mem _ hog'))
        (fun og' hog' => hu og' (List.mem_cons_of_mem _ hog'))
        (fun w hw => ?_) (x + n) ((hnu (x + n)).mpr ⟨x, hx, rfl⟩)
      obtain ⟨z, hz, rfl⟩ := (hnu w).mp hw
      exact Nat.le_trans (hm z hz) (Nat.le_add_right _ _)

/--
**A symbol in a conflict group never loses its order.**  This is what `Covers` needs for
the conflicting symbols; the non-conflicting ones are covered by `relayerOrder_replicates`.
-/
theorem foldl_relayer_mem (oa : Oa) (m : OrderMap)
    (before : List (Nat × List (List Sym))) (o : Nat) (grp : List (List Sym))
    (after : List (Nat × List (List Sym))) (u : Sym) (p : Nat)
    (hbefore : ∀ og ∈ before, o < og.1) (hafter : ∀ og ∈ after, og.1 < o)
    (hub : ∀ og ∈ before, u ∉ og.2.flatten) (hua : ∀ og ∈ after, u ∉ og.2.flatten)
    (hmu : ∀ x ∈ m.ordersOf u, x = o)
    (huniqU : ∀ i : Nat, u ∈ grp.filterMap (fun g => g[i]?) ↔ i = p)
    (hpsize : p < grp.foldl (fun a g => max a g.length) 0)
    (humem : u ∈ grp.flatten) :
    ((before ++ (o, grp) :: after).foldl
      (fun m og => relayerOrder oa m og.1 og.2) m).ordersOf u ≠ [] := by
  rw [List.foldl_append, List.foldl_cons]
  set m' := before.foldl (fun m og => relayerOrder oa m og.1 og.2) m with hm'
  have hmu' : ∀ x ∈ m'.ordersOf u, x = o := fun x hx =>
    hmu x ((foldl_relayer_below oa before m u o hbefore hub
      (fun w hw => Nat.le_of_eq (hmu w hw)) x).mp hx)
  have hband := relayerOrder_ordersOf_at_band oa m' o grp u p huniqU hpsize humem hmu'
  obtain ⟨y, hy⟩ := foldl_relayer_mono oa after _ u o hafter hua
    (fun x hx => by rw [hband x] at hx; omega) (o + p) ((hband _).mpr rfl)
  intro hnil
  rw [hnil] at hy
  exact absurd hy (by simp)

/-!
### `LearnedSpec` is decidable, so the pipeline can discharge it on its own input

Every clause of `LearnedSpec` quantifies over a finite list, so the whole of it is a
decidable property of the learned pair.  `learnedSpecB` is the check and
`learnedSpec_of_check` its soundness proof, which lets a concrete grammar and a concrete
set of examples discharge the hypothesis of `genTA_sound₂` (and so of Theorem 3.1(2)) by
computation rather than by assumption.
-/

theorem not_mem_of_contains_false {l : List Sym} {x : Sym} (h : l.contains x = false) :
    x ∉ l := by
  intro hx
  rw [show l.contains x = true by simp [hx]] at h
  exact Bool.noConfusion h

theorem contains_false_of_not_mem {l : List Sym} {x : Sym} (h : x ∉ l) :
    l.contains x = false := by
  cases hc : l.contains x
  · rfl
  · exact absurd (by simpa using hc) h

/-- The decision procedure for `LearnedSpec`. -/
def learnedSpecB (g : CFG) (neg : List TreeExample) (b : Bool) (oa : Oa) (op : OrderMap) :
    Bool :=
  op.symbols.all (fun s => g.rankedProds.any (fun sp => sp.1 == s))
    && neg.all (fun e => !(trivSyms g b).contains e.top && !(trivSyms g b).contains e.bot)
    && neg.all (fun e => !e.isPrec ||
        (op.ordersOf e.top).all fun i => (op.ordersOf e.bot).all fun j => decide (j < i))
    && neg.all (fun e => !e.isAssoc || (oa.positionsOf e.top).contains e.idx)
    && neg.all (fun e => !e.isAssoc ||
        (op.ordersOf e.top).all fun i => (op.ordersOf e.top).all fun j => i == j)

theorem learnedSpec_of_check {g : CFG} {neg : List TreeExample} {b : Bool} {oa : Oa}
    {op : OrderMap} (h : learnedSpecB g neg b oa op = true) : LearnedSpec g neg b oa op := by
  simp only [learnedSpecB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have := List.all_eq_true.mp h1 s hs
    simp only [List.any_eq_true, beq_iff_eq] at this
    exact this
  · intro e he
    have := List.all_eq_true.mp h2 e he
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact ⟨not_mem_of_contains_false this.1, not_mem_of_contains_false this.2⟩
  · intro e he hp i hi j hj
    have := List.all_eq_true.mp h3 e he
    rw [hp] at this
    simp only [Bool.not_true, Bool.false_or] at this
    have := List.all_eq_true.mp this i hi
    simpa using List.all_eq_true.mp this j hj
  · intro e he ha
    have := List.all_eq_true.mp h4 e he
    rw [ha] at this
    simpa using this
  · intro e he ha i hi j hj
    have := List.all_eq_true.mp h5 e he
    rw [ha] at this
    simp only [Bool.not_true, Bool.false_or] at this
    have := List.all_eq_true.mp this i hi
    simpa using List.all_eq_true.mp this j hj

instance (g : CFG) (neg : List TreeExample) (b : Bool) (oa : Oa) (op : OrderMap) :
    Decidable (LearnedSpec g neg b oa op) := by
  refine decidable_of_iff (learnedSpecB g neg b oa op = true) ⟨learnedSpec_of_check, ?_⟩
  intro h
  simp only [learnedSpecB, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact List.all_eq_true.mpr fun s hs => by
      obtain ⟨sp, hsp, he⟩ := h.ofGrammar s hs
      exact List.any_eq_true.mpr ⟨sp, hsp, by simp [he]⟩
  · exact List.all_eq_true.mpr fun e he => by
      obtain ⟨ht, hb⟩ := h.notTrivial e he
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨contains_false_of_not_mem ht, contains_false_of_not_mem hb⟩
  · refine List.all_eq_true.mpr fun e he => ?_
    by_cases hp : e.isPrec = true
    · rw [hp]
      simp only [Bool.not_true, Bool.false_or]
      exact List.all_eq_true.mpr fun i hi => List.all_eq_true.mpr fun j hj => by
        simpa using h.strat e he hp i hi j hj
    · have hpf : e.isPrec = false := by simpa using hp
      simp [hpf]
  · refine List.all_eq_true.mpr fun e he => ?_
    by_cases ha : e.isAssoc = true
    · rw [ha]; simpa using h.assocRecorded e he ha
    · have haf : e.isAssoc = false := by simpa using ha
      simp [haf]
  · refine List.all_eq_true.mpr fun e he => ?_
    by_cases ha : e.isAssoc = true
    · rw [ha]
      simp only [Bool.not_true, Bool.false_or]
      exact List.all_eq_true.mpr fun i hi => List.all_eq_true.mpr fun j hj => by
        simpa using h.assocSingle e he ha i hi j hj
    · have haf : e.isAssoc = false := by simpa using ha
      simp [haf]

/-!
### `Fits` and `Covers` are checkable too

`Fits` quantifies over an unbounded child position `k`, so it is not decidable by
enumeration as it stands.  It does not need to be: `fitsB` below is a *sufficient*
condition that ranges only over the forbidden positions `O_a` records, and
`fits_of_check` proves it enough.  The case `k` outside `O_a` is handled uniformly,
because `oaFill` then demands only level `i`.
-/

/-- A rejected precedence example forbidding `s'` directly under `s`. -/
def hasPrecExample (neg : List TreeExample) (s s' : Sym) : Bool :=
  neg.any fun e => e.isPrec && e.top == s && e.bot == s'

/-- A rejected associativity example forbidding `s'` at child position `k` of `s`. -/
def hasAssocExample (neg : List TreeExample) (s s' : Sym) (k : Nat) : Bool :=
  neg.any fun e => e.isAssoc && e.top == s && e.bot == s' && e.idx == k

/--
A sufficient condition for `Fits`, checkable on the input.  It ranges over the
parent/child pairs the grammar actually admits, which is what `ChildAt` restricts `Fits`
to, and over the forbidden positions `O_a` records.
-/
def fitsB (g : CFG) (neg : List TreeExample) (b : Bool) (oa : Oa) (op : OrderMap) : Bool :=
  g.rankedProds.all fun sp =>
    (op.ordersOf sp.1).all fun i =>
      (List.range sp.2.2.length).all fun k =>
        g.rankedProds.all fun sq =>
          !(sp.2.2[k]? == some (.nt sq.2.1))
            || (trivSyms g b).contains sq.1
            || hasPrecExample neg sp.1 sq.1
            || hasAssocExample neg sp.1 sq.1 k
            || (op.ordersOf sq.1).any fun j =>
                 decide ((if (oa.positionsOf sp.1).contains k then i + 1 else i) ≤ j)

theorem fits_of_check {g : CFG} {neg : List TreeExample} {b : Bool} {oa : Oa} {op : OrderMap}
    (h : fitsB g neg b oa op = true) : Fits g neg b oa op := by
  intro s s' i k hi hchild htriv hneg
  unfold ChildAt at hchild
  obtain ⟨sp, hsp, hs1, sq, hsq, hs2, hrhs⟩ := hchild
  subst hs1
  subst hs2
  have hklt : k < sp.2.2.length := (List.getElem?_eq_some_iff.mp hrhs).1
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp h sp hsp) i hi) k (List.mem_range.mpr hklt)) sq hsq
  -- strip the four vacuous disjuncts
  rcases Bool.or_eq_true _ _ |>.mp h1 with h2 | hlast
  · rcases Bool.or_eq_true _ _ |>.mp h2 with h3 | hassoc
    · rcases Bool.or_eq_true _ _ |>.mp h3 with h4 | hprec
      · rcases Bool.or_eq_true _ _ |>.mp h4 with hne | htr
        · rw [show (sp.2.2[k]? == some (SigmaElt.nt sq.2.1)) = true by simp [hrhs]] at hne
          exact absurd hne (by simp)
        · exact absurd (by simpa using htr) htriv
      · simp only [hasPrecExample, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hprec
        obtain ⟨e, he, ⟨hp, ht⟩, hb⟩ := hprec
        refine absurd ⟨ht, hb, fun ha => ?_⟩ (hneg e he)
        simp only [TreeExample.isPrec, Bool.not_eq_true'] at hp
        exact absurd ha (by simp [hp])
    · simp only [hasAssocExample, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hassoc
      obtain ⟨e, he, ⟨⟨-, ht⟩, hb⟩, hidx⟩ := hassoc
      exact absurd ⟨ht, hb, fun _ => hidx.symm⟩ (hneg e he)
  · simp only [List.any_eq_true, decide_eq_true_eq] at hlast
    obtain ⟨j, hj, hij⟩ := hlast
    refine ⟨j, hj, fun l hl => ?_⟩
    by_cases hk : (oa.positionsOf sp.1).contains k = true
    · rw [if_pos hk] at hij
      simp only [oaFill, if_pos hk, GState.lvl.injEq] at hl
      omega
    · rw [if_neg hk] at hij
      simp only [oaFill, if_neg hk, GState.lvl.injEq] at hl
      omega

/-- `Covers` as a check. -/
def coversB (g : CFG) (b : Bool) (op : OrderMap) : Bool :=
  g.rankedProds.all fun sp => (trivSyms g b).contains sp.1 || !(op.ordersOf sp.1).isEmpty

theorem covers_of_check {g : CFG} {b : Bool} {op : OrderMap} (h : coversB g b op = true) :
    Covers g b op := by
  intro sp hsp htriv
  have := List.all_eq_true.mp h sp hsp
  rcases Bool.or_eq_true _ _ |>.mp this with h1 | h1
  · exact absurd (by simpa using h1) htriv
  · intro hnil
    rw [hnil] at h1
    simp at h1

/-- No start nonterminal is trivial, as a check. -/
def startsOK (g : CFG) (b : Bool) : Bool :=
  g.starts.all fun A => !(trivNts g b).contains A

theorem starts_of_check {g : CFG} {b : Bool} (h : startsOK g b = true) :
    ∀ A ∈ g.starts, A ∉ trivNts g b := by
  intro A hA hmem
  have := List.all_eq_true.mp h A hA
  rw [show (trivNts g b).contains A = true by simp [hmem]] at this
  exact Bool.noConfusion this

/-!
### Theorem 3.1(2) for the pipeline

`repairOnceSpec_correct` in `Greta.Soundness` takes both halves of Theorem 3.1 about the
pipeline's own output as hypotheses.  The second half can now be discharged by a check the
tool runs on its input.
-/

/-- The learned pair for a grammar and a set of rejected examples. -/
abbrev learnedPair (g : CFG) (neg : List TreeExample) (b : Bool) : Oa × OrderMap :=
  learnOaOp g neg (toMapOf (g.baseOrder b) neg) b

/-- The two decidable side conditions Theorem 3.1(2) needs of the pipeline. -/
def pipelineOK (g : CFG) (neg : List TreeExample) (b : Bool) : Bool :=
  learnedSpecB g neg b (learnedPair g neg b).1 (learnedPair g neg b).2
    && (g.highToLow (g.baseOrder b) (learnedPair g neg b).2).isEmpty

/--
**Theorem 3.1(2) for the pipeline.**  When the check passes on the input, the automaton
that Algorithm 3.1 followed by Algorithm 3.2 produces rejects every excluded tree.
-/
theorem genTA_sound₂_pipeline (g : CFG) (neg : List TreeExample) (b : Bool)
    (h : pipelineOK g neg b = true) :
    GenTASound₂ g neg (genTA g (learnedPair g neg b).1 (learnedPair g neg b).2 b) := by
  simp only [pipelineOK, Bool.and_eq_true, List.isEmpty_iff] at h
  exact genTA_sound₂ (learnedSpec_of_check h.1) h.2

/--
**Theorem 3.2 for the pipeline**, with Theorem 3.1(2) discharged by the check and only
statement (1) left as a hypothesis.  Compare `repairOnceSpec_correct`, which assumes both.
-/
theorem repairOnceSpec_correct_checked (g : CFG) (neg : List TreeExample) (b : Bool)
    (h : pipelineOK g neg b = true)
    (h₁ : GenTASound₁ g neg (genTA g (learnedPair g neg b).1 (learnedPair g neg b).2 b))
    (t : Tree) :
    (repairOnceSpec g neg b).Lang t ↔ g.repairedLang neg t = true :=
  greta_correct g neg _ h₁ (genTA_sound₂_pipeline g neg b h) t

/-!
### Theorem 3.2 for the pipeline, with every side condition discharged
-/

theorem repairOnceSpec_eq (g : CFG) (neg : List TreeExample) (b : Bool) :
    repairOnceSpec g neg b =
      prodTA (genTA g (learnedPair g neg b).1 (learnedPair g neg b).2 b) g.toTA := rfl

/-- Every side condition Theorem 3.2 needs of the pipeline, as a single check. -/
def pipelineFullOK (g : CFG) (neg : List TreeExample) (b : Bool) : Bool :=
  pipelineOK g neg b
    && fitsB g neg b (learnedPair g neg b).1 (learnedPair g neg b).2
    && coversB g b (learnedPair g neg b).2
    && startsOK g b

/--
**Theorem 3.2 for the pipeline.**  Learn `(O_a, O_p)` with Algorithm 3.1, build `A_r` with
Algorithm 3.2, intersect with `A_g` using the verified product: the result recognises
exactly `L_g \ L⁻`.  Every hypothesis of `greta_correct_of_spec` is discharged by
`pipelineFullOK`, a decidable check the tool can run on its own input.
-/
theorem repairOnceSpec_correct_pipeline (g : CFG) (neg : List TreeExample) (b : Bool)
    (h : pipelineFullOK g neg b = true) (t : Tree) :
    (repairOnceSpec g neg b).Lang t ↔ g.repairedLang neg t = true := by
  simp only [pipelineFullOK, pipelineOK, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨hspec, hAc⟩, hfits⟩, hcov⟩, hstart⟩ := h
  rw [repairOnceSpec_eq]
  exact greta_correct_of_spec (learnedSpec_of_check hspec) (fits_of_check hfits)
    (covers_of_check hcov) (starts_of_check hstart) hAc t

end Greta
