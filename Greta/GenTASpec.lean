/-
The shape of the automaton `GenTA` produces, and Theorem 3.1(2) proved from it.

The strategy is the one set out in `docs/proof-plan.md`: rather than reasoning about the
language of `A_r` directly, pin down its transitions (`mem_nonTrivTrans` and friends),
show that its ε-graph is the chain `e_0 ←ε e_1 ←ε … ←ε e_m`, and deduce that
ε-reachability between ordered states is `≤` on levels (`epsReach_lvl`).  After that every
argument is arithmetic on levels.

`LearnedSpec` collects what `LearnOaOp` has to deliver; `docs/divergences.md` explains
where each clause comes from.
-/
import Greta.Soundness

namespace Greta

/-! ### Reading off an order map -/

theorem OrderMap.mem_ordersOf {m : OrderMap} {s : Sym} {i : Nat} :
    i ∈ m.ordersOf s ↔ ∃ ss, (i, ss) ∈ m ∧ s ∈ ss := by
  simp only [OrderMap.ordersOf, List.mem_map, List.mem_filter, List.elem_iff]
  constructor
  · rintro ⟨p, ⟨hp, hs⟩, rfl⟩; exact ⟨p.2, hp, hs⟩
  · rintro ⟨ss, hp, hs⟩; exact ⟨(i, ss), ⟨hp, hs⟩, rfl⟩

theorem OrderMap.mem_symbols {m : OrderMap} {s : Sym} :
    s ∈ m.symbols ↔ ∃ p ∈ m, s ∈ p.2 := by
  simp [OrderMap.symbols, List.mem_dedup, List.mem_flatMap]

theorem OrderMap.mem_symbols_of_mem_ordersOf {m : OrderMap} {s : Sym} {i : Nat}
    (h : i ∈ m.ordersOf s) : s ∈ m.symbols := by
  obtain ⟨ss, hp, hs⟩ := OrderMap.mem_ordersOf.mp h
  exact OrderMap.mem_symbols.mpr ⟨(i, ss), hp, hs⟩

/-! ### Inverting the four groups of transitions -/

theorem mem_deltaGen {g : CFG} {tn : List Nonterminal} {target : GState} {fill : Nat → GState}
    {f : Sym} {tr : Transition GState} :
    deltaGen g tn target fill f = some tr ↔
      ∃ p, g.prodOfSym f = some p ∧ tr = ⟨target, f, fillRhs tn p.2 fill⟩ := by
  simp only [deltaGen, Option.map_eq_some_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

theorem mem_nonTrivTrans {g : CFG} {oa : Oa} {op : OrderMap} {tn : List Nonterminal}
    {tr : Transition GState} :
    tr ∈ nonTrivTrans g oa op tn ↔
      ∃ i ss, (i, ss) ∈ op ∧ ∃ s ∈ ss, ∃ p, g.prodOfSym s = some p ∧
        tr = ⟨.lvl i, s, fillRhs tn p.2 (oaFill oa s i)⟩ := by
  simp only [nonTrivTrans, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨oss, hoss, s, hs, hd⟩
    obtain ⟨p, hp, rfl⟩ := mem_deltaGen.mp hd
    exact ⟨oss.1, oss.2, hoss, s, hs, p, hp, rfl⟩
  · rintro ⟨i, ss, hp, s, hs, p, hpp, rfl⟩
    exact ⟨(i, ss), hp, s, hs, mem_deltaGen.mpr ⟨p, hpp, rfl⟩⟩

theorem mem_trivialTrans {g : CFG} {ts : List Sym} {tr : Transition GState} :
    tr ∈ trivialTrans g ts ↔
      ∃ s ∈ ts, ∃ p, g.prodOfSym s = some p ∧
        tr = ⟨.triv p.1, s, fillRhs [] p.2 (fun _ => .triv p.1)⟩ := by
  simp only [trivialTrans, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨s, hs, p, hp, rfl⟩; exact ⟨s, hs, p, hp, rfl⟩
  · rintro ⟨s, hs, p, hp, rfl⟩; exact ⟨s, hs, p, hp, rfl⟩

theorem mem_epsChain {m : Nat} {tr : Transition GState} :
    tr ∈ epsChain m ↔ ∃ i < m, tr = ⟨.lvl i, epsSym, [.state (.lvl (i + 1))]⟩ := by
  simp only [epsChain, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

/-! ### The symbols a transition can carry -/

theorem trivialSyms_ne_eps {g : CFG} {s : Sym} (h : s ∈ g.trivialSyms) : s ≠ epsSym := by
  simp only [CFG.trivialSyms, List.mem_filterMap] at h
  obtain ⟨sp, hsp, hif⟩ := h
  split at hif
  · simp only [Option.some.injEq] at hif
    exact hif ▸ CFG.rankedProds_sym_ne_eps hsp
  · simp at hif

theorem trivSyms_ne_eps {g : CFG} {b : Bool} {s : Sym} (h : s ∈ trivSyms g b) : s ≠ epsSym := by
  simp only [trivSyms] at h
  split at h
  · exact trivialSyms_ne_eps h
  · simp at h

theorem highToLow_sym_ne_eps {g : CFG} {obp op : OrderMap} {pr} (h : pr ∈ g.highToLow obp op) :
    pr.2.1 ≠ epsSym := by
  simp only [CFG.highToLow, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨sh, hsh, sl, _, hif⟩ := h
  split at hif
  · next => split at hif
            · simp only [Option.some.injEq] at hif; exact hif ▸ CFG.rankedProds_sym_ne_eps hsh
            · simp at hif
  · simp at hif

/-! ### The ε-graph of `A_r` is a chain -/

/-- `O_p` mentions only symbols of `g`; true of everything `baseOrder` and `learnOaOp` build. -/
def OrderOfGrammar (g : CFG) (op : OrderMap) : Prop :=
  ∀ s ∈ op.symbols, ∃ sp ∈ g.rankedProds, sp.1 = s

theorem OrderOfGrammar.sym_ne_eps {g : CFG} {op : OrderMap} (h : OrderOfGrammar g op)
    {s : Sym} (hs : s ∈ op.symbols) : s ≠ epsSym := by
  obtain ⟨sp, hsp, rfl⟩ := h s hs
  exact CFG.rankedProds_sym_ne_eps hsp

theorem genTA_epsEdges_iff {g : CFG} {oa : Oa} {op : OrderMap} {b : Bool}
    (hog : OrderOfGrammar g op) {x y : GState} :
    (x, y) ∈ (genTA g oa op b).epsEdges ↔
      ∃ i < op.maxOrder, x = .lvl (i + 1) ∧ y = .lvl i := by
  rw [mem_epsEdges]
  constructor
  · rintro ⟨tr, htr, hsym, hrhs, htgt⟩
    rw [genTA_trans] at htr
    rcases List.mem_append.mp htr with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · -- non-trivial transitions carry a symbol of the grammar
          obtain ⟨i, ss, hp, s, hs, p, _, rfl⟩ := mem_nonTrivTrans.mp h
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
    exact ⟨_, genTA_eps_mem hi, rfl, rfl, rfl⟩

/-- ε-reachability in `A_r` is `≤` on levels.  This is Lemma B.1 in usable form. -/
theorem epsReach_genTA {g : CFG} {oa : Oa} {op : OrderMap} {b : Bool}
    (hog : OrderOfGrammar g op) {x y : GState} (h : EpsReach (genTA g oa op b) x y) :
    x = y ∨ ∃ i j, x = .lvl j ∧ y = .lvl i ∧ i < j := by
  induction h with
  | refl => exact Or.inl rfl
  | @step x z y he _ ih =>
      obtain ⟨i, _, rfl, rfl⟩ := (genTA_epsEdges_iff hog).mp he
      rcases ih with rfl | ⟨i', j', hz, hy, hlt⟩
      · exact Or.inr ⟨i, i + 1, rfl, rfl, by omega⟩
      · simp only [GState.lvl.injEq] at hz
        subst hz
        exact Or.inr ⟨i', i + 1, rfl, hy, by omega⟩

/-- A trivial state is never ε-reachable from an ordered one, nor the other way round. -/
theorem epsReach_lvl_triv {g : CFG} {oa : Oa} {op : OrderMap} {b : Bool}
    (hog : OrderOfGrammar g op) {j : Nat} {A : Nonterminal}
    (h : EpsReach (genTA g oa op b) (.lvl j) (.triv A)) : False := by
  rcases epsReach_genTA hog h with heq | ⟨_, _, _, hy, _⟩
  · exact absurd heq (by simp)
  · exact absurd hy (by simp)

/-- Between ordered states, ε-reachability forces the target to sit at or above the source. -/
theorem epsReach_lvl {g : CFG} {oa : Oa} {op : OrderMap} {b : Bool}
    (hog : OrderOfGrammar g op) {i j : Nat}
    (h : EpsReach (genTA g oa op b) (.lvl j) (.lvl i)) : i ≤ j := by
  rcases epsReach_genTA hog h with heq | ⟨i', j', hx, hy, hlt⟩
  · simp only [GState.lvl.injEq] at heq; omega
  · simp only [GState.lvl.injEq] at hx hy; omega

/-! ### Inverting a run of `A_r` -/

/--
Every state `A_r` assigns to a node is either the level of the node's symbol in `O_p`,
with the node's children matched against that level's transition, or the state of a
trivial symbol.

The hypothesis `hAc` — `HighToLow` reports nothing — is the acyclicity side condition of
`docs/divergences.md`: a cycle transition targets a level unrelated to the symbol's own,
and the conclusion would be false without it.
-/
theorem evalT_genTA_inv {g : CFG} {oa : Oa} {op : OrderMap} {b : Bool}
    (hAc : g.highToLow (g.baseOrder b) op = []) {f : Sym} {ts : List Tree} {q : GState}
    (hq : q ∈ (genTA g oa op b).evalT (genTA g oa op b).epsTable (.node f ts)) :
    (∃ i, q = .lvl i ∧ i ∈ op.ordersOf f ∧ ∃ p, g.prodOfSym f = some p ∧
        (genTA g oa op b).matchAll (genTA g oa op b).epsTable ts
          (fillRhs (trivNts g b) p.2 (oaFill oa f i)) = true)
      ∨ (f ∈ trivSyms g b ∧ ∃ p, g.prodOfSym f = some p ∧ q = .triv p.1 ∧
          (genTA g oa op b).matchAll (genTA g oa op b).epsTable ts
            (fillRhs [] p.2 (fun _ => .triv p.1)) = true) := by
  obtain ⟨tr, htr, hsym, hm, htgt⟩ := TA.mem_evalT_node.mp hq
  simp only [TA.realTrans, List.mem_filter, bne_iff_ne, ne_eq, decide_eq_true_eq] at htr
  obtain ⟨htr, hne⟩ := htr
  rw [genTA_trans] at htr
  rcases List.mem_append.mp htr with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨i, ss, hp, s, hs, p, hpp, rfl⟩ := mem_nonTrivTrans.mp h
        subst hsym
        exact Or.inl ⟨i, htgt.symm, OrderMap.mem_ordersOf.mpr ⟨ss, hp, hs⟩, p, hpp, hm⟩
      · obtain ⟨s, hs, p, hpp, rfl⟩ := mem_trivialTrans.mp h
        subst hsym
        exact Or.inr ⟨hs, p, hpp, htgt.symm, hm⟩
    · obtain ⟨i, _, rfl⟩ := mem_epsChain.mp h
      exact absurd rfl hne
  · rw [cycleTrans, hAc] at h; simp at h

/-- Whichever transition a node uses, its children are matched against a filled right-hand
side — which is all the recursion in `occursIn_false` needs. -/
theorem evalT_genTA_children {g : CFG} {oa : Oa} {op : OrderMap} {b : Bool}
    (hAc : g.highToLow (g.baseOrder b) op = []) {f : Sym} {ts : List Tree} {q : GState}
    (hq : q ∈ (genTA g oa op b).evalT (genTA g oa op b).epsTable (.node f ts)) :
    ∃ (tn : List Nonterminal) (fill : Nat → GState) (p : Production),
      g.prodOfSym f = some p ∧
      (genTA g oa op b).matchAll (genTA g oa op b).epsTable ts (fillRhs tn p.2 fill) = true := by
  rcases evalT_genTA_inv hAc hq with ⟨i, -, -, p, hp, hm⟩ | ⟨-, p, hp, -, hm⟩
  · exact ⟨_, _, p, hp, hm⟩
  · exact ⟨_, _, p, hp, hm⟩

/-- The state a level-`i` transition sends a child to is never shallower than `i`. -/
theorem oaFill_level (oa : Oa) (s : Sym) (i k : Nat) :
    ∃ l, oaFill oa s i k = .lvl l ∧ i ≤ l := by
  unfold oaFill; split
  · exact ⟨i + 1, rfl, by omega⟩
  · exact ⟨i, rfl, Nat.le_refl i⟩

theorem oaFill_of_mem (oa : Oa) (s : Sym) (i k : Nat) (h : k ∈ oa.positionsOf s) :
    oaFill oa s i k = .lvl (i + 1) := by
  simp [oaFill, h]

/-! ### What `LearnOaOp` has to deliver -/

/--
The properties of the learned `(O_a, O_p)` that Theorem 3.1(2) uses.  Each clause is one
of the side conditions of `docs/divergences.md`; `S2` and `S4` there explain why they are
hypotheses rather than facts about `learnOaOp`.
-/
structure LearnedSpec (g : CFG) (neg : List TreeExample) (b : Bool) (oa : Oa) (op : OrderMap) :
    Prop where
  /-- `O_p` mentions only symbols of the grammar. -/
  ofGrammar : OrderOfGrammar g op
  /-- No symbol of a tree example is trivial: Section 3.1.1 excludes those from conflicts. -/
  notTrivial : ∀ e ∈ neg, e.top ∉ trivSyms g b ∧ e.bot ∉ trivSyms g b
  /-- A rejected precedence example puts its top strictly above its bottom. -/
  strat : ∀ e ∈ neg, e.isPrec = true → ∀ i ∈ op.ordersOf e.top, ∀ j ∈ op.ordersOf e.bot, j < i
  /-- A rejected associativity example is recorded in `O_a`. -/
  assocRecorded : ∀ e ∈ neg, e.isAssoc = true → e.idx ∈ oa.positionsOf e.top
  /-- A symbol in an associativity conflict sits at exactly one order. -/
  assocSingle : ∀ e ∈ neg, e.isAssoc = true →
    ∀ i ∈ op.ordersOf e.top, ∀ j ∈ op.ordersOf e.top, i = j

/-! ### Theorem 3.1(2) -/

section
variable {g : CFG} {neg : List TreeExample} {b : Bool} {oa : Oa} {op : OrderMap}

/-- The forbidden parent/child pattern never occurs at the root of an evaluable node. -/
theorem matchesHere_false (hspec : LearnedSpec g neg b oa op)
    (hAc : g.highToLow (g.baseOrder b) op = [])
    {e : TreeExample} (he : e ∈ neg) {k : Nat} (hk : e.isAssoc = true → k = e.idx)
    {f : Sym} {ts : List Tree} {q : GState}
    (hq : q ∈ (genTA g oa op b).evalT (genTA g oa op b).epsTable (.node f ts)) :
    (TreeExample.mk e.top e.bot k).matchesHere (.node f ts) = false := by
  by_contra hcon
  simp only [Bool.not_eq_false] at hcon
  obtain ⟨rfl, h, us, hget, rfl⟩ := TreeExample.matchesHere_node.mp hcon
  -- the node's own run
  rcases evalT_genTA_inv hAc hq with ⟨i, rfl, hi, p, hp, hm⟩ | ⟨htriv, _⟩
  case inr => exact (hspec.notTrivial e he).1 htriv
  -- the child sits at position `k` of the right-hand side
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hget
  have hlen : k < (fillRhs (trivNts g b) p.2 (oaFill oa e.top i)).length := by
    rw [← TA.matchAll_length ts _ hm]; exact hlt
  obtain ⟨Q, hQ, r, hr, hQr⟩ :=
    TA.matchAll_state_of_node hm hget (by rw [List.getElem?_eq_getElem hlen]; rfl)
  -- identify the state the transition demands there
  rw [getElem?_fillRhs] at hQ
  simp only [Option.map_eq_some_iff] at hQ
  obtain ⟨x, hx, hfill⟩ := hQ
  -- the child's own run
  have hbot := (hspec.notTrivial e he).2
  rcases evalT_genTA_inv hAc hr with ⟨j, rfl, hj, -⟩ | ⟨htriv, -⟩
  case inr => exact hbot htriv
  have hreach : EpsReach (genTA g oa op b) (.lvl j) Q :=
    ((genTA g oa op b).isEpsClosure_epsTable _ _).mp hQr
  cases x with
  | term a => simp [fillOne] at hfill
  | nt B =>
      simp only [fillOne] at hfill
      split at hfill
      · -- a trivial nonterminal keeps its own state, which no level can reach
        simp only [Beta.state.injEq] at hfill
        exact epsReach_lvl_triv hspec.ofGrammar (hfill ▸ hreach)
      · simp only [Beta.state.injEq] at hfill
        subst hfill
        obtain ⟨l, hl, hil⟩ := oaFill_level oa e.top i k
        rw [hl] at hreach
        have hlj : l ≤ j := epsReach_lvl hspec.ofGrammar hreach
        cases hassoc : e.isAssoc with
        | true =>
            have hidx : k = e.idx := hk hassoc
            have htb : e.top = e.bot := by
              simpa [TreeExample.isAssoc] using hassoc
            rw [hidx, oaFill_of_mem oa e.top i e.idx (hspec.assocRecorded e he hassoc)] at hl
            simp only [GState.lvl.injEq] at hl
            have : i = j := hspec.assocSingle e he hassoc i hi j (htb ▸ hj)
            omega
        | false =>
            have hprec : e.isPrec = true := by simp [TreeExample.isPrec, hassoc]
            have := hspec.strat e he hprec i hi j hj
            omega

/-- The forbidden pattern occurs nowhere in a tree the automaton accepts. -/
theorem occursIn_false (hspec : LearnedSpec g neg b oa op)
    (hAc : g.highToLow (g.baseOrder b) op = [])
    {e : TreeExample} (he : e ∈ neg) {k : Nat} (hk : e.isAssoc = true → k = e.idx) :
    ∀ t : Tree,
      (∀ f ts, t = .node f ts → ∃ q, q ∈ (genTA g oa op b).evalT (genTA g oa op b).epsTable t) →
      (TreeExample.mk e.top e.bot k).occursIn t = false := by
  intro t
  induction t using Tree.rec' with
  | hleaf a => intro _; simp [TreeExample.occursIn_leaf]
  | hnode f ts ih =>
      intro hev
      obtain ⟨q, hq⟩ := hev f ts rfl
      rw [TreeExample.occursIn_node, matchesHere_false hspec hAc he hk hq, Bool.false_or]
      refine TreeExample.occursInAny_false _ ts fun u hu => ih u hu ?_
      -- every child that is a node is itself evaluable
      intro f' us hu'
      subst hu'
      obtain ⟨tn, fill, p, -, hm⟩ := evalT_genTA_children hAc hq
      obtain ⟨n, hn, hnu⟩ := List.mem_iff_getElem.mp hu
      have hget : ts[n]? = some (.node f' us) := by
        rw [List.getElem?_eq_getElem hn, hnu]
      have hlen : n < (fillRhs tn p.2 fill).length := by
        rw [← TA.matchAll_length ts _ hm]; exact hn
      obtain ⟨Q, -, r, hr, -⟩ :=
        TA.matchAll_state_of_node hm hget (by rw [List.getElem?_eq_getElem hlen]; rfl)
      exact ⟨r, hr⟩

/--
**Theorem 3.1(2).**  Under the side conditions of `LearnedSpec` and acyclicity of the
symbol order, the automaton `GenTA` produces rejects every tree the user excluded:
`L_r ∩ L⁻ = ∅`.
-/
theorem genTA_sound₂ (hspec : LearnedSpec g neg b oa op)
    (hAc : g.highToLow (g.baseOrder b) op = []) :
    GenTASound₂ g neg (genTA g oa op b) := by
  intro t ht
  simp only [CFG.excludedLang]
  by_contra hcon
  simp only [not_forall, List.any_eq_true, Bool.not_eq_false] at hcon
  obtain ⟨e, he, hex⟩ := hcon
  -- the root of an accepted tree carries a state
  have hev : ∀ f ts, t = .node f ts →
      ∃ q, q ∈ (genTA g oa op b).evalT (genTA g oa op b).epsTable t := by
    intro f ts hts
    simp only [TA.Lang, TA.accepts, List.any_eq_true] at ht
    obtain ⟨q, hq, -⟩ := ht
    exact ⟨q, hq⟩
  simp only [CFG.excludedBy] at hex
  split at hex
  · -- associativity-related: the pattern uses the example's own index
    have key : e.occursIn t = false := occursIn_false hspec hAc he (fun _ => rfl) t hev
    simp only [CFG.parseTreesOf, Bool.and_eq_true, key] at hex
    simp at hex
  · -- precedence-related: the pattern may use any child position
    next hassoc =>
      simp only [List.any_eq_true] at hex
      obtain ⟨n, -, hn⟩ := hex
      simp only [CFG.parseTreesOf, Bool.and_eq_true] at hn
      have key : (TreeExample.mk e.top e.bot n).occursIn t = false :=
        occursIn_false hspec hAc he (k := n) (fun h => absurd h hassoc) t hev
      simp only [key] at hn
      simp at hn

end

/-! ### Theorem 3.1(1)

For the other half a run has to be *built*, which needs the ε-chain in the other direction
and a guarantee that a child symbol always has a level at or above the one its parent's
transition demands.  The latter is `Fits`, the local condition `S6` of
`docs/divergences.md` discusses.
-/

theorem mem_genTA_epsEdges {g : CFG} {oa : Oa} {op : OrderMap} {b : Bool} {i : Nat}
    (hi : i < op.maxOrder) :
    ((GState.lvl (i + 1)), (GState.lvl i)) ∈ (genTA g oa op b).epsEdges :=
  mem_epsEdges.mpr ⟨_, genTA_eps_mem hi, rfl, rfl, rfl⟩

private theorem epsReach_add {g : CFG} {oa : Oa} {op : OrderMap} {b : Bool} :
    ∀ (d l : Nat), l + d ≤ op.maxOrder →
      EpsReach (genTA g oa op b) (.lvl (l + d)) (.lvl l)
  | 0,     l, _ => .refl _
  | d + 1, l, h =>
      (EpsReach.step (mem_genTA_epsEdges (i := l + d) (by omega)) (.refl _)).trans
        (epsReach_add d l (by omega))

/-- The ε-chain promotes any level to any shallower one. -/
theorem epsReach_of_le {g : CFG} {oa : Oa} {op : OrderMap} {b : Bool} {l j : Nat}
    (hlj : l ≤ j) (hj : j ≤ op.maxOrder) : EpsReach (genTA g oa op b) (.lvl j) (.lvl l) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = l + d := ⟨j - l, by omega⟩
  exact epsReach_add d l hj

/-! ### Trivial symbols and their nonterminals -/

theorem trivSyms_prod {g : CFG} {b : Bool} {sp : Sym × Production}
    (hsp : sp ∈ g.rankedProds) (h : sp.1 ∈ trivSyms g b) : ∃ a, sp.2.2 = [.term a] := by
  simp only [trivSyms] at h
  split at h
  · simp only [CFG.trivialSyms, List.mem_filterMap] at h
    obtain ⟨sq, hsq, hif⟩ := h
    split at hif
    · next hcond =>
        simp only [Option.some.injEq] at hif
        have : sq = sp := CFG.rankedProds_inj hsq hsp hif
        subst this
        have := hcond.1
        simp only [CFG.isSingleTerminalProd] at this
        split at this
        · next a heq => exact ⟨a, heq⟩
        · simp at this
    · simp at hif
  · simp at h

theorem mem_trivNts_of_trivSyms {g : CFG} {b : Bool} {sp : Sym × Production}
    (hsp : sp ∈ g.rankedProds) (h : sp.1 ∈ trivSyms g b) : sp.2.1 ∈ trivNts g b := by
  simp only [trivNts, List.mem_dedup, List.mem_filterMap]
  exact ⟨sp.1, h, by rw [CFG.prodOfSym_eq hsp]; rfl⟩

theorem trivSyms_of_mem_trivNts {g : CFG} {b : Bool} {A : Nonterminal}
    (hA : A ∈ trivNts g b) {sp : Sym × Production} (hsp : sp ∈ g.rankedProds)
    (hlhs : sp.2.1 = A) : sp.1 ∈ trivSyms g b := by
  simp only [trivNts, List.mem_dedup, List.mem_filterMap] at hA
  obtain ⟨f, hf, hmap⟩ := hA
  simp only [trivSyms] at hf ⊢
  split at hf
  · next hb =>
      rw [if_pos hb]
      -- `f` is trivial, so every production of its left-hand side is a single terminal
      simp only [CFG.trivialSyms, List.mem_filterMap] at hf ⊢
      obtain ⟨sq, hsq, hif⟩ := hf
      split at hif
      · next hcond =>
          simp only [Option.some.injEq] at hif
          subst hif
          rw [CFG.prodOfSym_eq hsq] at hmap
          simp only [Option.map_some, Option.some.injEq] at hmap
          refine ⟨sp, hsp, ?_⟩
          have hall := hcond.2
          have hprod : sp.2 ∈ g.prods := by
            obtain ⟨n, hn, rfl⟩ := CFG.mem_rankedProds_iff.mp hsp
            exact List.mem_of_getElem? (i := n) (by
              simp only [List.getElem?_eq_getElem hn])
          have hsingle : CFG.isSingleTerminalProd sp.2 = true := by
            have : sp.2 ∈ g.prods.filter fun p => p.1 == sq.2.1 := by
              simp only [List.mem_filter, beq_iff_eq]
              exact ⟨hprod, by rw [hlhs, hmap]⟩
            exact List.all_eq_true.mp hall _ this
          rw [if_pos ⟨hsingle, by
            have : sp.2.1 = sq.2.1 := by rw [hlhs, hmap]
            rw [this]; exact hall⟩]
      · simp at hif
  · simp at hf

/-! ### The local condition Theorem 3.1(1) needs -/

/--
`S6` of `docs/divergences.md`: a symbol that may legitimately sit at child position `k` of
an `s`-node at level `i` has a level at or above the one the transition demands.
-/
def Fits (g : CFG) (neg : List TreeExample) (b : Bool) (oa : Oa) (op : OrderMap) : Prop :=
  ∀ (s s' : Sym) (i k : Nat), i ∈ op.ordersOf s →
    (∃ sp ∈ g.rankedProds, sp.1 = s') → s' ∉ trivSyms g b →
    (∀ e ∈ neg, ¬(e.top = s ∧ e.bot = s' ∧ (e.isAssoc = true → k = e.idx))) →
    ∃ j ∈ op.ordersOf s', ∀ l, oaFill oa s i k = .lvl l → l ≤ j

/-- No forbidden pattern occurs in `t`, at any child position the grammar admits. -/
def NoPattern (neg : List TreeExample) (t : Tree) : Prop :=
  ∀ e ∈ neg, ∀ k < e.top.rank, (e.isAssoc = true → k = e.idx) →
    (TreeExample.mk e.top e.bot k).occursIn t = false

theorem NoPattern.subtree {neg : List TreeExample} {f : Sym} {ts : List Tree} {u : Tree}
    (h : NoPattern neg (.node f ts)) (hu : u ∈ ts) : NoPattern neg u :=
  fun e he k hk hidx => TreeExample.occursIn_of_mem (h e he k hk hidx) hu

/-! ### Building a run -/

section
variable {g : CFG} {neg : List TreeExample} {b : Bool} {oa : Oa} {op : OrderMap}

/--
Every parse tree that no tree example rules out is accepted by `A_r`, at any level of its
root symbol.  This is the level assignment of Step 6 of `docs/proof-plan.md`, built
top-down: `Fits` supplies a level for each child at or below the one its parent's
transition demands, and the ε-chain promotes it.
-/
theorem run_exists (hfits : Fits g neg b oa op) :
    ∀ (t : Tree) (A : Nonterminal), g.isParseTreeOf A t = true → NoPattern neg t →
      (A ∈ trivNts g b →
        (GState.triv A) ∈ (genTA g oa op b).evalT (genTA g oa op b).epsTable t) ∧
      (A ∉ trivNts g b → ∀ f ts, t = .node f ts → ∀ i ∈ op.ordersOf f,
        (GState.lvl i) ∈ (genTA g oa op b).evalT (genTA g oa op b).epsTable t) := by
  set Ar := genTA g oa op b with hAr
  intro t
  induction t using Tree.rec' with
  | hleaf a => intro A hpt _; simp at hpt
  | hnode f ts ih =>
      intro A hpt hnp
      obtain ⟨sp, hsp, rfl, hlhs, hmr⟩ := CFG.isParseTreeOf_node.mp hpt
      have hprod : g.prodOfSym sp.1 = some sp.2 := CFG.prodOfSym_eq hsp
      have hrank : sp.1.rank = sp.2.2.length := by
        obtain ⟨n, hn, heq⟩ := CFG.mem_rankedProds_iff.mp hsp
        rw [heq]; rfl
      refine ⟨fun htriv => ?_, fun hntriv f' ts' heq i hi => ?_⟩
      · -- the root symbol is trivial, so its production is a single terminal
        have hft : sp.1 ∈ trivSyms g b := trivSyms_of_mem_trivNts htriv hsp hlhs
        obtain ⟨a, ha⟩ := trivSyms_prod hsp hft
        have hlen : ts.length = 1 := by rw [CFG.matchRhs_length ts _ hmr, ha]; rfl
        have htr : (⟨.triv sp.2.1, sp.1, fillRhs [] sp.2.2 (fun _ => .triv sp.2.1)⟩ :
            Transition GState) ∈ Ar.realTrans := by
          simp only [hAr, TA.realTrans, List.mem_filter, bne_iff_ne, ne_eq, decide_eq_true_eq,
            genTA_trans]
          exact ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
            (mem_trivialTrans.mpr ⟨sp.1, hft, sp.2, hprod, rfl⟩))),
            CFG.rankedProds_sym_ne_eps hsp⟩
        refine hlhs ▸ TA.mem_evalT_node.mpr ⟨_, htr, rfl, ?_, rfl⟩
        refine TA.matchAll_of_forall ts _ (by simp [ha, hlen]) fun k u β hu hβ => ?_
        rw [getElem?_fillRhs, ha] at hβ
        cases k with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hβ
            rw [← hβ]
            simpa [fillOne] using CFG.matchRhs_get ts _ hmr 0 u (.term a) hu (by rw [ha]; rfl)
        | succ k => simp at hβ
      · -- the root symbol is not trivial: use its level-`i` transition
        injection heq with hfeq htseq
        subst hfeq; subst htseq
        have hnt : sp.1 ∉ trivSyms g b := fun hc => hntriv (hlhs ▸ mem_trivNts_of_trivSyms hsp hc)
        obtain ⟨ss, hss, hmem⟩ := OrderMap.mem_ordersOf.mp hi
        have htr : (⟨.lvl i, sp.1, fillRhs (trivNts g b) sp.2.2 (oaFill oa sp.1 i)⟩ :
            Transition GState) ∈ Ar.realTrans := by
          simp only [hAr, TA.realTrans, List.mem_filter, bne_iff_ne, ne_eq, decide_eq_true_eq,
            genTA_trans]
          exact ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (mem_nonTrivTrans.mpr ⟨i, ss, hss, sp.1, hmem, sp.2, hprod, rfl⟩))),
            CFG.rankedProds_sym_ne_eps hsp⟩
        refine TA.mem_evalT_node.mpr ⟨_, htr, rfl, ?_, rfl⟩
        refine TA.matchAll_of_forall ts _ (by simp [CFG.matchRhs_length ts _ hmr]) ?_
        intro k u β hu hβ
        rw [getElem?_fillRhs] at hβ
        simp only [Option.map_eq_some_iff] at hβ
        obtain ⟨x, hx, hfill⟩ := hβ
        have hmatch := CFG.matchRhs_get ts _ hmr k u x hu hx
        have humem : u ∈ ts := List.mem_of_getElem? hu
        have hnpu : NoPattern neg u := hnp.subtree humem
        cases x with
        | term a => rw [← hfill]; simpa [fillOne] using hmatch
        | nt B =>
            simp only [fillOne] at hfill
            split at hfill
            · -- a trivial nonterminal keeps its own state
              next hBt =>
                rw [← hfill]
                exact ⟨.triv B, ((ih u humem B hmatch hnpu).1 (by simpa using hBt)),
                  Ar.mem_closeFrom_self _⟩
            · -- an ordinary nonterminal: place the child with `Fits`
              next hBt =>
                rw [← hfill]
                have hBt' : B ∉ trivNts g b := by simpa using hBt
                cases u with
                | leaf c => simp at hmatch
                | node f' us =>
                    obtain ⟨sq, hsq, rfl, hlhs', hmr'⟩ := CFG.isParseTreeOf_node.mp hmatch
                    have hsq' : sq.1 ∉ trivSyms g b :=
                      fun hc => hBt' (hlhs' ▸ mem_trivNts_of_trivSyms hsq hc)
                    have hklt : k < sp.1.rank := by
                      rw [hrank]
                      obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hx
                      exact h
                    have hfree : ∀ e ∈ neg,
                        ¬(e.top = sp.1 ∧ e.bot = sq.1 ∧ (e.isAssoc = true → k = e.idx)) := by
                      rintro e he ⟨htop, hbot, hidx⟩
                      have hno := hnp e he k (by rw [htop]; exact hklt) hidx
                      rw [TreeExample.occursIn_node, Bool.or_eq_false_iff] at hno
                      have hyes : (TreeExample.mk e.top e.bot k).matchesHere
                          (.node sp.1 ts) = true :=
                        TreeExample.matchesHere_node.mpr ⟨htop.symm, sq.1, us, hu, hbot.symm⟩
                      rw [hyes] at hno
                      simp at hno
                    obtain ⟨j, hj, hle⟩ := hfits sp.1 sq.1 i k hi ⟨sq, hsq, rfl⟩ hsq' hfree
                    obtain ⟨l, hl, -⟩ := oaFill_level oa sp.1 i k
                    obtain ⟨ss', hss', -⟩ := OrderMap.mem_ordersOf.mp hj
                    refine ⟨.lvl j, (ih _ humem B hmatch hnpu).2 hBt' _ _ rfl j hj, ?_⟩
                    rw [hl]
                    exact (Ar.isEpsClosure_epsTable _ _).mpr
                      (epsReach_of_le (hle l hl) (OrderMap.le_maxOrder hss'))

/-- `O_p` gives every non-trivial symbol of the grammar a level. -/
def Covers (g : CFG) (b : Bool) (op : OrderMap) : Prop :=
  ∀ sp ∈ g.rankedProds, sp.1 ∉ trivSyms g b → op.ordersOf sp.1 ≠ []

private theorem any_false {α : Type} {l : List α} {p : α → Bool} (h : l.any p = false)
    {x : α} (hx : x ∈ l) : p x = false := by
  by_contra hc
  simp only [Bool.not_eq_false] at hc
  rw [List.any_eq_true.mpr ⟨x, hx, hc⟩] at h
  simp at h

/-- A tree the user did not exclude carries no forbidden pattern. -/
theorem noPattern_of_repaired {t : Tree} (hrep : g.repairedLang neg t = true) :
    NoPattern neg t := by
  simp only [CFG.repairedLang, Bool.and_eq_true, Bool.not_eq_true'] at hrep
  obtain ⟨hpt, hexl⟩ := hrep
  intro e he k hk hidx
  have hex : g.excludedBy e t = false := any_false hexl he
  simp only [CFG.excludedBy] at hex
  split at hex
  · next hassoc =>
      rw [hidx hassoc]
      simp only [CFG.parseTreesOf, Bool.and_eq_false_iff] at hex
      rcases hex with h | h
      · exact absurd hpt (by rw [h]; simp)
      · exact h
  · have hk' := any_false hex (List.mem_range.mpr hk)
    simp only [CFG.parseTreesOf, Bool.and_eq_false_iff] at hk'
    rcases hk' with h | h
    · exact absurd hpt (by rw [h]; simp)
    · exact h

/--
**Theorem 3.1(1).**  Under `Fits`, `Covers` and the assumption that no start nonterminal
is trivial, the automaton `GenTA` produces keeps every parse tree the user did not
exclude: `L_r ⊇ L_g \ L⁻`.
-/
theorem genTA_sound₁ (hfits : Fits g neg b oa op) (hcov : Covers g b op)
    (hstart : ∀ A ∈ g.starts, A ∉ trivNts g b) :
    GenTASound₁ g neg (genTA g oa op b) := by
  intro t hrep
  have hnp : NoPattern neg t := noPattern_of_repaired hrep
  simp only [CFG.repairedLang, Bool.and_eq_true] at hrep
  obtain ⟨hpt, -⟩ := hrep
  simp only [CFG.isParseTree, List.any_eq_true] at hpt
  obtain ⟨A, hA, hptA⟩ := hpt
  -- a complete parse tree is a node
  cases t with
  | leaf a => simp at hptA
  | node f ts =>
      obtain ⟨sp, hsp, rfl, hlhs, -⟩ := CFG.isParseTreeOf_node.mp hptA
      have hAtriv : A ∉ trivNts g b := hstart A hA
      have hnt : sp.1 ∉ trivSyms g b :=
        fun hc => hAtriv (hlhs ▸ mem_trivNts_of_trivSyms hsp hc)
      obtain ⟨i, hi⟩ : ∃ i, i ∈ op.ordersOf sp.1 := by
        have hne := hcov sp hsp hnt
        cases hords : op.ordersOf sp.1 with
        | nil => exact absurd hords hne
        | cons j js => exact ⟨j, by simp⟩
      have hrun := (run_exists hfits _ A hptA hnp).2 hAtriv sp.1 ts rfl i hi
      obtain ⟨ss, hss, -⟩ := OrderMap.mem_ordersOf.mp hi
      simp only [TA.Lang, TA.accepts, List.any_eq_true, decide_eq_true_eq]
      exact ⟨.lvl i, hrun, .lvl 0,
        ((genTA g oa op b).isEpsClosure_epsTable _ _).mpr
          (epsReach_of_le (Nat.zero_le i) (OrderMap.le_maxOrder hss)),
        by simp⟩

/--
**Theorem 3.1.**  Both halves, under the side conditions of `docs/divergences.md`.
-/
theorem genTA_sound (hspec : LearnedSpec g neg b oa op) (hfits : Fits g neg b oa op)
    (hcov : Covers g b op) (hstart : ∀ A ∈ g.starts, A ∉ trivNts g b)
    (hAc : g.highToLow (g.baseOrder b) op = []) :
    GenTASound₁ g neg (genTA g oa op b) ∧ GenTASound₂ g neg (genTA g oa op b) :=
  ⟨genTA_sound₁ hfits hcov hstart, genTA_sound₂ hspec hAc⟩

/--
**Theorem 3.2, with Theorem 3.1 discharged.**  One round of repair, done with the verified
product construction, recognises exactly `L_g \ L⁻`.
-/
theorem greta_correct_of_spec (hspec : LearnedSpec g neg b oa op) (hfits : Fits g neg b oa op)
    (hcov : Covers g b op) (hstart : ∀ A ∈ g.starts, A ∉ trivNts g b)
    (hAc : g.highToLow (g.baseOrder b) op = []) (t : Tree) :
    (prodTA (genTA g oa op b) g.toTA).Lang t ↔ g.repairedLang neg t = true :=
  greta_correct g neg _ (genTA_sound₁ hfits hcov hstart) (genTA_sound₂ hspec hAc) t

end

end Greta
