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

end Greta
