/-
**Theorem 3.1 for the learner Greta ships.**

`Greta.GenTASpec` proves Theorem 3.1 about `genTA`, the automaton Algorithm 3.2 builds from
the order Algorithm 3.1 *as printed* produces.  Statement (1) of that theorem is false for
any grammar with a bracketing production (`docs/divergences.md`, §8): the published learner
copies a non-conflicting symbol to every order, and Algorithm 3.2 then fills its
right-hand side with that order, so a bracketed expression can never hold an operator of
lower precedence than its context.

`Greta.RefLearn` formalises what `learner.ml` does instead: the symbol is placed once, and
`learn_ta` gives it a back-edge to the order it came from.  This file proves Theorem 3.1 for
that automaton, in both halves, and Theorem 3.2 with it.  The proofs follow
`Greta.GenTASpec` step for step; only the fill function changes, and with it two things.

* **Statement (1) becomes provable.**  `RefFits` is `Fits` with `refOaFill` in place of
  `oaFill`, so a special loop symbol demands its children at the order its back-edge points
  at rather than at its own.  `refFitsB` decides it, and it holds on the grammars where
  `fitsB` fails, the paper's Section 1 grammar among them.
* **Statement (2) needs one condition more.**  `SpecsAvoidTops`: no symbol that a rejected
  example names at the top carries a back-edge.  That is automatic — the special loop
  symbols are the ones *no* conflict group holds, and the top of an example is always in a
  group — and it is decidable, so the tool checks it rather than assuming it.
-/
import Greta.RefLearn

namespace Greta

section
variable {g : CFG} {neg : List TreeExample} {b : Bool} {oa : Oa} {specs : SpecMap}
  {op : OrderMap}

/-! ### The fill function of `learn_ta` -/

/-- A back-edge still names a level, so a run always has a state to aim at. -/
theorem refOaFill_level' (oa : Oa) (specs : SpecMap) (s : Sym) (i k : Nat) :
    ∃ l, refOaFill oa specs s i k = .lvl l := by
  unfold refOaFill; split
  · exact ⟨i + 1, rfl⟩
  · exact ⟨_, rfl⟩

/-- Where a symbol carries no back-edge, `learn_ta` fills exactly as Algorithm 3.2 does. -/
theorem refOaFill_eq_oaFill {s : Sym} (h : specs.lookup s = none) (oa : Oa) (i k : Nat) :
    refOaFill oa specs s i k = oaFill oa s i k := by
  unfold refOaFill oaFill; split
  · rfl
  · rw [h]; rfl

/--
No symbol that a rejected example names at the top carries a back-edge.  The special loop
symbols are exactly those no conflict group holds, and the top of an example is always in a
group, so this holds of the pipeline; `refPipelineOK` checks it.
-/
def SpecsAvoidTops (neg : List TreeExample) (specs : SpecMap) : Prop :=
  ∀ e ∈ neg, specs.lookup e.top = none

/-- For such a symbol the fill is the published one, so it is never shallower than `i`. -/
theorem refOaFill_level {s : Sym} (h : specs.lookup s = none) (oa : Oa) (i k : Nat) :
    ∃ l, refOaFill oa specs s i k = .lvl l ∧ i ≤ l := by
  rw [refOaFill_eq_oaFill h]; exact oaFill_level oa s i k

theorem refOaFill_of_mem {s : Sym} (h : specs.lookup s = none) (oa : Oa) (i k : Nat)
    (hk : k ∈ oa.positionsOf s) : refOaFill oa specs s i k = .lvl (i + 1) := by
  rw [refOaFill_eq_oaFill h]; exact oaFill_of_mem oa s i k hk

/-- The ε-graph of the shipped `A_r` is the same chain, so the same two facts hold of it. -/
theorem refEpsReach_genTA (hog : OrderOfGrammar g op) {x y : GState}
    (h : EpsReach (refGenTA g oa specs op b) x y) :
    x = y ∨ ∃ i j, x = .lvl j ∧ y = .lvl i ∧ i < j := by
  induction h with
  | refl => exact Or.inl rfl
  | @step x z y he _ ih =>
      obtain ⟨i, _, rfl, rfl⟩ := (refGenTA_epsEdges_iff hog).mp he
      rcases ih with rfl | ⟨i', j', hz, hy, hlt⟩
      · exact Or.inr ⟨i, i + 1, rfl, rfl, by omega⟩
      · simp only [GState.lvl.injEq] at hz
        subst hz
        exact Or.inr ⟨i', i + 1, rfl, hy, by omega⟩

theorem refEpsReach_lvl_triv (hog : OrderOfGrammar g op) {j : Nat} {A : Nonterminal}
    (h : EpsReach (refGenTA g oa specs op b) (.lvl j) (.triv A)) : False := by
  rcases refEpsReach_genTA hog h with heq | ⟨_, _, _, hy, _⟩
  · exact absurd heq (by simp)
  · exact absurd hy (by simp)

/--
What statement (1) needs of the shipped learner: a symbol that may legitimately sit at
child position `k` of an `s`-node at level `i` has a level at or above the one the
transition demands — where, for a symbol with a back-edge, that is the order the back-edge
points at.
-/
def RefFits (g : CFG) (neg : List TreeExample) (b : Bool) (oa : Oa) (specs : SpecMap)
    (op : OrderMap) : Prop :=
  ∀ (s s' : Sym) (i k : Nat), i ∈ op.ordersOf s →
    ChildAt g s s' k → s' ∉ trivSyms g b →
    (∀ e ∈ neg, ¬(e.top = s ∧ e.bot = s' ∧ (e.isAssoc = true → k = e.idx))) →
    ∃ j ∈ op.ordersOf s', ∀ l, refOaFill oa specs s i k = .lvl l → l ≤ j

/-! ### Inverting a run of the shipped `A_r` -/

theorem evalT_refGenTA_inv {g : CFG} {oa : Oa} {op : OrderMap} {b : Bool}
    (hAc : g.highToLow (g.baseOrder b) op = []) {f : Sym} {ts : List Tree} {q : GState}
    (hq : q ∈ (refGenTA g oa specs op b).evalT (refGenTA g oa specs op b).epsTable (.node f ts)) :
    (∃ i, q = .lvl i ∧ i ∈ op.ordersOf f ∧ ∃ p, g.prodOfSym f = some p ∧
        (refGenTA g oa specs op b).matchAll (refGenTA g oa specs op b).epsTable ts
          (fillRhs (trivNts g b) p.2 (refOaFill oa specs f i)) = true)
      ∨ (f ∈ trivSyms g b ∧ ∃ p, g.prodOfSym f = some p ∧ q = .triv p.1 ∧
          (refGenTA g oa specs op b).matchAll (refGenTA g oa specs op b).epsTable ts
            (fillRhs [] p.2 (fun _ => .triv p.1)) = true) := by
  obtain ⟨tr, htr, hsym, hm, htgt⟩ := TA.mem_evalT_node.mp hq
  simp only [TA.realTrans, List.mem_filter, bne_iff_ne, ne_eq, decide_eq_true_eq] at htr
  obtain ⟨htr, hne⟩ := htr
  rw [refGenTA_trans] at htr
  rcases List.mem_append.mp htr with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨i, ss, hp, s, hs, p, hpp, rfl⟩ := mem_refNonTrivTrans.mp h
        subst hsym
        exact Or.inl ⟨i, htgt.symm, OrderMap.mem_ordersOf.mpr ⟨ss, hp, hs⟩, p, hpp, hm⟩
      · obtain ⟨s, hs, p, hpp, rfl⟩ := mem_trivialTrans.mp h
        subst hsym
        exact Or.inr ⟨hs, p, hpp, htgt.symm, hm⟩
    · obtain ⟨i, _, rfl⟩ := mem_epsChain.mp h
      exact absurd rfl hne
  · rw [cycleTrans, hAc] at h; simp at h

/-- Whichever transition a node uses, its children are matched against a filled right-hand
side — all the recursion in `refOccursIn_false` needs. -/
theorem evalT_refGenTA_children (hAc : g.highToLow (g.baseOrder b) op = []) {f : Sym}
    {ts : List Tree} {q : GState}
    (hq : q ∈ (refGenTA g oa specs op b).evalT (refGenTA g oa specs op b).epsTable
      (.node f ts)) :
    ∃ (tn : List Nonterminal) (fill : Nat → GState) (p : Production),
      g.prodOfSym f = some p ∧
      (refGenTA g oa specs op b).matchAll (refGenTA g oa specs op b).epsTable ts
        (fillRhs tn p.2 fill) = true := by
  rcases evalT_refGenTA_inv hAc hq with ⟨i, -, -, p, hp, hm⟩ | ⟨-, p, hp, -, hm⟩
  · exact ⟨_, _, p, hp, hm⟩
  · exact ⟨_, _, p, hp, hm⟩

/-! ### Theorem 3.1(2) for the shipped automaton -/

/-- The forbidden parent/child pattern never occurs at the root of an evaluable node. -/
theorem refMatchesHere_false (hspec : LearnedSpec g neg b oa op)
    (hns : SpecsAvoidTops neg specs)
    (hAc : g.highToLow (g.baseOrder b) op = [])
    {e : TreeExample} (he : e ∈ neg) {k : Nat} (hk : e.isAssoc = true → k = e.idx)
    {f : Sym} {ts : List Tree} {q : GState}
    (hq : q ∈ (refGenTA g oa specs op b).evalT (refGenTA g oa specs op b).epsTable (.node f ts)) :
    (TreeExample.mk e.top e.bot k).matchesHere (.node f ts) = false := by
  by_contra hcon
  simp only [Bool.not_eq_false] at hcon
  obtain ⟨rfl, h, us, hget, rfl⟩ := TreeExample.matchesHere_node.mp hcon
  -- the node's own run
  rcases evalT_refGenTA_inv hAc hq with ⟨i, rfl, hi, p, hp, hm⟩ | ⟨htriv, _⟩
  case inr => exact (hspec.notTrivial e he).1 htriv
  -- the child sits at position `k` of the right-hand side
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hget
  have hlen : k < (fillRhs (trivNts g b) p.2 (refOaFill oa specs e.top i)).length := by
    rw [← TA.matchAll_length ts _ hm]; exact hlt
  obtain ⟨Q, hQ, r, hr, hQr⟩ :=
    TA.matchAll_state_of_node hm hget (by rw [List.getElem?_eq_getElem hlen]; rfl)
  -- identify the state the transition demands there
  rw [getElem?_fillRhs] at hQ
  simp only [Option.map_eq_some_iff] at hQ
  obtain ⟨x, hx, hfill⟩ := hQ
  -- the child's own run
  have hbot := (hspec.notTrivial e he).2
  rcases evalT_refGenTA_inv hAc hr with ⟨j, rfl, hj, -⟩ | ⟨htriv, -⟩
  case inr => exact hbot htriv
  have hreach : EpsReach (refGenTA g oa specs op b) (.lvl j) Q :=
    ((refGenTA g oa specs op b).isEpsClosure_epsTable _ _).mp hQr
  cases x with
  | term a => simp [fillOne] at hfill
  | nt B =>
      simp only [fillOne] at hfill
      split at hfill
      · -- a trivial nonterminal keeps its own state, which no level can reach
        simp only [Beta.state.injEq] at hfill
        exact refEpsReach_lvl_triv hspec.ofGrammar (hfill ▸ hreach)
      · simp only [Beta.state.injEq] at hfill
        subst hfill
        obtain ⟨l, hl, hil⟩ := refOaFill_level (hns e he) oa i k
        rw [hl] at hreach
        have hlj : l ≤ j := refEpsReach_lvl hspec.ofGrammar hreach
        cases hassoc : e.isAssoc with
        | true =>
            have hidx : k = e.idx := hk hassoc
            have htb : e.top = e.bot := by
              simpa [TreeExample.isAssoc] using hassoc
            rw [hidx, refOaFill_of_mem (hns e he) oa i e.idx
              (hspec.assocRecorded e he hassoc)] at hl
            simp only [GState.lvl.injEq] at hl
            have : i = j := hspec.assocSingle e he hassoc i hi j (htb ▸ hj)
            omega
        | false =>
            have hprec : e.isPrec = true := by simp [TreeExample.isPrec, hassoc]
            have := hspec.strat e he hprec i hi j hj
            omega

/-- The forbidden pattern occurs nowhere in a tree the automaton accepts. -/
theorem refOccursIn_false (hspec : LearnedSpec g neg b oa op)
    (hns : SpecsAvoidTops neg specs)
    (hAc : g.highToLow (g.baseOrder b) op = [])
    {e : TreeExample} (he : e ∈ neg) {k : Nat} (hk : e.isAssoc = true → k = e.idx) :
    ∀ t : Tree,
      (∀ f ts, t = .node f ts → ∃ q, q ∈ (refGenTA g oa specs op b).evalT (refGenTA g oa specs op b).epsTable t) →
      (TreeExample.mk e.top e.bot k).occursIn t = false := by
  intro t
  induction t using Tree.rec' with
  | hleaf a => intro _; simp [TreeExample.occursIn_leaf]
  | hnode f ts ih =>
      intro hev
      obtain ⟨q, hq⟩ := hev f ts rfl
      rw [TreeExample.occursIn_node, refMatchesHere_false hspec hns hAc he hk hq, Bool.false_or]
      refine TreeExample.occursInAny_false _ ts fun u hu => ih u hu ?_
      -- every child that is a node is itself evaluable
      intro f' us hu'
      subst hu'
      obtain ⟨tn, fill, p, -, hm⟩ := evalT_refGenTA_children hAc hq
      obtain ⟨n, hn, hnu⟩ := List.mem_iff_getElem.mp hu
      have hget : ts[n]? = some (.node f' us) := by
        rw [List.getElem?_eq_getElem hn, hnu]
      have hlen : n < (fillRhs tn p.2 fill).length := by
        rw [← TA.matchAll_length ts _ hm]; exact hn
      obtain ⟨Q, -, r, hr, -⟩ :=
        TA.matchAll_state_of_node hm hget (by rw [List.getElem?_eq_getElem hlen]; rfl)
      exact ⟨r, hr⟩

theorem refGenTA_sound₂ (hspec : LearnedSpec g neg b oa op)
    (hns : SpecsAvoidTops neg specs)
    (hAc : g.highToLow (g.baseOrder b) op = []) :
    GenTASound₂ g neg (refGenTA g oa specs op b) := by
  intro t ht
  simp only [CFG.excludedLang]
  by_contra hcon
  simp only [not_forall, List.any_eq_true, Bool.not_eq_false] at hcon
  obtain ⟨e, he, hex⟩ := hcon
  -- the root of an accepted tree carries a state
  have hev : ∀ f ts, t = .node f ts →
      ∃ q, q ∈ (refGenTA g oa specs op b).evalT (refGenTA g oa specs op b).epsTable t := by
    intro f ts hts
    simp only [TA.Lang, TA.accepts, List.any_eq_true] at ht
    obtain ⟨q, hq, -⟩ := ht
    exact ⟨q, hq⟩
  simp only [CFG.excludedBy] at hex
  split at hex
  · -- associativity-related: the pattern uses the example's own index
    have key : e.occursIn t = false := refOccursIn_false hspec hns hAc he (fun _ => rfl) t hev
    simp only [CFG.parseTreesOf, Bool.and_eq_true, key] at hex
    simp at hex
  · -- precedence-related: the pattern may use any child position
    next hassoc =>
      simp only [List.any_eq_true] at hex
      obtain ⟨n, -, hn⟩ := hex
      simp only [CFG.parseTreesOf, Bool.and_eq_true] at hn
      have key : (TreeExample.mk e.top e.bot n).occursIn t = false :=
        refOccursIn_false hspec hns hAc he (k := n) (fun h => absurd h hassoc) t hev
      simp only [key] at hn
      simp at hn

/-! ### Theorem 3.1(1) for the shipped automaton -/

theorem refRun_exists (hfits : RefFits g neg b oa specs op) :
    ∀ (t : Tree) (A : Nonterminal), g.isParseTreeOf A t = true → NoPattern neg t →
      (A ∈ trivNts g b →
        (GState.triv A) ∈ (refGenTA g oa specs op b).evalT (refGenTA g oa specs op b).epsTable t) ∧
      (A ∉ trivNts g b → ∀ f ts, t = .node f ts → ∀ i ∈ op.ordersOf f,
        (GState.lvl i) ∈ (refGenTA g oa specs op b).evalT (refGenTA g oa specs op b).epsTable t) := by
  set Ar := refGenTA g oa specs op b with hAr
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
            refGenTA_trans]
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
        have htr : (⟨.lvl i, sp.1, fillRhs (trivNts g b) sp.2.2 (refOaFill oa specs sp.1 i)⟩ :
            Transition GState) ∈ Ar.realTrans := by
          simp only [hAr, TA.realTrans, List.mem_filter, bne_iff_ne, ne_eq, decide_eq_true_eq,
            refGenTA_trans]
          exact ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (mem_refNonTrivTrans.mpr ⟨i, ss, hss, sp.1, hmem, sp.2, hprod, rfl⟩))),
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
                    obtain ⟨j, hj, hle⟩ := hfits sp.1 sq.1 i k hi
                      ⟨sp, hsp, rfl, sq, hsq, rfl, by rw [hlhs']; exact hx⟩ hsq' hfree
                    obtain ⟨l, hl⟩ := refOaFill_level' oa specs sp.1 i k
                    obtain ⟨ss', hss', -⟩ := OrderMap.mem_ordersOf.mp hj
                    refine ⟨.lvl j, (ih _ humem B hmatch hnpu).2 hBt' _ _ rfl j hj, ?_⟩
                    rw [hl]
                    exact (Ar.isEpsClosure_epsTable _ _).mpr
                      (refEpsReach_of_le (hle l hl) (OrderMap.le_maxOrder hss'))

theorem refGenTA_sound₁ (hfits : RefFits g neg b oa specs op) (hcov : Covers g b op)
    (hstart : ∀ A ∈ g.starts, A ∉ trivNts g b) :
    GenTASound₁ g neg (refGenTA g oa specs op b) := by
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
      have hrun := (refRun_exists hfits _ A hptA hnp).2 hAtriv sp.1 ts rfl i hi
      obtain ⟨ss, hss, -⟩ := OrderMap.mem_ordersOf.mp hi
      simp only [TA.Lang, TA.accepts, List.any_eq_true, decide_eq_true_eq]
      exact ⟨.lvl i, hrun, .lvl 0,
        ((refGenTA g oa specs op b).isEpsClosure_epsTable _ _).mpr
          (refEpsReach_of_le (Nat.zero_le i) (OrderMap.le_maxOrder hss)),
        by simp⟩

/-- **Theorem 3.1 for the shipped learner**, both halves. -/
theorem refGenTA_sound (hspec : LearnedSpec g neg b oa op) (hns : SpecsAvoidTops neg specs)
    (hfits : RefFits g neg b oa specs op) (hcov : Covers g b op)
    (hstart : ∀ A ∈ g.starts, A ∉ trivNts g b)
    (hAc : g.highToLow (g.baseOrder b) op = []) :
    GenTASound₁ g neg (refGenTA g oa specs op b) ∧
      GenTASound₂ g neg (refGenTA g oa specs op b) :=
  ⟨refGenTA_sound₁ hfits hcov hstart, refGenTA_sound₂ hspec hns hAc⟩

/--
**Theorem 3.2 for the shipped learner.**  One round of repair, built from the order
`learner.ml` computes and intersected with the verified product, recognises exactly
`L_g \ L⁻`.
-/
theorem refGreta_correct_of_spec (hspec : LearnedSpec g neg b oa op)
    (hns : SpecsAvoidTops neg specs) (hfits : RefFits g neg b oa specs op)
    (hcov : Covers g b op) (hstart : ∀ A ∈ g.starts, A ∉ trivNts g b)
    (hAc : g.highToLow (g.baseOrder b) op = []) (t : Tree) :
    (prodTA (refGenTA g oa specs op b) g.toTA).Lang t ↔ g.repairedLang neg t = true :=
  greta_correct g neg _ (refGenTA_sound₁ hfits hcov hstart) (refGenTA_sound₂ hspec hns hAc) t

/-!
### The side conditions, checked on the input

As in `Greta.LearnSpec`, every condition is decided or soundly approximated by a `Bool`, so
the tool establishes Theorem 3.2 for its own input by computation.  The difference is that
these checks pass on the grammars where the published ones fail.
-/

/-- `SpecsAvoidTops` as a check. -/
def specsAvoidTopsB (neg : List TreeExample) (specs : SpecMap) : Bool :=
  neg.all fun e => (specs.lookup e.top).isNone

theorem specsAvoidTops_of_check (h : specsAvoidTopsB neg specs = true) :
    SpecsAvoidTops neg specs := by
  intro e he
  simpa using List.all_eq_true.mp h e he

/--
A sufficient condition for `RefFits`, checkable on the input.  It is `fitsB` with the
back-edge in the level it demands: where `learn_ta` sends a child to `e_d`, the child needs
a level at or above `d`, not at or above the parent's own level.
-/
def refFitsB (g : CFG) (neg : List TreeExample) (b : Bool) (oa : Oa) (specs : SpecMap)
    (op : OrderMap) : Bool :=
  g.rankedProds.all fun sp =>
    (op.ordersOf sp.1).all fun i =>
      (List.range sp.2.2.length).all fun k =>
        g.rankedProds.all fun sq =>
          !(sp.2.2[k]? == some (.nt sq.2.1))
            || (trivSyms g b).contains sq.1
            || hasPrecExample neg sp.1 sq.1
            || hasAssocExample neg sp.1 sq.1 k
            || (op.ordersOf sq.1).any fun j =>
                 decide ((if (oa.positionsOf sp.1).contains k then i + 1
                          else (specs.lookup sp.1).getD i) ≤ j)

theorem refFits_of_check (h : refFitsB g neg b oa specs op = true) :
    RefFits g neg b oa specs op := by
  intro s s' i k hi hchild htriv hneg
  unfold ChildAt at hchild
  obtain ⟨sp, hsp, hs1, sq, hsq, hs2, hrhs⟩ := hchild
  subst hs1
  subst hs2
  have hklt : k < sp.2.2.length := (List.getElem?_eq_some_iff.mp hrhs).1
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp h sp hsp) i hi) k (List.mem_range.mpr hklt)) sq hsq
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
      simp only [refOaFill, if_pos hk, GState.lvl.injEq] at hl
      omega
    · rw [if_neg hk] at hij
      simp only [refOaFill, if_neg hk, GState.lvl.injEq] at hl
      omega

/-! ### Theorem 3.2 for the pipeline Greta ships -/

/-- The triple the shipped learner computes for a grammar and its rejected examples. -/
abbrev refLearned (g : CFG) (neg : List TreeExample) (b : Bool) : Oa × OrderMap × SpecMap :=
  refLearnOaOp g neg (toMapOf (g.baseOrder b) neg) b

/-- Every side condition Theorem 3.2 needs of the shipped pipeline, as one check. -/
def refPipelineOK (g : CFG) (neg : List TreeExample) (b : Bool) : Bool :=
  let r := refLearned g neg b
  learnedSpecB g neg b r.1 r.2.1
    && specsAvoidTopsB neg r.2.2
    && (g.highToLow (g.baseOrder b) r.2.1).isEmpty
    && refFitsB g neg b r.1 r.2.2 r.2.1
    && coversB g b r.2.1
    && startsOK g b

/--
**Theorem 3.2 for the learner Greta ships.**  Learn the order with `learner.ml`'s
algorithm, build `A_r` with its back-edges, intersect with `A_g` using the verified
product: the result recognises exactly `L_g \ L⁻`.  Every hypothesis is discharged by
`refPipelineOK`, a check on the input.
-/
theorem refGreta_correct_pipeline (g : CFG) (neg : List TreeExample) (b : Bool)
    (h : refPipelineOK g neg b = true) (t : Tree) :
    (prodTA (refGenTA g (refLearned g neg b).1 (refLearned g neg b).2.2
      (refLearned g neg b).2.1 b) g.toTA).Lang t ↔ g.repairedLang neg t = true := by
  simp only [refPipelineOK, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨hspec, hns⟩, hAc⟩, hfits⟩, hcov⟩, hstart⟩ := h
  exact refGreta_correct_of_spec (learnedSpec_of_check hspec)
    (specsAvoidTops_of_check hns) (refFits_of_check hfits) (covers_of_check hcov)
    (starts_of_check hstart) hAc t

end

end Greta

