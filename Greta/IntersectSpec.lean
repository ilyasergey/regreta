/-
Correctness of **Algorithm 3.3 (IntersectTA)**, the optimised intersection that Greta
actually runs: `Greta.intersectTA` recognises `L(A) ∩ L(B)`, the same language as the
textbook product `Greta.prodTA` of Section 2.4 (`Greta.prodTA_lang`).

The algorithm is three independent optimisations, each a flag of `IntersectOpts`, and each
is treated separately here.

* **Reachability** (`Greta.stage0_lang`).  The worklist loop explores only the product
  states reachable downwards from the accepting pairs, and looks up transitions *through*
  the ε-transitions of the two inputs (`TA.transAt`), retargeting the result at the pair it
  came from.  So the result is not a sub-automaton of the product: the ε-closures of `A`
  and `B` are inlined and the output has no ε-transitions at all.  Two ingredients:
  `mem_epsDown_iff`, the mirror image of `TA.closeFrom` for the reversed ε-graph, and
  `reachLoop_spec`, a fuel-adequacy argument in the style of `saturate_closed`.
* **Duplicate merging** (`Greta.merge_lang`, Algorithm 3.4).  Its heart is `sigEq_evalT`:
  two states whose incoming transitions agree once each is replaced by a placeholder
  accept the same trees.
* **ε-introduction** (`Greta.introEpsAll_lang`).  Its heart is `shapes_ev`, the
  subsumption lemma: when every transition shape of `eᵢ` is also one of `eⱼ`, everything
  `eᵢ` accepts `eⱼ` accepts, so the new ε-edge adds nothing while the transitions it
  replaces are recovered through `eᵢ`.  This needs no acyclicity hypothesis.

Everything is phrased through `TA.Ev`, the set of states a tree may be assigned *after*
ε-promotion, which is the only thing `TA.matchAll` and `TA.accepts` ever inspect.

The top-level result is `Greta.intersectTA_lang`; see its docstring for the two decidable
side conditions, and `Greta.intersectTA_lang_default` for the configuration Greta runs,
which discharges both.
-/
import Greta.Intersect

namespace Greta

variable {σ σ₁ σ₂ : Type} [DecidableEq σ] [DecidableEq σ₁] [DecidableEq σ₂]

/-! ### The three stages of `intersectTA`, named -/

/-- The pairs and transitions produced by the first stage of Algorithm 3.3. -/
def interStage0 (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts) :
    List (σ₁ × σ₂) × List (Transition (σ₁ × σ₂)) :=
  if opts.reachability then
    reachLoop A B (A.mentionedStates.length * B.mentionedStates.length + 1)
      (pairs A.finals B.finals) (pairs A.finals B.finals) []
  else allPairsProduct A B

/-- The pairs and transitions after duplicate merging. -/
def interStage1 (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts) :
    List (σ₁ × σ₂) × List (Transition (σ₁ × σ₂)) :=
  if opts.dedupStates then mergeDups (interStage0 A B opts).1 (interStage0 A B opts).2
  else interStage0 A B opts

/-- The transitions after ε-introduction. -/
def interStage2 (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts) :
    List (Transition (σ₁ × σ₂)) :=
  if opts.introEps then introEpsAll (interStage1 A B opts).1 (interStage1 A B opts).2
  else (interStage1 A B opts).2

theorem intersectTA_eq (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts) :
    intersectTA A B opts =
      { states    := (interStage1 A B opts).1
        alphabet  := (A.alphabet.filter fun f => B.alphabet.contains f) ++ [epsSym]
        terminals := A.terminals.filter fun a => B.terminals.contains a
        finals    := (pairs A.finals B.finals).filter
                       fun q => (interStage1 A B opts).1.contains q
        trans     := interStage2 A B opts } := rfl


/-! ### ε-saturated evaluation

Every algorithm below is analysed through `TA.Ev`: the set of states a tree may be
assigned *after* ε-promotion.  This is the only thing the child-matching of `TA.matchAll`
and the acceptance test of `TA.accepts` ever look at, so two automata whose `Ev` agree on
every tree have the same language, whatever their transitions look like.
-/

/-- `C.Ev t q`: a run of `C` may assign `q` to the root of `t`, ε-promotions included. -/
def TA.Ev (C : TA σ) (t : Tree) (q : σ) : Prop :=
  ∃ r ∈ C.evalT C.epsTable t, EpsReach C r q

theorem TA.ev_def {C : TA σ} {t : Tree} {q : σ} :
    C.Ev t q ↔ ∃ r ∈ C.evalT C.epsTable t, EpsReach C r q := Iff.rfl

theorem TA.mem_epsTable {C : TA σ} {q p : σ} : p ∈ C.epsTable q ↔ EpsReach C q p :=
  C.isEpsClosure_epsTable q p

/-- `Ev` may be computed with any valid ε-closure table. -/
theorem TA.ev_iff_tbl {C : TA σ} {tbl : EpsTable σ} (h : IsEpsClosure C tbl) {t : Tree}
    {q : σ} : C.Ev t q ↔ ∃ r ∈ C.evalT tbl t, q ∈ tbl r := by
  have hev : C.evalT C.epsTable t = C.evalT tbl t :=
    TA.evalT_congr (IsEpsClosure.mem_iff C.isEpsClosure_epsTable h) t
  simp only [TA.Ev, hev]
  exact ⟨fun ⟨r, hr, hq⟩ => ⟨r, hr, (h r q).mpr hq⟩, fun ⟨r, hr, hq⟩ => ⟨r, hr, (h r q).mp hq⟩⟩

theorem TA.ev_of_mem_evalT {C : TA σ} {t : Tree} {q : σ}
    (h : q ∈ C.evalT C.epsTable t) : C.Ev t q := ⟨q, h, .refl _⟩

theorem TA.ev_of_mem_evalT_tbl {C : TA σ} {tbl : EpsTable σ} (hcl : IsEpsClosure C tbl)
    {t : Tree} {q : σ} (h : q ∈ C.evalT tbl t) : C.Ev t q :=
  (TA.ev_iff_tbl hcl).mpr ⟨q, h, (hcl q q).mpr (.refl _)⟩

theorem TA.ev_promote {C : TA σ} {t : Tree} {q p : σ} (h : C.Ev t q)
    (hr : EpsReach C q p) : C.Ev t p := by
  obtain ⟨r, hr', hq⟩ := h
  exact ⟨r, hr', hq.trans hr⟩

@[simp] theorem TA.ev_leaf {C : TA σ} {a : Terminal} {q : σ} : ¬ C.Ev (.leaf a) q := by
  rintro ⟨r, hr, -⟩; simp at hr

/-- Acceptance, phrased through `Ev`. -/
theorem TA.lang_iff_ev {C : TA σ} {t : Tree} : C.Lang t ↔ ∃ q ∈ C.finals, C.Ev t q := by
  simp only [TA.Lang, TA.accepts, List.any_eq_true, decide_eq_true_eq, TA.Ev,
    TA.mem_epsTable]
  exact ⟨fun ⟨r, hr, p, hp, hf⟩ => ⟨p, hf, r, hr, hp⟩,
         fun ⟨p, hf, r, hr, hp⟩ => ⟨r, hr, p, hp, hf⟩⟩

/-- Matching children depends on them only through `Ev`. -/
theorem matchAll_ev_congr {C D : TA σ} {tC tD : EpsTable σ}
    (hC : IsEpsClosure C tC) (hD : IsEpsClosure D tD) :
    ∀ (ts : List Tree) (bs : List (Beta σ)), (∀ u ∈ ts, ∀ q, C.Ev u q ↔ D.Ev u q) →
      C.matchAll tC ts bs = D.matchAll tD ts bs := by
  intro ts
  induction ts with
  | nil => intro bs _; cases bs <;> simp [TA.matchAll]
  | cons u us ih =>
      intro bs hev
      have hhd : ∀ q, C.Ev u q ↔ D.Ev u q := hev u (List.mem_cons_self ..)
      have htl : ∀ v ∈ us, ∀ q, C.Ev v q ↔ D.Ev v q := fun v hv => hev v (List.mem_cons_of_mem _ hv)
      cases bs with
      | nil => simp [TA.matchAll]
      | cons b bs =>
          cases b with
          | term a => simp only [TA.matchAll, ih bs htl]
          | state q =>
              simp only [TA.matchAll, ih bs htl]
              congr 1
              rw [Bool.eq_iff_iff]
              simp only [List.any_eq_true, decide_eq_true_eq]
              rw [← TA.ev_iff_tbl hC, ← TA.ev_iff_tbl hD]
              exact hhd q

/-! ### ε-free automata

The first two stages of Algorithm 3.3 produce automata without ε-transitions, where the
closure table is the identity.
-/

/-- No transition is an ε-transition. -/
def TA.NoEps (C : TA σ) : Prop := ∀ tr ∈ C.trans, tr.sym ≠ epsSym

theorem TA.epsReach_of_noEps {C : TA σ} (h : C.NoEps) {q p : σ} (hr : EpsReach C q p) :
    q = p := by
  induction hr with
  | refl => rfl
  | step he _ _ =>
      obtain ⟨tr, htr, hsym, _, _⟩ := mem_epsEdges.mp he
      exact absurd hsym (h tr htr)

theorem TA.isEpsClosure_singleton {C : TA σ} (h : C.NoEps) :
    IsEpsClosure C (fun q => [q]) := by
  intro q p
  simp only [List.mem_singleton]
  exact ⟨fun hp => hp ▸ .refl _, fun hr => (TA.epsReach_of_noEps h hr).symm⟩

theorem TA.ev_iff_mem_evalT {C : TA σ} (h : C.NoEps) {t : Tree} {q : σ} :
    C.Ev t q ↔ q ∈ C.evalT (fun x => [x]) t := by
  rw [TA.ev_iff_tbl (TA.isEpsClosure_singleton h)]
  exact ⟨fun ⟨r, hr, hq⟩ => by simpa using (List.mem_singleton.mp hq) ▸ hr,
         fun hq => ⟨q, hq, by simp⟩⟩


/-! ### Looking through ε-transitions: `epsDown`, `transAt`, `symsAt`

`TA.epsDown A q` saturates the ε-edges of `A` *backwards*, so it computes the states that
may be promoted to `q`.  The argument is the mirror image of `TA.closeFrom` in
`Greta.Closure`, with the same fuel-adequacy lemma `saturate_closed` doing the work.
-/

omit [DecidableEq σ] in
/-- Decomposition of an ε-path at its last step. -/
theorem EpsReach.cases_last {A : TA σ} {q p : σ} (h : EpsReach A q p) :
    q = p ∨ ∃ x, EpsReach A q x ∧ (x, p) ∈ A.epsEdges := by
  induction h with
  | refl => exact Or.inl rfl
  | @step a b c he _ ih =>
      rcases ih with rfl | ⟨x, hx, hxe⟩
      · exact Or.inr ⟨a, .refl _, he⟩
      · exact Or.inr ⟨x, .step he hx, hxe⟩

omit [DecidableEq σ] in
theorem mem_swap_epsEdges {A : TA σ} {a b : σ} :
    (a, b) ∈ A.epsEdges.map Prod.swap ↔ (b, a) ∈ A.epsEdges := by
  simp only [List.mem_map, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
  exact ⟨fun ⟨x, y, hxy, hx, hy⟩ => by subst hx; subst hy; exact hxy,
         fun h => ⟨b, a, h, rfl, rfl⟩⟩

theorem saturate_swap_sound {A : TA σ} (n : Nat) {qs : List σ} {q : σ}
    (h : ∀ p ∈ qs, EpsReach A p q) :
    ∀ p ∈ saturate (A.epsEdges.map Prod.swap) n qs, EpsReach A p q := by
  induction n generalizing qs with
  | zero => simpa [saturate] using h
  | succ n ih =>
      simp only [saturate]
      split
      · exact h
      · refine ih ?_
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact h p hp
        · obtain ⟨a, hmem, ha, _⟩ := mem_newTargets.mp hp
          exact (EpsReach.step (mem_swap_epsEdges.mp hmem) (.refl _)).trans (h a ha)

theorem mem_epsDown_self {A : TA σ} (q : σ) : q ∈ A.epsDown q :=
  subset_saturate _ _ _ (by simp)

theorem epsDown_sound {A : TA σ} {q p : σ} (h : p ∈ A.epsDown q) : EpsReach A p q :=
  saturate_swap_sound _ (by intro p hp; simp only [List.mem_singleton] at hp; exact hp ▸ .refl _) p h

theorem epsDown_closed {A : TA σ} {q : σ} (hq : q ∈ A.mentionedStates) :
    EdgeClosed (A.epsEdges.map Prod.swap) (A.epsDown q) := by
  refine saturate_closed _ (by simp) (by simpa using hq) (fun a b h => ?_) ?_
  · exact TA.epsEdges_source_mem (mem_swap_epsEdges.mp h)
  · simp only [List.length_singleton]; omega

theorem epsDown_complete {A : TA σ} {q p : σ} (hq : q ∈ A.mentionedStates)
    (h : EpsReach A p q) : p ∈ A.epsDown q := by
  have hclosed := epsDown_closed (A := A) hq
  have gen : ∀ {x y : σ}, EpsReach A x y → y = q → x ∈ A.epsDown q := by
    intro x y hxy
    induction hxy with
    | refl => rintro rfl; exact mem_epsDown_self _
    | @step a b c he _ ih => intro hc; exact hclosed b a (mem_swap_epsEdges.mpr he) (ih hc)
  exact gen h rfl

/-- `epsDown` computes exactly the states that may be ε-promoted to `q`. -/
theorem mem_epsDown_iff {A : TA σ} {q p : σ} : p ∈ A.epsDown q ↔ EpsReach A p q := by
  refine ⟨epsDown_sound, fun h => ?_⟩
  by_cases hq : q ∈ A.mentionedStates
  · exact epsDown_complete hq h
  · rcases h.cases_last with rfl | ⟨x, _, hxe⟩
    · exact mem_epsDown_self _
    · exact absurd (TA.epsEdges_target_mem hxe) hq

/-- The transitions `Algorithm 3.3` finds at `q`: those producing a state that may be
promoted to `q`. -/
theorem mem_transAt {A : TA σ} {q : σ} {s : Sym} {tr : Transition σ} :
    tr ∈ A.transAt q s ↔ tr ∈ A.realTrans ∧ EpsReach A tr.target q ∧ tr.sym = s := by
  simp only [TA.transAt, List.mem_flatMap, List.mem_filter, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨q', hq', htr, htgt, hsym⟩
    exact ⟨htr, htgt ▸ mem_epsDown_iff.mp hq', hsym⟩
  · rintro ⟨htr, hreach, hsym⟩
    exact ⟨tr.target, mem_epsDown_iff.mpr hreach, htr, rfl, hsym⟩

theorem mem_symsAt {A : TA σ} {q : σ} {s : Sym} :
    s ∈ A.symsAt q ↔ ∃ tr ∈ A.realTrans, EpsReach A tr.target q ∧ tr.sym = s := by
  simp only [TA.symsAt, List.mem_dedup, List.mem_flatMap, List.mem_map, List.mem_filter,
    beq_iff_eq]
  constructor
  · rintro ⟨q', hq', tr, ⟨htr, htgt⟩, hsym⟩
    exact ⟨tr, htr, htgt ▸ mem_epsDown_iff.mp hq', hsym⟩
  · rintro ⟨tr, htr, hreach, hsym⟩
    exact ⟨tr.target, mem_epsDown_iff.mpr hreach, tr, ⟨htr, rfl⟩, hsym⟩

/-- What the cross product at one pair produces. -/
theorem mem_transitionsAtPair {A : TA σ₁} {B : TA σ₂} {q : σ₁ × σ₂}
    {tr : Transition (σ₁ × σ₂)} :
    tr ∈ transitionsAtPair A B q ↔
      ∃ t₁ ∈ A.realTrans, ∃ t₂ ∈ B.realTrans,
        EpsReach A t₁.target q.1 ∧ EpsReach B t₂.target q.2 ∧
        t₁.sym = t₂.sym ∧ compatAll t₁.rhs t₂.rhs = true ∧
        tr = ⟨q, t₁.sym, zipBetas t₁.rhs t₂.rhs⟩ := by
  simp only [transitionsAtPair, List.mem_flatMap, List.mem_filter, List.mem_filterMap,
    List.elem_eq_mem, decide_eq_true_eq, crossTrans]
  constructor
  · rintro ⟨s, ⟨-, -⟩, t₁, ht₁, t₂, ht₂, hif⟩
    split at hif
    · next hc =>
        simp only [Option.some.injEq] at hif
        obtain ⟨h₁, hr₁, hs₁⟩ := mem_transAt.mp ht₁
        obtain ⟨h₂, hr₂, hs₂⟩ := mem_transAt.mp ht₂
        exact ⟨t₁, h₁, t₂, h₂, hr₁, hr₂, hs₁.trans hs₂.symm, hc, hif.symm⟩
    · simp at hif
  · rintro ⟨t₁, h₁, t₂, h₂, hr₁, hr₂, hsym, hc, rfl⟩
    refine ⟨t₁.sym, ⟨mem_symsAt.mpr ⟨t₁, h₁, hr₁, rfl⟩,
      mem_symsAt.mpr ⟨t₂, h₂, hr₂, hsym.symm⟩⟩, t₁, mem_transAt.mpr ⟨h₁, hr₁, rfl⟩,
      t₂, mem_transAt.mpr ⟨h₂, hr₂, hsym.symm⟩, ?_⟩
    rw [if_pos hc]


/-! ### Where the states of the product live -/

omit [DecidableEq σ] in
theorem TA.realTrans_subset {A : TA σ} {tr : Transition σ} (h : tr ∈ A.realTrans) :
    tr ∈ A.trans := (List.mem_filter.mp h).1

theorem TA.mem_mentioned_of_final {A : TA σ} {q : σ} (h : q ∈ A.finals) :
    q ∈ A.mentionedStates := by
  simp only [TA.mentionedStates, List.mem_dedup, List.mem_append]
  exact Or.inl (Or.inl (Or.inr h))

theorem TA.mem_mentioned_of_rhs {A : TA σ} {tr : Transition σ} (htr : tr ∈ A.trans)
    {p : σ} (h : Beta.state p ∈ tr.rhs) : p ∈ A.mentionedStates := by
  simp only [TA.mentionedStates, List.mem_dedup, List.mem_append, List.mem_flatMap]
  refine Or.inr ⟨tr, htr, ?_⟩
  simp only [List.mem_filterMap]
  exact ⟨Beta.state p, h, rfl⟩

omit [DecidableEq σ] in
theorem mem_rhsStates {tr : Transition σ} {x : σ} :
    x ∈ rhsStates tr ↔ Beta.state x ∈ tr.rhs := by
  simp only [rhsStates, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, hx⟩
    cases b with
    | term a => simp at hx
    | state y => simp only [Option.some.injEq] at hx; exact hx ▸ hb
  · intro h; exact ⟨Beta.state x, h, rfl⟩

omit [DecidableEq σ₁] [DecidableEq σ₂] in
/-- A state entry of a zipped right-hand side comes from state entries on both sides. -/
theorem mem_zipBetas_state {p : σ₁ × σ₂} :
    ∀ (bs₁ : List (Beta σ₁)) (bs₂ : List (Beta σ₂)), Beta.state p ∈ zipBetas bs₁ bs₂ →
      Beta.state p.1 ∈ bs₁ ∧ Beta.state p.2 ∈ bs₂ := by
  intro bs₁
  induction bs₁ with
  | nil => intro bs₂ h; simp [zipBetas] at h
  | cons b₁ l₁ ih =>
      intro bs₂ h
      cases bs₂ with
      | nil => simp [zipBetas] at h
      | cons b₂ l₂ =>
          simp only [zipBetas, List.mem_cons] at h
          rcases h with h | h
          · cases b₁ with
            | term a => simp [zipB] at h
            | state x =>
                cases b₂ with
                | term a => simp [zipB] at h
                | state y =>
                    simp only [zipB, Beta.state.injEq] at h
                    subst h
                    exact ⟨by simp, by simp⟩
          · obtain ⟨h₁, h₂⟩ := ih l₂ h
            exact ⟨List.mem_cons_of_mem _ h₁, List.mem_cons_of_mem _ h₂⟩

/-- Every state on the right-hand side of a transition of the cross product is a pair of
states mentioned by the two automata. -/
theorem transitionsAtPair_rhs_mem {A : TA σ₁} {B : TA σ₂} {q : σ₁ × σ₂}
    {tr : Transition (σ₁ × σ₂)} (h : tr ∈ transitionsAtPair A B q) {x : σ₁ × σ₂}
    (hx : Beta.state x ∈ tr.rhs) : x ∈ pairs A.mentionedStates B.mentionedStates := by
  obtain ⟨t₁, h₁, t₂, h₂, -, -, -, -, rfl⟩ := mem_transitionsAtPair.mp h
  obtain ⟨hx₁, hx₂⟩ := mem_zipBetas_state t₁.rhs t₂.rhs hx
  exact mem_pairs.mpr ⟨TA.mem_mentioned_of_rhs (TA.realTrans_subset h₁) hx₁,
    TA.mem_mentioned_of_rhs (TA.realTrans_subset h₂) hx₂⟩

theorem transitionsAtPair_target {A : TA σ₁} {B : TA σ₂} {q : σ₁ × σ₂}
    {tr : Transition (σ₁ × σ₂)} (h : tr ∈ transitionsAtPair A B q) : tr.target = q := by
  obtain ⟨t₁, -, t₂, -, -, -, -, -, rfl⟩ := mem_transitionsAtPair.mp h
  rfl

theorem transitionsAtPair_sym_ne_eps {A : TA σ₁} {B : TA σ₂} {q : σ₁ × σ₂}
    {tr : Transition (σ₁ × σ₂)} (h : tr ∈ transitionsAtPair A B q) : tr.sym ≠ epsSym := by
  obtain ⟨t₁, h₁, t₂, -, -, -, -, -, rfl⟩ := mem_transitionsAtPair.mp h
  simpa using (List.mem_filter.mp h₁).2

/-! ### What the first stage guarantees -/

/-- The specification of the first stage of Algorithm 3.3: the transitions are exactly the
cross products taken at the pairs of `qs`, and `qs` is closed under the states they
mention and contains the accepting pairs. -/
structure Stage0Spec (A : TA σ₁) (B : TA σ₂) (qs : List (σ₁ × σ₂))
    (δ : List (Transition (σ₁ × σ₂))) : Prop where
  /-- Every transition produced is a cross product taken at one of the pairs. -/
  sound : ∀ tr ∈ δ, ∃ p ∈ qs, tr ∈ transitionsAtPair A B p
  /-- Every cross product at a pair of `qs` is produced. -/
  complete : ∀ p ∈ qs, ∀ tr ∈ transitionsAtPair A B p, tr ∈ δ
  /-- The accepting pairs are explored. -/
  finals : ∀ p ∈ pairs A.finals B.finals, p ∈ qs
  /-- `qs` is closed under the states the transitions mention. -/
  closed : ∀ tr ∈ δ, ∀ x, Beta.state x ∈ tr.rhs → x ∈ qs

theorem Stage0Spec.noEps {A : TA σ₁} {B : TA σ₂} {qs : List (σ₁ × σ₂)}
    {δ : List (Transition (σ₁ × σ₂))} (h : Stage0Spec A B qs δ) {tr : Transition (σ₁ × σ₂)}
    (htr : tr ∈ δ) : tr.sym ≠ epsSym := by
  obtain ⟨p, -, hp⟩ := h.sound tr htr
  exact transitionsAtPair_sym_ne_eps hp

/-- The `reachability := false` path. -/
theorem allPairsProduct_spec (A : TA σ₁) (B : TA σ₂) :
    Stage0Spec A B (allPairsProduct A B).1 (allPairsProduct A B).2 where
  sound := by
    intro tr htr
    simp only [allPairsProduct, List.mem_dedup, List.mem_flatMap] at htr
    exact htr
  complete := by
    intro p hp tr htr
    simp only [allPairsProduct, List.mem_dedup, List.mem_flatMap]
    exact ⟨p, hp, htr⟩
  finals := by
    intro p hp
    obtain ⟨h₁, h₂⟩ := mem_pairs.mp hp
    exact mem_pairs.mpr ⟨TA.mem_mentioned_of_final h₁, TA.mem_mentioned_of_final h₂⟩
  closed := by
    intro tr htr x hx
    simp only [allPairsProduct, List.mem_dedup, List.mem_flatMap] at htr
    obtain ⟨p, -, hp⟩ := htr
    exact transitionsAtPair_rhs_mem hp hx


/-! ### The worklist loop

`reachLoop` terminates on a fixed point provided its fuel exceeds the number of product
states still to be discovered.  The potential `|w| + (|U| - |q|)` drops by exactly one per
iteration, which is the same counting argument as `saturate_closed` in `Greta.Closure`.
-/

/-- The invariants the worklist loop maintains. -/
structure LoopOut (A : TA σ₁) (B : TA σ₂)
    (r : List (σ₁ × σ₂) × List (Transition (σ₁ × σ₂))) (q : List (σ₁ × σ₂)) : Prop where
  mono : q ⊆ r.1
  complete : ∀ p ∈ r.1, ∀ tr ∈ transitionsAtPair A B p, tr ∈ r.2
  sound : ∀ tr ∈ r.2, ∃ p ∈ r.1, tr ∈ transitionsAtPair A B p
  closed : ∀ tr ∈ r.2, ∀ x, Beta.state x ∈ tr.rhs → x ∈ r.1

theorem reachLoop_spec (A : TA σ₁) (B : TA σ₂) (fuel : Nat) :
    ∀ (w q : List (σ₁ × σ₂)) (δ : List (Transition (σ₁ × σ₂))),
      q.Nodup → w ⊆ q → q ⊆ pairs A.mentionedStates B.mentionedStates →
      (∀ p ∈ q, p ∉ w → ∀ tr ∈ transitionsAtPair A B p, tr ∈ δ) →
      (∀ tr ∈ δ, ∃ p ∈ q, tr ∈ transitionsAtPair A B p) →
      (∀ tr ∈ δ, ∀ x, Beta.state x ∈ tr.rhs → x ∈ q) →
      w.length + (pairs A.mentionedStates B.mentionedStates).length ≤ q.length + fuel →
      LoopOut A B (reachLoop A B fuel w q δ) q := by
  induction fuel with
  | zero =>
      intro w q δ hnd hwq hqU hproc hsnd hclo hbud
      have hlen : q.length ≤ (pairs A.mentionedStates B.mentionedStates).length :=
        List.Nodup.length_le_of_subset hnd hqU
      have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hw
      exact { mono := fun _ hx => hx
              complete := fun p hp => hproc p hp (by simp)
              sound := hsnd
              closed := hclo }
  | succ fuel ih =>
      intro w q δ hnd hwq hqU hproc hsnd hclo hbud
      cases w with
      | nil =>
          exact { mono := fun _ hx => hx
                  complete := fun p hp => hproc p hp (by simp)
                  sound := hsnd
                  closed := hclo }
      | cons x ws =>
          have hxq : x ∈ q := hwq (by simp)
          set newTrans := transitionsAtPair A B x with hnewT
          set reached := (newTrans.flatMap rhsStates).dedup with hreach
          set fresh := reached.filter (fun p => !q.contains p) with hfresh
          have hmem_reached : ∀ z, z ∈ reached ↔ ∃ tr ∈ newTrans, Beta.state z ∈ tr.rhs := by
            intro z
            simp only [hreach, List.mem_dedup, List.mem_flatMap, mem_rhsStates]
          have hmem_fresh : ∀ z, z ∈ fresh ↔ z ∈ reached ∧ z ∉ q := by
            intro z; simp [hfresh, List.mem_filter]
          have heq : reachLoop A B (fuel + 1) (x :: ws) q δ =
              reachLoop A B fuel (ws ++ fresh) (q ++ fresh) ((δ ++ newTrans).dedup) := rfl
          rw [heq]
          have hres := ih (ws ++ fresh) (q ++ fresh) ((δ ++ newTrans).dedup)
            -- `q ++ fresh` is still duplicate-free
            (List.Nodup.append hnd (List.Nodup.filter _ (List.nodup_dedup _))
              (fun z hz hz' => ((hmem_fresh z).mp hz').2 hz))
            -- the worklist is contained in the explored set
            (by
              intro z hz
              rcases List.mem_append.mp hz with hz | hz
              · exact List.mem_append_left _ (hwq (List.mem_cons_of_mem _ hz))
              · exact List.mem_append_right _ hz)
            -- everything explored is a pair of mentioned states
            (by
              intro z hz
              rcases List.mem_append.mp hz with hz | hz
              · exact hqU hz
              · obtain ⟨tr, htr, hst⟩ := (hmem_reached z).mp ((hmem_fresh z).mp hz).1
                exact transitionsAtPair_rhs_mem htr hst)
            -- everything explored but no longer queued has its transitions recorded
            (by
              intro p hp hpw tr htr
              have hpf : p ∉ fresh := fun h => hpw (List.mem_append_right _ h)
              have hpq : p ∈ q := by
                rcases List.mem_append.mp hp with h | h
                · exact h
                · exact absurd h hpf
              by_cases hpx : p = x
              · subst hpx
                exact List.mem_dedup.mpr (List.mem_append_right _ htr)
              · refine List.mem_dedup.mpr (List.mem_append_left _ (hproc p hpq ?_ tr htr))
                intro hmem
                rcases List.mem_cons.mp hmem with h | h
                · exact hpx h
                · exact hpw (List.mem_append_left _ h))
            -- every recorded transition comes from an explored pair
            (by
              intro tr htr
              rcases List.mem_append.mp (List.mem_dedup.mp htr) with h | h
              · obtain ⟨p, hp, hp'⟩ := hsnd tr h
                exact ⟨p, List.mem_append_left _ hp, hp'⟩
              · exact ⟨x, List.mem_append_left _ hxq, h⟩)
            -- the explored set is closed under the states the transitions mention
            (by
              intro tr htr z hz
              rcases List.mem_append.mp (List.mem_dedup.mp htr) with h | h
              · exact List.mem_append_left _ (hclo tr h z hz)
              · by_cases hzq : z ∈ q
                · exact List.mem_append_left _ hzq
                · exact List.mem_append_right _
                    ((hmem_fresh z).mpr ⟨(hmem_reached z).mpr ⟨tr, h, hz⟩, hzq⟩))
            -- the potential drops by one
            (by
              simp only [List.length_append, List.length_cons] at hbud ⊢
              omega)
          exact { mono := fun z hz => hres.mono (List.mem_append_left _ hz)
                  complete := hres.complete
                  sound := hres.sound
                  closed := hres.closed }


theorem length_pairs {α β : Type} (l₁ : List α) (l₂ : List β) :
    (pairs l₁ l₂).length = l₁.length * l₂.length := by
  induction l₁ with
  | nil => simp [pairs]
  | cons a l ih =>
      simp only [pairs, List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons] at ih ⊢
      rw [ih, Nat.succ_mul, Nat.add_comm]

theorem pairs_nodup {α β : Type} {l₁ : List α} {l₂ : List β} (h₁ : l₁.Nodup)
    (h₂ : l₂.Nodup) : (pairs l₁ l₂).Nodup := by
  induction l₁ with
  | nil => simp [pairs]
  | cons a l ih =>
      simp only [pairs, List.flatMap_cons] at ih ⊢
      refine List.Nodup.append ((List.nodup_map_iff_inj_on h₂).mpr ?_) (ih (List.Nodup.of_cons h₁)) ?_
      · intro x _ y _ hxy; simpa using hxy
      · intro z hz hz'
        simp only [List.mem_map] at hz
        simp only [List.mem_flatMap, List.mem_map] at hz'
        obtain ⟨b, -, rfl⟩ := hz
        obtain ⟨a', ha', b', -, heq⟩ := hz'
        simp only [Prod.mk.injEq] at heq
        exact (List.nodup_cons.mp h₁).1 (heq.1 ▸ ha')

/-- The `reachability := true` path.  The fuel of Algorithm 3.3 suffices as long as the
accepting pairs are not listed twice. -/
theorem reachLoop_stage0 (A : TA σ₁) (B : TA σ₂)
    (hnd : (pairs A.finals B.finals).Nodup) :
    Stage0Spec A B
      (reachLoop A B (A.mentionedStates.length * B.mentionedStates.length + 1)
        (pairs A.finals B.finals) (pairs A.finals B.finals) []).1
      (reachLoop A B (A.mentionedStates.length * B.mentionedStates.length + 1)
        (pairs A.finals B.finals) (pairs A.finals B.finals) []).2 := by
  have hsub : pairs A.finals B.finals ⊆ pairs A.mentionedStates B.mentionedStates := by
    intro p hp
    obtain ⟨h₁, h₂⟩ := mem_pairs.mp hp
    exact mem_pairs.mpr ⟨TA.mem_mentioned_of_final h₁, TA.mem_mentioned_of_final h₂⟩
  have hout := reachLoop_spec A B (A.mentionedStates.length * B.mentionedStates.length + 1)
    (pairs A.finals B.finals) (pairs A.finals B.finals) [] hnd (fun _ h => h) hsub
    (by intro p hp hnot; exact absurd hp hnot) (by simp) (by simp)
    (by rw [length_pairs A.mentionedStates B.mentionedStates]; omega)
  exact { sound := hout.sound
          complete := hout.complete
          finals := fun p hp => hout.mono hp
          closed := hout.closed }

/-- Either way, the first stage meets its specification. -/
theorem interStage0_spec (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts)
    (hnd : opts.reachability = true → (pairs A.finals B.finals).Nodup) :
    Stage0Spec A B (interStage0 A B opts).1 (interStage0 A B opts).2 := by
  simp only [interStage0]
  split
  · next h => exact reachLoop_stage0 A B (hnd h)
  · exact allPairsProduct_spec A B


/-! ### The first stage recognises the intersection

The cross product taken at a pair `q` looks *through* the ε-transitions of the two inputs
(`TA.transAt`) and retargets the result at `q`, so the ε-closures of `A` and `B` are
inlined and the result has no ε-transitions of its own.  The evaluation lemma is therefore
stated with `TA.Ev`, which hides the promotion step on both sides.
-/

theorem matchAll_state_ev {C : TA σ} {t : Tree} {ts : List Tree} {q : σ}
    {bs : List (Beta σ)} :
    C.matchAll C.epsTable (t :: ts) (.state q :: bs) = true ↔
      (C.Ev t q ∧ C.matchAll C.epsTable ts bs = true) := by
  rw [TA.ev_def]
  simp only [TA.matchAll, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨r, hr, hq⟩, hrest⟩
    exact ⟨⟨r, hr, TA.mem_epsTable.mp hq⟩, hrest⟩
  · rintro ⟨⟨r, hr, hq⟩, hrest⟩
    exact ⟨⟨r, hr, TA.mem_epsTable.mpr hq⟩, hrest⟩

theorem matchAll_state_triv {C : TA σ} {t : Tree} {ts : List Tree} {q : σ}
    {bs : List (Beta σ)} :
    C.matchAll (fun z => [z]) (t :: ts) (.state q :: bs) = true ↔
      (q ∈ C.evalT (fun z => [z]) t ∧ C.matchAll (fun z => [z]) ts bs = true) := by
  simp only [TA.matchAll, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq,
    List.mem_singleton]
  constructor
  · rintro ⟨⟨r, hr, rfl⟩, h⟩; exact ⟨hr, h⟩
  · rintro ⟨hq, h⟩; exact ⟨⟨q, hq, rfl⟩, h⟩

section Stage0

variable {A : TA σ₁} {B : TA σ₂} {C : TA (σ₁ × σ₂)} {qs : List (σ₁ × σ₂)}
  {δ : List (Transition (σ₁ × σ₂))}

theorem Stage0Spec.trans_noEps (hspec : Stage0Spec A B qs δ) (hC : C.trans = δ) :
    C.NoEps := by
  intro tr htr
  exact hspec.noEps (hC ▸ htr)

theorem Stage0Spec.mem_realTrans (hspec : Stage0Spec A B qs δ) (hC : C.trans = δ)
    {tr : Transition (σ₁ × σ₂)} : tr ∈ C.realTrans ↔ tr ∈ δ := by
  simp only [TA.realTrans, List.mem_filter, hC, bne_iff_ne, ne_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, hspec.noEps h⟩⟩

/-- Splitting a match of a zipped right-hand side into matches in the two factors. -/
theorem matchAll_zip_split :
    ∀ (ts : List Tree),
      (∀ u ∈ ts, ∀ x : σ₁ × σ₂, x ∈ C.evalT (fun z => [z]) u → A.Ev u x.1 ∧ B.Ev u x.2) →
      ∀ (bs₁ : List (Beta σ₁)) (bs₂ : List (Beta σ₂)), compatAll bs₁ bs₂ = true →
        C.matchAll (fun z => [z]) ts (zipBetas bs₁ bs₂) = true →
        A.matchAll A.epsTable ts bs₁ = true ∧ B.matchAll B.epsTable ts bs₂ = true := by
  intro ts
  induction ts with
  | nil =>
      intro _ bs₁ bs₂ hc hm
      cases bs₁ <;> cases bs₂ <;> simp_all [compatAll, zipBetas, TA.matchAll]
  | cons u us ih =>
      intro hev bs₁ bs₂ hc hm
      have hhd := hev u (List.mem_cons_self ..)
      have htl : ∀ v ∈ us, ∀ x : σ₁ × σ₂, x ∈ C.evalT (fun z => [z]) v →
          A.Ev v x.1 ∧ B.Ev v x.2 := fun v hv => hev v (List.mem_cons_of_mem _ hv)
      cases bs₁ with
      | nil => cases bs₂ <;> simp_all [compatAll, zipBetas, TA.matchAll]
      | cons b₁ l₁ =>
        cases bs₂ with
        | nil => simp [compatAll] at hc
        | cons b₂ l₂ =>
          simp only [compatAll, Bool.and_eq_true] at hc
          cases b₁ with
          | term a =>
            cases b₂ with
            | term a' =>
                have haa : a = a' := by simpa [betaCompat] using hc.1
                subst haa
                simp only [zipBetas, zipB, TA.matchAll, Bool.and_eq_true] at hm ⊢
                exact ⟨⟨hm.1, (ih htl l₁ l₂ hc.2 hm.2).1⟩, ⟨hm.1, (ih htl l₁ l₂ hc.2 hm.2).2⟩⟩
            | state q => simp [betaCompat] at hc
          | state x₁ =>
            cases b₂ with
            | term a' => simp [betaCompat] at hc
            | state x₂ =>
                simp only [zipBetas, zipB] at hm
                rw [matchAll_state_triv] at hm
                obtain ⟨hx, hrest⟩ := hm
                obtain ⟨he₁, he₂⟩ := hhd (x₁, x₂) hx
                refine ⟨?_, ?_⟩
                · rw [matchAll_state_ev]
                  exact ⟨he₁, (ih htl l₁ l₂ hc.2 hrest).1⟩
                · rw [matchAll_state_ev]
                  exact ⟨he₂, (ih htl l₁ l₂ hc.2 hrest).2⟩

/-- Building a match of a zipped right-hand side from matches in the two factors. -/
theorem matchAll_zip_build :
    ∀ (ts : List Tree),
      (∀ u ∈ ts, ∀ x : σ₁ × σ₂, x ∈ qs → A.Ev u x.1 → B.Ev u x.2 →
        x ∈ C.evalT (fun z => [z]) u) →
      ∀ (bs₁ : List (Beta σ₁)) (bs₂ : List (Beta σ₂)),
        (∀ x : σ₁ × σ₂, Beta.state x ∈ zipBetas bs₁ bs₂ → x ∈ qs) →
        compatAll bs₁ bs₂ = true →
        A.matchAll A.epsTable ts bs₁ = true → B.matchAll B.epsTable ts bs₂ = true →
        C.matchAll (fun z => [z]) ts (zipBetas bs₁ bs₂) = true := by
  intro ts
  induction ts with
  | nil =>
      intro _ bs₁ bs₂ _ hc h₁ h₂
      cases bs₁ <;> cases bs₂ <;> simp_all [compatAll, zipBetas, TA.matchAll]
  | cons u us ih =>
      intro hev bs₁ bs₂ hqs hc h₁ h₂
      have hhd := hev u (List.mem_cons_self ..)
      have htl : ∀ v ∈ us, ∀ x : σ₁ × σ₂, x ∈ qs → A.Ev v x.1 → B.Ev v x.2 →
          x ∈ C.evalT (fun z => [z]) v := fun v hv => hev v (List.mem_cons_of_mem _ hv)
      cases bs₁ with
      | nil => simp [TA.matchAll] at h₁
      | cons b₁ l₁ =>
        cases bs₂ with
        | nil => simp [compatAll] at hc
        | cons b₂ l₂ =>
          simp only [compatAll, Bool.and_eq_true] at hc
          have hqs' : ∀ x : σ₁ × σ₂, Beta.state x ∈ zipBetas l₁ l₂ → x ∈ qs := by
            intro x hx
            exact hqs x (by simp only [zipBetas]; exact List.mem_cons_of_mem _ hx)
          cases b₁ with
          | term a =>
            cases b₂ with
            | term a' =>
                have haa : a = a' := by simpa [betaCompat] using hc.1
                subst haa
                simp only [TA.matchAll, Bool.and_eq_true] at h₁ h₂
                simp only [zipBetas, zipB, TA.matchAll, Bool.and_eq_true]
                exact ⟨h₁.1, ih htl l₁ l₂ hqs' hc.2 h₁.2 h₂.2⟩
            | state q => simp [betaCompat] at hc
          | state x₁ =>
            cases b₂ with
            | term a' => simp [betaCompat] at hc
            | state x₂ =>
                rw [matchAll_state_ev] at h₁ h₂
                simp only [zipBetas, zipB]
                rw [matchAll_state_triv]
                refine ⟨hhd (x₁, x₂) (hqs (x₁, x₂) (by simp [zipBetas, zipB])) h₁.1 h₂.1, ?_⟩
                exact ih htl l₁ l₂ hqs' hc.2 h₁.2 h₂.2

/-- Soundness of the first stage: every state it assigns is assigned by both inputs. -/
theorem stage0_sound (hspec : Stage0Spec A B qs δ) (hC : C.trans = δ) :
    ∀ (t : Tree) (x : σ₁ × σ₂), x ∈ C.evalT (fun z => [z]) t → A.Ev t x.1 ∧ B.Ev t x.2 := by
  intro t
  induction t using Tree.rec' with
  | hleaf a => intro x hx; simp at hx
  | hnode f ts ih =>
      intro x hx
      obtain ⟨tr, htr, hsym, hm, htgt⟩ := TA.mem_evalT_node.mp hx
      obtain ⟨p, -, hp⟩ := hspec.sound tr ((hspec.mem_realTrans hC).mp htr)
      obtain ⟨t₁, h₁, t₂, h₂, hr₁, hr₂, hs₁₂, hcompat, rfl⟩ := mem_transitionsAtPair.mp hp
      simp only at htgt hsym hm
      subst htgt
      obtain ⟨hm₁, hm₂⟩ := matchAll_zip_split (A := A) (B := B) (C := C) ts ih t₁.rhs t₂.rhs hcompat hm
      constructor
      · exact TA.ev_promote (TA.ev_of_mem_evalT
          (TA.mem_evalT_node.mpr ⟨t₁, h₁, hsym, hm₁, rfl⟩)) hr₁
      · exact TA.ev_promote (TA.ev_of_mem_evalT
          (TA.mem_evalT_node.mpr ⟨t₂, h₂, hs₁₂ ▸ hsym, hm₂, rfl⟩)) hr₂

/-- Completeness of the first stage: every pair it explored is assigned whenever both
components are. -/
theorem stage0_complete (hspec : Stage0Spec A B qs δ) (hC : C.trans = δ) :
    ∀ (t : Tree) (x : σ₁ × σ₂), x ∈ qs → A.Ev t x.1 → B.Ev t x.2 →
      x ∈ C.evalT (fun z => [z]) t := by
  intro t
  induction t using Tree.rec' with
  | hleaf a => intro x _ h; exact absurd h TA.ev_leaf
  | hnode f ts ih =>
      rintro x hxqs ⟨r₁, hr₁, hp₁⟩ ⟨r₂, hr₂, hp₂⟩
      obtain ⟨t₁, h₁, hs₁, hm₁, ht₁⟩ := TA.mem_evalT_node.mp hr₁
      obtain ⟨t₂, h₂, hs₂, hm₂, ht₂⟩ := TA.mem_evalT_node.mp hr₂
      have hcompat : compatAll t₁.rhs t₂.rhs = true :=
        compatAll_of_match A B ts t₁.rhs t₂.rhs hm₁ hm₂
      have hmem : (⟨x, t₁.sym, zipBetas t₁.rhs t₂.rhs⟩ : Transition (σ₁ × σ₂)) ∈
          transitionsAtPair A B x :=
        mem_transitionsAtPair.mpr ⟨t₁, h₁, t₂, h₂, ht₁ ▸ hp₁, ht₂ ▸ hp₂,
          hs₁.trans hs₂.symm, hcompat, rfl⟩
      have hin : (⟨x, t₁.sym, zipBetas t₁.rhs t₂.rhs⟩ : Transition (σ₁ × σ₂)) ∈ δ :=
        hspec.complete x hxqs _ hmem
      have hqs : ∀ y : σ₁ × σ₂, Beta.state y ∈ zipBetas t₁.rhs t₂.rhs → y ∈ qs := by
        intro y hy
        exact hspec.closed _ hin y hy
      refine TA.mem_evalT_node.mpr ⟨⟨x, t₁.sym, zipBetas t₁.rhs t₂.rhs⟩,
        (hspec.mem_realTrans hC).mpr hin, hs₁, ?_, rfl⟩
      exact matchAll_zip_build (A := A) (B := B) (C := C) ts ih t₁.rhs t₂.rhs hqs hcompat hm₁ hm₂

/-- **The first stage of Algorithm 3.3 is correct**: it recognises `L(A) ∩ L(B)`. -/
theorem stage0_lang (hspec : Stage0Spec A B qs δ) (hC : C.trans = δ)
    (hfin : ∀ p : σ₁ × σ₂, p ∈ C.finals ↔ p ∈ pairs A.finals B.finals) (t : Tree) :
    C.Lang t ↔ A.Lang t ∧ B.Lang t := by
  have hne : C.NoEps := hspec.trans_noEps hC
  rw [TA.lang_iff_ev, TA.lang_iff_ev, TA.lang_iff_ev]
  constructor
  · rintro ⟨x, hx, hev⟩
    obtain ⟨hf₁, hf₂⟩ := mem_pairs.mp ((hfin x).mp hx)
    obtain ⟨e₁, e₂⟩ := stage0_sound hspec hC t x ((TA.ev_iff_mem_evalT hne).mp hev)
    exact ⟨⟨x.1, hf₁, e₁⟩, ⟨x.2, hf₂, e₂⟩⟩
  · rintro ⟨⟨f₁, hf₁, he₁⟩, ⟨f₂, hf₂, he₂⟩⟩
    refine ⟨(f₁, f₂), (hfin _).mpr (mem_pairs.mpr ⟨hf₁, hf₂⟩), ?_⟩
    refine (TA.ev_iff_mem_evalT hne).mpr ?_
    exact stage0_complete hspec hC t (f₁, f₂)
      (hspec.finals _ (mem_pairs.mpr ⟨hf₁, hf₂⟩)) he₁ he₂

end Stage0


/-! ### The second stage: merging duplicate states (Algorithm 3.4)

Two states with the same *signature* — the same incoming transitions, once each is
replaced by a placeholder in its own right-hand sides — accept exactly the same trees.
The proof is an induction on the size of the tree: a transition into `e₁` has a twin into
`e₂` whose right-hand side differs only where `betaSubst` put the placeholder, and there
the children are strictly smaller trees.
-/

/-- Two states have the same incoming transitions, up to renaming themselves. -/
def SigEq (δ : List (Transition σ)) (e₁ e₂ : σ) : Prop :=
  ∀ x, x ∈ stateSig δ e₁ ↔ x ∈ stateSig δ e₂

theorem SigEq.refl (δ : List (Transition σ)) (e : σ) : SigEq δ e e := fun _ => Iff.rfl

theorem SigEq.symm {δ : List (Transition σ)} {e₁ e₂ : σ} (h : SigEq δ e₁ e₂) :
    SigEq δ e₂ e₁ := fun x => (h x).symm

theorem SigEq.trans {δ : List (Transition σ)} {e₁ e₂ e₃ : σ} (h₁ : SigEq δ e₁ e₂)
    (h₂ : SigEq δ e₂ e₃) : SigEq δ e₁ e₃ := fun x => (h₁ x).trans (h₂ x)

theorem mem_stateSig {δ : List (Transition σ)} {e : σ} {x : Sym × List (Beta (Option σ))} :
    x ∈ stateSig δ e ↔ ∃ tr ∈ δ, tr.target = e ∧ (tr.sym, tr.rhs.map (betaSubst e)) = x := by
  simp only [stateSig, List.mem_dedup, List.mem_map, List.mem_filter, beq_iff_eq]
  exact ⟨fun ⟨tr, ⟨htr, htgt⟩, hx⟩ => ⟨tr, htr, htgt, hx⟩,
         fun ⟨tr, htr, htgt, hx⟩ => ⟨tr, ⟨htr, htgt⟩, hx⟩⟩

theorem sameElems_iff {α : Type} [DecidableEq α] {l₁ l₂ : List α} :
    sameElems l₁ l₂ = true ↔ ∀ x, x ∈ l₁ ↔ x ∈ l₂ := by
  simp only [sameElems, Bool.and_eq_true, List.all_eq_true, List.elem_eq_mem,
    decide_eq_true_eq]
  exact ⟨fun ⟨h₁, h₂⟩ x => ⟨fun h => h₁ x h, fun h => h₂ x h⟩,
         fun h => ⟨fun x hx => (h x).mp hx, fun x hx => (h x).mpr hx⟩⟩

theorem mem_findDupStates {qs : List σ} {δ : List (Transition σ)} {p : σ × σ} :
    p ∈ findDupStates qs δ ↔
      p.1 ∈ qs ∧ p.2 ∈ qs ∧ p.2 ≠ p.1 ∧
        sameElems (stateSig δ p.1) (stateSig δ p.2) = true := by
  simp only [findDupStates, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨ei, hei, ej, ⟨hej, hne⟩, hif⟩
    split at hif
    · next hs =>
        simp only [Option.some.injEq] at hif
        subst hif
        exact ⟨hei, hej, hne, hs⟩
    · simp at hif
  · rintro ⟨h₁, h₂, hne, hs⟩
    exact ⟨p.1, h₁, p.2, ⟨h₂, hne⟩, by rw [if_pos hs]⟩

theorem keepStep_subset (acc : List (σ × σ)) (p : σ × σ) : keepStep acc p ⊆ acc ++ [p] := by
  simp only [keepStep]
  split
  · exact fun _ h => List.mem_append_left _ h
  · split
    · exact fun _ h => List.mem_append_left _ h
    · exact fun _ h => h

theorem foldl_keepStep_subset :
    ∀ (l acc : List (σ × σ)), l.foldl keepStep acc ⊆ acc ++ l := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons p l ih =>
      intro acc
      refine fun z hz => ?_
      have := ih (keepStep acc p) hz
      rcases List.mem_append.mp this with h | h
      · rcases List.mem_append.mp (keepStep_subset acc p h) with h' | h'
        · exact List.mem_append_left _ h'
        · exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl (by simpa using h')))
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

theorem mergeKeep_mem {qs : List σ} {δ : List (Transition σ)} {p : σ × σ}
    (h : p ∈ mergeKeep qs δ) : p ∈ findDupStates qs δ ∧ p.1 ≠ p.2 := by
  have := foldl_keepStep_subset _ [] h
  simp only [List.nil_append, List.mem_filter, bne_iff_ne, ne_eq] at this
  exact this

theorem canonOf_cases (dups : List (σ × σ)) (e : σ) :
    canonOf dups e = e ∨ ∃ p ∈ dups, p.2 = e ∧ canonOf dups e = p.1 := by
  simp only [canonOf]
  split
  · next p h =>
      have hp := List.mem_of_find?_eq_some h
      have hsat := List.find?_eq_some_iff_getElem.mp h
      refine Or.inr ⟨p, hp, ?_, rfl⟩
      have : (p.2 == e && p.1 != e) = true := hsat.1
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact this.1
  · exact Or.inl rfl

/-- Every state is sent by `canonOf` to a state with the same signature. -/
theorem canonOf_mergeKeep_sigEq (qs : List σ) (δ : List (Transition σ)) (e : σ) :
    SigEq δ (canonOf (mergeKeep qs δ) e) e := by
  rcases canonOf_cases (mergeKeep qs δ) e with h | ⟨p, hp, hp2, hcan⟩
  · rw [h]; exact SigEq.refl _ _
  · rw [hcan]
    obtain ⟨hdup, -⟩ := mergeKeep_mem hp
    have hs := (mem_findDupStates.mp hdup).2.2.2
    rw [← hp2]
    exact fun x => sameElems_iff.mp hs x

theorem betaSubst_eq_cases {e₁ e₂ : σ} {b b' : Beta σ}
    (h : betaSubst e₂ b' = betaSubst e₁ b) :
    (∃ a, b = .term a ∧ b' = .term a) ∨ (b = .state e₁ ∧ b' = .state e₂) ∨
      (∃ x, b = .state x ∧ b' = .state x) := by
  cases b with
  | term a =>
      cases b' with
      | term a' =>
          simp only [betaSubst, Beta.term.injEq] at h
          exact Or.inl ⟨a, rfl, by rw [h]⟩
      | state y => simp [betaSubst] at h
  | state x =>
      cases b' with
      | term a' => simp [betaSubst] at h
      | state y =>
          simp only [betaSubst, Beta.state.injEq] at h
          by_cases hx : x = e₁
          · rw [if_pos hx] at h
            by_cases hy : y = e₂
            · exact Or.inr (Or.inl ⟨by rw [hx], by rw [hy]⟩)
            · rw [if_neg hy] at h; exact absurd h (by simp)
          · rw [if_neg hx] at h
            by_cases hy : y = e₂
            · rw [if_pos hy] at h; exact absurd h (by simp)
            · rw [if_neg hy, Option.some.injEq] at h
              subst h
              exact Or.inr (Or.inr ⟨y, rfl, rfl⟩)


/-- **The key lemma of Algorithm 3.4.**  States with equal signatures accept the same
trees.  (Stated for ε-free automata, which is what the first two stages produce.) -/
theorem sigEq_evalT {C : TA σ} :
    ∀ (t : Tree) (e₁ e₂ : σ), SigEq C.trans e₁ e₂ →
      e₁ ∈ C.evalT (fun z => [z]) t → e₂ ∈ C.evalT (fun z => [z]) t := by
  intro t
  induction t using Tree.rec' with
  | hleaf a => intro e₁ e₂ _ h; simp at h
  | hnode fs ts ih =>
      intro e₁ e₂ hsig h
      obtain ⟨tr, htr, hsym, hm, htgt⟩ := TA.mem_evalT_node.mp h
      have hmem : (tr.sym, tr.rhs.map (betaSubst e₁)) ∈ stateSig C.trans e₁ :=
        mem_stateSig.mpr ⟨tr, TA.realTrans_subset htr, htgt, rfl⟩
      obtain ⟨tr', htr', htgt', heq⟩ := mem_stateSig.mp ((hsig _).mp hmem)
      have hsym' : tr'.sym = tr.sym := by
        have := congrArg Prod.fst heq; simpa using this
      have hrhs : tr'.rhs.map (betaSubst e₂) = tr.rhs.map (betaSubst e₁) := by
        have := congrArg Prod.snd heq; simpa using this
      have hne' : (tr'.sym != epsSym) = true := by
        rw [hsym']; exact (List.mem_filter.mp htr).2
      have hreal : tr' ∈ C.realTrans := List.mem_filter.mpr ⟨htr', hne'⟩
      have hlen : tr'.rhs.length = tr.rhs.length := by
        have := congrArg List.length hrhs; simpa using this
      have hlents : ts.length = tr.rhs.length := TA.matchAll_length ts tr.rhs hm
      refine TA.mem_evalT_node.mpr ⟨tr', hreal, hsym'.trans hsym, ?_, htgt'⟩
      refine TA.matchAll_of_forall ts tr'.rhs (by omega) ?_
      intro k u b' hu hb'
      have hk : k < tr.rhs.length := by
        have hk' : k < tr'.rhs.length := (List.getElem?_eq_some_iff.mp hb').1
        omega
      obtain ⟨b, hb⟩ : ∃ b, tr.rhs[k]? = some b := ⟨tr.rhs[k], List.getElem?_eq_getElem hk⟩
      have hmapeq : betaSubst e₂ b' = betaSubst e₁ b := by
        have h1 : (tr'.rhs.map (betaSubst e₂))[k]? = some (betaSubst e₂ b') := by
          rw [List.getElem?_map, hb']; rfl
        have h2 : (tr.rhs.map (betaSubst e₁))[k]? = some (betaSubst e₁ b) := by
          rw [List.getElem?_map, hb]; rfl
        rw [hrhs, h2, Option.some.injEq] at h1
        exact h1.symm
      have hgot := TA.matchAll_get ts tr.rhs hm k u b hu hb
      have humem : u ∈ ts := List.mem_of_getElem? hu
      rcases betaSubst_eq_cases hmapeq with ⟨a, ha, ha'⟩ | ⟨ha, ha'⟩ | ⟨x, ha, ha'⟩
      · subst ha; subst ha'; exact hgot
      · subst ha; subst ha'
        simp only at hgot ⊢
        obtain ⟨r, hr, hq⟩ := hgot
        have hre : r = e₁ := (List.mem_singleton.mp hq).symm
        subst hre
        exact ⟨e₂, ih u humem r e₂ hsig hr, by simp⟩
      · subst ha; subst ha'; exact hgot

/-! ### Merging along a signature-preserving renaming -/

/-- The action of `renameTrans` on one right-hand-side entry. -/
def renameBeta (f : σ → σ) : Beta σ → Beta σ
  | .state x => .state (f x)
  | .term a  => .term a

omit [DecidableEq σ] in
theorem renameTrans_rhs (f : σ → σ) (tr : Transition σ) :
    (renameTrans f tr).rhs = tr.rhs.map (renameBeta f) := rfl

section Merge

variable {C D : TA σ} {f : σ → σ}

/-- The image of a transition under the renaming. -/
theorem mem_renamed {δ : List (Transition σ)} {tr : Transition σ} (h : tr ∈ δ) :
    renameTrans f tr ∈ (δ.map (renameTrans f)).dedup :=
  List.mem_dedup.mpr (List.mem_map_of_mem h)

theorem renamed_mem {δ : List (Transition σ)} {tr' : Transition σ}
    (h : tr' ∈ (δ.map (renameTrans f)).dedup) : ∃ tr ∈ δ, renameTrans f tr = tr' := by
  simpa using List.mem_dedup.mp h

omit [DecidableEq σ] in
theorem renameTrans_rhs_getElem {tr : Transition σ} {k : Nat} {b : Beta σ}
    (h : tr.rhs[k]? = some b) :
    (renameTrans f tr).rhs[k]? = some (renameBeta f b) := by
  rw [renameTrans_rhs, List.getElem?_map, h]; rfl

theorem renameTrans_noEps (hne : C.NoEps)
    (hD : D.trans = (C.trans.map (renameTrans f)).dedup) : D.NoEps := by
  intro tr htr
  obtain ⟨tr₀, htr₀, rfl⟩ := renamed_mem (hD ▸ htr)
  exact hne tr₀ htr₀

theorem mem_realTrans_renamed (hD : D.trans = (C.trans.map (renameTrans f)).dedup)
    {tr : Transition σ} (h : tr ∈ C.realTrans) : renameTrans f tr ∈ D.realTrans := by
  refine List.mem_filter.mpr ⟨hD ▸ mem_renamed (TA.realTrans_subset h), ?_⟩
  exact (List.mem_filter.mp h).2

/-- The renaming is a homomorphism: whatever `C` assigns, `D` assigns to the image. -/
theorem merge_hom (hD : D.trans = (C.trans.map (renameTrans f)).dedup) :
    ∀ (t : Tree) (q : σ), q ∈ C.evalT (fun z => [z]) t →
      f q ∈ D.evalT (fun z => [z]) t := by
  intro t
  induction t using Tree.rec' with
  | hleaf a => intro q h; simp at h
  | hnode fs ts ih =>
      intro q h
      obtain ⟨tr, htr, hsym, hm, htgt⟩ := TA.mem_evalT_node.mp h
      have hlents : ts.length = tr.rhs.length := TA.matchAll_length ts tr.rhs hm
      refine TA.mem_evalT_node.mpr ⟨renameTrans f tr, mem_realTrans_renamed hD htr,
        hsym, ?_, by simp only [renameTrans]; rw [htgt]⟩
      refine TA.matchAll_of_forall ts (renameTrans f tr).rhs ?_ ?_
      · rw [renameTrans_rhs, List.length_map]; exact hlents
      · intro k u b' hu hb'
        have hk : k < tr.rhs.length := by
          have : k < ts.length := (List.getElem?_eq_some_iff.mp hu).1
          omega
        obtain ⟨b, hb⟩ : ∃ b, tr.rhs[k]? = some b := ⟨tr.rhs[k], List.getElem?_eq_getElem hk⟩
        have hb'' : (renameTrans f tr).rhs[k]? = some (renameBeta f b) :=
          renameTrans_rhs_getElem hb
        rw [hb', Option.some.injEq] at hb''
        subst hb''
        have hgot := TA.matchAll_get ts tr.rhs hm k u b hu hb
        have humem : u ∈ ts := List.mem_of_getElem? hu
        cases b with
        | term a => exact hgot
        | state x =>
            simp only [renameBeta] at *
            obtain ⟨r, hr, hq⟩ := hgot
            have hxr : x = r := List.mem_singleton.mp hq
            have hx : x ∈ C.evalT (fun z => [z]) u := by rw [hxr]; exact hr
            exact ⟨f x, ih u humem x hx, by simp⟩

/-- Conversely, everything `D` assigns comes from something `C` assigns. -/
theorem merge_inv (hD : D.trans = (C.trans.map (renameTrans f)).dedup)
    (hsig : ∀ e, SigEq C.trans (f e) e) :
    ∀ (t : Tree) (q' : σ), q' ∈ D.evalT (fun z => [z]) t →
      ∃ q, q ∈ C.evalT (fun z => [z]) t ∧ f q = q' := by
  intro t
  induction t using Tree.rec' with
  | hleaf a => intro q h; simp at h
  | hnode fs ts ih =>
      intro q' h
      obtain ⟨tr', htr', hsym, hm, htgt⟩ := TA.mem_evalT_node.mp h
      obtain ⟨tr, htr, rfl⟩ := renamed_mem (hD ▸ TA.realTrans_subset htr')
      have hreal : tr ∈ C.realTrans :=
        List.mem_filter.mpr ⟨htr, (List.mem_filter.mp htr').2⟩
      have hlents : ts.length = tr.rhs.length := by
        have := TA.matchAll_length ts (renameTrans f tr).rhs hm
        rw [renameTrans_rhs, List.length_map] at this
        exact this
      refine ⟨tr.target, TA.mem_evalT_node.mpr ⟨tr, hreal, hsym, ?_, rfl⟩, htgt⟩
      refine TA.matchAll_of_forall ts tr.rhs hlents ?_
      intro k u b hu hb
      have hgot := TA.matchAll_get ts (renameTrans f tr).rhs hm k u (renameBeta f b) hu
        (renameTrans_rhs_getElem hb)
      have humem : u ∈ ts := List.mem_of_getElem? hu
      cases b with
      | term a => exact hgot
      | state x =>
          simp only [renameBeta] at *
          obtain ⟨r, hr, hq⟩ := hgot
          have hfr : f x = r := List.mem_singleton.mp hq
          obtain ⟨y, hy, hfy⟩ := ih u humem r hr
          have hfy' : SigEq C.trans (f y) x := by rw [hfy, ← hfr]; exact hsig x
          exact ⟨x, sigEq_evalT u y x ((hsig y).symm.trans hfy') hy, by simp⟩

end Merge


/-! ### Two automata with the same transitions have the same `Ev` -/

omit [DecidableEq σ] in
theorem epsReach_congr {C D : TA σ}
    (hed : ∀ x y : σ, (x, y) ∈ C.epsEdges ↔ (x, y) ∈ D.epsEdges) {x y : σ} :
    EpsReach C x y ↔ EpsReach D x y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | step he _ ih => exact .step ((hed _ _).mp he) ih
  · intro h
    induction h with
    | refl => exact .refl _
    | step he _ ih => exact .step ((hed _ _).mpr he) ih

theorem TA.ev_congr {C D : TA σ}
    (htr : ∀ tr : Transition σ, tr ∈ C.realTrans ↔ tr ∈ D.realTrans)
    (hed : ∀ x y : σ, (x, y) ∈ C.epsEdges ↔ (x, y) ∈ D.epsEdges) (t : Tree) (q : σ) :
    C.Ev t q ↔ D.Ev t q := by
  have hclD : IsEpsClosure D D.epsTable := D.isEpsClosure_epsTable
  have hclC : IsEpsClosure C D.epsTable := by
    intro a b
    rw [hclD a b]
    exact (epsReach_congr hed).symm
  rw [TA.ev_iff_tbl hclC, TA.ev_iff_tbl hclD]
  constructor
  · rintro ⟨r, hr, hq⟩
    exact ⟨r, evalT_mono (fun tr h => (htr tr).mp h) (fun _ _ h => h) t r hr, hq⟩
  · rintro ⟨r, hr, hq⟩
    exact ⟨r, evalT_mono (fun tr h => (htr tr).mpr h) (fun _ _ h => h) t r hr, hq⟩

theorem TA.ev_congr_trans {C D : TA σ} (h : C.trans = D.trans) (t : Tree) (q : σ) :
    C.Ev t q ↔ D.Ev t q :=
  TA.ev_congr (by rw [TA.realTrans, TA.realTrans, h]; exact fun _ => Iff.rfl)
    (by rw [TA.epsEdges, TA.epsEdges, h]; exact fun _ _ => Iff.rfl) t q

/-! ### The third stage: introducing ε-transitions

One step replaces, at `eⱼ`, every transition whose shape is also a shape of `eᵢ` by the
single ε-transition `eⱼ ←ε eᵢ`.  Soundness rests on the *subsumption lemma*: when every
shape of `eᵢ` is a shape of `eⱼ`, anything `eᵢ` accepts `eⱼ` accepts too, so the new
ε-edge adds nothing; and the removed transitions are recovered through `eᵢ`.  No acyclicity
is needed: the argument never looks at the ε-graph as a whole.
-/

theorem mem_shapesOf {δ : List (Transition σ)} {e : σ} {x : Sym × List (Beta σ)} :
    x ∈ shapesOf δ e ↔ ∃ tr ∈ δ, tr.target = e ∧ (tr.sym, tr.rhs) = x := by
  simp only [shapesOf, List.mem_dedup, List.mem_map, List.mem_filter, beq_iff_eq]
  exact ⟨fun ⟨tr, ⟨htr, htgt⟩, hx⟩ => ⟨tr, htr, htgt, hx⟩,
         fun ⟨tr, htr, htgt, hx⟩ => ⟨tr, ⟨htr, htgt⟩, hx⟩⟩

section IntroEps

variable {C D : TA σ} {ei ej : σ}

/-- Shapes of `eᵢ` that are shapes of `eⱼ` transfer direct assignments. -/
theorem shapes_evalT (hsub : ∀ x ∈ shapesOf C.trans ei, x ∈ shapesOf C.trans ej)
    (tbl : EpsTable σ) (t : Tree) (h : ei ∈ C.evalT tbl t) : ej ∈ C.evalT tbl t := by
  cases t with
  | leaf a => simp at h
  | node fs ts =>
      obtain ⟨tr, htr, hsym, hm, htgt⟩ := TA.mem_evalT_node.mp h
      obtain ⟨tr', htr', htgt', heq⟩ := mem_shapesOf.mp
        (hsub _ (mem_shapesOf.mpr ⟨tr, TA.realTrans_subset htr, htgt, rfl⟩))
      have hs : tr'.sym = tr.sym := by have := congrArg Prod.fst heq; simpa using this
      have hr : tr'.rhs = tr.rhs := by have := congrArg Prod.snd heq; simpa using this
      refine TA.mem_evalT_node.mpr ⟨tr', List.mem_filter.mpr ⟨htr', ?_⟩, ?_, ?_, htgt'⟩
      · rw [hs]; exact (List.mem_filter.mp htr).2
      · rw [hs]; exact hsym
      · rw [hr]; exact hm

/-- The same for ε-edges. -/
theorem shapes_edge (hsub : ∀ x ∈ shapesOf C.trans ei, x ∈ shapesOf C.trans ej) {x : σ}
    (h : (x, ei) ∈ C.epsEdges) : (x, ej) ∈ C.epsEdges := by
  obtain ⟨tr, htr, hsym, hrhs, htgt⟩ := mem_epsEdges.mp h
  obtain ⟨tr', htr', htgt', heq⟩ := mem_shapesOf.mp
    (hsub _ (mem_shapesOf.mpr ⟨tr, htr, htgt, rfl⟩))
  have hs : tr'.sym = tr.sym := by have := congrArg Prod.fst heq; simpa using this
  have hr : tr'.rhs = tr.rhs := by have := congrArg Prod.snd heq; simpa using this
  exact mem_epsEdges.mpr ⟨tr', htr', hs.trans hsym, hr.trans hrhs, htgt'⟩

/-- **The subsumption lemma.**  If every shape of `eᵢ` is a shape of `eⱼ`, then every tree
that may be assigned `eᵢ` may be assigned `eⱼ`. -/
theorem shapes_ev (hsub : ∀ x ∈ shapesOf C.trans ei, x ∈ shapesOf C.trans ej) (t : Tree)
    (h : C.Ev t ei) : C.Ev t ej := by
  obtain ⟨r, hr, hreach⟩ := h
  rcases hreach.cases_last with heq | ⟨x, hx, hxe⟩
  · subst heq
    exact TA.ev_of_mem_evalT (shapes_evalT hsub _ t hr)
  · exact ⟨r, hr, hx.trans (.step (shapes_edge hsub hxe) (.refl _))⟩

/-- The transitions of one ε-introduction step, as a membership criterion. -/
def IntroStep (C D : TA σ) (ei ej : σ) : Prop :=
  ∀ tr : Transition σ, tr ∈ D.trans ↔
    ((tr ∈ C.trans ∧ ¬(tr.target = ej ∧ (tr.sym, tr.rhs) ∈ shapesOf C.trans ei)) ∨
      tr = ⟨ej, epsSym, [.state ei]⟩)

theorem introStep_realTrans (hD : IntroStep C D ei ej) {tr : Transition σ}
    (h : tr ∈ D.realTrans) : tr ∈ C.realTrans := by
  have hsym : (tr.sym != epsSym) = true := (List.mem_filter.mp h).2
  rcases (hD tr).mp (List.mem_filter.mp h).1 with ⟨htr, -⟩ | rfl
  · exact List.mem_filter.mpr ⟨htr, hsym⟩
  · simp at hsym

theorem introStep_new_edge (hD : IntroStep C D ei ej) : (ei, ej) ∈ D.epsEdges :=
  mem_epsEdges.mpr ⟨⟨ej, epsSym, [.state ei]⟩, (hD _).mpr (Or.inr rfl), rfl, rfl, rfl⟩

/-- Every ε-edge of the old automaton is still available, possibly through `eᵢ`. -/
theorem introStep_edge_old (hne : ei ≠ ej)
    (hsub : ∀ x ∈ shapesOf C.trans ei, x ∈ shapesOf C.trans ej) (hD : IntroStep C D ei ej)
    {x y : σ} (h : (x, y) ∈ C.epsEdges) : EpsReach D x y := by
  obtain ⟨tr, htr, hsym, hrhs, htgt⟩ := mem_epsEdges.mp h
  by_cases hrem : tr.target = ej ∧ (tr.sym, tr.rhs) ∈ shapesOf C.trans ei
  · -- the ε-transition was removed; the twin at `eᵢ` survives, and `eᵢ ≤ε eⱼ` is new
    obtain ⟨tr', htr', htgt', heq⟩ := mem_shapesOf.mp hrem.2
    have hs : tr'.sym = tr.sym := by have := congrArg Prod.fst heq; simpa using this
    have hr : tr'.rhs = tr.rhs := by have := congrArg Prod.snd heq; simpa using this
    have hmem : tr' ∈ D.trans := (hD tr').mpr (Or.inl ⟨htr', by
      rw [htgt']; exact fun hc => hne hc.1⟩)
    have hedge : (x, ei) ∈ D.epsEdges :=
      mem_epsEdges.mpr ⟨tr', hmem, hs.trans hsym, hr.trans hrhs, htgt'⟩
    have hy : y = ej := by rw [← htgt, hrem.1]
    subst hy
    exact .step hedge (.step (introStep_new_edge hD) (.refl _))
  · exact .step (mem_epsEdges.mpr ⟨tr, (hD tr).mpr (Or.inl ⟨htr, hrem⟩), hsym, hrhs, htgt⟩)
      (.refl _)

theorem introStep_edge_inv (hD : IntroStep C D ei ej) {x y : σ} (h : (x, y) ∈ D.epsEdges) :
    (x, y) ∈ C.epsEdges ∨ (x = ei ∧ y = ej) := by
  obtain ⟨tr, htr, hsym, hrhs, htgt⟩ := mem_epsEdges.mp h
  rcases (hD tr).mp htr with ⟨htr', -⟩ | rfl
  · exact Or.inl (mem_epsEdges.mpr ⟨tr, htr', hsym, hrhs, htgt⟩)
  · have hx : ei = x := by simpa using hrhs
    exact Or.inr ⟨hx.symm, htgt.symm⟩

/-- **One ε-introduction step preserves the language**, at the level of `Ev`. -/
theorem introStep_ev (hne : ei ≠ ej)
    (hsub : ∀ x ∈ shapesOf C.trans ei, x ∈ shapesOf C.trans ej) (hD : IntroStep C D ei ej) :
    ∀ (t : Tree) (q : σ), D.Ev t q ↔ C.Ev t q := by
  intro t
  induction t using Tree.rec' with
  | hleaf a => intro q; exact ⟨fun h => absurd h TA.ev_leaf, fun h => absurd h TA.ev_leaf⟩
  | hnode fs ts ih =>
      have hmatch : ∀ bs : List (Beta σ),
          D.matchAll D.epsTable ts bs = C.matchAll C.epsTable ts bs :=
        fun bs => matchAll_ev_congr D.isEpsClosure_epsTable C.isEpsClosure_epsTable ts bs ih
      have hV1 : ∀ q, q ∈ D.evalT D.epsTable (.node fs ts) →
          q ∈ C.evalT C.epsTable (.node fs ts) := by
        intro q hq
        obtain ⟨tr, htr, hsym, hm, htgt⟩ := TA.mem_evalT_node.mp hq
        exact TA.mem_evalT_node.mpr ⟨tr, introStep_realTrans hD htr, hsym,
          by rw [← hmatch]; exact hm, htgt⟩
      have hV2 : ∀ q, q ∈ C.evalT C.epsTable (.node fs ts) → D.Ev (.node fs ts) q := by
        intro q hq
        obtain ⟨tr, htr, hsym, hm, htgt⟩ := TA.mem_evalT_node.mp hq
        by_cases hrem : tr.target = ej ∧ (tr.sym, tr.rhs) ∈ shapesOf C.trans ei
        · obtain ⟨tr', htr', htgt', heq⟩ := mem_shapesOf.mp hrem.2
          have hs : tr'.sym = tr.sym := by have := congrArg Prod.fst heq; simpa using this
          have hr : tr'.rhs = tr.rhs := by have := congrArg Prod.snd heq; simpa using this
          have hmem : tr' ∈ D.trans := (hD tr').mpr (Or.inl ⟨htr', by
            rw [htgt']; exact fun hc => hne hc.1⟩)
          have hreal : tr' ∈ D.realTrans := by
            refine List.mem_filter.mpr ⟨hmem, ?_⟩
            rw [hs]; exact (List.mem_filter.mp htr).2
          have hei : ei ∈ D.evalT D.epsTable (.node fs ts) :=
            TA.mem_evalT_node.mpr ⟨tr', hreal, by rw [hs]; exact hsym,
              by rw [hr, hmatch]; exact hm, htgt'⟩
          have hq' : q = ej := by rw [← htgt, hrem.1]
          rw [hq']
          exact ⟨ei, hei, .step (introStep_new_edge hD) (.refl _)⟩
        · have hmem : tr ∈ D.trans :=
            (hD tr).mpr (Or.inl ⟨TA.realTrans_subset htr, hrem⟩)
          refine TA.ev_of_mem_evalT (TA.mem_evalT_node.mpr ⟨tr,
            List.mem_filter.mpr ⟨hmem, (List.mem_filter.mp htr).2⟩, hsym, ?_, htgt⟩)
          rw [hmatch]; exact hm
      intro q
      constructor
      · rintro ⟨r, hr, hreach⟩
        have hCr : C.Ev (.node fs ts) r := TA.ev_of_mem_evalT (hV1 r hr)
        have gen : ∀ x y : σ, EpsReach D x y →
            C.Ev (.node fs ts) x → C.Ev (.node fs ts) y := by
          intro x y h
          induction h with
          | refl => exact id
          | @step a b _ he _ ihh =>
              intro hEv
              refine ihh ?_
              rcases introStep_edge_inv hD he with hc | ⟨hx, hy⟩
              · exact TA.ev_promote hEv (.step hc (.refl _))
              · rw [hy]; rw [hx] at hEv; exact shapes_ev hsub _ hEv
        exact gen r q hreach hCr
      · rintro ⟨r, hr, hreach⟩
        have hDr : D.Ev (.node fs ts) r := hV2 r hr
        have gen : ∀ x y : σ, EpsReach C x y →
            D.Ev (.node fs ts) x → D.Ev (.node fs ts) y := by
          intro x y h
          induction h with
          | refl => exact id
          | @step a b _ he _ ihh =>
              intro hEv
              exact ihh (TA.ev_promote hEv (introStep_edge_old hne hsub hD he))
        exact gen r q hreach hDr


/-- The membership criterion `IntroStep`, read off the definition of `introEpsStep`. -/
theorem introEpsStep_ev (C D : TA σ) (ei ej : σ)
    (hD : D.trans = introEpsStep C.trans ei ej) :
    ∀ (t : Tree) (q : σ), D.Ev t q ↔ C.Ev t q := by
  by_cases hg : (ei != ej && !(shapesOf C.trans ei).isEmpty &&
      (shapesOf C.trans ei).all fun x => (shapesOf C.trans ej).contains x) = true
  · have hg' := hg
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, List.elem_eq_mem,
      decide_eq_true_eq] at hg'
    have hne : ei ≠ ej := hg'.1.1
    have hsub : ∀ x ∈ shapesOf C.trans ei, x ∈ shapesOf C.trans ej := hg'.2
    have hstep : introEpsStep C.trans ei ej =
        (C.trans.filter fun tr =>
            !(tr.target == ej && (shapesOf C.trans ei).contains (tr.sym, tr.rhs)))
          ++ [⟨ej, epsSym, [.state ei]⟩] := by
      simp only [introEpsStep]
      rw [if_pos hg]
    have hcond : ∀ tr : Transition σ,
        ((!(tr.target == ej && (shapesOf C.trans ei).contains (tr.sym, tr.rhs))) = true) ↔
          ¬(tr.target = ej ∧ (tr.sym, tr.rhs) ∈ shapesOf C.trans ei) := by
      intro tr
      cases h₁ : (tr.target == ej) <;>
        cases h₂ : ((shapesOf C.trans ei).contains (tr.sym, tr.rhs)) <;>
        simp_all
    refine introStep_ev hne hsub ?_
    intro tr
    rw [hD, hstep]
    simp only [List.mem_append, List.mem_filter, List.mem_singleton, hcond]
  · have heq : introEpsStep C.trans ei ej = C.trans := by
      simp only [introEpsStep, if_neg hg]
    intro t q
    exact TA.ev_congr_trans (by rw [hD, heq]) t q

end IntroEps


/-! ### The ε-introduction loop -/

/-- Replace the transitions of an automaton. -/
def TA.setTrans (C : TA σ) (δ : List (Transition σ)) : TA σ := { C with trans := δ }

omit [DecidableEq σ] in
@[simp] theorem TA.setTrans_trans (C : TA σ) (δ : List (Transition σ)) :
    (C.setTrans δ).trans = δ := rfl

omit [DecidableEq σ] in
@[simp] theorem TA.setTrans_finals (C : TA σ) (δ : List (Transition σ)) :
    (C.setTrans δ).finals = C.finals := rfl

theorem introEpsStep_setTrans_ev (C : TA σ) (δ : List (Transition σ)) (ei ej : σ) (t : Tree)
    (q : σ) : (C.setTrans (introEpsStep δ ei ej)).Ev t q ↔ (C.setTrans δ).Ev t q :=
  introEpsStep_ev (C.setTrans δ) (C.setTrans (introEpsStep δ ei ej)) ei ej rfl t q

theorem foldl_introEpsStep_ev (C : TA σ) (ei : σ) :
    ∀ (l : List σ) (δ : List (Transition σ)) (t : Tree) (q : σ),
      (C.setTrans (l.foldl (fun acc ej => introEpsStep acc ei ej) δ)).Ev t q ↔
        (C.setTrans δ).Ev t q := by
  intro l
  induction l with
  | nil => intro δ t q; exact Iff.rfl
  | cons ej l ih =>
      intro δ t q
      exact (ih (introEpsStep δ ei ej) t q).trans (introEpsStep_setTrans_ev C δ ei ej t q)

theorem foldl_introEpsOuter_ev (C : TA σ) (ordered : List σ) :
    ∀ (l : List (σ × Nat)) (δ : List (Transition σ)) (t : Tree) (q : σ),
      (C.setTrans (l.foldl (fun acc pi =>
        (ordered.drop (pi.2 + 1)).foldl (fun acc' ej => introEpsStep acc' pi.1 ej) acc)
          δ)).Ev t q ↔ (C.setTrans δ).Ev t q := by
  intro l
  induction l with
  | nil => intro δ t q; exact Iff.rfl
  | cons pi l ih =>
      intro δ t q
      exact (ih _ t q).trans (foldl_introEpsStep_ev C pi.1 (ordered.drop (pi.2 + 1)) δ t q)

/-- **The ε-introduction loop preserves the language**, whatever the order of visits. -/
theorem introEpsAll_ev (C : TA σ) (qs : List σ) (δ : List (Transition σ)) (t : Tree)
    (q : σ) : (C.setTrans (introEpsAll qs δ)).Ev t q ↔ (C.setTrans δ).Ev t q := by
  simp only [introEpsAll]
  exact foldl_introEpsOuter_ev C _ _ δ t q

theorem introEpsAll_lang (C : TA σ) (qs : List σ) (δ : List (Transition σ)) (t : Tree) :
    (C.setTrans (introEpsAll qs δ)).Lang t ↔ (C.setTrans δ).Lang t := by
  rw [TA.lang_iff_ev, TA.lang_iff_ev]
  simp only [TA.setTrans_finals]
  exact ⟨fun ⟨f, hf, hev⟩ => ⟨f, hf, (introEpsAll_ev C qs δ t f).mp hev⟩,
         fun ⟨f, hf, hev⟩ => ⟨f, hf, (introEpsAll_ev C qs δ t f).mpr hev⟩⟩


/-! ### Merging preserves the language -/

theorem merge_lang {C D : TA σ} {f : σ → σ}
    (hD : D.trans = (C.trans.map (renameTrans f)).dedup) (hne : C.NoEps)
    (hsig : ∀ e, SigEq C.trans (f e) e)
    (hfin₁ : ∀ q ∈ C.finals, f q ∈ D.finals) (hfin₂ : ∀ q ∈ D.finals, q ∈ C.finals)
    (t : Tree) : D.Lang t ↔ C.Lang t := by
  have hneD : D.NoEps := renameTrans_noEps hne hD
  rw [TA.lang_iff_ev, TA.lang_iff_ev]
  constructor
  · rintro ⟨q', hq', hev⟩
    obtain ⟨q, hq, hfq⟩ := merge_inv hD hsig t q' ((TA.ev_iff_mem_evalT hneD).mp hev)
    have hsq : SigEq C.trans q q' := by rw [← hfq]; exact (hsig q).symm
    exact ⟨q', hfin₂ q' hq', (TA.ev_iff_mem_evalT hne).mpr (sigEq_evalT t q q' hsq hq)⟩
  · rintro ⟨q, hq, hev⟩
    exact ⟨f q, hfin₁ q hq, (TA.ev_iff_mem_evalT hneD).mpr
      (merge_hom hD t q ((TA.ev_iff_mem_evalT hne).mp hev))⟩

/-! ### The accepting pairs come first

With the reachability restriction on, the worklist starts from the accepting pairs, so they
are a prefix of the explored states.  That is what makes duplicate merging keep them: a
state is always merged into one that occurs *earlier*.
-/

theorem reachLoop_fst_append (A : TA σ₁) (B : TA σ₂) :
    ∀ (fuel : Nat) (w q : List (σ₁ × σ₂)) (δ : List (Transition (σ₁ × σ₂))),
      ∃ rest, (reachLoop A B fuel w q δ).1 = q ++ rest ∧ ∀ z ∈ rest, z ∉ q := by
  intro fuel
  induction fuel with
  | zero => intro w q δ; exact ⟨[], by simp [reachLoop], by simp⟩
  | succ fuel ih =>
      intro w q δ
      cases w with
      | nil => exact ⟨[], by simp [reachLoop], by simp⟩
      | cons x ws =>
          obtain ⟨rest, heq, hrest⟩ := ih (ws ++ (((transitionsAtPair A B x).flatMap
            rhsStates).dedup.filter fun p => !q.contains p))
            (q ++ (((transitionsAtPair A B x).flatMap rhsStates).dedup.filter
              fun p => !q.contains p)) ((δ ++ transitionsAtPair A B x).dedup)
          refine ⟨(((transitionsAtPair A B x).flatMap rhsStates).dedup.filter
            fun p => !q.contains p) ++ rest, ?_, ?_⟩
          · show (reachLoop A B fuel _ _ _).1 = _
            rw [heq, List.append_assoc]
          · intro z hz
            rcases List.mem_append.mp hz with hz | hz
            · simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
                List.elem_eq_mem, decide_eq_false_iff_not] at hz
              exact hz.2
            · exact fun hq => hrest z hz (List.mem_append_left _ hq)

/-! ### The fold that chooses representatives -/

theorem snds_foldl_keepStep_mono :
    ∀ (l acc : List (σ × σ)), (acc.map Prod.snd) ⊆ ((l.foldl keepStep acc).map Prod.snd) := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons p l ih =>
      intro acc
      refine fun z hz => ih (keepStep acc p) ?_
      simp only [keepStep]
      split
      · exact hz
      · split
        · exact hz
        · simp only [List.map_append]
          exact List.mem_append_left _ hz

/-- After the fold, every pair of the list has had one of its two states merged away. -/
theorem foldl_keepStep_processed :
    ∀ (l acc : List (σ × σ)), ∀ p ∈ l,
      p.1 ∈ ((l.foldl keepStep acc).map Prod.snd) ∨
      p.2 ∈ ((l.foldl keepStep acc).map Prod.snd) := by
  intro l
  induction l with
  | nil => intro acc p hp; simp at hp
  | cons x l ih =>
      intro acc p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · have hstep : p.1 ∈ ((keepStep acc p).map Prod.snd) ∨
            p.2 ∈ ((keepStep acc p).map Prod.snd) := by
          simp only [keepStep]
          split
          · next h =>
              refine Or.inr ?_
              simpa using h
          · split
            · next h =>
                refine Or.inl ?_
                simpa using h
            · refine Or.inr ?_
              simp only [List.map_append]
              exact List.mem_append_right _ (by simp)
        rcases hstep with h | h
        · exact Or.inl (snds_foldl_keepStep_mono l _ h)
        · exact Or.inr (snds_foldl_keepStep_mono l _ h)
      · exact ih (keepStep acc x) p hp

/-- A property that is stable under the fold: pairs are only added when neither state has
been merged away already. -/
theorem foldl_keepStep_invariant (P : σ × σ → Prop) :
    ∀ (l acc : List (σ × σ)), (∀ p ∈ acc, P p) →
      (∀ p ∈ l, P p ∨ p.1 ∈ (acc.map Prod.snd) ∨ p.2 ∈ (acc.map Prod.snd)) →
      ∀ p ∈ l.foldl keepStep acc, P p := by
  intro l
  induction l with
  | nil => intro acc hacc _ p hp; exact hacc p hp
  | cons x l ih =>
      intro acc hacc hl p hp
      have hmono : (acc.map Prod.snd) ⊆ ((keepStep acc x).map Prod.snd) := by
        simp only [keepStep]
        split
        · exact fun _ h => h
        · split
          · exact fun _ h => h
          · simp only [List.map_append]
            exact fun _ h => List.mem_append_left _ h
      refine ih (keepStep acc x) ?_ ?_ p hp
      · intro y hy
        simp only [keepStep] at hy
        split at hy
        · exact hacc y hy
        · split at hy
          · exact hacc y hy
          · next h₂ h₁ =>
              rcases List.mem_append.mp hy with hy | hy
              · exact hacc y hy
              · have hyx : y = x := by simpa using hy
                subst hyx
                rcases hl y (List.mem_cons_self ..) with h | h | h
                · exact h
                · exact absurd h (by simpa using h₁)
                · exact absurd h (by simpa using h₂)
      · intro y hy
        rcases hl y (List.mem_cons_of_mem _ hy) with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (hmono h))
        · exact Or.inr (Or.inr (hmono h))


/-- The pairs `findDupStates` produces for one state. -/
def dupBlock (qs : List σ) (δ : List (Transition σ)) (ei : σ) : List (σ × σ) :=
  (qs.filter fun ej => ej != ei).filterMap fun ej =>
    if sameElems (stateSig δ ei) (stateSig δ ej) then some (ei, ej) else none

theorem findDupStates_eq (qs : List σ) (δ : List (Transition σ)) :
    findDupStates qs δ = qs.flatMap (dupBlock qs δ) := rfl

theorem mem_dupBlock {qs : List σ} {δ : List (Transition σ)} {ei : σ} {p : σ × σ} :
    p ∈ dupBlock qs δ ei ↔
      p.1 = ei ∧ p.2 ∈ qs ∧ p.2 ≠ ei ∧
        sameElems (stateSig δ ei) (stateSig δ p.2) = true := by
  simp only [dupBlock, List.mem_filterMap, List.mem_filter, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨ej, ⟨hej, hne⟩, hif⟩
    split at hif
    · next hs =>
        simp only [Option.some.injEq] at hif
        subst hif
        exact ⟨rfl, hej, hne, hs⟩
    · simp at hif
  · rintro ⟨h1, h2, hne, hs⟩
    refine ⟨p.2, ⟨h2, hne⟩, ?_⟩
    rw [if_pos hs, ← h1]

theorem sameElems_symm {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (h : sameElems l₁ l₂ = true) : sameElems l₂ l₁ = true :=
  sameElems_iff.mpr fun x => (sameElems_iff.mp h x).symm

/-- **Merging never eliminates a state of the prefix.**  If the states of `F` all occur
before those of `G`, a state of `F` is never merged into a state outside `F`: the pairs
`findDupStates` produces are symmetric, and the one with the `F`-state as representative
is visited first. -/
theorem mergeKeep_keeps_prefix {F G : List σ} {δ : List (Transition σ)}
    {p : σ × σ} (hp : p ∈ mergeKeep (F ++ G) δ) (h2 : p.2 ∈ F) : p.1 ∈ F := by
  set qs := F ++ G with hqs
  set pred : σ × σ → Bool := fun p => p.1 != p.2 with hpred
  set L₁ := (F.flatMap (dupBlock qs δ)).filter pred with hL₁
  set L₂ := (G.flatMap (dupBlock qs δ)).filter pred with hL₂
  have hsplit : ((findDupStates qs δ).filter pred) = L₁ ++ L₂ := by
    rw [findDupStates_eq, hqs, List.flatMap_append, List.filter_append]
  have hfold : mergeKeep qs δ = L₂.foldl keepStep (L₁.foldl keepStep []) := by
    rw [mergeKeep, hsplit, List.foldl_append]
  have hL₁fst : ∀ x ∈ L₁, x.1 ∈ F := by
    intro x hx
    obtain ⟨hx', -⟩ := List.mem_filter.mp hx
    obtain ⟨e, he, hxe⟩ := List.mem_flatMap.mp hx'
    rw [(mem_dupBlock.mp hxe).1]
    exact he
  refine foldl_keepStep_invariant (fun x => x.2 ∈ F → x.1 ∈ F) L₂ _ ?_ ?_ p (hfold ▸ hp) h2
  · intro x hx
    have := foldl_keepStep_subset L₁ [] hx
    simp only [List.nil_append] at this
    exact fun _ => hL₁fst x this
  · intro x hx
    by_cases hx2 : x.2 ∈ F
    · -- the swapped pair lives in the `F` block, which has already been processed
      obtain ⟨hx', hpr⟩ := List.mem_filter.mp hx
      obtain ⟨e, he, hxe⟩ := List.mem_flatMap.mp hx'
      obtain ⟨he1, he2, hne, hs⟩ := mem_dupBlock.mp hxe
      have hne' : x.1 ≠ x.2 := by
        simp only [hpred, bne_iff_ne, ne_eq] at hpr
        exact hpr
      have hswap : (x.2, x.1) ∈ L₁ := by
        refine List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨x.2, hx2, ?_⟩, ?_⟩
        · refine mem_dupBlock.mpr ⟨rfl, ?_, ?_, ?_⟩
          · show x.1 ∈ qs
            rw [he1]; exact List.mem_append_right _ he
          · show x.1 ≠ x.2
            exact hne'
          · show sameElems (stateSig δ x.2) (stateSig δ x.1) = true
            refine sameElems_symm ?_
            rw [he1]; exact hs
        · show (x.2 != x.1) = true
          simp only [bne_iff_ne, ne_eq]
          exact fun hc => hne' hc.symm
      rcases foldl_keepStep_processed L₁ [] (x.2, x.1) hswap with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · exact Or.inl (fun hc => absurd hc hx2)

theorem canonOf_mergeKeep_mem_prefix {F G : List σ} {δ : List (Transition σ)}
    {q : σ} (hq : q ∈ F) : canonOf (mergeKeep (F ++ G) δ) q ∈ F := by
  rcases canonOf_cases (mergeKeep (F ++ G) δ) q with h | ⟨p, hp, hp2, hcan⟩
  · rw [h]; exact hq
  · rw [hcan]
    exact mergeKeep_keeps_prefix hp (by rw [hp2]; exact hq)



/-! ### The one side condition

`mergeDups` rewrites every state to a canonical representative.  Nothing forces that
representative to be an accepting pair when the state it replaces is one, and the final
states of `intersectTA` are the accepting pairs that *survive* the merge — so an accepting
pair merged into a non-accepting one is lost.  With `reachability := true` this cannot
happen (`dedupKeepsFinals_of_reachability`); with `reachability := false` it can, and the
language is then genuinely wrong.
-/

/-- Duplicate merging keeps accepting pairs accepting.  Vacuous when the optimisation is
switched off. -/
def DedupKeepsFinals (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts) : Prop :=
  opts.dedupStates = true →
    ∀ q ∈ pairs A.finals B.finals,
      canonOf (mergeKeep (interStage0 A B opts).1 (interStage0 A B opts).2) q ∈
        pairs A.finals B.finals

instance (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts) :
    Decidable (DedupKeepsFinals A B opts) :=
  inferInstanceAs (Decidable (opts.dedupStates = true → ∀ q ∈ pairs A.finals B.finals,
    canonOf (mergeKeep (interStage0 A B opts).1 (interStage0 A B opts).2) q ∈
      pairs A.finals B.finals))

/-- The side condition is automatic when the reachability restriction is on: the worklist
starts from the accepting pairs, so they are a prefix of the states, and
`mergeKeep_keeps_prefix` applies. -/
theorem dedupKeepsFinals_of_reachability (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts)
    (h : opts.reachability = true) : DedupKeepsFinals A B opts := by
  intro _ q hq
  simp only [interStage0, if_pos h]
  obtain ⟨rest, heq, -⟩ := reachLoop_fst_append A B
    (A.mentionedStates.length * B.mentionedStates.length + 1)
    (pairs A.finals B.finals) (pairs A.finals B.finals) []
  rw [heq]
  exact canonOf_mergeKeep_mem_prefix (G := rest) hq

/-! ### Putting the three stages together -/

theorem lang_congr {C D : TA σ} (htr : C.trans = D.trans)
    (hfin : ∀ q, q ∈ C.finals ↔ q ∈ D.finals) (t : Tree) : C.Lang t ↔ D.Lang t := by
  rw [TA.lang_iff_ev, TA.lang_iff_ev]
  exact ⟨fun ⟨f, hf, hev⟩ => ⟨f, (hfin f).mp hf, (TA.ev_congr_trans htr t f).mp hev⟩,
         fun ⟨f, hf, hev⟩ => ⟨f, (hfin f).mpr hf, (TA.ev_congr_trans htr t f).mpr hev⟩⟩

/-- The automaton after the first stage, with the accepting pairs as final states. -/
def interTA0 (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts) : TA (σ₁ × σ₂) where
  states    := (interStage0 A B opts).1
  alphabet  := (A.alphabet.filter fun f => B.alphabet.contains f) ++ [epsSym]
  terminals := A.terminals.filter fun a => B.terminals.contains a
  finals    := pairs A.finals B.finals
  trans     := (interStage0 A B opts).2

/-- The automaton after the second stage. -/
def interTA1 (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts) : TA (σ₁ × σ₂) where
  states    := (interStage1 A B opts).1
  alphabet  := (A.alphabet.filter fun f => B.alphabet.contains f) ++ [epsSym]
  terminals := A.terminals.filter fun a => B.terminals.contains a
  finals    := (pairs A.finals B.finals).filter
                 fun q => (interStage1 A B opts).1.contains q
  trans     := (interStage1 A B opts).2

theorem intersectTA_eq_setTrans (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts) :
    intersectTA A B opts = (interTA1 A B opts).setTrans (interStage2 A B opts) := rfl

/-- **The third stage changes nothing.** -/
theorem interTA1_lang_of_stage2 (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts) (t : Tree) :
    (intersectTA A B opts).Lang t ↔ (interTA1 A B opts).Lang t := by
  rw [intersectTA_eq_setTrans]
  simp only [interStage2]
  split
  · exact introEpsAll_lang (interTA1 A B opts) _ _ t
  · exact Iff.rfl

/-- **The second stage changes nothing**, given the side condition. -/
theorem interTA1_lang (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts)
    (hnd : opts.reachability = true → (pairs A.finals B.finals).Nodup)
    (hkeep : DedupKeepsFinals A B opts) (t : Tree) :
    (interTA1 A B opts).Lang t ↔ (interTA0 A B opts).Lang t := by
  have hspec := interStage0_spec A B opts hnd
  by_cases hdup : opts.dedupStates = true
  · set qs₀ := (interStage0 A B opts).1 with hqs₀
    set δ₀ := (interStage0 A B opts).2 with hδ₀
    set f := canonOf (mergeKeep qs₀ δ₀) with hf
    have hstage1 : interStage1 A B opts = ((qs₀.map f).dedup, (δ₀.map (renameTrans f)).dedup) := by
      simp only [interStage1, if_pos hdup, mergeDups]
      rfl
    refine merge_lang (C := interTA0 A B opts) (D := interTA1 A B opts) (f := f) ?_ ?_ ?_ ?_ ?_ t
    · simp only [interTA1, interTA0, hstage1]
      rfl
    · exact hspec.trans_noEps rfl
    · exact fun e => canonOf_mergeKeep_sigEq qs₀ δ₀ e
    · intro q hq
      simp only [interTA0] at hq
      refine List.mem_filter.mpr ⟨hkeep hdup q hq, ?_⟩
      simp only [hstage1, List.elem_eq_mem, decide_eq_true_eq, List.mem_dedup]
      exact List.mem_map_of_mem (hspec.finals q hq)
    · intro q hq
      exact (List.mem_filter.mp hq).1
  · have hdup' : opts.dedupStates = false := by
      cases h : opts.dedupStates with
      | false => rfl
      | true => exact absurd h hdup
    have hstage1 : interStage1 A B opts = interStage0 A B opts := by
      simp [interStage1, hdup']
    refine lang_congr ?_ ?_ t
    · simp only [interTA1, interTA0, hstage1]
    · intro q
      simp only [interTA1, interTA0, hstage1, List.mem_filter, List.elem_eq_mem,
        decide_eq_true_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, hspec.finals q h⟩⟩

/-- **The first stage recognises the intersection.** -/
theorem interTA0_lang (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts)
    (hnd : opts.reachability = true → (pairs A.finals B.finals).Nodup) (t : Tree) :
    (interTA0 A B opts).Lang t ↔ A.Lang t ∧ B.Lang t :=
  stage0_lang (interStage0_spec A B opts hnd) rfl (fun _ => Iff.rfl) t


/--
**Algorithm 3.3 is correct**: the optimised intersection recognises `L(A) ∩ L(B)`, the
same language as the textbook product `Greta.prodTA` of Section 2.4
(`Greta.prodTA_lang`).

Two decidable side conditions, each attached to the optimisation that needs it, and both
discharged in the configuration Greta runs (`IntersectOpts.default`, see
`intersectTA_lang_default`); with every optimisation off neither has any content
(`intersectTA_lang_none`):

* `hnd`: with the reachability restriction on, the accepting pairs must be listed once
  each — which holds as soon as `A.finals` and `B.finals` are duplicate-free
  (`pairs_nodup`).  It is what makes the fuel of the worklist loop, `|Q_A| * |Q_B| + 1`
  iterations, sufficient to reach a fixed point: one iteration is spent per queued pair,
  and a pair queued twice leaves the budget one short.
* `hkeep`: duplicate merging does not merge an accepting pair into a non-accepting one.
  This is automatic when `opts.reachability = true`
  (`dedupKeepsFinals_of_reachability`), because the worklist starts from the accepting
  pairs and merges a state only into an earlier one.  It is vacuous when
  `opts.dedupStates = false`, and **it cannot be dropped** when reachability is off: with
  `{reachability := false}` there are automata whose intersection `intersectTA` gets
  wrong, because the surviving representative of an accepting pair need not be accepting
  and the final states of the result are filtered by survival.
-/
theorem intersectTA_lang (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts)
    (hnd : opts.reachability = true → (pairs A.finals B.finals).Nodup)
    (hkeep : DedupKeepsFinals A B opts) (t : Tree) :
    (intersectTA A B opts).Lang t ↔ A.Lang t ∧ B.Lang t :=
  ((interTA1_lang_of_stage2 A B opts t).trans
    (interTA1_lang A B opts hnd hkeep t)).trans (interTA0_lang A B opts hnd t)

/-- **Algorithm 3.3 agrees with the verified product construction.** -/
theorem intersectTA_lang_prodTA (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts)
    (hnd : opts.reachability = true → (pairs A.finals B.finals).Nodup)
    (hkeep : DedupKeepsFinals A B opts) (t : Tree) :
    (intersectTA A B opts).Lang t ↔ (prodTA A B).Lang t :=
  (intersectTA_lang A B opts hnd hkeep t).trans (prodTA_lang A B t).symm

/-- The configuration Greta actually runs needs no side condition beyond duplicate-free
final states. -/
theorem intersectTA_lang_default (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts)
    (hreach : opts.reachability = true) (hA : A.finals.Nodup) (hB : B.finals.Nodup)
    (t : Tree) : (intersectTA A B opts).Lang t ↔ A.Lang t ∧ B.Lang t :=
  intersectTA_lang A B opts (fun _ => pairs_nodup hA hB)
    (dedupKeepsFinals_of_reachability A B opts hreach) t

/-- Without duplicate merging the construction is correct outright. -/
theorem intersectTA_lang_of_no_dedup (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts)
    (hnd : opts.reachability = true → (pairs A.finals B.finals).Nodup)
    (hdup : opts.dedupStates = false) (t : Tree) :
    (intersectTA A B opts).Lang t ↔ A.Lang t ∧ B.Lang t := by
  refine intersectTA_lang A B opts hnd ?_ t
  intro hd
  rw [hdup] at hd
  exact absurd hd (by simp)

/-- With every optimisation of Table 1 switched off — the configuration `I¹²³` — the
theorem needs no side condition at all. -/
theorem intersectTA_lang_none (A : TA σ₁) (B : TA σ₂) (t : Tree) :
    (intersectTA A B IntersectOpts.none).Lang t ↔ A.Lang t ∧ B.Lang t :=
  intersectTA_lang_of_no_dedup A B IntersectOpts.none (by simp [IntersectOpts.none]) rfl t

/-! ### The side condition cannot be dropped

Two one-transition automata over the single symbol `(a,1)`.  `B` has two states with the
same incoming transition, only one of which is accepting, and it lists the non-accepting
one first, so `allPairsProduct` enumerates `(qA,rB)` before `(qA,qB)`; Algorithm 3.4 then
elects `(qA,rB)` as the representative of the class, `intersectTA` filters its final states
by survival, and the accepting pair is gone.  Both trees below are checked at build time.
-/

namespace DedupWitness

/-- The only symbol of the witness: rank one, printed `a`. -/
def wSym : Sym := ⟨1, "a", 1⟩

/-- One state, accepting, with the single transition `qA ←(a,1) a`. -/
def wA : TA String where
  states := ["qA"]; alphabet := [wSym]; terminals := ["a"]; finals := ["qA"]
  trans := [⟨"qA", wSym, [.term "a"]⟩]

/-- Two states with the same incoming transition; the accepting one is listed second. -/
def wB : TA String where
  states := ["rB", "qB"]; alphabet := [wSym]; terminals := ["a"]; finals := ["qB"]
  trans := [⟨"rB", wSym, [.term "a"]⟩, ⟨"qB", wSym, [.term "a"]⟩]

/-- The single tree both automata accept. -/
def wTree : Tree := .node wSym [.leaf "a"]

-- the intersection is non-empty …
#guard wA.langB wTree && wB.langB wTree
#guard (prodTA wA wB).langB wTree
-- … and the default configuration of Algorithm 3.3 agrees …
#guard (intersectTA wA wB {}).langB wTree
-- … but with the reachability restriction off and merging on the tree is lost.
#guard !((intersectTA wA wB { reachability := false }).langB wTree)
-- The side condition of `intersectTA_lang` is exactly what fails there.
#guard decide (DedupKeepsFinals wA wB { reachability := false }) = false
#guard decide (DedupKeepsFinals wA wB {}) = true

end DedupWitness

end Greta
