/-
The product (intersection) of two tree automata.

This is the mathematical core of Theorem 3.2 of the paper: `Greta.prodTA A B` recognises
exactly `L(A) ∩ L(B)`.  Following Section 2.4 of the paper, two transitions are combined
only when their right-hand sides *match*: same length, and at each position either two
states or one and the same terminal.

The optimised algorithm actually implemented by Greta (Algorithm 3.3) is in
`Greta.Intersect`; it is related to this construction there.
-/
import Greta.Semantics

namespace Greta

variable {σ₁ σ₂ : Type} [DecidableEq σ₁] [DecidableEq σ₂]

/-! ### Matching right-hand sides -/

/-- Two right-hand-side entries match when they are two states, or the same terminal. -/
def betaCompat : Beta σ₁ → Beta σ₂ → Bool
  | .term a,   .term a'  => a == a'
  | .state _,  .state _  => true
  | _,         _         => false

/-- The combined entry of two matching right-hand-side entries. -/
def zipB : Beta σ₁ → Beta σ₂ → Beta (σ₁ × σ₂)
  | .term a,  _         => .term a
  | .state q₁, .state q₂ => .state (q₁, q₂)
  | .state _, .term a   => .term a

/-- Positionwise matching of two right-hand sides. -/
def compatAll : List (Beta σ₁) → List (Beta σ₂) → Bool
  | [],        []        => true
  | b₁ :: bs₁, b₂ :: bs₂ => betaCompat b₁ b₂ && compatAll bs₁ bs₂
  | _,         _         => false

/-- Positionwise combination of two matching right-hand sides. -/
def zipBetas : List (Beta σ₁) → List (Beta σ₂) → List (Beta (σ₁ × σ₂))
  | b₁ :: bs₁, b₂ :: bs₂ => zipB b₁ b₂ :: zipBetas bs₁ bs₂
  | _,         _         => []

/-! ### The construction -/

/-- Cross product of the non-ε transitions of two automata. -/
def prodTrans (A : TA σ₁) (B : TA σ₂) : List (Transition (σ₁ × σ₂)) :=
  A.realTrans.flatMap fun t₁ =>
    B.realTrans.filterMap fun t₂ =>
      if t₁.sym = t₂.sym ∧ compatAll t₁.rhs t₂.rhs = true then
        some ⟨(t₁.target, t₂.target), t₁.sym, zipBetas t₁.rhs t₂.rhs⟩
      else none

/--
ε-transitions of the product: a product state may be promoted componentwise, so the
ε-closure of `(r₁, r₂)` is the product of the ε-closures of `r₁` and `r₂`.
-/
def prodEps (A : TA σ₁) (B : TA σ₂) : List (Transition (σ₁ × σ₂)) :=
  (pairs A.mentionedStates B.mentionedStates).flatMap fun r =>
    (pairs (A.closeFrom r.1) (B.closeFrom r.2)).filterMap fun p =>
      if p = r then none else some ⟨p, epsSym, [.state r]⟩

/-- The product automaton. -/
def prodTA (A : TA σ₁) (B : TA σ₂) : TA (σ₁ × σ₂) where
  states    := pairs A.states B.states
  alphabet  := A.alphabet.filter fun f => B.alphabet.contains f
  terminals := A.terminals.filter fun a => B.terminals.contains a
  finals    := pairs A.finals B.finals
  trans     := prodTrans A B ++ prodEps A B

/-- The ε-closure table of the product: the product of the component closures. -/
def prodTable (A : TA σ₁) (B : TA σ₂) : EpsTable (σ₁ × σ₂) := fun r =>
  if r.1 ∈ A.mentionedStates ∧ r.2 ∈ B.mentionedStates then
    pairs (A.closeFrom r.1) (B.closeFrom r.2)
  else [r]

/-! ### The ε-closure of the product -/

theorem closeFrom_subset_mentioned {A : TA σ₁} {q : σ₁} (hq : q ∈ A.mentionedStates) :
    A.closeFrom q ⊆ A.mentionedStates :=
  saturate_subset _ (by simpa using hq) fun _ _ h => TA.epsEdges_target_mem h

theorem prodTrans_sym_ne_eps {A : TA σ₁} {B : TA σ₂} {tr : Transition (σ₁ × σ₂)}
    (h : tr ∈ prodTrans A B) : tr.sym ≠ epsSym := by
  simp only [prodTrans, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨t₁, ht₁, t₂, _, hif⟩ := h
  split at hif
  · next hc =>
      simp only [Option.some.injEq] at hif
      subst hif
      simp only [TA.realTrans, List.mem_filter, bne_iff_ne, ne_eq, decide_eq_true_eq] at ht₁
      exact ht₁.2
  · simp at hif

theorem mem_prodEps_iff {A : TA σ₁} {B : TA σ₂} {tr : Transition (σ₁ × σ₂)} :
    tr ∈ prodEps A B ↔
      ∃ r p, r.1 ∈ A.mentionedStates ∧ r.2 ∈ B.mentionedStates ∧
        p.1 ∈ A.closeFrom r.1 ∧ p.2 ∈ B.closeFrom r.2 ∧ p ≠ r ∧
        tr = ⟨p, epsSym, [.state r]⟩ := by
  simp only [prodEps, List.mem_flatMap, List.mem_filterMap, mem_pairs]
  constructor
  · rintro ⟨r, hr, p, hp, hif⟩
    split at hif
    · simp at hif
    · next hne =>
        simp only [Option.some.injEq] at hif
        exact ⟨r, p, hr.1, hr.2, hp.1, hp.2, hne, hif.symm⟩
  · rintro ⟨r, p, hr₁, hr₂, hp₁, hp₂, hne, rfl⟩
    exact ⟨r, ⟨hr₁, hr₂⟩, p, ⟨hp₁, hp₂⟩, by rw [if_neg hne]⟩

theorem mem_prodEpsEdges {A : TA σ₁} {B : TA σ₂} {r p : σ₁ × σ₂} :
    (r, p) ∈ (prodTA A B).epsEdges ↔
      r.1 ∈ A.mentionedStates ∧ r.2 ∈ B.mentionedStates ∧
      p.1 ∈ A.closeFrom r.1 ∧ p.2 ∈ B.closeFrom r.2 ∧ p ≠ r := by
  rw [mem_epsEdges]
  constructor
  · rintro ⟨tr, htr, hsym, hrhs, htgt⟩
    rcases List.mem_append.mp htr with h | h
    · exact absurd hsym (prodTrans_sym_ne_eps h)
    · obtain ⟨r', p', hr₁, hr₂, hp₁, hp₂, hne, rfl⟩ := mem_prodEps_iff.mp h
      simp only [Transition.mk.injEq, List.cons.injEq] at hrhs htgt
      have hr : r' = r := by
        have := hrhs; simp only [List.cons.injEq, Beta.state.injEq] at this; exact this.1
      subst hr; subst htgt
      exact ⟨hr₁, hr₂, hp₁, hp₂, hne⟩
  · rintro ⟨hr₁, hr₂, hp₁, hp₂, hne⟩
    exact ⟨⟨p, epsSym, [.state r]⟩,
      List.mem_append_right _ (mem_prodEps_iff.mpr ⟨r, p, hr₁, hr₂, hp₁, hp₂, hne, rfl⟩),
      rfl, rfl, rfl⟩

theorem prodTable_apply {A : TA σ₁} {B : TA σ₂} {r : σ₁ × σ₂}
    (h₁ : r.1 ∈ A.mentionedStates) (h₂ : r.2 ∈ B.mentionedStates) :
    prodTable A B r = pairs (A.closeFrom r.1) (B.closeFrom r.2) := by
  simp [prodTable, h₁, h₂]

theorem isEpsClosure_prodTable (A : TA σ₁) (B : TA σ₂) :
    IsEpsClosure (prodTA A B) (prodTable A B) := by
  intro r p
  constructor
  · -- membership in the table gives an ε-path (of length at most one)
    intro hp
    simp only [prodTable] at hp
    split at hp
    · next hr =>
        simp only [mem_pairs] at hp
        by_cases heq : p = r
        · exact heq ▸ .refl _
        · exact .step (mem_prodEpsEdges.mpr ⟨hr.1, hr.2, hp.1, hp.2, heq⟩) (.refl _)
    · simp only [List.mem_singleton] at hp; exact hp ▸ .refl _
  · intro h
    induction h with
    | refl q =>
        simp only [prodTable]
        split
        · simp [TA.mem_closeFrom_self]
        · simp
    | @step x y z he _ ih =>
        obtain ⟨hx₁, hx₂, hy₁, hy₂, _⟩ := mem_prodEpsEdges.mp he
        have hy₁' : y.1 ∈ A.mentionedStates := closeFrom_subset_mentioned hx₁ hy₁
        have hy₂' : y.2 ∈ B.mentionedStates := closeFrom_subset_mentioned hx₂ hy₂
        rw [prodTable_apply hy₁' hy₂', mem_pairs] at ih
        rw [prodTable_apply hx₁ hx₂, mem_pairs]
        exact ⟨TA.closeFrom_complete hx₁ ((TA.closeFrom_sound hy₁).trans
                 (TA.closeFrom_sound ih.1)),
               TA.closeFrom_complete hx₂ ((TA.closeFrom_sound hy₂).trans
                 (TA.closeFrom_sound ih.2))⟩

/-! ### The product evaluates componentwise -/

theorem evalT_mem_mentioned {σ : Type} [DecidableEq σ] (A : TA σ) (tbl : EpsTable σ) :
    ∀ (t : Tree) (q : σ), q ∈ A.evalT tbl t → q ∈ A.mentionedStates := by
  intro t q hq
  match t with
  | .leaf a => simp [TA.evalT] at hq
  | .node f ts =>
      simp only [TA.evalT, List.mem_filterMap] at hq
      obtain ⟨tr, htr, hif⟩ := hq
      split at hif
      · simp only [Option.some.injEq] at hif
        simp only [TA.realTrans, List.mem_filter] at htr
        subst hif
        simp only [TA.mentionedStates, List.mem_dedup, List.mem_append]
        exact Or.inl (Or.inr (List.mem_map_of_mem htr.1))
      · simp at hif

theorem isLeafOf_eq {t : Tree} {a : Terminal} (h : isLeafOf t a = true) : t = .leaf a := by
  cases t with
  | leaf a' => simp only [isLeafOf, beq_iff_eq] at h; rw [h]
  | node => simp [isLeafOf] at h

theorem realTrans_prodTA (A : TA σ₁) (B : TA σ₂) :
    (prodTA A B).realTrans = prodTrans A B := by
  simp only [TA.realTrans, prodTA, List.filter_append]
  rw [List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr, List.append_nil]
  · intro tr htr
    obtain ⟨r, p, _, _, _, _, _, rfl⟩ := mem_prodEps_iff.mp htr
    simp
  · intro tr htr
    simpa using prodTrans_sym_ne_eps htr

theorem mem_prodTrans_iff {A : TA σ₁} {B : TA σ₂} {tr : Transition (σ₁ × σ₂)} :
    tr ∈ prodTrans A B ↔
      ∃ t₁ ∈ A.realTrans, ∃ t₂ ∈ B.realTrans,
        t₁.sym = t₂.sym ∧ compatAll t₁.rhs t₂.rhs = true ∧
        tr = ⟨(t₁.target, t₂.target), t₁.sym, zipBetas t₁.rhs t₂.rhs⟩ := by
  simp only [prodTrans, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨t₁, ht₁, t₂, ht₂, hif⟩
    split at hif
    · next hc =>
        simp only [Option.some.injEq] at hif
        exact ⟨t₁, ht₁, t₂, ht₂, hc.1, hc.2, hif.symm⟩
    · simp at hif
  · rintro ⟨t₁, ht₁, t₂, ht₂, hsym, hc, rfl⟩
    exact ⟨t₁, ht₁, t₂, ht₂, by rw [if_pos ⟨hsym, hc⟩]⟩

/-- Matching in two automata forces their right-hand sides to be compatible. -/
theorem compatAll_of_match (A : TA σ₁) (B : TA σ₂) :
    ∀ (ts : List Tree) (bs₁ : List (Beta σ₁)) (bs₂ : List (Beta σ₂)),
      A.matchAll A.epsTable ts bs₁ = true → B.matchAll B.epsTable ts bs₂ = true →
      compatAll bs₁ bs₂ = true := by
  intro ts
  induction ts with
  | nil =>
      intro bs₁ bs₂ h₁ h₂
      cases bs₁ <;> cases bs₂ <;> simp_all [TA.matchAll, compatAll]
  | cons t ts ih =>
      intro bs₁ bs₂ h₁ h₂
      cases bs₁ with
      | nil => simp [TA.matchAll] at h₁
      | cons b₁ l₁ =>
        cases bs₂ with
        | nil => simp [TA.matchAll] at h₂
        | cons b₂ l₂ =>
          cases b₁ with
          | term a =>
            simp only [TA.matchAll, Bool.and_eq_true] at h₁
            cases b₂ with
            | term a' =>
                simp only [TA.matchAll, Bool.and_eq_true] at h₂
                have ht₁ := isLeafOf_eq h₁.1
                have ht₂ := isLeafOf_eq h₂.1
                have : a = a' := by
                  rw [ht₁] at ht₂; simpa using ht₂
                simp only [compatAll, betaCompat, this, beq_self_eq_true, Bool.true_and]
                exact ih l₁ l₂ h₁.2 h₂.2
            | state q =>
                exfalso
                simp only [TA.matchAll, Bool.and_eq_true] at h₂
                rw [isLeafOf_eq h₁.1] at h₂
                simp [TA.evalT] at h₂
          | state q =>
            simp only [TA.matchAll, Bool.and_eq_true] at h₁
            cases b₂ with
            | term a' =>
                exfalso
                simp only [TA.matchAll, Bool.and_eq_true] at h₂
                rw [isLeafOf_eq h₂.1] at h₁
                simp [TA.evalT] at h₁
            | state q' =>
                simp only [TA.matchAll, Bool.and_eq_true] at h₂
                simp only [compatAll, betaCompat, Bool.true_and]
                exact ih l₁ l₂ h₁.2 h₂.2

theorem bool_ac (x y a b : Bool) : ((x && y) && (a && b)) = ((x && a) && (y && b)) := by
  cases x <;> cases y <;> cases a <;> cases b <;> rfl

theorem any_prod_iff (A : TA σ₁) (B : TA σ₂) (t : Tree) (q₁ : σ₁) (q₂ : σ₂)
    (hih : ∀ q : σ₁ × σ₂, q ∈ (prodTA A B).evalT (prodTable A B) t ↔
      q.1 ∈ A.evalT A.epsTable t ∧ q.2 ∈ B.evalT B.epsTable t) :
    (∃ r ∈ (prodTA A B).evalT (prodTable A B) t, (q₁, q₂) ∈ prodTable A B r) ↔
      ((∃ r₁ ∈ A.evalT A.epsTable t, q₁ ∈ A.epsTable r₁) ∧
       (∃ r₂ ∈ B.evalT B.epsTable t, q₂ ∈ B.epsTable r₂)) := by
  constructor
  · rintro ⟨r, hr, hq⟩
    have h := (hih r).mp hr
    rw [prodTable_apply (evalT_mem_mentioned A _ t r.1 h.1)
        (evalT_mem_mentioned B _ t r.2 h.2), mem_pairs] at hq
    exact ⟨⟨r.1, h.1, hq.1⟩, ⟨r.2, h.2, hq.2⟩⟩
  · rintro ⟨⟨r₁, hr₁, hq₁⟩, ⟨r₂, hr₂, hq₂⟩⟩
    refine ⟨(r₁, r₂), (hih (r₁, r₂)).mpr ⟨hr₁, hr₂⟩, ?_⟩
    rw [prodTable_apply (evalT_mem_mentioned A _ t r₁ hr₁)
        (evalT_mem_mentioned B _ t r₂ hr₂), mem_pairs]
    exact ⟨hq₁, hq₂⟩

theorem matchAll_prod (A : TA σ₁) (B : TA σ₂) :
    ∀ (ts : List Tree),
      (∀ t ∈ ts, ∀ q : σ₁ × σ₂, q ∈ (prodTA A B).evalT (prodTable A B) t ↔
        q.1 ∈ A.evalT A.epsTable t ∧ q.2 ∈ B.evalT B.epsTable t) →
      ∀ (bs₁ : List (Beta σ₁)) (bs₂ : List (Beta σ₂)), compatAll bs₁ bs₂ = true →
        (prodTA A B).matchAll (prodTable A B) ts (zipBetas bs₁ bs₂)
          = ((A.matchAll A.epsTable ts bs₁) && (B.matchAll B.epsTable ts bs₂)) := by
  intro ts
  induction ts with
  | nil =>
      intro _ bs₁ bs₂ hc
      cases bs₁ <;> cases bs₂ <;> simp_all [compatAll, zipBetas, TA.matchAll]
  | cons t ts ih =>
      intro hts bs₁ bs₂ hc
      have hhd := hts t (List.mem_cons_self ..)
      have htl : ∀ u ∈ ts, ∀ q : σ₁ × σ₂, q ∈ (prodTA A B).evalT (prodTable A B) u ↔
          q.1 ∈ A.evalT A.epsTable u ∧ q.2 ∈ B.evalT B.epsTable u :=
        fun u hu => hts u (List.mem_cons_of_mem _ hu)
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
                simp only [zipBetas, zipB, TA.matchAll, ih htl l₁ l₂ hc.2]
                cases isLeafOf t a <;> simp
            | state q => simp [betaCompat] at hc
          | state q₁ =>
            cases b₂ with
            | term a' => simp [betaCompat] at hc
            | state q₂ =>
                have hx := any_prod_iff A B t q₁ q₂ hhd
                simp only [zipBetas, zipB, TA.matchAll, ih htl l₁ l₂ hc.2]
                rw [Bool.eq_iff_iff]
                simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
                constructor
                · rintro ⟨he, hmA, hmB⟩
                  obtain ⟨he₁, he₂⟩ := hx.mp he
                  exact ⟨⟨he₁, hmA⟩, he₂, hmB⟩
                · rintro ⟨⟨he₁, hmA⟩, he₂, hmB⟩
                  exact ⟨hx.mpr ⟨he₁, he₂⟩, hmA, hmB⟩

/-- The product automaton evaluates componentwise. -/
theorem mem_evalT_prod (A : TA σ₁) (B : TA σ₂) :
    ∀ (t : Tree) (q : σ₁ × σ₂),
      q ∈ (prodTA A B).evalT (prodTable A B) t ↔
        q.1 ∈ A.evalT A.epsTable t ∧ q.2 ∈ B.evalT B.epsTable t := by
  intro t
  induction t using Tree.rec' with
  | hleaf a => intro q; simp [TA.evalT]
  | hnode f ts ih =>
      have hkey := matchAll_prod A B ts ih
      intro q
      simp only [TA.evalT, realTrans_prodTA, List.mem_filterMap]
      constructor
      · rintro ⟨tr, htr, hif⟩
        split at hif
        · next hcond =>
            simp only [Option.some.injEq] at hif
            obtain ⟨t₁, ht₁, t₂, ht₂, hsym, hcompat, rfl⟩ := mem_prodTrans_iff.mp htr
            rw [hkey t₁.rhs t₂.rhs hcompat] at hcond
            simp only [Bool.and_eq_true] at hcond
            subst hif
            exact ⟨⟨t₁, ht₁, by rw [if_pos ⟨hcond.1, hcond.2.1⟩]⟩,
                   ⟨t₂, ht₂, by rw [if_pos ⟨hsym ▸ hcond.1, hcond.2.2⟩]⟩⟩
        · simp at hif
      · rintro ⟨⟨t₁, ht₁, h₁⟩, ⟨t₂, ht₂, h₂⟩⟩
        split at h₁
        · next hc₁ =>
          split at h₂
          · next hc₂ =>
              simp only [Option.some.injEq] at h₁ h₂
              have hcompat := compatAll_of_match A B ts t₁.rhs t₂.rhs hc₁.2 hc₂.2
              refine ⟨⟨(t₁.target, t₂.target), t₁.sym, zipBetas t₁.rhs t₂.rhs⟩,
                mem_prodTrans_iff.mpr ⟨t₁, ht₁, t₂, ht₂, hc₁.1.trans hc₂.1.symm, hcompat, rfl⟩, ?_⟩
              rw [if_pos ⟨hc₁.1, by rw [hkey t₁.rhs t₂.rhs hcompat]; simp [hc₁.2, hc₂.2]⟩]
              simp [h₁, h₂]
          · simp at h₂
        · simp at h₁

/--
**Intersection of tree automata.**  `prodTA A B` accepts exactly the trees accepted by
both `A` and `B`.  Combined with Theorem 3.1 of the paper this yields Theorem 3.2
(Correctness of Greta); see `Greta.Soundness`.
-/
theorem prodTA_lang (A : TA σ₁) (B : TA σ₂) (t : Tree) :
    (prodTA A B).Lang t ↔ A.Lang t ∧ B.Lang t := by
  rw [TA.lang_iff_accepts (isEpsClosure_prodTable A B),
      TA.lang_iff_accepts (A.isEpsClosure_epsTable),
      TA.lang_iff_accepts (B.isEpsClosure_epsTable)]
  simp only [TA.accepts, List.any_eq_true, decide_eq_true_eq, prodTA]
  constructor
  · rintro ⟨q, hq, p, hp, hf⟩
    have h := (mem_evalT_prod A B t q).mp hq
    rw [prodTable_apply (evalT_mem_mentioned A _ t q.1 h.1)
        (evalT_mem_mentioned B _ t q.2 h.2)] at hp
    have hp' := mem_pairs.mp hp
    have hf' : p.1 ∈ A.finals ∧ p.2 ∈ B.finals := by simpa using hf
    exact ⟨⟨q.1, h.1, p.1, hp'.1, hf'.1⟩, ⟨q.2, h.2, p.2, hp'.2, hf'.2⟩⟩
  · rintro ⟨⟨q₁, hq₁, p₁, hp₁, hf₁⟩, ⟨q₂, hq₂, p₂, hp₂, hf₂⟩⟩
    refine ⟨(q₁, q₂), (mem_evalT_prod A B t (q₁, q₂)).mpr ⟨hq₁, hq₂⟩, (p₁, p₂), ?_, ?_⟩
    · rw [prodTable_apply (evalT_mem_mentioned A _ t q₁ hq₁)
          (evalT_mem_mentioned B _ t q₂ hq₂)]
      exact mem_pairs.mpr ⟨hp₁, hp₂⟩
    · have hfin : (p₁, p₂) ∈ pairs A.finals B.finals := mem_pairs.mpr ⟨hf₁, hf₂⟩
      simpa using hfin

end Greta

