/-
ε-closure of a tree automaton (Definition A.6).

ε-transitions only relate *states*, so their closure is an ordinary finite-graph
reachability problem.  This module gives

* `EpsReach`, the specification (reflexive-transitive closure of `TA.epsEdges`);
* `saturate`, a terminating executable saturation procedure;
* `TA.epsTable`, the closure table of an automaton, together with a proof that it
  computes `EpsReach` exactly (`TA.isEpsClosure_epsTable`).

Everything here is proved; nothing is assumed.
-/
import Greta.Basic

namespace Greta

variable {σ : Type} [DecidableEq σ]

/--
`EpsReach A q p` holds when a subtree evaluating to `q` may be promoted to `p` by a
(possibly empty) sequence of ε-transitions.
-/
inductive EpsReach (A : TA σ) : σ → σ → Prop where
  | refl (q : σ) : EpsReach A q q
  | step {q q' p : σ} : (q, q') ∈ A.epsEdges → EpsReach A q' p → EpsReach A q p

theorem EpsReach.trans {A : TA σ} {q p r : σ}
    (h₁ : EpsReach A q p) (h₂ : EpsReach A p r) : EpsReach A q r := by
  induction h₁ with
  | refl => exact h₂
  | step he _ ih => exact .step he (ih h₂)

theorem mem_epsEdges {A : TA σ} {a b : σ} :
    (a, b) ∈ A.epsEdges ↔
      ∃ tr ∈ A.trans, tr.sym = epsSym ∧ tr.rhs = [Beta.state a] ∧ tr.target = b := by
  simp only [TA.epsEdges, List.mem_filterMap]
  constructor
  · rintro ⟨tr, htr, hb⟩
    refine ⟨tr, htr, ?_⟩
    by_cases hs : tr.sym = epsSym
    · rw [if_pos hs] at hb
      split at hb
      · next q' heq =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          exact ⟨hs, by rw [heq, hb.1], hb.2⟩
      · simp at hb
    · rw [if_neg hs] at hb; simp at hb
  · rintro ⟨tr, htr, hs, hrhs, htgt⟩
    exact ⟨tr, htr, by rw [if_pos hs, hrhs, htgt]⟩

/-! ### Executable saturation -/

/-- Targets of edges leaving `qs` that are not yet in `qs`. -/
def newTargets (edges : List (σ × σ)) (qs : List σ) : List σ :=
  (edges.filterMap fun e => if e.1 ∈ qs ∧ e.2 ∉ qs then some e.2 else none).dedup

/-- One saturation step. -/
def stepOnce (edges : List (σ × σ)) (qs : List σ) : List σ :=
  qs ++ newTargets edges qs

/-- `qs` is closed under `edges`. -/
def EdgeClosed (edges : List (σ × σ)) (qs : List σ) : Prop :=
  ∀ a b, (a, b) ∈ edges → a ∈ qs → b ∈ qs

/-- Saturation with a step budget. -/
def saturate (edges : List (σ × σ)) : Nat → List σ → List σ
  | 0,     qs => qs
  | n + 1, qs =>
      let qs' := stepOnce edges qs
      if qs'.length ≤ qs.length then qs else saturate edges n qs'

/-! ### Basic facts about one step -/

theorem mem_newTargets {edges : List (σ × σ)} {qs : List σ} {b : σ} :
    b ∈ newTargets edges qs ↔ ∃ a, (a, b) ∈ edges ∧ a ∈ qs ∧ b ∉ qs := by
  simp only [newTargets, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨⟨a, b'⟩, hmem, hb⟩
    split at hb
    · next hcond =>
        simp only [Option.some.injEq] at hb
        subst hb
        exact ⟨a, hmem, hcond.1, hcond.2⟩
    · simp at hb
  · rintro ⟨a, hmem, ha, hb⟩
    exact ⟨(a, b), hmem, by simp [ha, hb]⟩

theorem newTargets_nodup (edges : List (σ × σ)) (qs : List σ) :
    (newTargets edges qs).Nodup := List.nodup_dedup _

theorem subset_stepOnce (edges : List (σ × σ)) (qs : List σ) : qs ⊆ stepOnce edges qs :=
  fun _ hx => List.mem_append_left _ hx

theorem stepOnce_nodup {edges : List (σ × σ)} {qs : List σ} (h : qs.Nodup) :
    (stepOnce edges qs).Nodup := by
  refine List.Nodup.append h (newTargets_nodup edges qs) ?_
  intro x hx hx'
  obtain ⟨_, _, _, hnot⟩ := mem_newTargets.mp hx'
  exact hnot hx

theorem stepOnce_subset {edges : List (σ × σ)} {qs U : List σ}
    (hq : qs ⊆ U) (he : ∀ a b, (a, b) ∈ edges → b ∈ U) : stepOnce edges qs ⊆ U := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hq h
  · obtain ⟨a, hmem, _, _⟩ := mem_newTargets.mp h
    exact he a x hmem

/-- If a step adds nothing, the set is already closed. -/
theorem edgeClosed_of_step_eq {edges : List (σ × σ)} {qs : List σ}
    (h : (stepOnce edges qs).length ≤ qs.length) : EdgeClosed edges qs := by
  intro a b hmem ha
  by_contra hb
  have hmem' : b ∈ newTargets edges qs := mem_newTargets.mpr ⟨a, hmem, ha, hb⟩
  have hpos : 0 < (newTargets edges qs).length := by
    cases hnt : newTargets edges qs with
    | nil => rw [hnt] at hmem'; simp at hmem'
    | cons _ _ => simp
  simp only [stepOnce, List.length_append] at h
  omega

/-- Every state added by one step is ε-reachable from the previous set. -/
theorem stepOnce_sound {A : TA σ} {qs : List σ} {q : σ}
    (h : ∀ p ∈ qs, EpsReach A q p) : ∀ p ∈ stepOnce A.epsEdges qs, EpsReach A q p := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp
  · obtain ⟨a, hmem, ha, _⟩ := mem_newTargets.mp hp
    exact (h a ha).trans (.step hmem (.refl _))

/-! ### Correctness of `saturate` -/

theorem subset_saturate (edges : List (σ × σ)) (n : Nat) (qs : List σ) :
    qs ⊆ saturate edges n qs := by
  induction n generalizing qs with
  | zero => simp [saturate]
  | succ n ih =>
      simp only [saturate]
      split
      · exact fun _ h => h
      · exact fun x hx => ih (stepOnce edges qs) (subset_stepOnce edges qs hx)

theorem saturate_sound {A : TA σ} (n : Nat) {qs : List σ} {q : σ}
    (h : ∀ p ∈ qs, EpsReach A q p) : ∀ p ∈ saturate A.epsEdges n qs, EpsReach A q p := by
  induction n generalizing qs with
  | zero => simpa [saturate] using h
  | succ n ih =>
      simp only [saturate]
      split
      · exact h
      · exact ih (stepOnce_sound h)

theorem saturate_nodup {edges : List (σ × σ)} (n : Nat) {qs : List σ} (h : qs.Nodup) :
    (saturate edges n qs).Nodup := by
  induction n generalizing qs with
  | zero => simpa [saturate] using h
  | succ n ih =>
      simp only [saturate]
      split
      · exact h
      · exact ih (stepOnce_nodup h)

theorem saturate_subset {edges : List (σ × σ)} (n : Nat) {qs U : List σ}
    (hq : qs ⊆ U) (he : ∀ a b, (a, b) ∈ edges → b ∈ U) : saturate edges n qs ⊆ U := by
  induction n generalizing qs with
  | zero => simpa [saturate] using hq
  | succ n ih =>
      simp only [saturate]
      split
      · exact hq
      · exact ih (stepOnce_subset hq he)

/--
The key finiteness lemma: with a budget exceeding the size of the universe `U`,
saturation really does reach a fixed point.
-/
theorem saturate_closed {edges : List (σ × σ)} (n : Nat) {qs U : List σ}
    (hnd : qs.Nodup) (hq : qs ⊆ U) (he : ∀ a b, (a, b) ∈ edges → b ∈ U)
    (hbud : U.length + 1 ≤ qs.length + n) :
    EdgeClosed edges (saturate edges n qs) := by
  induction n generalizing qs with
  | zero =>
      exact absurd (List.Nodup.length_le_of_subset hnd hq) (by omega)
  | succ n ih =>
      simp only [saturate]
      split
      · next h => exact edgeClosed_of_step_eq h
      · next h =>
          refine ih (stepOnce_nodup hnd) (stepOnce_subset hq he) ?_
          have hlt : qs.length < (stepOnce edges qs).length := by omega
          omega

/-! ### Closure tables -/

/-- A closure table maps each state to the states it may be promoted to. -/
abbrev EpsTable (σ : Type) := σ → List σ

/-- `tbl` is *the* ε-closure of `A`. -/
def IsEpsClosure (A : TA σ) (tbl : EpsTable σ) : Prop :=
  ∀ q p, p ∈ tbl q ↔ EpsReach A q p

namespace TA

/-- Closure of a single state, computed by saturation. -/
def closeFrom (A : TA σ) (q : σ) : List σ :=
  saturate A.epsEdges (A.mentionedStates.length + 1) [q]

/-- The ε-closure table of an automaton. -/
def epsTable (A : TA σ) : EpsTable σ := A.closeFrom

theorem epsEdges_target_mem {A : TA σ} {a b : σ} (h : (a, b) ∈ A.epsEdges) :
    b ∈ A.mentionedStates := by
  obtain ⟨tr, htr, _, _, htgt⟩ := mem_epsEdges.mp h
  subst htgt
  simp only [mentionedStates, List.mem_dedup, List.mem_append]
  exact Or.inl (Or.inr (List.mem_map_of_mem htr))

theorem epsEdges_source_mem {A : TA σ} {a b : σ} (h : (a, b) ∈ A.epsEdges) :
    a ∈ A.mentionedStates := by
  obtain ⟨tr, htr, _, hrhs, _⟩ := mem_epsEdges.mp h
  simp only [mentionedStates, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨tr, htr, by rw [hrhs]; simp⟩

theorem mem_closeFrom_self (A : TA σ) (q : σ) : q ∈ A.closeFrom q :=
  subset_saturate _ _ _ (by simp)

theorem closeFrom_sound {A : TA σ} {q p : σ} (h : p ∈ A.closeFrom q) : EpsReach A q p :=
  saturate_sound _ (by intro p hp; simp only [List.mem_singleton] at hp; exact hp ▸ .refl _) p h

theorem closeFrom_closed (A : TA σ) (q : σ) (hq : q ∈ A.mentionedStates) :
    EdgeClosed A.epsEdges (A.closeFrom q) := by
  refine saturate_closed _ (by simp) (by simpa using hq)
    (fun a b h => epsEdges_target_mem h) ?_
  simp only [List.length_singleton]
  omega

theorem closeFrom_complete {A : TA σ} {q p : σ} (hq : q ∈ A.mentionedStates)
    (h : EpsReach A q p) : p ∈ A.closeFrom q := by
  have hclosed := A.closeFrom_closed q hq
  have gen : ∀ {x y : σ}, EpsReach A x y → x ∈ A.closeFrom q → y ∈ A.closeFrom q := by
    intro x y hxy
    induction hxy with
    | refl => exact id
    | step he _ ih => exact fun hx => ih (hclosed _ _ he hx)
  exact gen h (A.mem_closeFrom_self q)

theorem isEpsClosure_epsTable (A : TA σ) : IsEpsClosure A A.epsTable := by
  intro q p
  refine ⟨closeFrom_sound, fun h => ?_⟩
  by_cases hq : q ∈ A.mentionedStates
  · exact closeFrom_complete hq h
  · cases h with
    | refl => exact A.mem_closeFrom_self q
    | step he _ => exact absurd (epsEdges_source_mem he) hq

end TA

/-- Any two ε-closure tables of the same automaton agree. -/
theorem IsEpsClosure.mem_iff {A : TA σ} {t₁ t₂ : EpsTable σ}
    (h₁ : IsEpsClosure A t₁) (h₂ : IsEpsClosure A t₂) (q p : σ) :
    p ∈ t₁ q ↔ p ∈ t₂ q := by rw [h₁, h₂]

end Greta
