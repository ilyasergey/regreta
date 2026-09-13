/-
Runs and acceptance for tree automata (Definitions A.7 and A.8).

The semantics is given as a *computable* bottom-up evaluator: `A.evalT tbl t` is the list
of states a run of `A` may assign to the root of `t`, where `tbl` supplies the ε-closure
(Definition A.6) used when promoting the state of a child.  Because the ε-closure of an
automaton is unique (`Greta.IsEpsClosure.mem_iff`) the evaluator does not depend on which
valid table is supplied; this is `TA.evalT_congr` below.
-/
import Greta.Closure

namespace Greta

variable {σ : Type} [DecidableEq σ]

/-- `isLeafOf t a` holds when `t` is the leaf carrying terminal `a`. -/
def isLeafOf (t : Tree) (a : Terminal) : Bool :=
  match t with
  | .leaf a' => a' == a
  | .node _ _ => false

namespace TA

mutual

/--
States that a run of `A` may assign to the root of `t`.  Leaves carry terminals and are
never assigned a state (Definition A.7); a node is assigned `tr.target` whenever some
transition `tr` labelled by the node's constructor matches its children.
-/
def evalT (A : TA σ) (tbl : EpsTable σ) : Tree → List σ
  | .leaf _ => []
  | .node f ts =>
      A.realTrans.filterMap fun tr =>
        if tr.sym = f ∧ matchAll A tbl ts tr.rhs = true then some tr.target else none
  termination_by t => sizeOf t

/--
Checks the children of a node against the right-hand side of a transition: a terminal
entry must be matched by a leaf carrying that terminal, a state entry `q` must be matched
by a subtree evaluating to some state whose ε-closure contains `q`.
-/
def matchAll (A : TA σ) (tbl : EpsTable σ) : List Tree → List (Beta σ) → Bool
  | [],      []              => true
  | t :: ts, .term a :: bs   =>
      isLeafOf t a && matchAll A tbl ts bs
  | t :: ts, .state q :: bs  =>
      (evalT A tbl t).any (fun r => decide (q ∈ tbl r)) && matchAll A tbl ts bs
  | _,       _               => false
  termination_by ts _ => sizeOf ts

end

/-- A tree is accepted when some state assignable to its root ε-reaches a final state. -/
def accepts (A : TA σ) (tbl : EpsTable σ) (t : Tree) : Bool :=
  (A.evalT tbl t).any fun q => (tbl q).any fun p => decide (p ∈ A.finals)

/-- The language of `A`: the set of trees it accepts (Definition A.8). -/
def Lang (A : TA σ) (t : Tree) : Prop := A.accepts A.epsTable t = true

/-- Decision procedure for `TA.Lang`. -/
def langB (A : TA σ) (t : Tree) : Bool := A.accepts A.epsTable t

theorem lang_iff_langB (A : TA σ) (t : Tree) : A.Lang t ↔ A.langB t = true := Iff.rfl

instance (A : TA σ) (t : Tree) : Decidable (A.Lang t) :=
  decidable_of_iff _ (A.lang_iff_langB t).symm

/-! ### Inverting the evaluator -/

@[simp] theorem evalT_leaf (A : TA σ) (tbl : EpsTable σ) (a : Terminal) :
    A.evalT tbl (.leaf a) = [] := by simp [evalT]

/-- A state is assigned to a node exactly when some transition for its constructor fits. -/
theorem mem_evalT_node {A : TA σ} {tbl : EpsTable σ} {f : Sym} {ts : List Tree} {q : σ} :
    q ∈ A.evalT tbl (.node f ts) ↔
      ∃ tr ∈ A.realTrans, tr.sym = f ∧ A.matchAll tbl ts tr.rhs = true ∧ tr.target = q := by
  simp only [evalT, List.mem_filterMap]
  constructor
  · rintro ⟨tr, htr, hif⟩
    split at hif
    · next hc =>
        simp only [Option.some.injEq] at hif
        exact ⟨tr, htr, hc.1, hc.2, hif⟩
    · simp at hif
  · rintro ⟨tr, htr, hs, hm, ht⟩
    exact ⟨tr, htr, by rw [if_pos ⟨hs, hm⟩, ht]⟩

/-- Matching forces the children and the right-hand side to have the same length. -/
theorem matchAll_length {A : TA σ} {tbl : EpsTable σ} :
    ∀ (ts : List Tree) (bs : List (Beta σ)), A.matchAll tbl ts bs = true →
      ts.length = bs.length := by
  intro ts
  induction ts with
  | nil => intro bs h; cases bs <;> simp_all [matchAll]
  | cons u us ih =>
      intro bs h
      cases bs with
      | nil => simp [matchAll] at h
      | cons c cs =>
          have : A.matchAll tbl us cs = true := by
            cases c <;> simp only [matchAll, Bool.and_eq_true] at h <;> exact h.2
          simp [ih cs this]

/-- Matching relates the children and the right-hand side positionwise. -/
theorem matchAll_get {A : TA σ} {tbl : EpsTable σ} :
    ∀ (ts : List Tree) (bs : List (Beta σ)), A.matchAll tbl ts bs = true →
      ∀ (k : Nat) (t : Tree) (b : Beta σ), ts[k]? = some t → bs[k]? = some b →
        (match b with
         | .term a  => isLeafOf t a = true
         | .state q => ∃ r ∈ A.evalT tbl t, q ∈ tbl r) := by
  intro ts
  induction ts with
  | nil => intro bs _ k t b ht _; simp at ht
  | cons u us ih =>
      intro bs hm k t b ht hb
      cases bs with
      | nil => simp [matchAll] at hm
      | cons c cs =>
          cases k with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at ht hb
              subst ht; subst hb
              cases c with
              | term a =>
                  simp only [matchAll, Bool.and_eq_true] at hm
                  exact hm.1
              | state q =>
                  simp only [matchAll, Bool.and_eq_true, List.any_eq_true,
                    decide_eq_true_eq] at hm
                  exact hm.1
          | succ k =>
              have hm' : A.matchAll tbl us cs = true := by
                cases c <;> simp only [matchAll, Bool.and_eq_true] at hm <;> exact hm.2
              simp only [List.getElem?_cons_succ] at ht hb
              exact ih cs hm' k t b ht hb

/-- A child that is a node cannot be matched against a terminal. -/
theorem matchAll_state_of_node {A : TA σ} {tbl : EpsTable σ} {ts : List Tree}
    {bs : List (Beta σ)} (hm : A.matchAll tbl ts bs = true) {k : Nat} {f : Sym} {us : List Tree}
    (ht : ts[k]? = some (.node f us)) (hlen : bs[k]?.isSome) :
    ∃ q, bs[k]? = some (.state q) ∧ ∃ r ∈ A.evalT tbl (.node f us), q ∈ tbl r := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hlen
  have := matchAll_get ts bs hm k _ b ht hb
  cases b with
  | term a => simp only [isLeafOf] at this; exact absurd this (by simp)
  | state q => exact ⟨q, hb, this⟩

/-! ### The evaluator does not depend on the choice of ε-closure table -/

theorem matchAll_congr {A : TA σ} {t₁ t₂ : EpsTable σ}
    (hcl : ∀ q p, p ∈ t₁ q ↔ p ∈ t₂ q) :
    ∀ (ts : List Tree) (bs : List (Beta σ)),
      (∀ t ∈ ts, A.evalT t₁ t = A.evalT t₂ t) → A.matchAll t₁ ts bs = A.matchAll t₂ ts bs := by
  intro ts
  induction ts with
  | nil => intro bs _; cases bs <;> simp [matchAll]
  | cons t ts ih =>
      intro bs hts
      have hhd : A.evalT t₁ t = A.evalT t₂ t := hts t (List.mem_cons_self ..)
      have htl : ∀ u ∈ ts, A.evalT t₁ u = A.evalT t₂ u := fun u hu =>
        hts u (List.mem_cons_of_mem _ hu)
      cases bs with
      | nil => simp [matchAll]
      | cons b bs =>
          cases b with
          | term a => simp only [matchAll, ih bs htl]
          | state q =>
              simp only [matchAll, ih bs htl, hhd]
              congr 2
              funext r
              exact decide_eq_decide.mpr (hcl r q)

theorem evalT_congr {A : TA σ} {t₁ t₂ : EpsTable σ} (hcl : ∀ q p, p ∈ t₁ q ↔ p ∈ t₂ q) :
    ∀ t : Tree, A.evalT t₁ t = A.evalT t₂ t := by
  intro t
  induction t using Tree.rec' with
  | hleaf a => simp [evalT]
  | hnode f ts ih =>
      simp only [evalT]
      congr 1
      funext tr
      rw [matchAll_congr hcl ts tr.rhs ih]

theorem accepts_congr {A : TA σ} {t₁ t₂ : EpsTable σ} (hcl : ∀ q p, p ∈ t₁ q ↔ p ∈ t₂ q)
    (t : Tree) : A.accepts t₁ t = A.accepts t₂ t := by
  rw [Bool.eq_iff_iff]
  simp only [accepts, List.any_eq_true, evalT_congr hcl t, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, p, hp, hf⟩; exact ⟨q, hq, p, (hcl q p).mp hp, hf⟩
  · rintro ⟨q, hq, p, hp, hf⟩; exact ⟨q, hq, p, (hcl q p).mpr hp, hf⟩

/--
Acceptance may be computed with *any* ε-closure table of `A`; in particular with the one
produced by `TA.epsTable`.
-/
theorem lang_iff_accepts {A : TA σ} {tbl : EpsTable σ} (h : IsEpsClosure A tbl) (t : Tree) :
    A.Lang t ↔ A.accepts tbl t = true := by
  unfold Lang
  rw [accepts_congr (IsEpsClosure.mem_iff A.isEpsClosure_epsTable h)]

end TA

end Greta
