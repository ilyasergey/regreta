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
