/-
**Algorithm 3.3 (IntersectTA)** and **Algorithm 3.4 (FindDupStates)**: the optimised
intersection of two tree automata that Greta actually runs.

It differs from the textbook product of `Greta.Product` in three ways, each of which the
paper ablates separately (`I¹`, `I²`, `I³` of Table 1) and each of which is a flag here:

* `reachability` — only product states that can be reached from the accepting pair are
  explored, and transitions are looked up through ε-transitions rather than being
  produced for every pair of states;
* `dedupStates` — states with identical incoming transitions are merged;
* `introEps` — when the transitions of one state are a subset of another's, the shared
  ones are replaced by a single ε-transition.

`Greta.prodTA_lang` proves `L(A ⊗ B) = L(A) ∩ L(B)` for the textbook construction; the
optimised algorithm below is checked against it by testing (see `docs/testing.md`).
-/
import Greta.Product
import Greta.CFG

namespace Greta

variable {σ σ₁ σ₂ : Type} [DecidableEq σ] [DecidableEq σ₁] [DecidableEq σ₂]

/-! ### Looking through ε-transitions -/

/--
States reachable *downwards* from `q` along ε-transitions: `q' ∈ epsDown A q` when a
subtree evaluating to `q'` may be promoted to `q`.  This is `find_intermediate_states` of
the reference implementation.
-/
def TA.epsDown (A : TA σ) (q : σ) : List σ :=
  saturate (A.epsEdges.map Prod.swap) (A.mentionedStates.length + 1) [q]

/-- Constructor labels usable at `q`, ε-transitions included. -/
def TA.symsAt (A : TA σ) (q : σ) : List Sym :=
  ((A.epsDown q).flatMap fun q' =>
    (A.realTrans.filter fun tr => tr.target == q').map Transition.sym).dedup

/-- Transitions producing `q` with label `s`, ε-transitions included. -/
def TA.transAt (A : TA σ) (q : σ) (s : Sym) : List (Transition σ) :=
  (A.epsDown q).flatMap fun q' =>
    A.realTrans.filter fun tr => tr.target == q' && tr.sym == s

/-! ### Step 1: reachability-driven cross product -/

/-- The cross product of two transitions, targeted at the product state we came from. -/
def crossTrans (q : σ₁ × σ₂) (t₁ : Transition σ₁) (t₂ : Transition σ₂) :
    Option (Transition (σ₁ × σ₂)) :=
  if compatAll t₁.rhs t₂.rhs then some ⟨q, t₁.sym, zipBetas t₁.rhs t₂.rhs⟩ else none

/-- Product states appearing on the right-hand side of a transition. -/
def rhsStates (tr : Transition σ) : List σ :=
  tr.rhs.filterMap fun
    | .state p => some p
    | .term _  => none

/-- All transitions the algorithm creates for one product state. -/
def transitionsAtPair (A : TA σ₁) (B : TA σ₂) (q : σ₁ × σ₂) : List (Transition (σ₁ × σ₂)) :=
  ((A.symsAt q.1).filter fun s => (B.symsAt q.2).contains s).flatMap fun s =>
    (A.transAt q.1 s).flatMap fun t₁ =>
      (B.transAt q.2 s).filterMap fun t₂ => crossTrans q t₁ t₂

/-- The worklist loop of Algorithm 3.3. -/
def reachLoop (A : TA σ₁) (B : TA σ₂) :
    Nat → List (σ₁ × σ₂) → List (σ₁ × σ₂) → List (Transition (σ₁ × σ₂)) →
    List (σ₁ × σ₂) × List (Transition (σ₁ × σ₂))
  | 0,        _,       q, δ => (q, δ)
  | _ + 1,    [],      q, δ => (q, δ)
  | fuel + 1, w :: ws, q, δ =>
      let newTrans := transitionsAtPair A B w
      let reached := (newTrans.flatMap rhsStates).dedup
      let fresh := reached.filter fun p => !q.contains p
      reachLoop A B fuel (ws ++ fresh) (q ++ fresh) (δ ++ newTrans).dedup

/-- Every product state and transition, without the reachability restriction. -/
def allPairsProduct (A : TA σ₁) (B : TA σ₂) :
    List (σ₁ × σ₂) × List (Transition (σ₁ × σ₂)) :=
  let qs := pairs A.mentionedStates B.mentionedStates
  (qs, (qs.flatMap (transitionsAtPair A B)).dedup)

/-! ### Step 2: removing duplicate states (Algorithm 3.4) -/

/-- Replace the state being analysed by a placeholder, so that two states' incoming
transitions can be compared up to renaming (the `e_tmp` of Algorithm 3.4). -/
def betaSubst (e : σ) : Beta σ → Beta (Option σ)
  | .term a  => .term a
  | .state x => .state (if x = e then none else some x)

/-- The *signature* of a state: its incoming transitions, up to renaming itself. -/
def stateSig (δ : List (Transition σ)) (e : σ) : List (Sym × List (Beta (Option σ))) :=
  ((δ.filter fun tr => tr.target == e).map fun tr => (tr.sym, tr.rhs.map (betaSubst e))).dedup

/-- Two lists have the same elements. -/
def sameElems {α : Type} [DecidableEq α] (l₁ l₂ : List α) : Bool :=
  l₁.all (fun x => l₂.contains x) && l₂.all (fun x => l₁.contains x)

/-- **Algorithm 3.4 (FindDupStates).** -/
def findDupStates (qs : List σ) (δ : List (Transition σ)) : List (σ × σ) :=
  qs.flatMap fun ei =>
    (qs.filter fun ej => ej != ei).filterMap fun ej =>
      if sameElems (stateSig δ ei) (stateSig δ ej) then some (ei, ej) else none

/-- Canonical representative of a state under a list of duplicate pairs. -/
def canonOf (dups : List (σ × σ)) (e : σ) : σ :=
  match dups.find? fun p => p.2 == e && p.1 != e with
  | some p => p.1
  | none   => e

/-- Rewrite a transition along a state renaming. -/
def renameTrans (f : σ → σ) (tr : Transition σ) : Transition σ :=
  ⟨f tr.target, tr.sym, tr.rhs.map fun
    | .state x => .state (f x)
    | .term a  => .term a⟩

/-- Merge duplicate states, keeping the first representative of each class. -/
def mergeDups (qs : List σ) (δ : List (Transition σ)) : List σ × List (Transition σ) :=
  -- keep only pairs whose first component is not itself eliminated
  let dups := (findDupStates qs δ).filter fun p => p.1 != p.2
  let keep : List (σ × σ) := dups.foldl (fun acc p =>
      if (acc.map Prod.snd).contains p.2 then acc
      else if (acc.map Prod.snd).contains p.1 then acc
      else acc ++ [p]) []
  let f := canonOf keep
  ((qs.map f).dedup, (δ.map (renameTrans f)).dedup)

/-! ### Step 3: introducing ε-transitions -/

/-- Transition shapes (label and right-hand side) producing `e`. -/
def shapesOf (δ : List (Transition σ)) (e : σ) : List (Sym × List (Beta σ)) :=
  ((δ.filter fun tr => tr.target == e).map fun tr => (tr.sym, tr.rhs)).dedup

/-- One `(i, j)` step of the ε-introduction loop of Algorithm 3.3. -/
def introEpsStep (δ : List (Transition σ)) (ei ej : σ) : List (Transition σ) :=
  let si := shapesOf δ ei
  let sj := shapesOf δ ej
  if ei != ej && !si.isEmpty && si.all (fun x => sj.contains x) then
    (δ.filter fun tr => !(tr.target == ej && si.contains (tr.sym, tr.rhs)))
      ++ [⟨ej, epsSym, [.state ei]⟩]
  else δ

/-- The ε-introduction loop: states are visited from fewest to most transitions. -/
def introEpsAll (qs : List σ) (δ : List (Transition σ)) : List (Transition σ) :=
  let ordered := qs.mergeSort fun a b => (shapesOf δ a).length ≤ (shapesOf δ b).length
  (ordered.zipIdx).foldl (fun acc pi =>
    (ordered.drop (pi.2 + 1)).foldl (fun acc' ej => introEpsStep acc' pi.1 ej) acc) δ

/-! ### Putting it together -/

/-- Which optimisations of Algorithm 3.3 to enable. -/
structure IntersectOpts where
  /-- Restrict the construction to product states reachable from the accepting pair. -/
  reachability : Bool := true
  /-- Merge states with identical incoming transitions (Algorithm 3.4). -/
  dedupStates : Bool := true
  /-- Replace repeated transitions by ε-transitions. -/
  introEps : Bool := true
deriving Repr, Inhabited

/-- All optimisations on: the default configuration `I^def` of the paper. -/
def IntersectOpts.default : IntersectOpts := {}

/-- All optimisations off: the configuration `I^123` of the paper. -/
def IntersectOpts.none : IntersectOpts :=
  { reachability := false, dedupStates := false, introEps := false }

/-- **Algorithm 3.3 (IntersectTA).** -/
def intersectTA (A : TA σ₁) (B : TA σ₂) (opts : IntersectOpts := {}) : TA (σ₁ × σ₂) :=
  let finals := pairs A.finals B.finals
  let fuel := A.mentionedStates.length * B.mentionedStates.length + 1
  let (qs₀, δ₀) :=
    if opts.reachability then reachLoop A B fuel finals finals []
    else allPairsProduct A B
  let (qs₁, δ₁) := if opts.dedupStates then mergeDups qs₀ δ₀ else (qs₀, δ₀)
  let δ₂ := if opts.introEps then introEpsAll qs₁ δ₁ else δ₁
  { states    := qs₁
    alphabet  := (A.alphabet.filter fun f => B.alphabet.contains f) ++ [epsSym]
    terminals := A.terminals.filter fun a => B.terminals.contains a
    finals    := finals.filter fun q => qs₁.contains q
    trans     := δ₂ }

/-! ### Rendering the result as a grammar

Un-labelling the transitions of a tree automaton turns it back into a CFG
(Section 2.4); ε-transitions become unit productions.
-/

/-- Name a product state, for printing the result as a CFG. -/
def pairName (nameOf : σ₁ → String) (nameOf' : σ₂ → String) (q : σ₁ × σ₂) : String :=
  "(" ++ nameOf q.1 ++ "," ++ nameOf' q.2 ++ ")"

/-- Turn a tree automaton back into a CFG by dropping the constructor labels. -/
def taToCFG (A : TA String) : CFG :=
  CFG.mk A.states A.terminals A.finals <| A.trans.map fun tr =>
    (tr.target, tr.rhs.map fun
      | .term a  => SigmaElt.term a
      | .state q => SigmaElt.nt q)

/-! ### Monotonicity of the evaluator

A sub-automaton of `A` (fewer transitions, smaller ε-closure) accepts fewer trees.  This
is what makes the reachability restriction of Algorithm 3.3 sound.
-/

theorem matchAll_mono {A B : TA σ} {tA tB : EpsTable σ}
    (hcl : ∀ q p, p ∈ tA q → p ∈ tB q) :
    ∀ (ts : List Tree) (bs : List (Beta σ)),
      (∀ t ∈ ts, ∀ q, q ∈ A.evalT tA t → q ∈ B.evalT tB t) →
      A.matchAll tA ts bs = true → B.matchAll tB ts bs = true := by
  intro ts
  induction ts with
  | nil => intro bs _ h; cases bs <;> simp_all [TA.matchAll]
  | cons t ts ih =>
      intro bs hts h
      have hhd := hts t (List.mem_cons_self ..)
      have htl : ∀ u ∈ ts, ∀ q, q ∈ A.evalT tA u → q ∈ B.evalT tB u :=
        fun u hu => hts u (List.mem_cons_of_mem _ hu)
      cases bs with
      | nil => simp [TA.matchAll] at h
      | cons b bs =>
          cases b with
          | term a =>
              simp only [TA.matchAll, Bool.and_eq_true] at h ⊢
              exact ⟨h.1, ih bs htl h.2⟩
          | state q =>
              simp only [TA.matchAll, Bool.and_eq_true, List.any_eq_true,
                decide_eq_true_eq] at h ⊢
              obtain ⟨⟨r, hr, hq⟩, hrest⟩ := h
              exact ⟨⟨r, hhd r hr, hcl r q hq⟩, ih bs htl hrest⟩

theorem evalT_mono {A B : TA σ} {tA tB : EpsTable σ}
    (htr : ∀ tr ∈ A.realTrans, tr ∈ B.realTrans)
    (hcl : ∀ q p, p ∈ tA q → p ∈ tB q) :
    ∀ (t : Tree) (q : σ), q ∈ A.evalT tA t → q ∈ B.evalT tB t := by
  intro t
  induction t using Tree.rec' with
  | hleaf a => intro q hq; simp [TA.evalT] at hq
  | hnode f ts ih =>
      intro q hq
      simp only [TA.evalT, List.mem_filterMap] at hq ⊢
      obtain ⟨tr, htrm, hif⟩ := hq
      split at hif
      · next hc =>
          refine ⟨tr, htr tr htrm, ?_⟩
          rw [if_pos ⟨hc.1, matchAll_mono hcl ts tr.rhs ih hc.2⟩]
          exact hif
      · simp at hif

theorem accepts_mono {A B : TA σ} {tA tB : EpsTable σ}
    (htr : ∀ tr ∈ A.realTrans, tr ∈ B.realTrans)
    (hcl : ∀ q p, p ∈ tA q → p ∈ tB q)
    (hfin : ∀ q ∈ A.finals, q ∈ B.finals) (t : Tree) :
    A.accepts tA t = true → B.accepts tB t = true := by
  simp only [TA.accepts, List.any_eq_true, decide_eq_true_eq]
  rintro ⟨q, hq, p, hp, hf⟩
  exact ⟨q, evalT_mono htr hcl t q hq, p, hcl q p hp, hfin p hf⟩

end Greta
