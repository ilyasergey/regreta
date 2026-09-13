/-
Core datatypes of the Greta development: ranked symbols, trees, and the variant of
bottom-up tree automata used in the paper (Appendix A, Definitions A.4–A.8).

The OCaml reference implementation fixes states to be strings (`lib/ta.ml`).  Here the
state type is a parameter, which lets the product construction of `Greta.Product` use
genuine pairs instead of a string encoding.  All executable algorithms are instantiated
at `σ := String` so that they line up with the reference implementation.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Perm.Subperm

namespace Greta

/-- Terminal symbols of the object language.  Strings, exactly as in `lib/ta.ml`. -/
abbrev Terminal := String

/--
A ranked-alphabet symbol (Definition A.4).  `id` is the identifier of the CFG production
the symbol was derived from, `name` is its display name (the first terminal of the
production's right-hand side, or `δ`), and `rank` is the length of that right-hand side.

Two symbols are equal iff all three components agree; this is `Ta.syms_equals` of the
reference implementation.
-/
structure Sym where
  id : Int
  name : String
  rank : Nat
deriving DecidableEq, Repr, Inhabited, Hashable

/-- Display name used for productions whose right-hand side contains no terminal. -/
def deltaName : String := "δ"

/-- Display name of the `ε` symbol. -/
def epsName : String := "ε"

/-- The distinguished rank-1 symbol `(ε, 1)` labelling ε-transitions (Definition A.6). -/
def epsSym : Sym := ⟨-1, epsName, 1⟩

/-- Right-hand-side entry of a transition: either a terminal or a state. -/
inductive Beta (σ : Type) where
  | term  : Terminal → Beta σ
  | state : σ → Beta σ
deriving DecidableEq, Repr, Inhabited

/-- A transition rule `target ←sym rhs` (Definition A.5). -/
structure Transition (σ : Type) where
  target : σ
  sym    : Sym
  rhs    : List (Beta σ)
deriving DecidableEq, Repr, Inhabited

/--
Trees over the ranked alphabet.  Leaves carry terminals, internal nodes carry a ranked
symbol.  This is `Ta.tree` of the reference implementation.
-/
inductive Tree where
  | leaf : Terminal → Tree
  | node : Sym → List Tree → Tree
deriving Repr, Inhabited

namespace Tree

/-- Structural equality on trees. -/
def beq : Tree → Tree → Bool
  | .leaf a,    .leaf b    => a == b
  | .node f ts, .node g us => f == g && beqs ts us
  | _,          _          => false
where
  beqs : List Tree → List Tree → Bool
    | [],      []      => true
    | t :: ts, u :: us => beq t u && beqs ts us
    | _,       _       => false

instance : BEq Tree := ⟨beq⟩

/-- Number of nodes of a tree. -/
def size : Tree → Nat
  | .leaf _ => 1
  | .node _ ts => 1 + sizes ts
where
  sizes : List Tree → Nat
    | [] => 0
    | t :: ts => size t + sizes ts

/-- Depth of a tree. -/
def depth : Tree → Nat
  | .leaf _ => 1
  | .node _ ts => 1 + depths ts
where
  depths : List Tree → Nat
    | [] => 0
    | t :: ts => max (depth t) (depths ts)

/-- The yield of a tree: its terminal leaves, left to right (used to state ambiguity). -/
def yield : Tree → List Terminal
  | .leaf a => [a]
  | .node _ ts => yields ts
where
  yields : List Tree → List Terminal
    | [] => []
    | t :: ts => yield t ++ yields ts

/--
Strong induction principle for the nested inductive type `Tree`: to prove a property of
every tree it suffices to handle leaves and to handle a node given the property for all
its immediate subtrees.
-/
def rec' {motive : Tree → Sort _}
    (hleaf : ∀ a, motive (.leaf a))
    (hnode : ∀ f ts, (∀ t ∈ ts, motive t) → motive (.node f ts)) : ∀ t, motive t
  | .leaf a => hleaf a
  | .node f ts => hnode f ts fun t ht =>
      have : sizeOf t < sizeOf (Tree.node f ts) := by
        have h₁ : sizeOf t < sizeOf ts := List.sizeOf_lt_of_mem ht
        simp only [Tree.node.sizeOf_spec]
        omega
      rec' hleaf hnode t
termination_by t => sizeOf t

end Tree

/--
A (finite, bottom-up) tree automaton, Definition A.5.  Terminals may occur directly in
the right-hand sides of transitions, which is the lightweight CFG-oriented variant of
tree automata the paper uses.
-/
structure TA (σ : Type) where
  states    : List σ
  alphabet  : List Sym
  terminals : List Terminal
  finals    : List σ
  trans     : List (Transition σ)
deriving Repr, Inhabited

/-- All pairs drawn from two lists, used by the product construction. -/
def pairs {α β : Type} (l₁ : List α) (l₂ : List β) : List (α × β) :=
  l₁.flatMap fun a => l₂.map fun b => (a, b)

@[simp] theorem mem_pairs {α β : Type} {l₁ : List α} {l₂ : List β} {p : α × β} :
    p ∈ pairs l₁ l₂ ↔ p.1 ∈ l₁ ∧ p.2 ∈ l₂ := by
  obtain ⟨a, b⟩ := p
  simp [pairs]

namespace TA

variable {σ : Type} [DecidableEq σ]

/-- Every state mentioned anywhere in the automaton. -/
def mentionedStates (A : TA σ) : List σ :=
  (A.states ++ A.finals ++ A.trans.map (·.target) ++
    A.trans.flatMap fun tr => tr.rhs.filterMap fun
      | .state q => some q
      | .term _  => none).dedup

/--
The ε-edges of an automaton, oriented in the direction in which they may be *used*:
`(q', q) ∈ epsEdges` when `q ←(ε,1) q'` is a transition, i.e. a subtree that evaluates
to `q'` may be promoted to `q`.
-/
def epsEdges (A : TA σ) : List (σ × σ) :=
  A.trans.filterMap fun tr =>
    if tr.sym = epsSym then
      match tr.rhs with
      | [.state q'] => some (q', tr.target)
      | _           => none
    else none

/-- Rename the states of an automaton. -/
def mapStates {σ τ : Type} (f : σ → τ) (A : TA σ) : TA τ where
  states    := A.states.map f
  alphabet  := A.alphabet
  terminals := A.terminals
  finals    := A.finals.map f
  trans     := A.trans.map fun tr =>
    ⟨f tr.target, tr.sym, tr.rhs.map fun
      | .term a  => .term a
      | .state q => .state (f q)⟩

/-- Transitions that are not ε-transitions.  ε-transitions never consume a tree node
(Definition A.6), so only these are used when matching a node's constructor. -/
def realTrans (A : TA σ) : List (Transition σ) :=
  A.trans.filter fun tr => tr.sym != epsSym

end TA

end Greta
