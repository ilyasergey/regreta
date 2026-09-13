/-
Tree examples, the parse trees they denote, and the excluded language `L⁻`
(Section 3 of the paper, "Grammar Repair by Example, Formally").

Greta supports tree examples that use exactly two productions, written `Eg(α, β, i)` in
the paper: a root labelled `α` whose `i`-th child is labelled `β`, with every other child
left as a wildcard.
-/
import Greta.Order

namespace Greta

/--
A tree example `Eg(top, bot, idx)`: the symbol `top` at the root with the symbol `bot`
nested at child position `idx`; all other children are wildcards.
-/
structure TreeExample where
  top : Sym
  bot : Sym
  idx : Nat
deriving DecidableEq, Repr, Inhabited

namespace TreeExample

/-- An example is associativity-related when its two symbols coincide (Section 3). -/
def isAssoc (e : TreeExample) : Bool := e.top == e.bot

/-- An example is precedence-related when its two symbols differ. -/
def isPrec (e : TreeExample) : Bool := !e.isAssoc

/-- The `idx`-th child of a node, if the tree is a node with that constructor. -/
def childAt (t : Tree) (f : Sym) (i : Nat) : Option Tree :=
  match t with
  | .node g ts => if g = f then ts[i]? else none
  | .leaf _    => none

/-- `t` is an occurrence of the pattern `Eg(top, bot, idx)` at its root. -/
def matchesHere (e : TreeExample) (t : Tree) : Bool :=
  match childAt t e.top e.idx with
  | some (.node g _) => g == e.bot
  | _                => false

mutual

/-- `t` contains an occurrence of the pattern somewhere. -/
def occursIn (e : TreeExample) : Tree → Bool
  | .leaf _ => false
  | .node f ts => e.matchesHere (.node f ts) || occursInAny e ts
  termination_by t => sizeOf t

/-- `occursIn` lifted to a list of subtrees. -/
def occursInAny (e : TreeExample) : List Tree → Bool
  | [] => false
  | t :: ts => e.occursIn t || e.occursInAny ts
  termination_by ts => sizeOf ts

end

end TreeExample

namespace CFG

/--
`ParseTrees(t)` of Section 3: the complete parse trees of `g` that contain an occurrence
of the example's pattern.
-/
def parseTreesOf (g : CFG) (e : TreeExample) (t : Tree) : Bool :=
  g.isParseTree t && e.occursIn t

/--
`P⁻(t)` of Section 3: the parse trees ruled out by a tree example the user did *not*
select.  For an associativity-related example this is `ParseTrees(t)`; for a
precedence-related one it is the union over all child positions of the root symbol.
-/
def excludedBy (g : CFG) (e : TreeExample) (t : Tree) : Bool :=
  if e.isAssoc then g.parseTreesOf e t
  else (List.range e.top.rank).any fun i => g.parseTreesOf { e with idx := i } t

/-- `L⁻ = ⋃_{t ∈ T⁻} P⁻(t)`: the trees Greta must remove (Section 3.1.4). -/
def excludedLang (g : CFG) (neg : List TreeExample) (t : Tree) : Bool :=
  neg.any fun e => g.excludedBy e t

/-- `L⁺ = ⋃_{t ∈ T⁺} ParseTrees(t)`: the trees the user's selections describe. -/
def selectedLang (g : CFG) (pos : List TreeExample) (t : Tree) : Bool :=
  pos.any fun e => g.parseTreesOf e t

/-- `L_g \ L⁻`, the language Greta is required to produce (Theorem 3.2). -/
def repairedLang (g : CFG) (neg : List TreeExample) (t : Tree) : Bool :=
  g.isParseTree t && !g.excludedLang neg t

theorem repairedLang_subset (g : CFG) (neg : List TreeExample) (t : Tree)
    (h : g.repairedLang neg t = true) : g.isParseTree t = true := by
  simp only [repairedLang, Bool.and_eq_true] at h
  exact h.1

theorem repairedLang_disjoint (g : CFG) (neg : List TreeExample) (t : Tree)
    (h : g.repairedLang neg t = true) : g.excludedLang neg t = false := by
  simp only [repairedLang, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

end CFG

end Greta
