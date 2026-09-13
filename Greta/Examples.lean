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

/-- The constructor at the root of a tree, if it has one. -/
def rootSym : Tree → Option Sym
  | .leaf _   => none
  | .node f _ => some f

/-- `t` is an occurrence of the pattern `Eg(top, bot, idx)` at its root. -/
def matchesHere (e : TreeExample) (t : Tree) : Bool :=
  match t with
  | .leaf _    => false
  | .node f ts => f == e.top && (ts[e.idx]?.bind rootSym) == some e.bot

theorem matchesHere_node {e : TreeExample} {f : Sym} {ts : List Tree} :
    e.matchesHere (.node f ts) = true ↔
      f = e.top ∧ ∃ h us, ts[e.idx]? = some (.node h us) ∧ h = e.bot := by
  simp only [matchesHere, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hf, hb⟩
    refine ⟨hf, ?_⟩
    cases hget : ts[e.idx]? with
    | none => rw [hget] at hb; simp at hb
    | some t =>
        cases t with
        | leaf a => rw [hget] at hb; simp [rootSym] at hb
        | node h us =>
            rw [hget] at hb
            simp only [Option.bind_some, rootSym, Option.some.injEq] at hb
            exact ⟨h, us, rfl, hb⟩
  · rintro ⟨hf, h, us, hget, rfl⟩
    exact ⟨hf, by rw [hget]; simp [rootSym]⟩

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

theorem occursIn_leaf (e : TreeExample) (a : Terminal) : e.occursIn (.leaf a) = false := by
  simp [occursIn]

theorem occursIn_node (e : TreeExample) (f : Sym) (ts : List Tree) :
    e.occursIn (.node f ts) = (e.matchesHere (.node f ts) || e.occursInAny ts) := by
  simp [occursIn]

theorem occursIn_of_mem {e : TreeExample} {f : Sym} {ts : List Tree} {u : Tree}
    (h : e.occursIn (.node f ts) = false) (hu : u ∈ ts) : e.occursIn u = false := by
  rw [occursIn_node, Bool.or_eq_false_iff] at h
  obtain ⟨-, hany⟩ := h
  revert hu
  induction ts with
  | nil => intro hu; simp at hu
  | cons v vs ih =>
      simp only [occursInAny, Bool.or_eq_false_iff] at hany
      intro hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hany.1
      · exact ih hany.2 hu

theorem occursInAny_false (e : TreeExample) :
    ∀ ts : List Tree, (∀ t ∈ ts, e.occursIn t = false) → e.occursInAny ts = false := by
  intro ts
  induction ts with
  | nil => intro _; simp [occursInAny]
  | cons t ts ih =>
      intro h
      simp only [occursInAny, Bool.or_eq_false_iff]
      exact ⟨h t (List.mem_cons_self ..), ih fun u hu => h u (List.mem_cons_of_mem _ hu)⟩


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
