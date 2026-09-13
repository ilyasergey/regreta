/-
**Algorithm 3.2 (GenTA)**: generating a tree automaton from the associativity set `O_a`,
the precedence order `O_p` and the input grammar.

The generated automaton has one *ordered* state `e_i` per level of `O_p`, one state per
trivial symbol, an ε-chain `e_i ←(ε,1) e_{i+1}` connecting consecutive levels, and the
cycle-restoring transitions supplied by `HighToLow`.

States are a datatype rather than strings.  The reference implementation names them
`"e0"`, `"e1"`, …, and `GState.name` reproduces those names for printing; but the proofs
in `Greta.GenTASpec` have to read a level back off a state, and `Nat`'s `toString` has no
injectivity lemma to hand.

The four groups of transitions are separate definitions and `genTA` is their
concatenation, with no `dedup`, so that membership in `(genTA …).trans` can be inverted
with `List.mem_append`.  Duplicates are harmless: `evalT` collects targets, so a repeated
transition contributes nothing.
-/
import Greta.Learn

namespace Greta

/-- States of the automaton `GenTA` builds. -/
inductive GState where
  /-- The ordered state `e_i`, one per level of `O_p`. -/
  | lvl : Nat → GState
  /-- The state a trivial symbol keeps, named by its nonterminal. -/
  | triv : Nonterminal → GState
deriving DecidableEq, Repr, Inhabited

namespace GState

/-- The name the reference implementation gives a state. -/
def name : GState → String
  | .lvl i  => "e" ++ toString i
  | .triv A => A

/-- The level of an ordered state. -/
def level? : GState → Option Nat
  | .lvl i  => some i
  | .triv _ => none

@[simp] theorem level?_lvl (i : Nat) : (GState.lvl i).level? = some i := rfl
@[simp] theorem level?_triv (A : Nonterminal) : (GState.triv A).level? = none := rfl

end GState

/-- The ordered state at level `i`. -/
abbrev stateName (i : Nat) : GState := .lvl i

/--
Fill the right-hand side of a production with states: terminals are kept, and the `k`-th
entry becomes `fill k` when it is a nonterminal.  Nonterminals associated with *trivial*
symbols keep their own state, as footnote 3 of Section 3.1.3 requires.  This is the
`δ`-generator `δ_F` of Algorithm 3.2.
-/
def fillRhs (tn : List Nonterminal) (rhs : List SigmaElt) (fill : Nat → GState) :
    List (Beta GState) :=
  rhs.zipIdx.map fun xi =>
    match xi.1 with
    | .term a => .term a
    | .nt B   => if tn.contains B then .state (.triv B) else .state (fill xi.2)

/-- `δ_F(target, fill, f)`: the transition for symbol `f` with the given target state. -/
def deltaGen (g : CFG) (tn : List Nonterminal) (target : GState) (fill : Nat → GState)
    (f : Sym) : Option (Transition GState) :=
  (g.prodOfSym f).map fun p => ⟨target, f, fillRhs tn p.2 fill⟩

/--
The state that a level-`i` transition for `s` puts at right-hand-side position `k`: one
level deeper at every position `O_a` forbids, the same level elsewhere.  All of a symbol's
restrictions apply, not just the first.
-/
def oaFill (oa : Oa) (s : Sym) (i k : Nat) : GState :=
  if (oa.positionsOf s).contains k then .lvl (i + 1) else .lvl i

/-- The trivial symbols `genTA` sets aside. -/
def trivSyms (g : CFG) (excludeTrivial : Bool) : List Sym :=
  if excludeTrivial then g.trivialSyms else []

/-- The nonterminals of those trivial symbols. -/
def trivNts (g : CFG) (excludeTrivial : Bool) : List Nonterminal :=
  ((trivSyms g excludeTrivial).filterMap fun f => (g.prodOfSym f).map Prod.fst).dedup

/-- Transitions for the non-trivial symbols (the first loop of Algorithm 3.2). -/
def nonTrivTrans (g : CFG) (oa : Oa) (op : OrderMap) (tn : List Nonterminal) :
    List (Transition GState) :=
  op.flatMap fun oss =>
    oss.2.filterMap fun s => deltaGen g tn (.lvl oss.1) (oaFill oa s oss.1) s

/-- Transitions for the trivial symbols (the second loop of Algorithm 3.2). -/
def trivialTrans (g : CFG) (ts : List Sym) : List (Transition GState) :=
  ts.filterMap fun s =>
    (g.prodOfSym s).map fun p => ⟨.triv p.1, s, fillRhs [] p.2 (fun _ => .triv p.1)⟩

/-- The ε-chain `e_i ←(ε,1) e_{i+1}` (the third loop of Algorithm 3.2). -/
def epsChain (m : Nat) : List (Transition GState) :=
  (List.range m).map fun i => ⟨.lvl i, epsSym, [.state (.lvl (i + 1))]⟩

/-- The cycle-restoring transitions (the last loop of Algorithm 3.2). -/
def cycleTrans (g : CFG) (obp op : OrderMap) (tn : List Nonterminal) :
    List (Transition GState) :=
  (g.highToLow obp op).filterMap fun pr =>
    deltaGen g tn (.lvl pr.2.2) (fun _ => .lvl pr.1.2) pr.2.1

/--
**Algorithm 3.2 (GenTA).**  `genTA g oa op` builds the tree automaton `A_r` encoding the
parsing preferences described by `oa` and `op`.
-/
def genTA (g : CFG) (oa : Oa) (op : OrderMap) (excludeTrivial : Bool := true) : TA GState where
  states    := ((List.range (op.maxOrder + 1)).map GState.lvl)
                 ++ (trivNts g excludeTrivial).map GState.triv
  alphabet  := (op.symbols ++ trivSyms g excludeTrivial ++ [epsSym]).dedup
  terminals := g.terms
  finals    := [.lvl 0]
  trans     := nonTrivTrans g oa op (trivNts g excludeTrivial)
                 ++ trivialTrans g (trivSyms g excludeTrivial)
                 ++ epsChain op.maxOrder
                 ++ cycleTrans g (g.baseOrder excludeTrivial) op (trivNts g excludeTrivial)

/-! ### Structural facts about the generated automaton -/

@[simp] theorem genTA_finals (g : CFG) (oa : Oa) (op : OrderMap) (b : Bool) :
    (genTA g oa op b).finals = [.lvl 0] := rfl

@[simp] theorem genTA_trans (g : CFG) (oa : Oa) (op : OrderMap) (b : Bool) :
    (genTA g oa op b).trans =
      nonTrivTrans g oa op (trivNts g b) ++ trivialTrans g (trivSyms g b)
        ++ epsChain op.maxOrder ++ cycleTrans g (g.baseOrder b) op (trivNts g b) := rfl

/-- The ε-chain of `GenTA` promotes a deeper level to the next shallower one. -/
theorem genTA_eps_mem {g : CFG} {oa : Oa} {op : OrderMap} {b : Bool} {i : Nat}
    (h : i < op.maxOrder) :
    (⟨.lvl i, epsSym, [.state (.lvl (i + 1))]⟩ : Transition GState) ∈ (genTA g oa op b).trans := by
  rw [genTA_trans]
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  exact List.mem_map_of_mem (List.mem_range.mpr h)

end Greta
