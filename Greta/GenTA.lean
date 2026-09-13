/-
**Algorithm 3.2 (GenTA)**: generating a tree automaton from the associativity set `O_a`,
the precedence order `O_p` and the input grammar.

The generated automaton has one *ordered* state `e_i` per level of `O_p`, one state per
trivial symbol, an ε-chain `e_i ←(ε,1) e_{i+1}` connecting consecutive levels, and the
cycle-restoring transitions supplied by `HighToLow`.
-/
import Greta.Learn

namespace Greta

/-- Name of the ordered state at level `i`. -/
def stateName (i : Nat) : String := "e" ++ toString i

/--
Fill the right-hand side of a production with states: terminals are kept, and the `k`-th
entry becomes `fill k` when it is a nonterminal.  Nonterminals associated with *trivial*
symbols keep their own state, as footnote 3 of Section 3.1.3 requires.  This is the
`δ`-generator `δ_F` of Algorithm 3.2.
-/
def fillRhs (trivNts : List Nonterminal) (rhs : List SigmaElt) (fill : Nat → String) :
    List (Beta String) :=
  rhs.zipIdx.map fun xi =>
    match xi.1 with
    | .term a => .term a
    | .nt B   => if trivNts.contains B then .state B else .state (fill xi.2)

/-- `δ_F(target, fill, f)`: the transition for symbol `f` with the given target state. -/
def deltaGen (g : CFG) (trivNts : List Nonterminal) (target : String) (fill : Nat → String)
    (f : Sym) : Option (Transition String) :=
  (g.prodOfSym f).map fun p => ⟨target, f, fillRhs trivNts p.2 fill⟩

/--
**Algorithm 3.2 (GenTA).**  `genTA g oa op` builds the tree automaton `A_r` encoding the
parsing preferences described by `oa` and `op`.
-/
def genTA (g : CFG) (oa : Oa) (op : OrderMap) (excludeTrivial : Bool := true) : TA String :=
  let obp := g.baseOrder excludeTrivial
  let m := op.maxOrder
  let ordStates := (List.range (m + 1)).map stateName
  let triv := if excludeTrivial then g.trivialSyms else []
  let trivNts := (triv.filterMap fun f => (g.prodOfSym f).map Prod.fst).dedup
  let trivStates := trivNts
  -- Transitions for non-trivial symbols.
  let nonTriv : List (Transition String) := op.flatMap fun oss =>
    oss.2.filterMap fun s =>
      match (oa.positionsOf s).head? with
      | some p => deltaGen g trivNts (stateName oss.1)
                    (fun k => if k = p then stateName (oss.1 + 1) else stateName oss.1) s
      | none   => deltaGen g trivNts (stateName oss.1) (fun _ => stateName oss.1) s
  -- Transitions for trivial symbols: they keep their own nonterminal as a state.
  let trivTrans : List (Transition String) := triv.filterMap fun s =>
    (g.prodOfSym s).map fun p => ⟨p.1, s, fillRhs [] p.2 (fun _ => p.1)⟩
  -- ε-transitions connecting consecutive levels: e_i ←(ε,1) e_{i+1}.
  let epsTrans : List (Transition String) := (List.range m).map fun i =>
    ⟨stateName i, epsSym, [.state (stateName (i + 1))]⟩
  -- Cycle-restoring transitions.
  let cycTrans : List (Transition String) := (g.highToLow obp op).filterMap fun pr =>
    deltaGen g trivNts (stateName pr.2.2) (fun _ => stateName pr.1.2) pr.2.1
  { states    := ordStates ++ trivStates
    alphabet  := (op.symbols ++ triv ++ [epsSym]).dedup
    terminals := g.terms
    finals    := [stateName 0]
    trans     := (nonTriv ++ trivTrans ++ epsTrans ++ cycTrans).dedup }

/-! ### Structural facts about the generated automaton -/

theorem genTA_finals (g : CFG) (oa : Oa) (op : OrderMap) (b : Bool) :
    (genTA g oa op b).finals = [stateName 0] := rfl

/-- The ε-chain of `GenTA` only ever promotes a deeper level to a shallower one. -/
theorem genTA_eps_shape {g : CFG} {oa : Oa} {op : OrderMap} {b : Bool} {i : Nat}
    (h : i < op.maxOrder) :
    (⟨stateName i, epsSym, [.state (stateName (i + 1))]⟩ : Transition String)
      ∈ (genTA g oa op b).trans := by
  simp only [genTA, List.mem_dedup, List.mem_append]
  refine Or.inl (Or.inr ?_)
  exact List.mem_map_of_mem (List.mem_range.mpr h)

end Greta
