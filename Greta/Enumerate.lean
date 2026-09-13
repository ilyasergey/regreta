/-
Bounded enumeration of the trees an automaton accepts, used to compare languages by
testing (`docs/testing.md`).
-/
import Greta.Serialize

namespace Greta

/-- Cartesian product of a list of choice lists, capped at `cap` results. -/
def choices (cap : Nat) : List (List α) → List (List α)
  | []      => [[]]
  | xs :: rest =>
      let tl := choices cap rest
      (xs.flatMap fun x => tl.map fun ys => x :: ys).take cap

/--
`gen A d q` enumerates trees of depth at most `d` that the automaton may assign the state
`q`, keeping at most `cap` trees per state.
-/
def gen (A : TA String) (cap : Nat) : Nat → String → List Tree
  | 0,     _ => []
  | d + 1, q =>
      let trs := (A.epsDown q).flatMap fun q' =>
        A.realTrans.filter fun tr => tr.target == q'
      -- Spread the budget over the transitions, so that a state with many rules does not
      -- have all but the first few silently dropped.
      let perTrans := max 1 (cap / max 1 trs.length)
      (trs.flatMap fun tr =>
        let opts : List (List Tree) := tr.rhs.map fun
          | .term a  => [Tree.leaf a]
          | .state p => gen A cap d p
        ((choices cap opts).map fun ts => Tree.node tr.sym ts).take perTrans).take cap

/-- Trees accepted by `A`, of depth at most `d`, at every depth from 1 to `d`. -/
def corpus (A : TA String) (cap d : Nat) : List Tree :=
  ((List.range (d + 1)).flatMap fun k => A.finals.flatMap (gen A cap k)).eraseDups.take (cap * 8)

/-- Result of comparing two automata on a corpus of trees. -/
structure LangDiff where
  checked      : Nat
  onlyLeft     : List Tree
  onlyRight    : List Tree
deriving Inhabited

/-- Compare `L(lhs)` with `L(rhs)` on the given corpus. -/
def compareOn (lhs rhs : TA String) (ts : List Tree) : LangDiff :=
  let tl := lhs.epsTable
  let tr := rhs.epsTable
  ts.foldl (fun acc t =>
    let l := lhs.accepts tl t
    let r := rhs.accepts tr t
    { checked := acc.checked + 1
      onlyLeft := if l && !r then acc.onlyLeft ++ [t] else acc.onlyLeft
      onlyRight := if r && !l then acc.onlyRight ++ [t] else acc.onlyRight })
    ⟨0, [], []⟩

/--
Corpus for comparing an intersection result against `A ⊗ B`: trees drawn from `A`, from
`B` and from the result itself, so that both over- and under-acceptance are visible.
-/
def intersectionCorpus (A B R : TA String) (cap d : Nat) : List Tree :=
  (corpus A cap d ++ corpus B cap d ++ corpus R cap d).eraseDups

end Greta
