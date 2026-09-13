/-
Executable test suite: the running example of the paper, and randomised property tests
comparing the optimised Algorithm 3.3 against the verified product construction.

Run with `lake exe greta selftest`.
-/
import Greta.Enumerate

namespace Greta
namespace Test

/-! ### The running example (Figure 1) -/

private def nt (s : String) : SigmaElt := .nt s
private def tm (s : String) : SigmaElt := .term s

/-- The ambiguous grammar `G` of Figure 1. -/
def runningExample : CFG where
  nonterms := ["stmt", "decl", "expr", "ident"]
  terms    := ["SEMI", "IF", "THEN", "ELSE", "PLUS", "STAR", "INT",
               "LPAREN", "RPAREN", "TINT", "EQ", "IDENT"]
  starts   := ["stmt"]
  prods    :=
    [ ("stmt",  [nt "decl", tm "SEMI"])                                     -- 0  (SEMI,2)
    , ("stmt",  [tm "IF", nt "expr", tm "THEN", nt "stmt"])                 -- 1  (IF,4)
    , ("stmt",  [tm "IF", nt "expr", tm "THEN", nt "stmt", tm "ELSE",
                 nt "stmt"])                                                -- 2  (IF,6)
    , ("decl",  [tm "TINT", nt "ident", tm "EQ", nt "expr"])                -- 3  (TINT,4)
    , ("ident", [tm "IDENT"])                                               -- 4  (IDENT,1)
    , ("expr",  [nt "expr", tm "PLUS", nt "expr"])                          -- 5  (PLUS,3)
    , ("expr",  [nt "expr", tm "STAR", nt "expr"])                          -- 6  (STAR,3)
    , ("expr",  [tm "INT"])                                                 -- 7  (INT,1)
    , ("expr",  [tm "LPAREN", nt "expr", tm "RPAREN"])                      -- 8  ((),3)
    , ("expr",  [nt "ident"]) ]                                             -- 9  (δ,1)

/-- The symbol of the `i`-th production of the running example. -/
def sym! (g : CFG) (i : Nat) : Sym :=
  match g.rankedProds[i]? with
  | some sp => sp.1
  | none    => epsSym

/-! ### Test harness -/

structure Report where
  passed : Nat := 0
  failed : Nat := 0
deriving Inhabited

def Report.record (r : Report) (ok : Bool) : Report :=
  if ok then { r with passed := r.passed + 1 } else { r with failed := r.failed + 1 }

def check (r : Report) (name : String) (ok : Bool) (detail : String := "") : IO Report := do
  if ok then
    IO.println s!"  ok   {name}"
  else
    IO.println s!"  FAIL {name}{if detail.isEmpty then "" else "  — " ++ detail}"
  return r.record ok

/-! ### A pseudo-random source -/

/-- A 32-bit linear congruential generator; deterministic, so failures reproduce. -/
def nextRand (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def randRange (s n : Nat) : Nat × Nat :=
  let s' := nextRand s
  (s' % (max n 1), s')

/-- A small random grammar over three nonterminals and three terminals. -/
def randomCFG (seed : Nat) : CFG × Nat :=
  let nts := ["A", "B", "C"]
  let tms := ["x", "y", "z"]
  let rec build (n : Nat) (s : Nat) (acc : List Production) : List Production × Nat :=
    match n with
    | 0 => (acc, s)
    | k + 1 =>
        let (li, s) := randRange s 3
        let (len, s) := randRange s 3
        let rec elts (m : Nat) (s : Nat) (acc : List SigmaElt) : List SigmaElt × Nat :=
          match m with
          | 0 => (acc, s)
          | j + 1 =>
              let (kind, s) := randRange s 2
              let (idx, s) := randRange s 3
              let e := if kind == 0 then SigmaElt.nt (nts[idx]!) else SigmaElt.term (tms[idx]!)
              elts j s (acc ++ [e])
        let (rhs, s) := elts (len + 1) s []
        build k s (acc ++ [(nts[li]!, rhs)])
  let (prods, s) := build 6 seed []
  ({ nonterms := nts, terms := tms, starts := ["A"], prods := prods }, s)

/-! ### The tests -/

def expectedBaseOrder : List (Nat × List Int) :=
  [ (0, [0, 1, 2])          -- (SEMI,2), (IF,4), (IF,6)  — productions of stmt
  , (1, [3, 5, 6, 7, 8, 9]) ]  -- (TINT,4) and the productions of expr

def orderIds (m : OrderMap) : List (Nat × List Int) :=
  m.normalise.map fun p => (p.1, (p.2.map Sym.id).mergeSort (· ≤ ·))

def testRunningExample (r : Report) : IO Report := do
  let g := runningExample
  let a := g.toTA
  let mut r := r
  r ← check r "A_g has the nonterminals as states" (a.states == g.nonterms)
  r ← check r "A_g accepts at the start nonterminal" (a.finals == ["stmt"])
  r ← check r "A_g has one transition per production"
        (a.trans.length == g.prods.length)
  r ← check r "the base precedence order matches the set printed in Section 2.3.1"
        (orderIds (g.baseOrder) == expectedBaseOrder)
        s!"got {orderIds (g.baseOrder)}"
  r ← check r "IDENT is the only trivial symbol"
        ((g.trivialSyms.map Sym.id) == [4])
        s!"got {g.trivialSyms.map Sym.id}"
  -- The translation theorem on concrete trees.
  let identTree := Tree.node (sym! g 4) [.leaf "IDENT"]
  let declTree := Tree.node (sym! g 3)
    [.leaf "TINT", identTree, .leaf "EQ", Tree.node (sym! g 7) [.leaf "INT"]]
  let stmtTree := Tree.node (sym! g 0) [declTree, .leaf "SEMI"]
  r ← check r "a complete parse tree is accepted" (a.langB stmtTree)
  r ← check r "the translation theorem agrees on that tree"
        (a.langB stmtTree == g.isParseTree stmtTree)
  r ← check r "an incomplete tree is rejected" (!(a.langB declTree))
  let bogus := Tree.node (sym! g 0) [declTree, .leaf "ELSE"]
  r ← check r "a tree with the wrong terminal is rejected" (!(a.langB bogus))
  return r

/-- Every combination of the three optimisations must preserve the language. -/
def allOpts : List (String × IntersectOpts) :=
  [ ("I^def", {})
  , ("I^1",   { reachability := false })
  , ("I^2",   { dedupStates := false })
  , ("I^3",   { introEps := false })
  , ("I^123", IntersectOpts.none) ]

def testIntersectionAgainstProduct (r : Report) (label : String)
    (a b : TA String) (depth : Nat) : IO Report := do
  let spec := Serialize.renamePairTA (prodTA a b)
  let mut r := r
  for (name, opts) in allOpts do
    let res := Serialize.renamePairTA (intersectTA a b opts)
    let ts := intersectionCorpus a b res 8 depth
    let d := compareOn spec res ts
    r ← check r s!"{label}: {name} agrees with the verified product"
          (d.onlyLeft.isEmpty && d.onlyRight.isEmpty)
          s!"{d.onlyLeft.length} missing, {d.onlyRight.length} extra, {d.checked} checked"
  return r

/-- The tree examples of Figure 3 that the user did *not* select. -/
def runningExampleNeg : List TreeExample :=
  let g := runningExample
  [ { top := sym! g 5, bot := sym! g 5, idx := 2 }    -- (PLUS,3) as a right child
  , { top := sym! g 6, bot := sym! g 6, idx := 2 }    -- (STAR,3) as a right child
  , { top := sym! g 6, bot := sym! g 5, idx := 0 }    -- (STAR,3) above (PLUS,3)
  , { top := sym! g 2, bot := sym! g 1, idx := 3 } ]  -- (IF,6) above (IF,4)

/-- `O_p` as printed in Section 2.3.2, by production identifier. -/
def expectedOp : List (Nat × List Int) :=
  [ (0, [0, 1])              -- (SEMI,2), (IF,4)
  , (1, [0, 2])              -- (SEMI,2), (IF,6)
  , (2, [3, 5, 7, 8, 9])     -- (TINT,4), (PLUS,3), (INT,1), ((),3), (δ,1)
  , (3, [3, 6, 7, 8, 9])     -- (TINT,4), (STAR,3), (INT,1), ((),3), (δ,1)
  , (4, [3, 7, 8, 9]) ]      -- (TINT,4), (INT,1), ((),3), (δ,1)

/-- One transition, rendered compactly so that it can be read against Figure 7. -/
def shapeOf (tr : Transition String) : String :=
  tr.target ++ " <" ++ toString tr.sym.id ++
    String.join (tr.rhs.map fun
      | .term a  => " " ++ a
      | .state q => " [" ++ q ++ "]")

/--
`A_r` as printed in Figure 7.  The `(TINT,4)` row at `e2` is printed there as
`TINT e2 EQ e2`; footnote 3 of Section 3.1.3 says the δ-generator leaves the states of
trivial symbols alone, which is what the rows at `e3` and `e4` do, so we expect
`TINT ident EQ e2`.  See docs/divergences.md.
-/
def expectedAr : List String :=
  [ "e0 <1 IF [e0] THEN [e0]"
  , "e0 <0 [e0] SEMI"
  , "e0 <-1 [e1]"
  , "e1 <2 IF [e1] THEN [e1] ELSE [e1]"
  , "e1 <0 [e1] SEMI"
  , "e1 <-1 [e2]"
  , "e2 <5 [e2] PLUS [e3]"
  , "e2 <3 TINT [ident] EQ [e2]"
  , "e2 <7 INT"
  , "e2 <8 LPAREN [e2] RPAREN"
  , "e2 <9 [ident]"
  , "e2 <-1 [e3]"
  , "e3 <6 [e3] STAR [e4]"
  , "e3 <3 TINT [ident] EQ [e3]"
  , "e3 <7 INT"
  , "e3 <8 LPAREN [e3] RPAREN"
  , "e3 <9 [ident]"
  , "e3 <-1 [e4]"
  , "e4 <3 TINT [ident] EQ [e4]"
  , "e4 <7 INT"
  , "e4 <8 LPAREN [e4] RPAREN"
  , "e4 <9 [ident]"
  , "ident <4 IDENT" ]

def testRunningExampleIntersection (r : Report) : IO Report := do
  let g := runningExample
  let neg := runningExampleNeg
  let obp := g.baseOrder
  let mto := toMapOf obp neg
  let (oa, op) := learnOaOp g neg mto
  let ar := genTA g oa op
  let arShape := (ar.trans.map shapeOf).mergeSort (· ≤ ·)
  let mut r := r
  r ← check r "the learned O_a records the two associativity conflicts"
        ((oa.map fun p => (p.1.id, p.2)) == [(5, 2), (6, 2)])
        s!"got {oa.map fun p => (p.1.id, p.2)}"
  r ← check r "the learned O_p matches the set printed in Section 2.3.2"
        (orderIds op == expectedOp)
        s!"got {orderIds op}"
  r ← check r "A_r matches Figure 7 transition for transition"
        (arShape == expectedAr.mergeSort (· ≤ ·))
        s!"{ar.trans.length} transitions, expected {expectedAr.length}"
  r ← check r "A_r accepts at e0" (ar.finals == ["e0"])
  testIntersectionAgainstProduct r "running example" ar g.toTA 4

/-- `S -> S + S | S * S | ( S ) | x | y | z`, the grammar of Section 1. -/
def arith : CFG where
  nonterms := ["S"]
  terms    := ["PLUS", "STAR", "LPAREN", "RPAREN", "X", "Y", "Z"]
  starts   := ["S"]
  prods    :=
    [ ("S", [nt "S", tm "PLUS", nt "S"])        -- 0
    , ("S", [nt "S", tm "STAR", nt "S"])        -- 1
    , ("S", [tm "LPAREN", nt "S", tm "RPAREN"]) -- 2
    , ("S", [tm "X"])                           -- 3
    , ("S", [tm "Y"])                           -- 4
    , ("S", [tm "Z"]) ]                         -- 5

/--
A symbol whose only conflict is with itself still has to be re-layered, so that `GenTA`
has a level to send the forbidden child to.  Section 3 puts such a symbol in a singleton
member of `S_E`; leaving it out leaves it at the top order, `e_{i+1}` does not exist, and
every tree using the symbol is rejected.  See docs/proof-plan.md.
-/
def testAssocOnly (r : Report) : IO Report := do
  let g := arith
  let neg : List TreeExample := [{ top := sym! g 0, bot := sym! g 0, idx := 2 }]
  let obp := g.baseOrder
  let (oa, op) := learnOaOp g neg (toMapOf obp neg)
  let ar := genTA g oa op
  let x := Tree.node (sym! g 3) [.leaf "X"]
  let plus := fun a b => Tree.node (sym! g 0) [a, .leaf "PLUS", b]
  let mut r := r
  r ← check r "an associativity-only conflict still creates a level above the symbol"
        (1 ≤ op.maxOrder) s!"max order {op.maxOrder}"
  r ← check r "a single PLUS is accepted" (ar.langB (plus x x))
  r ← check r "the left-associative nesting is accepted" (ar.langB (plus (plus x x) x))
  r ← check r "the right-associative nesting is rejected" (!(ar.langB (plus x (plus x x))))
  testIntersectionAgainstProduct r "arith, associativity only" ar g.toTA 4

def testRandom (r : Report) (rounds : Nat) : IO Report := do
  let mut r := r
  let mut seed := 20260913
  for i in List.range rounds do
    let (g, s) := randomCFG seed
    seed := s
    let (g', s) := randomCFG seed
    seed := s
    r ← testIntersectionAgainstProduct r s!"random #{i}" g.toTA g'.toTA 3
  return r

def runAll : IO UInt32 := do
  IO.println "running example"
  let mut r : Report := {}
  r ← testRunningExample r
  IO.println "learning and intersection"
  r ← testRunningExampleIntersection r
  IO.println "associativity-only conflicts"
  r ← testAssocOnly r
  IO.println "randomised intersection"
  r ← testRandom r 6
  IO.println s!"\n{r.passed} passed, {r.failed} failed"
  return (if r.failed == 0 then 0 else 1)

end Test
end Greta
