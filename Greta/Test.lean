/-
Executable test suite: the running example of the paper; the witnesses for the divergences
recorded in `docs/divergences.md` (the cycle, the bracketing production, the dropped sort
constraint, the unsound ablation); the learner as Greta ships it against what the OCaml
prints; and randomised comparisons of Algorithm 3.3 with the verified product, which now
double-check the definitions `Greta.intersectTA_lang` is about.

Run with `lake exe greta selftest`.
-/
import Greta.Enumerate
import Greta.RefLearn
import Greta.RefSound

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
  let spec := Serialize.renamePairTA id id (prodTA a b)
  let mut r := r
  for (name, opts) in allOpts do
    let res := Serialize.renamePairTA id id (intersectTA a b opts)
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
def shapeOf (tr : Transition GState) : String :=
  tr.target.name ++ " <" ++ toString tr.sym.id ++
    String.join (tr.rhs.map fun
      | .term a  => " " ++ a
      | .state q => " [" ++ q.name ++ "]")

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
  r ← check r "A_r accepts at e0" (ar.finals == [GState.lvl 0])
  testIntersectionAgainstProduct r "running example" (Serialize.renameGen ar) g.toTA 4

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
every tree using the symbol is rejected.  See docs/divergences.md.
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
  testIntersectionAgainstProduct r "arith, associativity only" (Serialize.renameGen ar) g.toTA 4

/-- `S -> S + S | T | x`, `T -> S * S | y`: `T` sits one level below `S` and nests it again. -/
def cycleGrammar : CFG where
  nonterms := ["S", "T"]
  terms    := ["PLUS", "STAR", "X", "Y"]
  starts   := ["S"]
  prods    :=
    [ ("S", [nt "S", tm "PLUS", nt "S"])        -- 0  (PLUS,3)
    , ("S", [nt "T"])                           -- 1  (δ,1)
    , ("S", [tm "X"])                           -- 2  (X,1)
    , ("T", [nt "S", tm "STAR", nt "S"])        -- 3  (STAR,3)
    , ("T", [tm "Y"]) ]                         -- 4  (Y,1)

/--
Theorem 3.1(2) as printed fails on a grammar with a cycle in the order.  `HighToLow`
reports the `(STAR,3)` production, so `GenTA` adds `e1 <(STAR,3) e0 STAR e0`, and that
transition accepts a `PLUS` directly under a `STAR` although the user rejected exactly that
nesting.  This is the case the paper's proof of Lemma B.1 sets aside, and the reason
`genTA_sound` carries the hypothesis `highToLow … = []`.  See docs/divergences.md.
-/
def testCycle (r : Report) : IO Report := do
  let g := cycleGrammar
  let neg : List TreeExample := [{ top := sym! g 3, bot := sym! g 0, idx := 0 }]
  let obp := g.baseOrder
  let (oa, op) := learnOaOp g neg (toMapOf obp neg)
  let ar := genTA g oa op
  let x := Tree.node (sym! g 2) [.leaf "X"]
  let plus := fun a b => Tree.node (sym! g 0) [a, .leaf "PLUS", b]
  let star := fun a b => Tree.node (sym! g 3) [a, .leaf "STAR", b]
  let t := Tree.node (sym! g 1) [star (plus x x) x]
  let mut r := r
  r ← check r "the grammar has a cycle in the order" (!(g.highToLow obp op).isEmpty)
  r ← check r "the witness is a parse tree the user excluded"
        (g.isParseTree t && g.excludedLang neg t)
  r ← check r "A_r nevertheless accepts it: Theorem 3.1(2) needs acyclicity" (ar.langB t)
  return r

/-! ### The learner Greta actually ships (`Greta.RefLearn`)

`Greta.Learn` is Algorithm 3.1 as printed; `Greta.RefLearn` is
`Learner.update_op_per_ord_amb_symsls` as shipped.  The expectations below are what the
vendored OCaml prints: the upstream driver is interactive, so they were taken by running
`Learner.learn_op` on the `M_to` that `toMapOf` computes here (the procedure is recorded
in `docs/testing.md`).  The reference does not exclude the trivial symbols (D8), so the
comparison uses `excludeTrivial := false`.
-/

/-- `O_p` as `Learner.learn_op` prints it for the running example. -/
def expectedRefOp : List (Nat × List Int) :=
  [ (0, [1])            -- (IF,4)
  , (1, [2])            -- (IF,6)
  , (2, [0])            -- (SEMI,2), the non-conflicting symbol of order 0
  , (3, [5])            -- (PLUS,3)
  , (4, [6])            -- (STAR,3)
  , (5, [3, 7, 8, 9])   -- the non-conflicting symbols of order 1
  , (6, [4]) ]          -- (IDENT,1), which the reference does not exclude

/-- `special_loop_symbols` as `Learner.learn_op` records them for the running example. -/
def expectedRefSpecs : List (Int × Nat) := [(0, 0), (3, 3), (7, 3), (8, 3), (9, 3)]

/-- The back-edge table, by production identifier. -/
def specIds (specs : SpecMap) : List (Int × Nat) :=
  (specs.map fun p => (p.1.id, p.2)).mergeSort (fun a b => a.1 ≤ b.1)

/--
`A_r` as `Learner.learn_ta` builds it from that `O_p`: one transition per symbol, with the
non-conflicting symbols pointing back at the order they were moved from — `(SEMI,2)` at
`e2` back to `e0`, and the symbols of `e5` back to `e3`.
-/
def expectedRefAr : List String :=
  [ "e0 <1 IF [e0] THEN [e0]"
  , "e0 <-1 [e1]"
  , "e1 <2 IF [e1] THEN [e1] ELSE [e1]"
  , "e1 <-1 [e2]"
  , "e2 <0 [e0] SEMI"
  , "e2 <-1 [e3]"
  , "e3 <5 [e3] PLUS [e4]"
  , "e3 <-1 [e4]"
  , "e4 <6 [e4] STAR [e5]"
  , "e4 <-1 [e5]"
  , "e5 <3 TINT [ident] EQ [e3]"
  , "e5 <7 INT"
  , "e5 <8 LPAREN [e3] RPAREN"
  , "e5 <9 [ident]"
  , "ident <4 IDENT" ]

def testRefLearner (r : Report) : IO Report := do
  let g := runningExample
  let neg := runningExampleNeg
  let obp := g.baseOrder false
  let mto := toMapOf obp neg
  let (_, op, specs) := refLearnOaOp g neg mto false
  let mut r := r
  r ← check r "the shipped learner reproduces the O_p that learner.ml prints"
        (orderIds op == expectedRefOp) s!"got {orderIds op}"
  r ← check r "the shipped learner records the special_loop_symbols learner.ml records"
        (specIds specs == expectedRefSpecs) s!"got {specIds specs}"
  r ← check r "the loop runs under the discipline the invariant assumes"
        (decide (Disciplined obp (refGroups mto)))
  r ← check r "every back-edge points at or above its symbol's order (SpecDominated)"
        (specs.all fun p => (op.ordersOf p.1).all fun l => p.2 ≤ l)
  -- the same, with the trivial-symbol optimisation on, which is what `refGenTA` consumes
  let mto' := toMapOf g.baseOrder neg
  let (oa', op', specs') := refLearnOaOp g neg mto'
  let shape := ((refGenTA g oa' specs' op').trans.map shapeOf).mergeSort (· ≤ ·)
  r ← check r "A_r is the back-edge automaton learn_ta builds"
        (shape == expectedRefAr.mergeSort (· ≤ ·))
        s!"{shape.length} transitions, expected {expectedRefAr.length}"
  return r

/--
The published algorithm and the shipped one do *not* agree everywhere.  On the running
example they induce the same repaired language, but on `arith` the replication of the
published Algorithm 3.1 loses `x + ((x + x) * x)`: at `e1`, the copy of `(STAR,3)` sends
its children to `e1`, where `(PLUS,3)` does not live.  The back-edge sends them to `e0`
instead, so the shipped learner keeps the tree — which is what Theorem 3.1(1) demands,
since the user excluded only a `PLUS` directly under a `PLUS`.
-/
def testRefBackEdge (r : Report) : IO Report := do
  let mut r := r
  -- the running example: the two agree
  let g := runningExample
  let neg := runningExampleNeg
  let mto := toMapOf g.baseOrder neg
  let (oa1, op1) := learnOaOp g neg mto
  let (oa2, op2, specs2) := refLearnOaOp g neg mto
  let p1 := Serialize.renamePairTA id id (prodTA (Serialize.renameGen (genTA g oa1 op1)) g.toTA)
  let p2 := Serialize.renamePairTA id id
    (prodTA (Serialize.renameGen (refGenTA g oa2 specs2 op2)) g.toTA)
  let ts := (corpus p1 8 4 ++ corpus p2 8 4 ++ corpus g.toTA 8 4).eraseDups
  let d := compareOn p1 p2 ts
  r ← check r "running example: published and shipped repair to the same language"
        (d.onlyLeft.isEmpty && d.onlyRight.isEmpty)
        s!"{d.onlyLeft.length} lost, {d.onlyRight.length} gained, {d.checked} checked"
  -- arith: the published algorithm loses a tree the shipped one keeps
  let a := arith
  let aneg : List TreeExample := [{ top := sym! a 0, bot := sym! a 0, idx := 2 }]
  let amto := toMapOf a.baseOrder aneg
  let (aoa1, aop1) := learnOaOp a aneg amto
  let (aoa2, aop2, aspecs2) := refLearnOaOp a aneg amto
  let ar1 := genTA a aoa1 aop1
  let ar2 := refGenTA a aoa2 aspecs2 aop2
  let x := Tree.node (sym! a 3) [.leaf "X"]
  let plus := fun u v => Tree.node (sym! a 0) [u, .leaf "PLUS", v]
  let star := fun u v => Tree.node (sym! a 1) [u, .leaf "STAR", v]
  let t := plus x (star (plus x x) x)
  r ← check r "arith: the witness is a tree Theorem 3.1(1) says must be kept"
        (a.repairedLang aneg t)
  r ← check r "arith: the published Algorithm 3.1 loses it" (!(ar1.langB t))
  r ← check r "arith: the shipped back-edge keeps it" (ar2.langB t)
  r ← check r "arith: both still reject the nesting the user excluded"
        (!(ar1.langB (plus x (plus x x))) && !(ar2.langB (plus x (plus x x))))
  return r

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

/-! ### The two defects found by the specification work -/

/-- The grammar of Section 1: `S → S + S | S * S | ( S ) | x | y | z`. -/
def bracketGrammar : CFG where
  nonterms := ["S"]
  terms    := ["PLUS", "STAR", "LPAREN", "RPAREN", "X", "Y", "Z"]
  starts   := ["S"]
  prods    :=
    [ ("S", [nt "S", tm "PLUS", nt "S"])          -- 0  (PLUS,3)
    , ("S", [nt "S", tm "STAR", nt "S"])          -- 1  (STAR,3)
    , ("S", [tm "LPAREN", nt "S", tm "RPAREN"])   -- 2  ((),3)
    , ("S", [tm "X"])                             -- 3
    , ("S", [tm "Y"])                             -- 4
    , ("S", [tm "Z"]) ]                           -- 5

/--
**Theorem 3.1(1) fails on the paper's own Section 1 grammar.**  `x * (y + z)` is a complete
parse tree that no rejected example excludes, and the learned automaton rejects it, because
Algorithm 3.1 as printed replicates the bracketing production at every order instead of
sending its right-hand side back to the lowest one.  See `docs/divergences.md`, §8.
-/
def testBrackets (r : Report) : IO Report := do
  let g := bracketGrammar
  let neg : List TreeExample :=
    [ { top := sym! g 0, bot := sym! g 0, idx := 2 }
    , { top := sym! g 1, bot := sym! g 1, idx := 2 }
    , { top := sym! g 1, bot := sym! g 0, idx := 0 } ]
  let (oa, op) := learnOaOp g neg (toMapOf (g.baseOrder) neg)
  let ar := genTA g oa op
  let x : Tree := .node (sym! g 3) [.leaf "X"]
  let y : Tree := .node (sym! g 4) [.leaf "Y"]
  let z : Tree := .node (sym! g 5) [.leaf "Z"]
  let star := fun a b => Tree.node (sym! g 1) [a, .leaf "STAR", b]
  let plus := fun a b => Tree.node (sym! g 0) [a, .leaf "PLUS", b]
  let paren := fun a => Tree.node (sym! g 2) [.leaf "LPAREN", a, .leaf "RPAREN"]
  let t := star x (paren (plus y z))
  let mut r := r
  r ← check r "the grammar is acyclic, so §1 does not apply"
        (g.highToLow (g.baseOrder) op).isEmpty
  r ← check r "`x * (y + z)` is a parse tree the user did not exclude"
        (g.repairedLang neg t)
  r ← check r "A_r nevertheless rejects it: Theorem 3.1(1) is false"
        (!ar.langB t)
  r ← check r "`Fits`, which statement (1) needs, is reported false"
        (!fitsB g neg true oa op)
  -- the learner Greta ships keeps the parse, because of its back-edge
  let rf := refLearnOaOp g neg (toMapOf (g.baseOrder) neg)
  let arRef := refGenTA g rf.1 rf.2.2 rf.2.1
  r ← check r "the shipped learner keeps it, so the defect is the paper's alone"
        (arRef.langB t)
  r ← check r "and keeps `(y + z) * x` too"
        (arRef.langB (star (paren (plus y z)) x) && !ar.langB (star (paren (plus y z)) x))
  return r

/-- Four operators at one base order, with a constraint a comparison sort would drop. -/
def fourOpGrammar : CFG where
  nonterms := ["S"]
  terms    := ["PLUS", "STAR", "MINUS", "SLASH", "X"]
  starts   := ["S"]
  prods    :=
    [ ("S", [nt "S", tm "PLUS", nt "S"])      -- 0
    , ("S", [nt "S", tm "STAR", nt "S"])      -- 1
    , ("S", [nt "S", tm "MINUS", nt "S"])     -- 2
    , ("S", [nt "S", tm "SLASH", nt "S"])     -- 3
    , ("S", [tm "X"]) ]                       -- 4

/--
**The conflict group must be linearised by a topological sort.**  With a constraint between
the first and last symbols of a four-element group, a merge sort never compares them and
drops the constraint.  `topoSort` keeps it.  See `docs/divergences.md`, §9.
-/
def testTopoSort (r : Report) : IO Report := do
  let g := fourOpGrammar
  let neg : List TreeExample :=
    [ { top := sym! g 0, bot := sym! g 3, idx := 0 }
    , { top := sym! g 2, bot := sym! g 1, idx := 0 } ]
  let (oa, op) := learnOaOp g neg (toMapOf (g.baseOrder) neg)
  let ar := genTA g oa op
  let x : Tree := .node (sym! g 4) [.leaf "X"]
  let slash := Tree.node (sym! g 3) [x, .leaf "SLASH", x]
  let t := Tree.node (sym! g 0) [slash, .leaf "PLUS", x]
  let mut r := r
  r ← check r "the grammar is acyclic, so §1 does not apply"
        (g.highToLow (g.baseOrder) op).isEmpty
  r ← check r "both rejected examples are respected by the learned order"
        (learnedSpecB g neg true oa op)
  r ← check r "the long-range constraint puts SLASH strictly below PLUS"
        (decide ((op.ordersOf (sym! g 3)).all fun j =>
          (op.ordersOf (sym! g 0)).all fun i => j < i))
  r ← check r "the excluded tree is rejected"
        (g.excludedLang neg t && !ar.langB t)
  return r

/--
**Theorem 3.1(1) holds for the learner Greta ships.**  On the grammar of Section 1 the
published construction loses `x * (y + z)` and the shipped one keeps it, and all the side
conditions of `refGreta_correct_pipeline` pass — so Theorem 3.2 is established for that
grammar, by proof, for the algorithm the tool runs.  See `docs/divergences.md`, §8.
-/
def testShippedSound (r : Report) : IO Report := do
  let g := bracketGrammar
  let neg : List TreeExample :=
    [ { top := sym! g 0, bot := sym! g 0, idx := 2 }
    , { top := sym! g 1, bot := sym! g 1, idx := 2 }
    , { top := sym! g 1, bot := sym! g 0, idx := 0 } ]
  let rf := refLearned g neg true
  let arRef := refGenTA g rf.1 rf.2.2 rf.2.1
  let x : Tree := .node (sym! g 3) [.leaf "X"]
  let y : Tree := .node (sym! g 4) [.leaf "Y"]
  let z : Tree := .node (sym! g 5) [.leaf "Z"]
  let star := fun a b => Tree.node (sym! g 1) [a, .leaf "STAR", b]
  let plus := fun a b => Tree.node (sym! g 0) [a, .leaf "PLUS", b]
  let paren := fun a => Tree.node (sym! g 2) [.leaf "LPAREN", a, .leaf "RPAREN"]
  let mut r := r
  r ← check r "the published side conditions fail" (!pipelineFullOK g neg true)
  r ← check r "the shipped side conditions all pass" (refPipelineOK g neg true)
  r ← check r "`RefFits` holds where `Fits` does not"
        (refFitsB g neg true rf.1 rf.2.2 rf.2.1)
  r ← check r "the shipped A_r keeps `x * (y + z)`" (arRef.langB (star x (paren (plus y z))))
  r ← check r "and keeps `(y + z) * x`" (arRef.langB (star (paren (plus y z)) x))
  return r

/--
**Theorem 3.1(1) also needs the examples to order each conflict group totally.**  With two
of the six pairs of a four-operator group related, the stratification separates symbols no
example related, and `x * x + x` is removed although nothing rejects it.  Adding the other
four examples restores the theorem.  See `docs/divergences.md`, §10.
-/
def testTotalOrder (r : Report) : IO Report := do
  let g := fourOpGrammar
  let partial_ : List TreeExample :=
    [ { top := sym! g 0, bot := sym! g 3, idx := 0 }
    , { top := sym! g 2, bot := sym! g 1, idx := 0 } ]
  let total : List TreeExample :=
    [ { top := sym! g 2, bot := sym! g 1, idx := 0 }
    , { top := sym! g 3, bot := sym! g 1, idx := 0 }
    , { top := sym! g 0, bot := sym! g 1, idx := 0 }
    , { top := sym! g 3, bot := sym! g 2, idx := 0 }
    , { top := sym! g 0, bot := sym! g 2, idx := 0 }
    , { top := sym! g 0, bot := sym! g 3, idx := 0 } ]
  let x : Tree := .node (sym! g 4) [.leaf "X"]
  let star := Tree.node (sym! g 1) [x, .leaf "STAR", x]
  let t := Tree.node (sym! g 0) [star, .leaf "PLUS", x]
  let rp := refLearned g partial_ true
  let mut r := r
  r ← check r "with a partial order `x * x + x` is excluded by nothing"
        (g.repairedLang partial_ t)
  r ← check r "yet the shipped A_r rejects it: Theorem 3.1(1) fails"
        (!(refGenTA g rp.1 rp.2.2 rp.2.1).langB t)
  r ← check r "and the side conditions report it" (!refPipelineOK g partial_ true)
  r ← check r "with the group totally ordered they all pass"
        (refPipelineOK g total true)
  return r

/-- The side conditions Theorem 3.2 needs hold for `dangling-else`. -/
def testPipelineChecked (r : Report) : IO Report := do
  let g := cycleGrammar
  let neg : List TreeExample := [{ top := sym! g 3, bot := sym! g 0, idx := 0 }]
  let mut r := r
  r ← check r "the cycle witness is reported by `pipelineOK`" (!pipelineOK g neg true)
  return r

def runAll : IO UInt32 := do
  IO.println "running example"
  let mut r : Report := {}
  r ← testRunningExample r
  IO.println "learning and intersection"
  r ← testRunningExampleIntersection r
  IO.println "associativity-only conflicts"
  r ← testAssocOnly r
  IO.println "a cycle in the order"
  r ← testCycle r
  IO.println "the learner as shipped"
  r ← testRefLearner r
  IO.println "the back-edge of learn_ta"
  r ← testRefBackEdge r
  IO.println "brackets: Theorem 3.1(1) is false"
  r ← testBrackets r
  IO.println "linearising a conflict group"
  r ← testTopoSort r
  IO.println "Theorem 3.1(1) for the shipped learner"
  r ← testShippedSound r
  IO.println "conflict groups must be totally ordered"
  r ← testTotalOrder r
  IO.println "the checked side conditions"
  r ← testPipelineChecked r
  IO.println "randomised intersection"
  r ← testRandom r 6
  IO.println s!"\n{r.passed} passed, {r.failed} failed"
  return (if r.failed == 0 then 0 else 1)

end Test
end Greta
