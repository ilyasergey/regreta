/-
Command-line driver for the Lean formalisation: enough to run the algorithms on concrete
inputs and to compare them with the OCaml reference implementation.
-/
import Greta
import Greta.Enumerate

open Greta Greta.Serialize

def readCFG (path : String) : IO CFG := do
  match parseCFG (← IO.FS.readFile path) with
  | .ok g => pure g
  | .error e => throw (IO.userError s!"{path}: {e}")

def readTA (path : String) : IO (TA String) := do
  match parseTA (← IO.FS.readFile path) with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{path}: {e}")

def optsOf (args : List String) : IntersectOpts :=
  { reachability := !args.contains "--no-reach"
    dedupStates  := !args.contains "--no-dedup"
    introEps     := !args.contains "--no-eps" }

/-- Build the learned automaton `A_r` from a grammar and the unselected examples. -/
def learnedTA (g : CFG) (neg : List TreeExample) (excludeTrivial : Bool) : TA String :=
  let obp := g.baseOrder excludeTrivial
  let mto := toMapOf obp neg
  let (oa, op) := learnOaOp g neg mto excludeTrivial
  genTA g oa op excludeTrivial

def usage : String :=
"greta — Lean formalisation of Grammar Repair with Examples and Tree Automata

  greta cfg2ta GRAMMAR                  print A_g, the tree automaton of a CFG
  greta obp GRAMMAR [--keep-trivial]    print the base precedence order O_bp
  greta genta GRAMMAR EXAMPLES          print A_r, the automaton learned from examples
  greta intersect TA1 TA2 [FLAGS]       run Algorithm 3.3 (IntersectTA)
  greta product TA1 TA2                 run the verified textbook product
  greta repair GRAMMAR EXAMPLES [FLAGS] one round of repair, printed as a grammar
  greta checkinter TA1 TA2 RESULT [D]   check L(RESULT) = L(TA1) ∩ L(TA2) on a corpus
  greta accepts TA GRAMMAR [D]          list the corpus trees TA accepts
  greta selftest                        run the built-in test suite

FLAGS: --no-reach, --no-dedup, --no-eps disable the corresponding optimisation of
Algorithm 3.3; --keep-trivial disables the trivial-symbol optimisation of Section 3.1.1."

def runCheckInter (p1 p2 pr : String) (depth : Nat) : IO UInt32 := do
  let a ← readTA p1
  let b ← readTA p2
  let r ← readTA pr
  let spec := Serialize.renamePairTA (prodTA a b)
  let ts := intersectionCorpus a b r 24 depth
  let d := compareOn spec r ts
  IO.println s!"checked {d.checked} trees"
  if d.onlyLeft.isEmpty && d.onlyRight.isEmpty then
    IO.println "OK: the result agrees with the verified product on the whole corpus"
    return 0
  else
    for t in d.onlyLeft.take 5 do
      IO.println s!"MISSING (in A ∩ B, rejected by the result): {treeToString t}"
    for t in d.onlyRight.take 5 do
      IO.println s!"EXTRA (accepted by the result, not in A ∩ B): {treeToString t}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["cfg2ta", p] => do
      IO.println (taToString (← readCFG p).toTA); return 0
  | "obp" :: p :: rest => do
      let g ← readCFG p
      IO.println (orderMapToString (g.baseOrder (!rest.contains "--keep-trivial"))); return 0
  | "genta" :: pg :: pe :: rest => do
      let g ← readCFG pg
      match parseExamples g (← IO.FS.readFile pe) with
      | .error e => throw (IO.userError e)
      | .ok neg =>
          IO.println (taToString (learnedTA g neg (!rest.contains "--keep-trivial"))); return 0
  | "intersect" :: p1 :: p2 :: rest => do
      let a ← readTA p1
      let b ← readTA p2
      IO.println (taToString (Serialize.renamePairTA (intersectTA a b (optsOf rest)))); return 0
  | ["product", p1, p2] => do
      let a ← readTA p1
      let b ← readTA p2
      IO.println (taToString (Serialize.renamePairTA (prodTA a b))); return 0
  | "repair" :: pg :: pe :: rest => do
      let g ← readCFG pg
      match parseExamples g (← IO.FS.readFile pe) with
      | .error e => throw (IO.userError e)
      | .ok neg =>
          let keep := !rest.contains "--keep-trivial"
          let ar := learnedTA g neg keep
          let res := Serialize.renamePairTA (intersectTA ar g.toTA (optsOf rest))
          IO.println (cfgToString (taToCFG res)); return 0
  | "checkinter" :: p1 :: p2 :: pr :: rest =>
      runCheckInter p1 p2 pr ((rest.head?.bind String.toNat?).getD 4)
  | "accepts" :: pa :: pg :: rest => do
      let a ← readTA pa
      let g ← readCFG pg
      let d := (rest.head?.bind String.toNat?).getD 4
      let tbl := a.epsTable
      let ag := g.toTA
      for t in corpus ag 12 d do
        if a.accepts tbl t then IO.println (treeToString t)
      return 0
  | ["selftest"] => Greta.Test.runAll
  | _ => IO.println usage; return 0
