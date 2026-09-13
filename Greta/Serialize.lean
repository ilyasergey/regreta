/-
A small line-based text format for grammars, tree automata and trees, shared with the
OCaml reference driver in `ocaml-ref/` so that the two implementations can be compared
directly.  See `docs/testing.md`.
-/
import Greta.Soundness

namespace Greta
namespace Serialize

/-- Empty symbol names are written `-` so that every field is a non-empty token. -/
def encName (s : String) : String := if s.isEmpty then "-" else s

def decName (s : String) : String := if s == "-" then "" else s

def symToString (s : Sym) : String :=
  toString s.id ++ " " ++ encName s.name ++ " " ++ toString s.rank

def betaToString : Beta String → String
  | .term a  => "T:" ++ encName a
  | .state q => "S:" ++ encName q

def parseBeta (s : String) : Except String (Beta String) :=
  if s.startsWith "T:" then .ok (.term (decName (s.drop 2).toString))
  else if s.startsWith "S:" then .ok (.state (decName (s.drop 2).toString))
  else .error s!"bad rhs entry: {s}"

def transToString (tr : Transition String) : String :=
  "trans " ++ encName tr.target ++ " " ++ symToString tr.sym ++
    String.join (tr.rhs.map fun b => " " ++ betaToString b)

/-- Canonical rendering of an automaton: every component sorted, duplicates removed. -/
def taToString (A : TA String) : String :=
  let line (kw : String) (xs : List String) := kw ++ " " ++ String.intercalate " " xs
  String.intercalate "\n" (
    [ line "states" (A.states.dedup.mergeSort (· ≤ ·))
    , line "finals" (A.finals.dedup.mergeSort (· ≤ ·))
    , line "terminals" (A.terminals.dedup.mergeSort (· ≤ ·)) ] ++
    ((A.trans.map transToString).dedup.mergeSort (· ≤ ·)))

def cfgToString (g : CFG) : String :=
  let sigToString : SigmaElt → String
    | .term a => "T:" ++ encName a
    | .nt A   => "N:" ++ encName A
  String.intercalate "\n" (
    [ "nonterms " ++ String.intercalate " " g.nonterms
    , "terms " ++ String.intercalate " " g.terms
    , "starts " ++ String.intercalate " " g.starts ] ++
    g.prods.map fun p =>
      "prod " ++ p.1 ++ String.join (p.2.map fun x => " " ++ sigToString x))

/-! ### Parsing -/

private def tokens (l : String) : List String :=
  (l.splitOn " ").filter (fun s => !s.isEmpty)

private def lines (s : String) : List (List String) :=
  ((s.splitOn "\n").map fun l => tokens (l.replace "\t" " " |>.replace "\r" "")).filter
    fun ts => !ts.isEmpty && ts.head! != "#"

def parseSym : List String → Except String (Sym × List String)
  | i :: n :: r :: rest =>
      match i.toInt?, r.toNat? with
      | some i', some r' => .ok (⟨i', decName n, r'⟩, rest)
      | _, _ => .error s!"bad symbol: {i} {n} {r}"
  | ts => .error s!"bad symbol: {ts}"

def parseTA (src : String) : Except String (TA String) := do
  let mut states : List String := []
  let mut finals : List String := []
  let mut terms : List String := []
  let mut trans : List (Transition String) := []
  for ts in lines src do
    match ts with
    | "states" :: xs => states := xs.map decName
    | "finals" :: xs => finals := xs.map decName
    | "terminals" :: xs => terms := xs.map decName
    | "trans" :: tgt :: rest =>
        let (sym, rhsToks) ← parseSym rest
        let rhs ← rhsToks.mapM parseBeta
        trans := trans ++ [⟨decName tgt, sym, rhs⟩]
    | t :: _ => throw s!"unknown directive: {t}"
    | [] => pure ()
  return { states, alphabet := (trans.map Transition.sym).dedup, terminals := terms,
           finals, trans }

def parseCFG (src : String) : Except String CFG := do
  let mut nonterms : List String := []
  let mut terms : List String := []
  let mut starts : List String := []
  let mut prods : List Production := []
  for ts in lines src do
    match ts with
    | "nonterms" :: xs => nonterms := xs
    | "terms" :: xs => terms := xs
    | "starts" :: xs => starts := xs
    | "prod" :: lhs :: rhs =>
        let elts ← rhs.mapM fun t =>
          if t.startsWith "T:" then Except.ok (SigmaElt.term (decName (t.drop 2).toString))
          else if t.startsWith "N:" then Except.ok (SigmaElt.nt (decName (t.drop 2).toString))
          else Except.error s!"bad rhs entry: {t}"
        prods := prods ++ [(lhs, elts)]
    | t :: _ => throw s!"unknown directive: {t}"
    | [] => pure ()
  return { nonterms, terms, starts, prods }

/-! ### Trees -/

def treeToString : Tree → String
  | .leaf a => "#" ++ encName a
  | .node f ts =>
      "(" ++ symToString f ++ String.join (ts.map fun t => " " ++ treeToString t) ++ ")"
  termination_by t => sizeOf t
decreasing_by
  · have : sizeOf t < sizeOf ts := List.sizeOf_lt_of_mem (by assumption)
    simp only [Tree.node.sizeOf_spec]; omega

/-! ### Order maps and examples -/

def orderMapToString (m : OrderMap) : String :=
  String.intercalate "\n" ((m.normalise).map fun p =>
    "order " ++ toString p.1 ++ String.join
      ((p.2.map fun s => " " ++ toString s.id).mergeSort (· ≤ ·)))

def examplesToString (es : List TreeExample) : String :=
  String.intercalate "\n" (es.map fun e =>
    "example " ++ toString e.top.id ++ " " ++ toString e.bot.id ++ " " ++ toString e.idx)

/-- Tree examples are given as triples of production identifiers and a child index. -/
def parseExamples (g : CFG) (src : String) : Except String (List TreeExample) := do
  let symOfId (i : Int) : Except String Sym :=
    match (g.rankedProds.find? fun sp => sp.1.id == i) with
    | some sp => .ok sp.1
    | none => .error s!"no production with id {i}"
  let mut out : List TreeExample := []
  for ts in lines src do
    match ts with
    | ["example", a, b, i] =>
        match a.toInt?, b.toInt?, i.toNat? with
        | some a', some b', some i' =>
            out := out ++ [{ top := ← symOfId a', bot := ← symOfId b', idx := i' }]
        | _, _, _ => throw s!"bad example: {ts}"
    | t :: _ => throw s!"unknown directive: {t}"
    | [] => pure ()
  return out

/-- Product states are named `(q1,q2)` when the result is printed. -/
def renamePairTA (A : TA (String × String)) : TA String :=
  let nm := pairName id id
  { states    := A.states.map nm
    alphabet  := A.alphabet
    terminals := A.terminals
    finals    := A.finals.map nm
    trans     := A.trans.map fun tr =>
      ⟨nm tr.target, tr.sym, tr.rhs.map fun
        | .term a  => .term a
        | .state q => .state (nm q)⟩ }

end Serialize
end Greta
