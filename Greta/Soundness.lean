/-
Theorem 3.1 (Soundness of GenTA) as two statements, Theorem 3.2 (Correctness of Greta)
derived from them, and the repair pipeline of Figure 4.

* `GenTASound₁` and `GenTASound₂` are the two halves of Theorem 3.1.  `Greta.GenTASpec`
  proves them for the automaton `genTA` returns, under the side conditions listed in
  `docs/divergences.md`.
* `greta_correct` derives Theorem 3.2 from them, from `Greta.CFG.toTA_correct` (Theorem
  A.10) and from `Greta.prodTA_lang`, exactly as the paper does ("Follows from Theorem 3.1
  and set intersection").
* `shift_mono` is the arithmetic fact underlying Lemma B.2: re-layering the precedence
  order never inverts the relative order of two symbols.  The lemma itself is proved in
  `Greta.LearnSpec`.
* `repairOnce` is one round of Figure 4 as Greta runs it, with Algorithm 3.3 as the
  intersection; `repairOnceSpec` is the same round with the verified product.
  `repairOnce_lang` identifies their languages, using `Greta.intersectTA_lang`, so
  Theorem 3.2 carries over to the round as run (`repairOnce_correct`).
-/
import Greta.GenTA
import Greta.Intersect
import Greta.IntersectSpec

namespace Greta

/-! ### Lemma B.2: re-layering preserves relative order -/

/-- The order map `pushN` applies to a single order. -/
def shift (o n x : Nat) : Nat := if o ≤ x then x + n else x

/-- Shifting a suffix of the orders upwards is monotone: it can never swap two symbols. -/
theorem shift_mono (o n : Nat) {x y : Nat} (h : x ≤ y) : shift o n x ≤ shift o n y := by
  unfold shift
  split <;> split <;> omega

/-- Shifting never moves an order below the threshold it was already above. -/
theorem le_shift (o n x : Nat) : x ≤ shift o n x := by
  unfold shift; split <;> omega

theorem pushN_eq_shift (m : OrderMap) (o n : Nat) :
    m.pushN o n = m.map fun p => (shift o n p.1, p.2) := by
  simp only [OrderMap.pushN, shift]
  congr 1
  funext p
  split <;> simp_all

/-! ### Theorem 3.1, as statements -/

/--
Theorem 3.1 (Soundness of GenTA), statement (1): the learned automaton keeps every parse
tree of the input grammar that the user did not exclude, `L_r ⊇ L_g \ L⁻`.
-/
def GenTASound₁ {σ : Type} [DecidableEq σ] (g : CFG) (neg : List TreeExample) (Ar : TA σ) :
    Prop :=
  ∀ t : Tree, g.repairedLang neg t = true → Ar.Lang t

/--
Theorem 3.1 (Soundness of GenTA), statement (2): the learned automaton rejects every
excluded tree, `L_r ∩ L⁻ = ∅`.
-/
def GenTASound₂ {σ : Type} [DecidableEq σ] (g : CFG) (neg : List TreeExample) (Ar : TA σ) :
    Prop :=
  ∀ t : Tree, Ar.Lang t → g.excludedLang neg t = false

/-! ### Theorem 3.2 -/

/--
**Theorem 3.2 (Correctness of Greta).**  Intersecting the automaton `A_r` learned from
the user's choices with the automaton `A_g` derived from the input grammar yields a tree
automaton recognising exactly `L_g \ L⁻`.

The proof is the paper's: the intersection recognises `L_r ∩ L_g` (`prodTA_lang`), `L_g`
is exactly the parse trees of `g` (`CFG.toTA_correct`), and the two halves of Theorem 3.1
pin down `L_r` on that set.
-/
theorem greta_correct {σ : Type} [DecidableEq σ]
    (g : CFG) (neg : List TreeExample) (Ar : TA σ)
    (h₁ : GenTASound₁ g neg Ar) (h₂ : GenTASound₂ g neg Ar) (t : Tree) :
    (prodTA Ar g.toTA).Lang t ↔ g.repairedLang neg t = true := by
  rw [prodTA_lang, CFG.toTA_correct]
  constructor
  · rintro ⟨hr, hg⟩
    simp only [CFG.repairedLang, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hg, h₂ t hr⟩
  · intro h
    exact ⟨h₁ t h, g.repairedLang_subset neg t h⟩

/--
The same statement in the "no tree is lost, no excluded tree survives" form used in the
paper's abstract: the repaired automaton accepts a tree iff the grammar did and the user
did not rule it out.
-/
theorem greta_no_loss {σ : Type} [DecidableEq σ]
    (g : CFG) (neg : List TreeExample) (Ar : TA σ)
    (h₁ : GenTASound₁ g neg Ar) (h₂ : GenTASound₂ g neg Ar) (t : Tree)
    (hg : g.isParseTree t = true) (hn : g.excludedLang neg t = false) :
    (prodTA Ar g.toTA).Lang t := by
  rw [greta_correct g neg Ar h₁ h₂ t]
  simp [CFG.repairedLang, hg, hn]

theorem greta_excludes {σ : Type} [DecidableEq σ]
    (g : CFG) (neg : List TreeExample) (Ar : TA σ)
    (h₁ : GenTASound₁ g neg Ar) (h₂ : GenTASound₂ g neg Ar) (t : Tree)
    (hn : g.excludedLang neg t = true) : ¬ (prodTA Ar g.toTA).Lang t := by
  rw [greta_correct g neg Ar h₁ h₂ t]
  simp [CFG.repairedLang, hn]

/-! ### The end-to-end pipeline -/

/--
One round of grammar repair (Figure 4): learn the restrictions from the unselected
examples, generate `A_r`, intersect it with `A_g`, and read the result back as a grammar.
-/
def repairOnce (g : CFG) (neg : List TreeExample)
    (opts : IntersectOpts := {}) (excludeTrivial : Bool := true) : TA (GState × String) :=
  let obp := g.baseOrder excludeTrivial
  let mto := toMapOf obp neg
  let (oa, op) := learnOaOp g neg mto excludeTrivial
  let ar := genTA g oa op excludeTrivial
  intersectTA ar g.toTA opts

/-- The same round, using the verified textbook product instead of Algorithm 3.3. -/
def repairOnceSpec (g : CFG) (neg : List TreeExample)
    (excludeTrivial : Bool := true) : TA (GState × String) :=
  let obp := g.baseOrder excludeTrivial
  let mto := toMapOf obp neg
  let (oa, op) := learnOaOp g neg mto excludeTrivial
  let ar := genTA g oa op excludeTrivial
  prodTA ar g.toTA

/--
For the verified pipeline, Theorem 3.2 applies directly: under the two halves of Theorem
3.1 for the automaton `GenTA` produces, one round of repair recognises `L_g \ L⁻`.
-/
theorem repairOnceSpec_correct (g : CFG) (neg : List TreeExample) (excludeTrivial : Bool)
    (h₁ : GenTASound₁ g neg
      (genTA g (learnOaOp g neg (toMapOf (g.baseOrder excludeTrivial) neg) excludeTrivial).1
        (learnOaOp g neg (toMapOf (g.baseOrder excludeTrivial) neg) excludeTrivial).2
        excludeTrivial))
    (h₂ : GenTASound₂ g neg
      (genTA g (learnOaOp g neg (toMapOf (g.baseOrder excludeTrivial) neg) excludeTrivial).1
        (learnOaOp g neg (toMapOf (g.baseOrder excludeTrivial) neg) excludeTrivial).2
        excludeTrivial))
    (t : Tree) :
    (repairOnceSpec g neg excludeTrivial).Lang t ↔ g.repairedLang neg t = true :=
  greta_correct g neg _ h₁ h₂ t

/--
**The pipeline Greta runs recognises the same language as the verified one.**  Algorithm
3.3 agrees with the product construction (`Greta.intersectTA_lang_prodTA`), so `repairOnce`
may be substituted for `repairOnceSpec` in `repairOnceSpec_correct`.

The two side conditions of `Greta.intersectTA_lang` specialise to one hypothesis on the
input grammar: `genTA` has the single accepting state `e₀`, so the accepting pairs are
duplicate-free as soon as the start nonterminals are listed once each, and the second
condition is discharged by `reachability := true`, which is the default.
-/
theorem repairOnce_lang (g : CFG) (neg : List TreeExample) (opts : IntersectOpts)
    (excludeTrivial : Bool) (hstarts : g.starts.Nodup) (hreach : opts.reachability = true)
    (t : Tree) :
    (repairOnce g neg opts excludeTrivial).Lang t ↔
      (repairOnceSpec g neg excludeTrivial).Lang t := by
  simp only [repairOnce, repairOnceSpec]
  refine intersectTA_lang_prodTA _ g.toTA opts ?_
    (dedupKeepsFinals_of_reachability _ _ _ hreach) t
  intro _
  rw [genTA_finals]
  exact pairs_nodup (by simp) hstarts

/-- One round of repair, as Greta runs it, is correct under the hypotheses of Theorem 3.1
and one round of `repairOnceSpec_correct`. -/
theorem repairOnce_correct (g : CFG) (neg : List TreeExample) (opts : IntersectOpts)
    (excludeTrivial : Bool)
    (h₁ : GenTASound₁ g neg
      (genTA g (learnOaOp g neg (toMapOf (g.baseOrder excludeTrivial) neg) excludeTrivial).1
        (learnOaOp g neg (toMapOf (g.baseOrder excludeTrivial) neg) excludeTrivial).2
        excludeTrivial))
    (h₂ : GenTASound₂ g neg
      (genTA g (learnOaOp g neg (toMapOf (g.baseOrder excludeTrivial) neg) excludeTrivial).1
        (learnOaOp g neg (toMapOf (g.baseOrder excludeTrivial) neg) excludeTrivial).2
        excludeTrivial))
    (hstarts : g.starts.Nodup) (hreach : opts.reachability = true) (t : Tree) :
    (repairOnce g neg opts excludeTrivial).Lang t ↔ g.repairedLang neg t = true :=
  (repairOnce_lang g neg opts excludeTrivial hstarts hreach t).trans
    (repairOnceSpec_correct g neg excludeTrivial h₁ h₂ t)

end Greta
