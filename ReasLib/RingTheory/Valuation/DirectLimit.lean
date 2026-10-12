/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Domain
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed colimits of valuation rings

This leaf owns the pre-valuation-ring and valuation-ring structures on a
directed ring colimit.  The pre-valuation-ring construction does not need
directed-system coherence; the valuation-ring structure combines it with the
neutral domain API.

@stack 0AS4
-/

@[expose] public section

universe u v

namespace Ring.DirectLimit

section PreValuationRing

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (A : I → Type u) [∀ i, CommRing (A i)] [∀ i, PreValuationRing (A i)]
variable (φ : ∀ i j, i ≤ j → A i →+* A j)

/-- A directed colimit of pre-valuation rings is a pre-valuation ring. -/
@[stacks 0AS4 "direct-limit pre-valuation component"]
instance preValuationRing :
    PreValuationRing (Ring.DirectLimit A (fun i j h ↦ φ i j h)) := sorry

end PreValuationRing

section ValuationRing

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (A : I → Type u) [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)]
variable [∀ i, PreValuationRing (A i)]
variable (φ : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (φ · · ·)]

/-- Lemma 10.50.6 (Tag 0AS4): a directed colimit of integral pre-valuation rings is a
valuation ring.  In particular, this applies to a directed colimit of valuation rings. -/
@[stacks 0AS4]
instance valuationRing :
    ValuationRing (Ring.DirectLimit A (fun i j h ↦ φ i j h)) := sorry

end ValuationRing

end Ring.DirectLimit
