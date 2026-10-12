/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Module.Polynomial
public import ReasLib.RingTheory.CohenMacaulay.Ring

/-!
# Cohen--Macaulay polynomial rings

This leaf upgrades the module-valued polynomial base-change API to the
ring-valued Cohen--Macaulay predicate.  The arbitrary finite index type is
the reusable owner; the `Fin n` theorem records the textbook presentation.
-/

@[expose] public section

universe u v

namespace CohenMacaulayRing

variable {R : Type u} [CommRing R]
variable {σ : Type v} [Finite σ]

/-- A finite-variable polynomial ring over a Cohen--Macaulay ring is
Cohen--Macaulay. -/
instance mvPolynomial [CohenMacaulayRing R] :
    CohenMacaulayRing (MvPolynomial σ R) := sorry

/-- Lemma 10.104.7 (Stacks tag `00ND`): the natural-number-indexed polynomial
presentation is the `Fin n` specialization of `mvPolynomial`. -/
@[stacks 00ND]
theorem mvPolynomial_fin [CohenMacaulayRing R] (n : ℕ) :
    CohenMacaulayRing (MvPolynomial (Fin n) R) := sorry

end CohenMacaulayRing
