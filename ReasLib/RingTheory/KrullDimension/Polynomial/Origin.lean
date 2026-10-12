/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import ReasLib.RingTheory.MvPolynomial.Origin

@[expose] public section

universe u v

namespace MvPolynomial

variable {R : Type u} [CommRing R]

/-- In a finite-variable polynomial ring, the origin ideal has height equal to the coefficient
ideal's height plus the number of variables. -/
theorem height_spanMapCX (σ : Type v) [IsNoetherianRing R] [Finite σ] (m : Ideal R)
    [m.IsMaximal] : (spanMapCX σ m).height = m.height + Nat.card σ :=
  sorry

/-- The localization of a finite-variable polynomial ring at its origin ideal has Krull dimension
equal to the coefficient ring's dimension plus the number of variables. -/
theorem ringKrullDim_localizationAtPrime_spanMapCX
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (n : ℕ) :
    ringKrullDim (Localization.AtPrime (spanMapCX (Fin n) (IsLocalRing.maximalIdeal R))) =
      ringKrullDim R + n :=
  sorry

end MvPolynomial
