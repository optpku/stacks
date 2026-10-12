/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

noncomputable section

universe u

namespace MvPolynomial

/-- The polynomial `X 0 ^ 3 + X 0 ^ 2 * X 1 ^ 2 + X 1 ^ 100` in `k[X 0, X 1]`. -/
def originCurveF (k : Type u) [CommRing k] : MvPolynomial (Fin 2) k :=
  X 0 ^ 3 + X 0 ^ 2 * X 1 ^ 2 + X 1 ^ 100

/-- The polynomial `X 1 ^ 3 - X 0 ^ 999` in `k[X 0, X 1]`. -/
def originCurveG (k : Type u) [CommRing k] : MvPolynomial (Fin 2) k :=
  X 1 ^ 3 - X 0 ^ 999

/-- The ideal of polynomials vanishing at the origin is maximal over a field. -/
instance instIsMaximalIdealOfVars (k : Type u) [Field k] :
    (idealOfVars (Fin 2) k).IsMaximal :=
  sorry

/-- The localization of `k[X 0, X 1]` at the ideal of the origin. -/
abbrev originLocalRing (k : Type u) [Field k] :=
  Localization.AtPrime (idealOfVars (Fin 2) k)

/-- The localized intersection of the two explicit plane curves has module length `9`. -/
theorem originCurves_length (k : Type u) [Field k] :
    Module.length (originLocalRing k)
        (originLocalRing k ⧸ Ideal.span
          {algebraMap (MvPolynomial (Fin 2) k) (originLocalRing k) (originCurveF k),
            algebraMap (MvPolynomial (Fin 2) k) (originLocalRing k) (originCurveG k)}) =
      (9 : ℕ∞) :=
  sorry

end MvPolynomial
