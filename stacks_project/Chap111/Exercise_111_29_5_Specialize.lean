/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Polynomial.FrobeniusSpecialization

/-! Compatibility bridge for the Frobenius-graph specialization API. -/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

/- The reusable definitions and their computation rules are owned by
`ReasLib.RingTheory.Polynomial.FrobeniusSpecialization`. -/
#check (Polynomial.evalXPowRingHom :
  ∀ {R S : Type} [CommSemiring R] [CommSemiring S],
    (R →+* S) → ℕ → R[X][Y] →+* S[X])
#check (Polynomial.intEvalXPowMod :
  ∀ (p : ℕ), ℤ[X][Y] → (ZMod p)[X])
