/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Polynomial.FrobeniusNorm

/-! Compatibility bridge for the adjoined-root norm API. -/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

/- The reusable definitions and theorem statements are owned by
`ReasLib.RingTheory.Polynomial.FrobeniusNorm`. -/
#check (Polynomial.adjoinRootPoly :
  ∀ {R : Type} [CommRing R], R[X] → R[X][Y])
#check (Polynomial.algebraNormSpecialize :
  ∀ (_ : ℤ[X]) (p : ℕ), ℤ[X][Y] → (ZMod p)[X])
