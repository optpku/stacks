/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

noncomputable section

open CategoryTheory

namespace Int.MulTwo

/-- The quotient of `ℤ` by the image of multiplication by `2`. -/
abbrev Cokernel := ℤ ⧸ LinearMap.range (LinearMap.mulLeft ℤ (2 : ℤ))

/-- The short complex formed by multiplication by `2` and its range quotient. -/
def shortComplex : ShortComplex (ModuleCat ℤ) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.mulLeft ℤ (2 : ℤ))
    (LinearMap.range (LinearMap.mulLeft ℤ (2 : ℤ))).mkQ
    (LinearMap.range_mkQ_comp (LinearMap.mulLeft ℤ (2 : ℤ)))

/-- Multiplication by `2` on `ℤ` gives a nonsplit short exact sequence. -/
theorem nonsplit : shortComplex.ShortExact ∧ ¬ Nonempty shortComplex.Splitting := sorry

end Int.MulTwo
