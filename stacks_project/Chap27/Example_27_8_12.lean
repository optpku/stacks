/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.MvPolynomial
import StacksCheckRecall

@[expose] public section

#check
  (MvPolynomial.standardGrading ℕ ℂ :
    ℕ → Submodule ℂ (MvPolynomial ℕ ℂ))

#check
  (AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.standardGrading ℕ ℂ) :
    AlgebraicGeometry.Proj (MvPolynomial.standardGrading ℕ ℂ) ⟶
      AlgebraicGeometry.Spec (.of (MvPolynomial.standardGrading ℕ ℂ 0)))

#check
  (MvPolynomial.standardGrading.degreeZeroRingEquiv ℕ ℂ :
    MvPolynomial.standardGrading ℕ ℂ 0 ≃+* ℂ)

#check
  (AlgebraicGeometry.MvPolynomialProj.degreeZeroSpecIso ℕ ℂ :
    AlgebraicGeometry.Spec (.of (MvPolynomial.standardGrading ℕ ℂ 0)) ≅
      AlgebraicGeometry.Spec (.of ℂ))

#check
  (AlgebraicGeometry.MvPolynomialProj.toSpec ℕ ℂ :
    AlgebraicGeometry.Proj (MvPolynomial.standardGrading ℕ ℂ) ⟶
      AlgebraicGeometry.Spec (.of ℂ))

/- Example 27.8.12
Let `ℂ[X₁, X₂, X₃, …]` carry the grading in which every variable has degree one. Map it
to `ℂ[t^α ; α ∈ ℚ≥0]` by `Xᵢ ↦ t^(1/i)`. Localizing the target at the ideal
`𝔪 = (t^α ; α > 0)` gives a valuation ring `A`; let `K` be its fraction field. The induced map
`Spec(K) ⟶ Proj(ℂ[X₁, X₂, X₃, …])` does not extend over `Spec(A)`: an extension would have
image in some `D₊(Xᵢ)`, but there `Xᵢ₊₁ / Xᵢ` would map to
`t^(1/(i+1) - 1/i)`, which is not in `A`.
-/
@[stacks 01MG] #check
  (AlgebraicGeometry.MvPolynomialProj.countableComplex_toSpec_not_valuativeCriterionExistence :
    ¬ AlgebraicGeometry.ValuativeCriterion.Existence
      (AlgebraicGeometry.MvPolynomialProj.toSpec ℕ ℂ))
