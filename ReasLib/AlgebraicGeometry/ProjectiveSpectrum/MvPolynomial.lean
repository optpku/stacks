module

public import ReasLib.RingTheory.MvPolynomial.StandardGrading
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.Data.Complex.Basic

/-!
# Projective spectra of multivariable polynomial rings

The degree-zero piece of the standard grading gives the canonical structure morphism from the
projective spectrum of a multivariable polynomial ring to the spectrum of its coefficient ring.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace MvPolynomialProj

/-- The degree-zero affine base of the standard multivariable-polynomial projective spectrum is
canonically the spectrum of the coefficient ring. -/
noncomputable def degreeZeroSpecIso (σ : Type u) (R : Type u) [CommRing R] :
    Spec (.of (MvPolynomial.standardGrading σ R 0)) ≅ Spec (.of R) :=
  (Scheme.Spec.mapIso
    (MvPolynomial.standardGrading.degreeZeroRingEquiv σ R).toCommRingCatIso.op).symm

/-- The canonical structure morphism from the projective spectrum of a standard graded
multivariable polynomial ring to the spectrum of its coefficient ring. -/
noncomputable def toSpec (σ : Type u) (R : Type u) [CommRing R] :
    Proj (MvPolynomial.standardGrading σ R) ⟶ Spec (.of R) :=
  Proj.toSpecZero (MvPolynomial.standardGrading σ R) ≫ (degreeZeroSpecIso σ R).hom

/-- The canonical structure morphism for a countably generated complex polynomial ring does not
satisfy the existence part of the valuative criterion. -/
theorem countableComplex_toSpec_not_valuativeCriterionExistence :
    ¬ ValuativeCriterion.Existence (toSpec ℕ ℂ) := sorry

end MvPolynomialProj
end AlgebraicGeometry
