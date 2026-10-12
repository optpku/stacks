/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The standard grading of a multivariable polynomial ring

The total-degree grading of a multivariable polynomial ring has degree-zero piece canonically
equivalent to the coefficient ring.
-/

@[expose] public section

noncomputable section

universe u v

namespace MvPolynomial

/-- The standard total-degree grading of a multivariable polynomial ring. -/
def standardGrading (σ : Type u) (R : Type v) [CommRing R] :
    ℕ → Submodule R (MvPolynomial σ R) :=
  homogeneousSubmodule σ R

namespace standardGrading

/-- The standard total-degree grading carries the canonical graded-algebra structure. -/
instance instGradedAlgebra (σ : Type u) (R : Type v) [CommRing R] :
    GradedAlgebra (standardGrading σ R) := by
  change GradedAlgebra (homogeneousSubmodule σ R)
  exact MvPolynomial.gradedAlgebra

/-- The canonical constant-polynomial embedding into the degree-zero graded piece. -/
noncomputable def degreeZeroC (σ : Type u) (R : Type v) [CommRing R] (r : R) :
    standardGrading σ R 0 :=
  ⟨MvPolynomial.C r, by
    change IsHomogeneous (MvPolynomial.C r : MvPolynomial σ R) 0
    exact @MvPolynomial.isHomogeneous_C σ R _ r⟩

/-- Constant coefficient and the degree-zero constant embedding are inverse on the degree-zero
graded piece. -/
theorem degreeZero_leftInverse (σ : Type u) (R : Type v) [CommRing R] :
    Function.LeftInverse (degreeZeroC σ R)
      (fun p : standardGrading σ R 0 ↦ MvPolynomial.constantCoeff p.1) := sorry

/-- The degree-zero piece of the standard grading is canonically equivalent to the coefficient
ring. -/
noncomputable def degreeZeroRingEquiv (σ : Type u) (R : Type v) [CommRing R] :
    standardGrading σ R 0 ≃+* R where
  toFun p := MvPolynomial.constantCoeff p.1
  invFun := degreeZeroC σ R
  left_inv := degreeZero_leftInverse σ R
  right_inv := fun r ↦ MvPolynomial.constantCoeff_C σ r
  map_mul' p q :=
    map_mul (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R) p.1 q.1
  map_add' p q :=
    map_add (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R) p.1 q.1

end standardGrading
end MvPolynomial
