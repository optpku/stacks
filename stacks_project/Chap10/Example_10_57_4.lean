module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import StacksCheckRecall

/-!
# Proj of a standard graded polynomial ring

@stack 00JQ

This file retains the concrete standard grading on `R[X]`, its degree-zero identification, and the
resulting isomorphism `Proj(R[X]) ~= Spec(R)` from Example 10.57.4. The direct-sum and localization
calculations used to establish these statements are proof infrastructure rather than chapter API.
-/

@[expose] public section

open scoped DirectSum
open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace Polynomial

variable (R : Type u) [CommRing R]

/-- The standard grading on `R[X]`, transported from the additive monoid algebra model `R[N]`. -/
abbrev standardGrading (n : ℕ) : Submodule R R[X] :=
  Submodule.map (Polynomial.toFinsuppIsoLinear R).symm.toLinearMap (AddMonoidAlgebra.grade R n)

instance instSetLikeGradedMonoidStandardGrading : SetLike.GradedMonoid (standardGrading R) := sorry

/-- A homogeneous polynomial of degree `n` is its `n`-th coefficient times `X^n`. -/
theorem standardGrading_eq_C_mul_X_pow_of_mem {n : ℕ} {f : R[X]}
    (hf : f ∈ standardGrading R n) :
    f = Polynomial.C (f.coeff n) * Polynomial.X ^ n := sorry

/-- The standard grading is an internal direct-sum decomposition of the polynomial ring. -/
theorem standardGrading_isInternal : DirectSum.IsInternal (standardGrading R) := sorry

instance instGradedAlgebraStandardGrading : GradedAlgebra (standardGrading R) :=
  DirectSum.IsInternal.gradedAlgebra (standardGrading_isInternal R)

/-- The homogeneous decomposition of a polynomial has the expected monomial components. -/
theorem standardGrading_decompose_eq_C_coeff_mul_X_pow (f : R[X]) (n : ℕ) :
    ((DirectSum.decompose (standardGrading R) f) n : Polynomial R) =
      Polynomial.C (f.coeff n) * Polynomial.X ^ n := sorry

/-- The degree-zero part of the standard polynomial grading is canonically the coefficient ring. -/
noncomputable def standardGradingDegreeZeroRingEquiv : ↥(standardGrading R 0) ≃+* R := sorry

end Polynomial

section

variable (R : Type u) [CommRing R]

/-- The degree-zero ring equivalence induces the canonical spectrum isomorphism. -/
noncomputable def standardGradingDegreeZeroSpecIso :
    Spec (.of ↥(Polynomial.standardGrading R 0)) ≅ Spec (.of R) :=
  (Scheme.Spec.mapIso (Polynomial.standardGradingDegreeZeroRingEquiv R).toCommRingCatIso.op).symm

/-- Example 10.57.4, map form: the natural morphism from the projective spectrum of standard
graded `R[X]` to `Spec(R)`. -/
@[stacks 00JQ "standard-grading structure morphism"]
noncomputable def polynomial_standardGrading_toSpec :
    Proj (Polynomial.standardGrading R) ⟶ Spec (.of R) :=
  Proj.toSpecZero (Polynomial.standardGrading R) ≫ (standardGradingDegreeZeroSpecIso R).hom

/-- The standard-grading structure morphism is an isomorphism. -/
instance polynomial_standardGrading_toSpec_isIso :
    IsIso (polynomial_standardGrading_toSpec R) := sorry

/-- Example 10.57.4: `Proj(R[X])` with `deg(X) = 1` is canonically isomorphic to `Spec(R)`. -/
@[stacks 00JQ "standard polynomial Proj"]
noncomputable def polynomial_standardGrading_isoSpec :
    Proj (Polynomial.standardGrading R) ≅ Spec (.of R) :=
  asIso (polynomial_standardGrading_toSpec R)

/-- A relevant homogeneous prime of standard graded `R[X]` is extended from its contraction to
the coefficient ring. -/
@[stacks 00JQ "homogeneous prime extension formula"]
theorem polynomial_standardGrading_point_asIdeal_eq_map_comap_C
    (p : ProjectiveSpectrum (Polynomial.standardGrading R)) :
    p.asHomogeneousIdeal.toIdeal =
      Ideal.map Polynomial.C (Ideal.comap Polynomial.C p.asHomogeneousIdeal.toIdeal) := sorry

end


#check @Proj.toSpecZero
#check @ProjectiveSpectrum
#check @Polynomial.C
