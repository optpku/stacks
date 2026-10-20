/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PlaneCurve.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus

/-!
# Rational plane curves

The family of homogeneous plane forms `X 1 ^ (n + 1) - X 0 ^ n * X 2` has
standard affine equation `X 0 ^ (n + 1) - X 1` and gives a genus-zero
normalization.
-/

@[expose] public section

open AlgebraicGeometry MvPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.PlaneCurve

/-- The homogeneous plane form `X 1 ^ (n + 1) - X 0 ^ n * X 2`. -/
def rationalForm (k : Type u) [CommRing k] (n : ℕ) :
    MvPolynomial (Fin 3) k :=
  X 1 ^ (n + 1) - X 0 ^ n * X 2

/-- The defining formula for `rationalForm`. -/
theorem rationalForm_eq (k : Type u) [CommRing k] (n : ℕ) :
    rationalForm k n = X 1 ^ (n + 1) - X 0 ^ n * X 2 := rfl

/-- The rational plane form is homogeneous of degree `n + 1`. -/
theorem rationalForm_mem_grading (k : Type u) [CommRing k] (n : ℕ) :
    rationalForm k n ∈ ProjectiveSpace.grading k 2 (n + 1) := sorry

/-- The rational plane form is nonzero over every nontrivial commutative ring. -/
theorem rationalForm_ne_zero (k : Type u) [CommRing k] [Nontrivial k] (n : ℕ) :
    rationalForm k n ≠ 0 := sorry

/-- The rational plane form is irreducible over a field. -/
theorem irreducible_rationalForm (k : Type u) [Field k] (n : ℕ) :
    Irreducible (rationalForm k n) := sorry

/-- Irreducibility of the rational plane form as a typeclass fact. -/
instance instFact_irreducible_rationalForm (k : Type u) [Field k] (n : ℕ) :
    Fact (Irreducible (rationalForm k n)) :=
  ⟨irreducible_rationalForm k n⟩

/-- The normalization of the plane hypersurface cut out by `rationalForm`. -/
abbrev rationalAbstractCurve (k : Type u) [Field k] (n : ℕ) : SchemeOverField k :=
  abstractCurve (n + 1) (rationalForm k n) (rationalForm_mem_grading k n)

/-- The normalization of the rational plane hypersurface is projective. -/
instance instProjective_rationalAbstractCurve (k : Type u) [Field k] (n : ℕ) :
    Projective (rationalAbstractCurve k n).hom := sorry

/-- The normalization of the rational plane hypersurface is smooth. -/
instance instSmooth_rationalAbstractCurve (k : Type u) [Field k] (n : ℕ) :
    Smooth (rationalAbstractCurve k n).hom := sorry

/-- The normalization of the rational plane hypersurface is geometrically irreducible. -/
instance instGeometricallyIrreducible_rationalAbstractCurve
    (k : Type u) [Field k] (n : ℕ) :
    GeometricallyIrreducible (rationalAbstractCurve k n).hom := sorry

/-- The actual total degree of the rational plane form is `n + 1`. -/
theorem rationalForm_totalDegree (k : Type u) [CommRing k] [Nontrivial k] (n : ℕ) :
    (rationalForm k n).totalDegree = n + 1 := sorry

/-- The standard affine equation of the rational plane form. -/
theorem affineEquation_rationalForm (k : Type u) [Field k] (n : ℕ) :
    affineEquation (rationalForm k n) = MvPolynomial.X 0 ^ (n + 1) - MvPolynomial.X 1 := sorry

/-- The standard affine equation of the rational plane form is irreducible. -/
theorem irreducible_affineEquation_rationalForm (k : Type u) [Field k] (n : ℕ) :
    Irreducible (affineEquation (rationalForm k n)) := sorry

/-- Irreducibility of the standard affine equation as a typeclass fact. -/
instance instFact_irreducible_affineEquation_rationalForm
    (k : Type u) [Field k] (n : ℕ) :
    Fact (Irreducible (affineEquation (rationalForm k n))) :=
  ⟨irreducible_affineEquation_rationalForm k n⟩

/-- The normalized rational plane curve has genus zero over an algebraically closed field. -/
theorem genus_rationalAbstractCurve (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) :
    Curve.genus (rationalAbstractCurve k n) = 0 := sorry

end AlgebraicGeometry.ProjectiveSpace.PlaneCurve
