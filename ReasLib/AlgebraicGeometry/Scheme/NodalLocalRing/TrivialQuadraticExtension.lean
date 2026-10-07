module

public import ReasLib.RingTheory.LocalRing.Nodal.TrivialQuadraticExtension
public import ReasLib.AlgebraicGeometry.Scheme.NodalLocalRing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PointsOver

@[expose] public section

noncomputable section

open AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Hom.PointsOver
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- At a nodal point with separable residue field on a locally Noetherian scheme over a field,
the quadratic residue-field algebra splits if and only if the normalization fiber consists of
exactly two distinct points whose induced residue-field maps are bijective. -/
theorem trivialQuadraticExtension_iff_two_normalization_points
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsLocallyNoetherian X.left] (x : X.left)
    [IsNodalLocalRing (stalkRing X x)]
    [Algebra.IsSeparableOver k (ResidueField (stalkRing X x))] :
    Nonempty
        (NodalLocalRing.quadraticAlgebra (stalkRing X x) ≃ₐ[ResidueField (stalkRing X x)]
          (ResidueField (stalkRing X x) × ResidueField (stalkRing X x))) ↔
      ∃ x₁ x₂ : pointsOver X.left.normalizationTo x, x₁ ≠ x₂ ∧
        (∀ y : pointsOver X.left.normalizationTo x, y = x₁ ∨ y = x₂) ∧
        Function.Bijective
            (residueFieldMap X.left.normalizationTo x x₁).hom ∧
          Function.Bijective
            (residueFieldMap X.left.normalizationTo x x₂).hom := sorry

end AlgebraicGeometry.SchemeOverField
