module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Reduction

/-!
# Normalization and scheme reduction

The normalization morphism factors through the reduction, and the resulting
map is the normalization morphism of the reduction up to canonical isomorphism.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Normalization

/-- The normalization morphism of a scheme factors through its reduction. -/
theorem factorsThroughReduction (X : Scheme.{u})
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    ∃ νred : X.normalization ⟶ X.reduction,
      νred ≫ X.reductionι = X.normalizationTo := sorry

/-- A factor of the normalization morphism through the reduction identifies the
normalization with the normalization of the reduction. -/
theorem reductionFactorIsNormalization (X : Scheme.{u})
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    {νred : X.normalization ⟶ X.reduction}
    (hνred : νred ≫ X.reductionι = X.normalizationTo) :
    ∃ e : X.normalization ≅ X.reduction.normalization,
      νred = e.hom ≫ X.reduction.normalizationTo := sorry

end AlgebraicGeometry.Scheme.Normalization
