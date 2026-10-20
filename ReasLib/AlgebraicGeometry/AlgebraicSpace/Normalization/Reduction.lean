module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents.Reduction

/-!
# Normalization and reduction of algebraic spaces

The absolute normalization morphism factors through the reduction, and the
resulting morphism is the normalization of the reduction up to isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Normalization

/-- The absolute normalization morphism of an algebraic space with finitely many
irreducible components on compact opens factors through its reduction. -/
theorem factorsThroughReduction {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    ∃ νred : X.normalization ⟶ X.reduction,
      νred ≫ X.reductionι = X.normalizationTo :=
  sorry

/-- A factor of the absolute normalization morphism through the reduction
identifies the normalization with the normalization of the reduction. -/
theorem reductionFactorIsNormalization {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    {νred : X.normalization ⟶ X.reduction}
    (hνred : νred ≫ X.reductionι = X.normalizationTo) :
    ∃ e : X.normalization ≅ X.reduction.normalization,
      νred = e.hom ≫ X.reduction.normalizationTo :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Normalization
