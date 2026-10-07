module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallyClosed

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsIntegralHom

/-- Integral morphisms of schemes are local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsIntegralHom : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsIntegralHom
