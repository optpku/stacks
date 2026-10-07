module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Affine

/-!
# Fpqc-locality of closed immersions

Closed immersions of schemes are local on the target for the fpqc precoverage.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsClosedImmersion

/-- Closed immersions of schemes are local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsClosedImmersion
