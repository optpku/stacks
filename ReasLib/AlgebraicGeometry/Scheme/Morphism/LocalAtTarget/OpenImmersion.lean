module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.AffineDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsOpenImmersion

/-- Open immersions of schemes are local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsOpenImmersion
