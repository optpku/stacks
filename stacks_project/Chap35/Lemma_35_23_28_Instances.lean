module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Syntomic

@[expose] public section

universe u

open CategoryTheory

/- Syntomicity of scheme morphisms is local on the target for the fpqc
precoverage. -/
#check
  (AlgebraicGeometry.Syntomic.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Syntomic : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
