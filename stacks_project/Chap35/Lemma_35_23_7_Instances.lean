module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Surjective

@[expose] public section

universe u

open CategoryTheory

#check (AlgebraicGeometry.Surjective.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Surjective : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
