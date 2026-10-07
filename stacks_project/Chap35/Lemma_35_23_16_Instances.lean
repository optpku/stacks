module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Proper

@[expose] public section

universe u

open CategoryTheory

#check (AlgebraicGeometry.IsProper.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsProper : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
