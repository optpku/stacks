module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.ClosedImmersion

@[expose] public section

universe u

#check
  (AlgebraicGeometry.IsClosedImmersion.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsClosedImmersion :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
