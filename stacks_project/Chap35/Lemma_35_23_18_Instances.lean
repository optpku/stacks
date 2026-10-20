module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.OpenImmersion

@[expose] public section

universe u

#check (AlgebraicGeometry.IsOpenImmersion.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsOpenImmersion :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
