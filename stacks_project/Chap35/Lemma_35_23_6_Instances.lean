module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Separated

@[expose] public section

universe u

#check (AlgebraicGeometry.IsSeparated.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsSeparated :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
