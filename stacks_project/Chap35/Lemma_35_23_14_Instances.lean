module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.FiniteType

@[expose] public section

universe u

#check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Scheme.Hom.FiniteType :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
