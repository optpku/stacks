module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFiniteType

@[expose] public section

universe u

#check (AlgebraicGeometry.LocallyOfFiniteType.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.LocallyOfFiniteType :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
