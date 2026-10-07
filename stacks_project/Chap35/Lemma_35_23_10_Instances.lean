module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallyInjective

@[expose] public section

universe u

#check (AlgebraicGeometry.UniversallyInjective.isLocalAtTargetFpqc :
  CategoryTheory.MorphismProperty.IsLocalAtTarget
    (@AlgebraicGeometry.UniversallyInjective :
      CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
    AlgebraicGeometry.Scheme.fpqcPrecoverage)
