module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.LocalAtSource

@[expose] public section

universe u

/- Syntomicity of scheme morphisms is local on the source for the syntomic precoverage. -/
#check
  (AlgebraicGeometry.Syntomic.isLocalAtSourceSyntomic :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Syntomic :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage)
