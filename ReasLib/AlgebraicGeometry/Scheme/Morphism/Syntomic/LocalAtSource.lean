module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Stability

@[expose] public section

universe u

namespace AlgebraicGeometry.Syntomic

/-- Syntomicity of scheme morphisms is local on the source for the syntomic precoverage. -/
instance isLocalAtSourceSyntomic :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Syntomic :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage := sorry

end AlgebraicGeometry.Syntomic
