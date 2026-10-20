module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Flat

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Flat

/-- Flatness of scheme morphisms is étale local on the source and target. -/
instance isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.Flat : MorphismProperty AlgebraicGeometry.Scheme.{u}) := sorry

end AlgebraicGeometry.Flat
