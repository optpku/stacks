module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Locality

@[expose] public section

universe u

#check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFiniteIsLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      ((@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.LocallyQuasiFinite) :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage)
