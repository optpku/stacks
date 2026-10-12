/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
