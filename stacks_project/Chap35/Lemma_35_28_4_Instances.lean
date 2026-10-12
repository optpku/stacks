/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyOpen.Locality

@[expose] public section

universe u

#check
  (AlgebraicGeometry.UniversallyOpen.isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.UniversallyOpen :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
