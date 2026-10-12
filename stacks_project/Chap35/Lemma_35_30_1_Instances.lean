/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.LocalAtSource

@[expose] public section

universe u

#check
  (AlgebraicGeometry.Smooth.isLocalAtSourceSmooth :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Smooth :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage)
