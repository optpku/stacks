/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.BaseChange

universe u

#check
  (AlgebraicGeometry.IndQuasiAffineHom.stableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.IndQuasiAffineHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}))
