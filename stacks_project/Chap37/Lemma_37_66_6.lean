/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.BaseChange
import StacksCheckRecall

universe u

/- Lemma 37.66.6: The property of being ind-quasi-affine is stable under base change. -/
@[stacks 0AP7] #check
  (AlgebraicGeometry.IndQuasiAffineHom.stableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.IndQuasiAffineHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}))
