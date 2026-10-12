/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.AtWorstNodal
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 53.20.9: being at worst nodal of relative dimension one is local on the
target for the fpqc precoverage. -/
@[stacks 0C5E] #check
  (AlgebraicGeometry.AtWorstNodal.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.AtWorstNodal :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
