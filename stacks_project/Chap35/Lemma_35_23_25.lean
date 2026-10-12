/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Finite
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.23.25: finite morphisms of schemes are local on the target for the
fpqc precoverage. -/
@[stacks 02LA] #check
  (AlgebraicGeometry.IsFinite.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsFinite :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
