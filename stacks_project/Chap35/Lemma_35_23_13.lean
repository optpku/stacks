/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFinitePresentation
import StacksCheckRecall

universe u

/- Lemma 35.23.13: the property `P(f)` given by “`f` is locally of finite
presentation” is fpqc local on the base. -/
@[stacks 02KY] #check (AlgebraicGeometry.LocallyOfFinitePresentation.isLocalAtTargetFpqc :
  CategoryTheory.MorphismProperty.IsLocalAtTarget
    (@AlgebraicGeometry.LocallyOfFinitePresentation :
      CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
    AlgebraicGeometry.Scheme.fpqcPrecoverage)
