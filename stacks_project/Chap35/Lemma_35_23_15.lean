/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.FinitePresentation
import StacksCheckRecall

universe u

/- Lemma 35.23.15: the property `P(f)` given by “`f` is of finite presentation”
is fpqc local on the base. -/
@[stacks 02L0] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Scheme.Hom.FinitePresentation :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
