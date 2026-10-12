/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFinitePresentation

universe u

#check (AlgebraicGeometry.LocallyOfFinitePresentation.isLocalAtTargetFpqc :
  CategoryTheory.MorphismProperty.IsLocalAtTarget
    (@AlgebraicGeometry.LocallyOfFinitePresentation :
      CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
    AlgebraicGeometry.Scheme.fpqcPrecoverage)
