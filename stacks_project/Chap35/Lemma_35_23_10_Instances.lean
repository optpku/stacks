/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallyInjective

@[expose] public section

universe u

#check (AlgebraicGeometry.UniversallyInjective.isLocalAtTargetFpqc :
  CategoryTheory.MorphismProperty.IsLocalAtTarget
    (@AlgebraicGeometry.UniversallyInjective :
      CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
    AlgebraicGeometry.Scheme.fpqcPrecoverage)
