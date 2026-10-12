/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Unramified
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.23.30 (1): unramifiedness of scheme morphisms is local on the target
for the fpqc precoverage. -/
@[stacks 02VM] #check
  (AlgebraicGeometry.Unramified.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Unramified :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)

/- Lemma 35.23.30 (2): G-unramifiedness of scheme morphisms is local on the target
for the fpqc precoverage. -/
@[stacks 02VM] #check
  (AlgebraicGeometry.GUnramified.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.GUnramified :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
