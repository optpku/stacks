/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Perfect
import StacksCheckRecall

universe u

/- Lemma 37.61.10: perfectness of scheme morphisms is local on the target for the
fpqc precoverage. -/
@[stacks 069B] #check
  (AlgebraicGeometry.LocallyOfType.isPerfectRingMap_isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap)
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
