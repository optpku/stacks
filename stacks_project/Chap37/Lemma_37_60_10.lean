/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.PseudoCoherent
import StacksCheckRecall

universe u

/- Lemma 37.60.10: pseudo-coherence of scheme morphisms is local on the target for the
fpqc precoverage. -/
@[stacks 0696] #check
  (AlgebraicGeometry.PseudoCoherent.isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.PseudoCoherent :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
