/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.LocalCompleteIntersection
import StacksCheckRecall

universe u

/- Lemma 37.62.20: the property that a scheme morphism is a local complete intersection
morphism is local on the source for the syntomic precoverage. -/
@[stacks 069P] #check
  (AlgebraicGeometry.LocallyOfType.isLocalCompleteIntersection_isLocalAtSourceSyntomic :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      ((fun _ _ f ↦ AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f) :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage)
