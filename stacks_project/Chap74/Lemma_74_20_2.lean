/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_20_2_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Lemma 74.20.2 (1): a property of morphisms of algebraic spaces over a scheme
`S` that is smooth local on source-and-target is smooth local on the source. -/
@[stacks 06F9] #check
  (IsSmoothLocalAtSourceAndTarget.toIsLocalAtSource :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [IsSmoothLocalAtSourceAndTarget P],
      P.IsLocalAtSource (smoothPrecoverage S))

/- Lemma 74.20.2 (2): a property of morphisms of algebraic spaces over a scheme
`S` that is smooth local on source-and-target is smooth local on the target. -/
@[stacks 06F9] #check
  (IsSmoothLocalAtSourceAndTarget.toIsLocalAtTarget :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [IsSmoothLocalAtSourceAndTarget P],
      P.IsLocalAtTarget (smoothPrecoverage S))

/- Lemma 74.20.2 (3): a property of morphisms of algebraic spaces over a scheme
`S` that is smooth local on source-and-target is stable under postcomposition
with smooth morphisms. -/
@[stacks 06F9] #check
  (IsSmoothLocalAtSourceAndTarget.toRespectsRightSmooth :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [IsSmoothLocalAtSourceAndTarget P],
      P.RespectsRight (@Smooth S : MorphismProperty (AlgebraicSpace S)))
