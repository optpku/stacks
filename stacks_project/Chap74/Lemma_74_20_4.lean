module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmoothLocal.Locality
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Lemma 74.20.4: if a morphism property `P` of algebraic spaces over a scheme `S`
is smooth local on the source, smooth local on the target, and stable under
postcomposition with smooth morphisms, then `P` is smooth local on the
source-and-target. -/
@[stacks 06FB] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget.of_isLocalAtSource_isLocalAtTarget :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [P.IsLocalAtSource (precoverage (@Smooth S))]
      [P.IsLocalAtTarget (precoverage (@Smooth S))]
      [P.RespectsRight (@Smooth S : MorphismProperty (AlgebraicSpace S))],
      IsSmoothLocalAtSourceAndTarget P)
