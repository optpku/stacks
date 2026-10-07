module

public import stacks_project.Chap74.Lemma_74_21_4_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Lemma 74.21.4: if a morphism property `P` of algebraic spaces over a scheme `S`
is étale local on the source, smooth local on the target, and stable under
postcomposition with open immersions, then `P` is étale-smooth local on the
source-and-target. -/
@[stacks 0CG2] #check
  (IsEtaleSmoothLocalAtSourceAndTarget.of_isLocalAtSource_isLocalAtTarget :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [P.IsLocalAtSource etalePrecoverage]
      [P.IsLocalAtTarget (smoothPrecoverage S)]
      [P.RespectsRight (@IsOpenImmersion S : MorphismProperty (AlgebraicSpace S))],
      IsEtaleSmoothLocalAtSourceAndTarget P)
