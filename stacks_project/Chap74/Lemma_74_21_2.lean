module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal.Locality
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Lemma 74.21.2 (1): a property of morphisms of algebraic spaces over a scheme
`S` that is étale-smooth local on source-and-target is étale local on the
source. -/
@[stacks 0CG0] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget.toIsLocalAtSource :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [IsEtaleSmoothLocalAtSourceAndTarget P],
      P.IsLocalAtSource (@etalePrecoverage S))

/- Lemma 74.21.2 (2): a property of morphisms of algebraic spaces over a scheme
`S` that is étale-smooth local on source-and-target is smooth local on the
target. -/
@[stacks 0CG0] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget.toIsLocalAtTarget :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [IsEtaleSmoothLocalAtSourceAndTarget P],
      P.IsLocalAtTarget (smoothPrecoverage S))

/- Lemma 74.21.2 (3): a property of morphisms of algebraic spaces over a scheme
`S` that is étale-smooth local on source-and-target is stable under
postcomposition with étale morphisms. -/
@[stacks 0CG0] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget.toRespectsRightEtale :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [IsEtaleSmoothLocalAtSourceAndTarget P],
      P.RespectsRight (@Etale S : MorphismProperty (AlgebraicSpace S)))

/- Lemma 74.21.2 (4): a property of morphisms of algebraic spaces over a scheme
`S` that is étale-smooth local on source-and-target descends along
postcomposition with étale morphisms. -/
@[stacks 0CG0] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget.toHasOfPostcompEtale :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [IsEtaleSmoothLocalAtSourceAndTarget P],
      P.HasOfPostcompProperty (@Etale S : MorphismProperty (AlgebraicSpace S)))
