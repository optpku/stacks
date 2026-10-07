module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 66.18.1: let `S` be a scheme and let `X` be an algebraic space over `S`.
The small étale site of `X` is the Grothendieck topology `SmallEtale.topology X` on the
category `SmallEtale.site X` of schemes étale over `X`, with coverings inherited from
the étale pretopology on schemes over `S`. -/
@[stacks 03ED] #check (AlgebraicGeometry.AlgebraicSpace.SmallEtale.topology :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.GrothendieckTopology
      (AlgebraicGeometry.AlgebraicSpace.SmallEtale.site X))
