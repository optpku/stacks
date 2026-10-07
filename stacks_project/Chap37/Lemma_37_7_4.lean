module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.FormallyUnramified
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry

/- Lemma 37.7.4: if the closed part of a universal first-order thickening over `X`
is formally unramified over `X`, then its ambient scheme is formally unramified over `X`. -/
@[stacks 04F6] #check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.formallyUnramified :
    ∀ {X : Scheme.{u}} (T : Thickening.Over X)
      [Thickening.IsUniversalFirstOrder T]
      [AlgebraicGeometry.FormallyUnramified T.left.hom],
      AlgebraicGeometry.FormallyUnramified T.right.hom)

end AlgebraicGeometry
