module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
import StacksCheckRecall

open CategoryTheory

universe u

namespace AlgebraicGeometry.AtWorstNodal

/- Lemma 53.20.7: If `f : X ⟶ S'` is at worst nodal of relative dimension one and
`e : S' ⟶ S` is étale, then `f ≫ e` is at worst nodal of relative dimension one. -/
@[stacks 0CD8]
#check (AlgebraicGeometry.AtWorstNodal.compEtale :
  ∀ {X S' S : Scheme.{u}} (f : X ⟶ S') (e : S' ⟶ S)
    [AlgebraicGeometry.AtWorstNodal f] [AlgebraicGeometry.Etale e],
    AlgebraicGeometry.AtWorstNodal (f ≫ e))

end AlgebraicGeometry.AtWorstNodal
