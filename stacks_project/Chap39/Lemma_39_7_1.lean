module

public import ReasLib.AlgebraicGeometry.GroupScheme.Topology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

open MonoidalCategory MonObj

universe u

/- Lemma 39.7.1: The multiplication map of a group scheme over a field is open. -/
@[stacks 047K] #check
  (AlgebraicGeometry.GroupScheme.isOpenMap_mul :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G], IsOpenMap (μ[G].left))

end AlgebraicGeometry
