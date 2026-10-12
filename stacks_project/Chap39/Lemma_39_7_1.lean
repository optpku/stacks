/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
