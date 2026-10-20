module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.Topology.Category.FinTopCat

@[expose] public section

open CategoryTheory
open scoped FintypeCatDiscrete

universe u

namespace CategoryTheory.DiscreteContAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The underlying-set functor on finite discrete continuous actions of a topological group. -/
def forgetFinite : DiscreteContAction FintypeCat.{u} G ⥤ Type u :=
  CategoryTheory.forget (DiscreteContAction FintypeCat.{u} G)

end CategoryTheory.DiscreteContAction
