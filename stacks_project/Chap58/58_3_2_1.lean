module

public import ReasLib.CategoryTheory.Action.Finite.Forget
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped FintypeCatDiscrete

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- 58.3.2.1: the forgetful functor from finite discrete continuous `G`-sets to `Sets`. -/
@[stacks 0BMT] #check
  (CategoryTheory.DiscreteContAction.forgetFinite G : DiscreteContAction FintypeCat.{u} G ⥤ Type u)
