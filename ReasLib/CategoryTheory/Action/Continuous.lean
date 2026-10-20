module

public import Mathlib.CategoryTheory.Action.Continuous

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- The identity functor is the canonical self-forgetful interface on `TopCat`. -/
instance hasForget₂Self : HasForget₂ TopCat TopCat where
  forget₂ := 𝟭 TopCat
  forget_comp := sorry

end TopCat

/-- An action with continuous action map and discrete underlying topology as a discrete
continuous action. -/
def DiscreteContAction.ofAction {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (action : Action TopCat G) (hcontinuous : action.IsContinuous)
    (hdiscrete : DiscreteTopology action.V) : DiscreteContAction TopCat G :=
  ⟨⟨action, hcontinuous⟩, hdiscrete⟩
