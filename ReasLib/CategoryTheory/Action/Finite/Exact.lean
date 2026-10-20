module

public import ReasLib.CategoryTheory.Action.Finite.Forget
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section

open CategoryTheory
open scoped FintypeCatDiscrete

universe u

namespace CategoryTheory.DiscreteContAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An exact finite-valued functor on finite discrete continuous actions is naturally
isomorphic to the underlying-set functor. -/
theorem exactFunctor_finite_iso_forget
    (F : DiscreteContAction FintypeCat G ⥤ Type u)
    (h_exact : exactFunctor (DiscreteContAction FintypeCat G) (Type u) F)
    (h_finite : ∀ X : DiscreteContAction FintypeCat G, Finite (F.obj X)) :
    Nonempty (F ≅ forgetFinite G) := sorry

end CategoryTheory.DiscreteContAction
