module

import ReasLib.CategoryTheory.Action.Finite.Exact
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped FintypeCatDiscrete

universe u

/- Lemma 58.3.4: Let `G` be a topological group. Let `F` be an exact functor from
finite continuous `G`-sets to sets with finite values. Then `F` is isomorphic to
the functor (58.3.2.1). -/
@[stacks 0BMV] #check
  (CategoryTheory.DiscreteContAction.exactFunctor_finite_iso_forget :
    ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (F : DiscreteContAction FintypeCat G ⥤ Type u),
      exactFunctor (DiscreteContAction FintypeCat G) (Type u) F →
        (∀ X : DiscreteContAction FintypeCat G, Finite (F.obj X)) →
          Nonempty (F ≅ CategoryTheory.DiscreteContAction.forgetFinite G))
