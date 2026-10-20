module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.ToIsoClass
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.InSetoids.Basic

/-!
# Equivalence of the canonical morphism to fibrewise isomorphism classes
-/

@[expose] public section

universe uC vC uG vG

namespace CategoryTheory.BasedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {G : Type uG} [Category.{vG} G]

/-- The canonical morphism to fibrewise isomorphism classes is an equivalence over the base
if and only if the opposite projection is fibered in setoids. -/
theorem toIsoClass_isEquivalence_iff_inSetoids (q : G ⥤ C)
    [Functor.IsFibered.InGroupoids q.op] :
    IsEquivalence (toIsoClass q) ↔ Functor.IsFibered.InSetoids q.op := sorry

end CategoryTheory.BasedFunctor
