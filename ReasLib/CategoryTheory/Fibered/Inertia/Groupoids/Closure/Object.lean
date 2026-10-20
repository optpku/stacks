module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Closure.Projection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Groupoid-fibred object closure

This leaf owns the object-property witness used to restrict neutral inertia
to the full subbicategory of categories fibred in groupoids.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace isFiberedInGroupoids

/-- Neutral based inertia preserves the object property of being fibred in groupoids. This is
the objectwise closure input for restricting the ambient inertia pseudofunctor to the canonical
full subbicategory. -/
@[stacks 04Z4 "groupoid-fibred inertia closure"]
theorem inertia
    {X : BasedCategory.{vS, uS} C}
    (hX : BasedCategory.isFiberedInGroupoids C X) :
    BasedCategory.isFiberedInGroupoids C (BasedCategory.inertia X) := sorry

end isFiberedInGroupoids

end BasedCategory

end CategoryTheory
