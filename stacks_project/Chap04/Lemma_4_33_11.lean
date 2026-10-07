module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Slice

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable {U : C} (p : S ⥤ Over U)
variable [(p ⋙ Over.forget U).IsFibered]

/- Lemma 4.33.11: if `p : S ⥤ Over U` becomes fibred after composing with
`Over.forget U : Over U ⥤ C`, then `p` is fibred over `Over U`. -/
@[stacks 02XR "fiberedness reflected from the slice forgetful composite"]
#check (isFibered_of_comp_over_forget p : p.IsFibered)

end CategoryTheory.Functor
