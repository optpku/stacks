module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Inertia.ToInertia.Construction

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory
namespace BasedCategory

open BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/- 4.34.2.4: forgetting the relative kernel condition defines the canonical comparison
`relativeInertia F ⥤ᵇ inertia X`. -/
@[stacks 04Z5]
#check (RelativeInertia.toInertia :
  (F : X ⥤ᵇ Y) → relativeInertia F ⥤ᵇ inertia X)

end BasedCategory
end CategoryTheory
