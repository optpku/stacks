module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Inertia.Based.Construction

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedFunctor

namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vS, w} C} {Y : BasedCategory.{vS, w} C}

/- 4.34.2.1 (1): relative inertia has its canonical structure map
`𝓘(X/Y) ⥤ X` in `Cat/C`. -/
@[stacks 042H "(1)"]
#check (RelativeInertia.forget :
  (F : X ⥤ᵇ Y) → relativeInertia F ⥤ᵇ X)

/- 4.34.2.1 (2): absolute inertia has its canonical structure map
`𝓘(X) ⥤ X` in `Cat/C`. -/
@[stacks 042H "(2)"]
#check (Inertia.forget :
  (X : BasedCategory.{vS, w} C) → inertia X ⥤ᵇ X)

end BasedCategory

end CategoryTheory
