module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map

/-!
# Chap04 4.34.2.3

This file is the source-facing recall for the two functorial clauses of Definition 4.34.2. The
computation, naturality, and typed-specialization inventory belongs to the ReasLib owner files and
their routing documentation, not to this numbered entry.
-/

@[expose] public section

universe u v u₁ v₁ u₁' v₁' u₂ v₂ u₂' v₂'

namespace CategoryTheory
namespace BasedCategory

open BasedFunctor

variable {C : Type u} [Category.{v} C]
variable
    {S₁ : BasedCategory.{v₁, u₁} C} {S₁' : BasedCategory.{v₁', u₁'} C}
    {S₂ : BasedCategory.{v₂, u₂} C} {S₂' : BasedCategory.{v₂', u₂'} C}

/- 4.34.2.3 (1): an invertibly commuting square in `Cat/C` induces a map on relative
inertia. -/
@[stacks 04Z4 "(1)"]
#check (RelativeInertia.map :
  {F₁ : S₁ ⥤ᵇ S₁'} → {F₂ : S₂ ⥤ᵇ S₂'} →
    (G : S₁ ⥤ᵇ S₂) → (G' : S₁' ⥤ᵇ S₂') →
      (comm : F₁ ⋙ G' ≅ G ⋙ F₂) →
        relativeInertia F₁ ⥤ᵇ relativeInertia F₂)

/- 4.34.2.3 (2): a morphism in `Cat/C` induces a map on absolute inertia. -/
@[stacks 04Z4 "(2)"]
#check (Inertia.map : (G : S₁ ⥤ᵇ S₂) → inertia S₁ ⥤ᵇ inertia S₂)

end BasedCategory
end CategoryTheory
