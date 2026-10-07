module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [HasPullbacksAlong f] [HasPullbacksAlong g]

/-
The source uses `HasPullbacksAlong` from Definition 4.6.4. Vertical pullback pasting supplies the
canonical typeclass instance for the composite, so this recall needs no project-specific wrapper.
-/

/- Lemma 4.6.5: if `f : X ⟶ Y` and `g : Y ⟶ Z` are representable, then their composite
`f ≫ g : X ⟶ Z` is representable. -/
@[stacks 001Y "representable morphisms are closed under composition"]
#check (inferInstance : HasPullbacksAlong (f ≫ g))

end CategoryTheory.Limits
