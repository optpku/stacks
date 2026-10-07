module

public import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms presenting sheafifications

A morphism of presheaves presents its target as a sheafification when it is inverted by
sheafification and its target is already a sheaf. This formulation uses the canonical
localizing class `GrothendieckTopology.W` and is independent of any chosen sheafification
functor.
-/

@[expose] public section

universe uC vC uA vA

namespace CategoryTheory.Presheaf

variable {C : Type uC} [Category.{vC} C]
variable {A : Type uA} [Category.{vA} A]

/-- A presheaf morphism presents its target as a sheafification when it belongs to the
sheafification localizing class and its target is a sheaf. -/
@[stacks 02ZP "presheaf morphism presenting a sheafification",
  stacks 02ZN "stackification Hom-presheaf sheafification predicate"]
def IsSheafification
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) : Prop :=
  J.W f ∧ IsSheaf J Q

/-- The two defining conditions for a presheaf morphism to present a sheafification. -/
@[stacks 02ZP "sheafification-presentation criterion",
  stacks 02ZN "stackification sheafification-presentation criterion"]
theorem isSheafification_iff
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    IsSheafification J f ↔ J.W f ∧ IsSheaf J Q := sorry

/-- A morphism presenting a sheafification belongs to the sheafification localizing class. -/
@[stacks 02ZP "localizing-class projection of a sheafification presentation",
  stacks 02ZN "stackification localizing-class projection"]
theorem IsSheafification.mem_W
    {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ A} {f : P ⟶ Q}
    (hf : IsSheafification J f) : J.W f := sorry

/-- The target of a morphism presenting a sheafification is a sheaf. -/
@[stacks 02ZP "target-sheaf projection of a sheafification presentation",
  stacks 02ZN "stackification target-sheaf projection"]
theorem IsSheafification.isSheaf
    {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ A} {f : P ⟶ Q}
    (hf : IsSheafification J f) : IsSheaf J Q := sorry

end CategoryTheory.Presheaf
