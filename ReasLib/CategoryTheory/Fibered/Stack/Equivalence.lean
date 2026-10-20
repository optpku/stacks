module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transport of stack conditions across equivalences

The stack condition is invariant under equivalences of fibered categories over the base. If
two categories over a site are equivalent via a based functor, one is a stack iff the other is.

## Main declarations

* `CategoryTheory.IsStack.OnSite.iff_of_isEquivalence` — transport across based equivalence.
* `CategoryTheory.IsStack.OnSite.of_isEquivalence` — forward direction.
* `CategoryTheory.IsStack.InGroupoids.iff_of_isEquivalence` — transport of the
  stack-in-groupoids condition.
* `CategoryTheory.IsStack.InSetoids.iff_of_isEquivalence` — transport of the
  stack-in-setoids condition.
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

variable {C : Type u₁} {S₁ : Type u₂} {S₂ : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} S₁] [Category.{v₃} S₂]

/-- The stack condition transfers across based equivalences over the same site. -/
@[stacks 042W]
theorem IsStack.OnSite.iff_of_isEquivalence
    (J : GrothendieckTopology C) {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalence) :
    IsStack.OnSite J p₁ ↔ IsStack.OnSite J p₂ := sorry

/-- A stack condition transports forward along a based equivalence. -/
@[stacks 042W "forward transport"]
theorem IsStack.OnSite.of_isEquivalence
    (J : GrothendieckTopology C) {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalence) (h₁ : IsStack.OnSite J p₁) :
    IsStack.OnSite J p₂ := sorry

attribute [stacks 042W "forward stack transport across equivalence"]
  IsStack.OnSite.of_isEquivalence

/-- The stack-in-groupoids condition transfers across based equivalences. -/
@[stacks 042X]
theorem IsStack.InGroupoids.iff_of_isEquivalence
    (J : GrothendieckTopology C) {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalence) :
    IsStack.InGroupoids J p₁ ↔ IsStack.InGroupoids J p₂ := sorry

/-- A stack-in-groupoids condition transports forward along a based equivalence. -/
@[stacks 042X "forward transport"]
theorem IsStack.InGroupoids.of_isEquivalence
    (J : GrothendieckTopology C) {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalence) (h₁ : IsStack.InGroupoids J p₁) :
    IsStack.InGroupoids J p₂ := sorry

/-- The stack-in-setoids condition transfers across an equivalence over the same base. -/
@[stacks 0431]
theorem IsStack.InSetoids.iff_of_isEquivalence
    (J : GrothendieckTopology C) {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalence) :
    IsStack.InSetoids J p₁ ↔ IsStack.InSetoids J p₂ := sorry

/-- A stack-in-setoids condition transports forward along a based equivalence. -/
@[stacks 0431 "forward transport"]
theorem IsStack.InSetoids.of_isEquivalence
    (J : GrothendieckTopology C) {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalence) (h₁ : IsStack.InSetoids J p₁) :
    IsStack.InSetoids J p₂ := sorry

end CategoryTheory
