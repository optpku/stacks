/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Inertia.Category

/-!
# Identity and composition laws for inertia functoriality

This leaf owns the strict identity and composition laws for the raw inertia action.
-/

@[expose] public section

open CategoryTheory

universe uC vC uD vD uE vE

namespace CategoryTheory
namespace Inertia

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]

/-- The inertia construction sends the identity functor to the identity inertia functor. -/
@[simp]
theorem map.id (C : Type uC) [Category.{vC} C] :
    map (𝟭 C) = 𝟭 (Inertia C) := sorry

/-- The inertia construction preserves composition of functors. -/
@[simp]
theorem map.comp (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) = map F ⋙ map G := sorry

end Inertia
end CategoryTheory
