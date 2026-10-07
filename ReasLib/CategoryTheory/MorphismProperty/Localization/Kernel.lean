module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Kernels of Localization Models

Any localization functor is obtained from the canonical localization model by an equivalence of
target categories.  Consequently, its objectwise kernel is independent of the chosen model.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MorphismProperty.Localization

open Limits

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- The objectwise kernel of a localization functor agrees with the kernel of the canonical
localization model. -/
@[stacks 05RT "kernels of localization models"]
theorem kernel_eq_model (W : MorphismProperty C) (L : C ⥤ D)
    [L.IsLocalization W] :
    Functor.kernel L = Functor.kernel W.Q := sorry

/-- An object becomes zero in an arbitrary localization model exactly when it becomes zero in
the canonical localization model. -/
@[stacks 05RT "zero objects in localization models"]
theorem objectIsZero_iff_model (W : MorphismProperty C) (L : C ⥤ D)
    [L.IsLocalization W] (X : C) :
    IsZero (L.obj X) ↔ IsZero (W.Q.obj X) := sorry


end CategoryTheory.MorphismProperty.Localization
