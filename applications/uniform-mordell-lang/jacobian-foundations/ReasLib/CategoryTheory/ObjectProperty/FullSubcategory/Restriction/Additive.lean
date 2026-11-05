module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive functors restricted to full subcategories

An additive functor remains additive after restricting its source and target to object-property
full subcategories. This leaf keeps the preadditive import out of the basic restriction API.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.FullSubcategory.restrict

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable {P : ObjectProperty C} {Q : ObjectProperty D}

/-- Restricting an additive functor to object-property full subcategories is additive. -/
@[stacks 001D "additivity of a functor restricted to full subcategories"]
instance (priority := 100) additive (F : C ⥤ D) [F.Additive]
    (hF : P ≤ Q.inverseImage F) :
    (restrict F hF).Additive := sorry

end CategoryTheory.ObjectProperty.FullSubcategory.restrict
