/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Maps
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.Maps

/-!
# Comparison laws for cartesian relative inertia

The relative-inertia structure map and identity section are compatible with the
relative-to-absolute comparison and with maps induced by invertible squares.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, max w vS, vS} C}

/-- The relative identity section is a right inverse to relative-inertia forgetting. -/
@[simp, stacks 04Z3 "cartesian relative-inertia section/forget compatibility"]
theorem identitySection.comp_forget (F : X ⟶ Y) :
    identitySection F ≫ forget F = 𝟙 X := sorry

/-- Retaining and then forgetting the selected relative automorphism agrees with forgetting it
directly. -/
@[simp, stacks 04Z5 "cartesian relative-to-absolute inertia comparison"]
theorem toInertia.comp_forget (F : X ⟶ Y) :
    FiberedCategoryOver.RelativeInertia.toInertia F ≫
        FiberedCategoryOver.Inertia.forget X =
      forget F := sorry

/-- The relative identity section followed by the relative-to-absolute comparison is the
absolute identity section. -/
@[simp, stacks 04Z5 "cartesian relative-to-absolute identity-section comparison"]
theorem identitySection.comp_toInertia (F : X ⟶ Y) :
    identitySection F ≫ FiberedCategoryOver.RelativeInertia.toInertia F =
      FiberedCategoryOver.Inertia.identitySection X := sorry

/-- Mapping relative inertia along an invertible square commutes with forgetting to the source
side of that square. -/
@[simp, stacks 04Z4 "cartesian relative-inertia map/forget compatibility"]
theorem map.comp_forget
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, max w vS, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.RelativeInertia.map G G' comm ≫ forget F₂ =
      forget F₁ ≫ G := sorry

/-- Mapping relative inertia along an invertible square carries the relative identity section to
the relative identity section. -/
@[simp, stacks 04Z4 "cartesian relative-inertia map/section compatibility"]
theorem identitySection.comp_map
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, max w vS, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    identitySection F₁ ≫ FiberedCategoryOver.RelativeInertia.map G G' comm =
      G ≫ identitySection F₂ := sorry

end FiberedCategoryOver.RelativeInertia

end CategoryTheory
