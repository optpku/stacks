/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.RelativeFunctoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.RelativeFunctoriality.Stable.Computations
import Mathlib.Tactic.CrossRefAttribute

/-! Stable-universe setoid-fibred relative inertia. -/

@[expose] public section

universe u v vS w

namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Setoids
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace RelativeInertia
variable {X Y : FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}

/-- Mapping relative inertia along an invertible square commutes with forgetting to the source
side of that square. -/
@[simp]
theorem map.comp_forget
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    RelativeInertia.map G G' comm ≫ RelativeInertia.forget F₂ =
      RelativeInertia.forget F₁ ≫ G := sorry

/-- Mapping relative inertia along an invertible square carries the neutral relative section to
the neutral relative section. -/
@[simp]
theorem identitySection.comp_map
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    RelativeInertia.identitySection F₁ ≫ RelativeInertia.map G G' comm =
      G ≫ RelativeInertia.identitySection F₂ := sorry

end RelativeInertia
end FiberedCategoryOver.Setoids
end CategoryTheory
