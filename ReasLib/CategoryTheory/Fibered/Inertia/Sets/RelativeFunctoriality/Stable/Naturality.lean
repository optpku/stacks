/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.RelativeFunctoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.RelativeFunctoriality.Stable.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsoluteTransformations.Maps.Construction
import Mathlib.Tactic.CrossRefAttribute

/-! Stable-universe set-fibred relative inertia. -/

@[expose] public section

universe u v vS w

namespace CategoryTheory
open BasedCategory BasedFunctor
namespace FiberedCategoryOver.Sets
open scoped Bicategory
variable {C : Type u} [Category.{v} C]
namespace RelativeInertia
variable {X Y : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}

/-- Retaining and then forgetting a relative automorphism agrees with direct forgetting. -/
@[simp]
theorem toInertia.comp_forget (F : X ⟶ Y) :
    toInertia F ≫ Inertia.forget X = forget F := sorry

/-- The relative identity section followed by retention is the absolute identity section. -/
@[simp]
theorem identitySection.comp_toInertia (F : X ⟶ Y) :
    identitySection F ≫ toInertia F = Inertia.identitySection X := sorry

/-- A relative-inertia square map commutes with forgetting to the source side. -/
@[simp]
theorem map.comp_forget
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    map G G' comm ≫ forget F₂ = forget F₁ ≫ G := sorry

/-- A relative-inertia square map carries the neutral section to the neutral section. -/
@[simp]
theorem identitySection.comp_map
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, max w vS, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    identitySection F₁ ≫ map G G' comm = G ≫ identitySection F₂ := sorry

end RelativeInertia
end FiberedCategoryOver.Sets
end CategoryTheory
