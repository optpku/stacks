/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Basic

/-!
# Displayed category structures

This leaf owns the property-neutral dependent hom data over a category.  A displayed object is
attached to each base object, and a displayed morphism is attached to a base morphism together
with its displayed endpoints.  The category laws are stated using Lean's primitive equality
transport; the named transport API is provided separately by `DisplayedCategory.Transport`.
-/

@[expose] public section

universe v u w₁ w₂

namespace CategoryTheory

set_option linter.checkUnivs false in
/-- A category of dependent objects and morphisms displayed over a base category `C`.

The object family `obj` assigns a type of displayed objects to every `X : C`.  The family `Hom`
assigns a type of displayed morphisms to a base morphism `f`, with displayed source and target.
Identity, composition, and their three laws are part of the displayed structure itself; the laws
use the canonical equality transport of the indexed `Hom` family.
-/
structure DisplayedCategory (C : Type u) [Category.{v} C] where
  /-- The type of displayed objects lying over a base object. -/
  obj : C → Type w₁
  /-- The type of displayed morphisms lying over a base morphism. -/
  Hom : ∀ {X Y : C}, (X ⟶ Y) → obj X → obj Y → Type w₂
  /-- The displayed identity over the identity of a base object. -/
  id : ∀ {X : C} (x : obj X), Hom (𝟙 X) x x
  /-- The displayed composite over a composite of base morphisms. -/
  comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {x : obj X} {y : obj Y} {z : obj Z},
    Hom f x y → Hom g y z → Hom (f ≫ g) x z
  /-- The displayed left identity law, transported along `Category.id_comp`. -/
  id_comp : ∀ {X Y : C} {f : X ⟶ Y}
    {x : obj X} {y : obj Y} (φ : Hom f x y),
    (Category.id_comp f) ▸ comp (id x) φ = φ
  /-- The displayed right identity law, transported along `Category.comp_id`. -/
  comp_id : ∀ {X Y : C} {f : X ⟶ Y}
    {x : obj X} {y : obj Y} (φ : Hom f x y),
    (Category.comp_id f) ▸ comp φ (id y) = φ
  /-- The displayed associativity law, transported along `Category.assoc`. -/
  assoc : ∀ {W X Y Z : C}
    {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {w : obj W} {x : obj X} {y : obj Y} {z : obj Z}
    (φ : Hom f w x) (ψ : Hom g x y) (χ : Hom h y z),
    (Category.assoc f g h) ▸ comp (comp φ ψ) χ = comp φ (comp ψ χ)

end CategoryTheory
