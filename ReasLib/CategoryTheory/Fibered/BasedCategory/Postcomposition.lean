/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic

/-!
# Heterogeneous postcomposition over a base

This module provides universe-polymorphic postcomposition on hom-categories of
strict functors over a fixed base. It is the right-action counterpart to
`BasedCategory.Precomposition`: the source based category is explicit because
it cannot be recovered from the postcomposed based functor.
-/

@[expose] public section

universe v u vX uX vY uY vZ uZ vW uW

namespace CategoryTheory

open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace BasedCategory

/-- Heterogeneous postcomposition preserves identity based natural transformations. -/
theorem postcomposition.map.id
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) :
    whiskerRight (𝟙 F) G = 𝟙 (BasedFunctor.comp F G) := sorry

/-- Heterogeneous postcomposition preserves vertical composition of based natural
transformations. -/
theorem postcomposition.map.comp
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} (G : Y ⥤ᵇ Z)
    {F F' F'' : X ⥤ᵇ Y} (η : F ⟶ F') (θ : F' ⟶ F'') :
    whiskerRight (η ≫ θ) G = whiskerRight η G ≫ whiskerRight θ G := sorry

/-- Postcomposition by a based functor on heterogeneous based-functor hom-categories.

The source based category `X` is explicit: it is an actual parameter of the
hom-category action and cannot be inferred from the target functor `G`. -/
def postcomposition
    (X : BasedCategory.{vX, uX} C) {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} (G : Y ⥤ᵇ Z) :
    (X ⥤ᵇ Y) ⥤ (X ⥤ᵇ Z) where
  obj F := BasedFunctor.comp F G
  map η := whiskerRight η G
  map_id := fun F => postcomposition.map.id F G
  map_comp := fun η θ => postcomposition.map.comp G η θ

/-- Postcomposition sends a based functor to ordinary based-functor composition. -/
@[simp]
theorem postcomposition.obj
    (X : BasedCategory.{vX, uX} C) {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} (G : Y ⥤ᵇ Z) (F : X ⥤ᵇ Y) :
    (postcomposition X G).obj F = BasedFunctor.comp F G := sorry

/-- Postcomposition sends a based natural transformation to its right whiskering. -/
@[simp]
theorem postcomposition.map
    (X : BasedCategory.{vX, uX} C) {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} (G : Y ⥤ᵇ Z)
    {F F' : X ⥤ᵇ Y} (η : F ⟶ F') :
    (postcomposition X G).map η = whiskerRight η G := sorry

/-- Postcomposition by the identity based functor is the identity on the
corresponding heterogeneous hom-category. -/
theorem postcomposition.id
    (X : BasedCategory.{vX, uX} C) (Y : BasedCategory.{vY, uY} C) :
    postcomposition X (BasedFunctor.id Y) = 𝟭 (X ⥤ᵇ Y) := sorry

/-- Postcomposition by a composite is the composite of the two postcomposition
functors in the ordinary order. -/
theorem postcomposition.comp
    (X : BasedCategory.{vX, uX} C) {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} {W : BasedCategory.{vW, uW} C}
    (F : Y ⥤ᵇ Z) (G : Z ⥤ᵇ W) :
    postcomposition X (BasedFunctor.comp F G) =
      postcomposition X F ⋙ postcomposition X G := sorry

end BasedCategory

end CategoryTheory
