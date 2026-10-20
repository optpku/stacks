/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic

/-!
# Heterogeneous precomposition over a base

This module provides universe-polymorphic precomposition on hom-categories of strict functors
over a fixed base, together with the canonical based slice-change map induced by `Over.map`.
The target based category is explicit because it cannot be recovered from the
precomposed based functor.
-/

@[expose] public section

universe v u vX uX vY uY vZ uZ vW uW

namespace CategoryTheory

open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace BasedCategory

/-- Heterogeneous precomposition preserves identity based natural transformations. -/
theorem precomposition.map.id
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) :
    whiskerLeft F (𝟙 G) = 𝟙 (BasedFunctor.comp F G) := sorry
/- Proof strategy: apply `BasedNatTrans.ext`; on underlying natural transformations use
`Functor.whiskerLeft_id`, while verticality is proof-irrelevant. -/

/-- Heterogeneous precomposition preserves vertical composition of based natural
transformations. -/
theorem precomposition.map.comp
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} (F : X ⥤ᵇ Y)
    {G H K : Y ⥤ᵇ Z} (η : G ⟶ H) (θ : H ⟶ K) :
    whiskerLeft F (η ≫ θ) = whiskerLeft F η ≫ whiskerLeft F θ := sorry
/- Proof strategy: apply `BasedNatTrans.ext`; on underlying natural transformations use
`Functor.whiskerLeft_comp`, while verticality is proof-irrelevant. -/

/-- Precomposition by a based functor on heterogeneous based-functor hom-categories. This is
the universe-polymorphic extension of `Bicategory.precomposing`, whose three objects must live
in one fixed `BasedCategory` universe.

The target based category `Z` is explicit: it is an actual parameter of the
hom-category action and cannot be inferred from the precomposed functor `F`. -/
def precomposition
    (Z : BasedCategory.{vZ, uZ} C) {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C} (F : X ⥤ᵇ Y) :
    (Y ⥤ᵇ Z) ⥤ (X ⥤ᵇ Z) where
  obj G := BasedFunctor.comp F G
  map η := whiskerLeft F η
  map_id := precomposition.map.id F
  map_comp := precomposition.map.comp F

/-- Precomposition sends a based functor to ordinary based-functor composition. -/
@[simp]
theorem precomposition.obj
    (Z : BasedCategory.{vZ, uZ} C) {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C} (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) :
    (precomposition Z F).obj G = BasedFunctor.comp F G := sorry

/-- Precomposition sends a based natural transformation to its left whiskering. -/
@[simp]
theorem precomposition.map
    (Z : BasedCategory.{vZ, uZ} C) {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C} (F : X ⥤ᵇ Y)
    {G H : Y ⥤ᵇ Z} (η : G ⟶ H) :
    (precomposition Z F).map η = whiskerLeft F η := sorry

/-- Precomposition by the identity based functor is the identity on the
corresponding heterogeneous hom-category. -/
theorem precomposition.id
    (Z : BasedCategory.{vZ, uZ} C) (X : BasedCategory.{vX, uX} C) :
    precomposition Z (BasedFunctor.id X) = 𝟭 (X ⥤ᵇ Z) := sorry

/-- Precomposition by a composite is the composite of the two precomposition
functors in the contravariant order. -/
theorem precomposition.comp
    (Z : BasedCategory.{vZ, uZ} C) {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C} {W : BasedCategory.{vW, uW} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ W) :
    precomposition Z (BasedFunctor.comp F G) =
      precomposition Z G ⋙ precomposition Z F := sorry

/-- The slice-change functor `C/U ⟶ C/V` induced by `f : U ⟶ V`, regarded as a morphism in
`Cat/C`. This is the reusable based-category packaging of `Over.map f`. -/
def overMap {U V : C} (f : U ⟶ V) :
    ofFunctor (Over.forget U) ⥤ᵇ ofFunctor (Over.forget V) :=
  BasedFunctor.ofFunctor (Over.map f) (Over.mapForget_eq f)

/-- The underlying functor of the based slice-change map is `Over.map f`. -/
@[simp]
theorem overMap.toFunctor {U V : C} (f : U ⟶ V) :
    (overMap f).toFunctor = Over.map f := sorry

/-- The based slice-change map induced by an identity base morphism is the identity. -/
@[simp]
theorem overMap.id (U : C) :
    overMap (𝟙 U) = 𝟙 (ofFunctor (Over.forget U)) := sorry
/- Proof strategy: unfold `overMap`, use `Over.mapId_eq`, and apply extensionality of based
functors; the projection-compatibility proofs are propositionally irrelevant. -/

/-- Based slice-change maps induced by base morphisms preserve composition. -/
@[simp]
theorem overMap.comp {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    overMap (f ≫ g) = BasedFunctor.comp (overMap f) (overMap g) := sorry
/- Proof strategy: unfold `overMap`, use `Over.mapComp_eq`, and apply extensionality of based
functors; the projection-compatibility proofs are propositionally irrelevant. -/

end BasedCategory

end CategoryTheory
