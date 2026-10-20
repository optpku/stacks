module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.GroupoidTarget
public import ReasLib.CategoryTheory.Fibered.Setoids.Hom

/-!
# Maps on fibrewise components

A morphism of categories fibred in setoids induces a natural transformation between their
presheaves of fibrewise isomorphism classes. This is the domain-specific specialization of the
neutral based-functor action used by later component constructions.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Setoids

/-- The natural transformation of fibrewise-component presheaves induced by a morphism of
categories fibred in setoids. -/
@[stacks 04SC "map on fibrewise components"]
noncomputable def componentsMap
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) :
    Functor.fiberIsoClassPresheaf X.p ⟶
      Functor.fiberIsoClassPresheaf Y.p :=
  BasedFunctor.fiberIsoClassMap
    (FiberedCategoryOver.Setoids.toBasedFunctor F)

/-- The component of `componentsMap` is the map induced by the ordinary fiber functor. -/
@[simp]
theorem componentsMap.app
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (U : Cᵒᵖ) :
    (componentsMap F).app U =
      TypeCat.ofHom (fiberFunctor F (unop U)).isoClassesMap := sorry

/-- On each base object, `componentsMap` applies the induced ordinary fiber functor to an
isomorphism class. -/
@[simp]
theorem componentsMap.app_mk
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y)
    (U : Cᵒᵖ) (x : X.p.Fiber (unop U)) :
    (componentsMap F).app U (Quotient.mk'' x) =
      Quotient.mk'' ((fiberFunctor F (unop U)).obj x) := sorry

/-- The component-presheaf map induced by an identity is the identity. -/
@[simp]
theorem componentsMap.id (X : FiberedCategoryOver.Setoids C) :
    componentsMap (𝟙 X) = 𝟙 (Functor.fiberIsoClassPresheaf X.p) := sorry

/-- The component-presheaf map induced by a composite is the composite of the induced maps. -/
@[simp]
theorem componentsMap.comp
    {X Y Z : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    componentsMap (F ≫ G) = componentsMap F ≫ componentsMap G := sorry

/-- A `2`-morphism induces equality of the maps on fibrewise isomorphism classes. -/
theorem componentsMap.eq_of_hom
    {X Y : FiberedCategoryOver.Setoids C} {F G : X ⟶ Y} (η : F ⟶ G) :
    componentsMap F = componentsMap G := sorry

end FiberedCategoryOver.Setoids

end CategoryTheory
