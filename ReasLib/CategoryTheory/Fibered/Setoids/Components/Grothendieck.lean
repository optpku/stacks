/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.Setoids.AssociatedSets.Basic
public import ReasLib.CategoryTheory.Fibered.Setoids.Components.Presheaf

/-!
# The fibrewise-components Grothendieck construction

Applying the discrete Grothendieck construction to the presheaf of fibrewise isomorphism classes
gives a pseudofunctor to categories fibred in sets and an ordinary functor from the homotopy
`1`-category. This file owns the construction and its concrete object and morphism API.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Opposite
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Setoids

variable (C) in
/-- Taking `π₀` in every fibre and applying the discrete Grothendieck construction defines a
pseudofunctor from categories fibred in setoids to the locally discrete bicategory on categories
fibred in sets. The base category is explicit because the construction has no value argument. -/
@[stacks 04SC "fibrewise components pseudofunctor"]
noncomputable def components.pseudofunctor :
    FiberedCategoryOver.Setoids C ⥤ᵖ LocallyDiscrete (FiberedCategoryOver.Sets C) :=
  (componentsPresheaf.pseudofunctor C).comp
    (FiberedCategoryOver.Sets.ofPresheaf C).toPseudofunctor

/-- The fibrewise-components pseudofunctor sends an object to its associated
category fibred in sets. -/
@[simp]
theorem components.pseudofunctor.obj
    (X : FiberedCategoryOver.Setoids C) :
    (components.pseudofunctor C).obj X =
      LocallyDiscrete.mk X.associatedSets := sorry

/-- The fibrewise-components pseudofunctor sends a `1`-morphism to the
discrete Grothendieck construction of its map on components. -/
@[simp]
theorem components.pseudofunctor.map
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) :
    (components.pseudofunctor C).map F =
      ((FiberedCategoryOver.Sets.ofPresheaf C).map (componentsMap F)).toLoc := sorry

/-- The `2`-cell action of the fibrewise-components pseudofunctor is the discrete
Grothendieck action on the corresponding component-presheaf `2`-cell. -/
@[simp]
theorem components.pseudofunctor.map₂
    {X Y : FiberedCategoryOver.Setoids C} {F G : X ⟶ Y} (η : F ⟶ G) :
    (components.pseudofunctor C).map₂ η =
      ((FiberedCategoryOver.Sets.ofPresheaf C).toPseudofunctor).map₂
        ((componentsPresheaf.pseudofunctor C).map₂ η) := sorry

/-- The identity comparison of the fibrewise-components pseudofunctor is the composition
comparison prescribed by `Pseudofunctor.comp`. -/
@[simp]
theorem components.pseudofunctor.mapId
    (X : FiberedCategoryOver.Setoids C) :
    (components.pseudofunctor C).mapId X =
      ((FiberedCategoryOver.Sets.ofPresheaf C).toPseudofunctor).map₂Iso
          ((componentsPresheaf.pseudofunctor C).mapId X) ≪≫
        ((FiberedCategoryOver.Sets.ofPresheaf C).toPseudofunctor).mapId
          ((componentsPresheaf.pseudofunctor C).obj X) := sorry

/-- The composition comparison of the fibrewise-components pseudofunctor is the composition
comparison prescribed by `Pseudofunctor.comp`. -/
@[simp]
theorem components.pseudofunctor.mapComp
    {X Y Z : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    (components.pseudofunctor C).mapComp F G =
      ((FiberedCategoryOver.Sets.ofPresheaf C).toPseudofunctor).map₂Iso
          ((componentsPresheaf.pseudofunctor C).mapComp F G) ≪≫
        ((FiberedCategoryOver.Sets.ofPresheaf C).toPseudofunctor).mapComp
          ((componentsPresheaf.pseudofunctor C).map F)
          ((componentsPresheaf.pseudofunctor C).map G) := sorry

variable (C) in
/-- The ordinary fibrewise-components functor obtained by descending
`components.pseudofunctor` to the homotopy `1`-category. The base category is explicit because
this global functor has no value argument. -/
@[stacks 04SC "fibrewise components functor"]
noncomputable def components :
    Bicategory.HomotopyCategory (FiberedCategoryOver.Setoids C) ⥤
      FiberedCategoryOver.Sets C :=
  Bicategory.HomotopyCategory.lift (components.pseudofunctor C)

/-- The object part of `components` is the associated category of elements. -/
@[simp]
theorem components.obj (X : FiberedCategoryOver.Setoids C) :
    (components C).obj (Bicategory.HomotopyCategory.mk X) =
      X.associatedSets := sorry

/-- The morphism between associated categories fibred in sets induced by an actual
`1`-morphism of categories fibred in setoids. Its data is the discrete Grothendieck construction
of the explicit map on fibrewise components. -/
@[stacks 04SC "Grothendieck map on fibrewise components"]
noncomputable def components.mapHom
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) :
    X.associatedSets ⟶ Y.associatedSets :=
  (FiberedCategoryOver.Sets.ofPresheaf C).map (componentsMap F)

/-- On a represented morphism, `components` is the short actual-morphism constructor
`components.mapHom`. -/
@[simp]
theorem components.map_mkHom
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) :
    (components C).map (Bicategory.HomotopyCategory.mkHom F) =
      components.mapHom F := sorry

/-- The actual-morphism constructor for fibrewise components preserves identity morphisms. -/
@[simp]
theorem components.mapHom.id (X : FiberedCategoryOver.Setoids C) :
    components.mapHom (𝟙 X) = 𝟙 X.associatedSets := sorry

/-- The actual-morphism constructor for fibrewise components preserves composition. -/
@[simp]
theorem components.mapHom.comp
    {X Y Z : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    components.mapHom (F ≫ G) = components.mapHom F ≫ components.mapHom G := sorry

/-- A `2`-morphism identifies the induced actual morphisms between the associated categories
fibred in sets. This is the Grothendieck-level form of `componentsMap.eq_of_hom`, so downstream
code does not need to unfold `components.mapHom`. -/
theorem components.mapHom.eq_of_hom
    {X Y : FiberedCategoryOver.Setoids C} {F G : X ⟶ Y} (η : F ⟶ G) :
    components.mapHom F = components.mapHom G := sorry

/-- The total functor underlying `components.mapHom F` is the opposite category-of-elements
functor induced by `componentsMap F`. -/
@[simp]
theorem components.mapHom.toFunctor
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.toFunctor (components.mapHom F) =
      (CategoryOfElements.map (componentsMap F)).op := sorry

/-- On total-category morphisms, `components.mapHom F` is the canonical
category-of-elements map induced by `componentsMap F`. -/
@[simp]
theorem components.mapHom.map
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y)
    {x y : (Functor.fiberIsoClassPresheaf X.p).Elementsᵒᵖ} (φ : x ⟶ y) :
    (FiberedCategoryOver.Sets.toFunctor (components.mapHom F)).map φ =
      (CategoryOfElements.map (componentsMap F)).op.map φ := sorry

/-- On total-category objects, `components.mapHom F` applies `componentsMap F` to the stored
fibrewise isomorphism class. -/
@[simp]
theorem components.mapHom.obj
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y)
    (x : (Functor.fiberIsoClassPresheaf X.p).Elementsᵒᵖ) :
    (FiberedCategoryOver.Sets.toFunctor (components.mapHom F)).obj x =
      op ⟨(unop x).1, (componentsMap F).app (unop x).1 (unop x).2⟩ := sorry

/-- On an isomorphism class represented by a fibre object, `components.mapHom F` applies the
ordinary functor induced by `F` on that fibre. -/
@[simp]
theorem components.mapHom.obj_mk
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y)
    (U : C) (x : X.p.Fiber U) :
    (FiberedCategoryOver.Sets.toFunctor (components.mapHom F)).obj
        (op ⟨op U, Quotient.mk'' x⟩) =
      op ⟨op U, Quotient.mk'' ((fiberFunctor F U).obj x)⟩ := sorry

/- Data and axiom audit (mathlib 4.32): `componentsMap` delegates its component functions to
`BasedFunctor.fiberIsoClassMap`, so no representatives of isomorphism classes are selected here.
`components.mapHom` then applies the explicit category-of-elements map to that transformation.
Their `sorryAx` dependencies are inherited from deferred naturality and based-functor laws. The
two ordinary functors have explicit object and map actions through `ConnectedComponents.liftFunctor`;
remaining `sorryAx` dependencies belong to functor laws and locally-discrete transport, not to
hidden object or morphism payload. -/

end FiberedCategoryOver.Setoids

end CategoryTheory
