/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.FinitePreadditive
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Image filtrations under additive functors between abelian categories. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section
universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A] [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B]
variable (F : A ⥤ B) [F.Additive]

/-- The images of mapped filtration-stage arrows form a decreasing filtration. -/
theorem imageMap_monotone (X : FilteredObject A) :
    Monotone (fun p : ℤᵒᵈ ↦ imageSubobject (F.map (X.filtration p).arrow)) := sorry

/-- Applying an additive functor to a filtered object gives the filtration by images of the
mapped stage inclusions on the image of its ambient object. -/
noncomputable def imageMap (X : FilteredObject A) : FilteredObject B :=
  FilteredObject.mk (F.obj X.obj)
    { toFun := fun p ↦ imageSubobject (F.map (X.filtration p).arrow)
      monotone' := imageMap_monotone F X }

/-- The ambient object of the image filtration is the functor's value on the ambient object. -/
@[simp] theorem imageMap_obj (X : FilteredObject A) :
    (imageMap F X).obj = F.obj X.obj := rfl

/-- Each image-filtration stage is the image of the mapped original stage inclusion. -/
@[simp] theorem imageMap_stage (X : FilteredObject A) (p : ℤ) :
    (imageMap F X).filtration.stage p =
      imageSubobject (F.map (X.filtration.stage p).arrow) := rfl

/-- Applying an additive functor to a filtered morphism preserves the image filtrations. -/
theorem imageMapHom_preserves {X Y : FilteredObject A} (f : X ⟶ Y) (p : ℤ) :
    ((imageMap F Y).filtration.stage p).Factors
      (((imageMap F X).filtration.stage p).arrow ≫ F.map f.hom) := sorry

/-- The morphism between image filtrations has the mapped ambient morphism as its underlying
map. -/
noncomputable def imageMapHom {X Y : FilteredObject A} (f : X ⟶ Y) :
    imageMap F X ⟶ imageMap F Y :=
  Hom.mk (F.map f.hom) (imageMapHom_preserves F f)

/-- Image-filtration morphisms preserve identities. -/
theorem imageMapHom_id (X : FilteredObject A) :
    imageMapHom F (𝟙 X) = 𝟙 (imageMap F X) := sorry

/-- Image-filtration morphisms preserve composition. -/
theorem imageMapHom_comp {X Y Z : FilteredObject A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    imageMapHom F (f ≫ g) = imageMapHom F f ≫ imageMapHom F g := sorry

/-- The functor taking a filtered object to the images of its mapped filtration stages. -/
noncomputable def imageMapFunctor : FilteredObject A ⥤ FilteredObject B where
  obj := imageMap F
  map := imageMapHom F
  map_id := imageMapHom_id F
  map_comp := imageMapHom_comp F

/-- The image-filtration functor of an additive functor is additive. -/
instance imageMapFunctor_additive : (imageMapFunctor F).Additive := sorry

namespace Finite

/-- Image filtrations of finite filtrations under additive functors remain finite. -/
theorem imageMap_isFinite {X : FilteredObject A} (hX : X.IsFinite) :
    (imageMap F X).IsFinite := sorry

/-- The restriction of the image-filtration functor to finite filtered objects. -/
noncomputable def imageMapFunctor : category A ⥤ category B :=
  ObjectProperty.lift (FilteredObject.IsFinite : ObjectProperty (FilteredObject B))
    (inclusion A ⋙ FilteredObject.imageMapFunctor F)
    (fun X ↦ imageMap_isFinite F X.property)

/-- The finite image-filtration functor computes objects by the general image construction. -/
@[simp] theorem imageMapFunctor_obj (X : category A) :
    ((imageMapFunctor F).obj X).obj = imageMap F X.obj := rfl

/-- The finite image-filtration functor computes morphisms by mapping their ambient maps. -/
@[simp] theorem imageMapFunctor_map {X Y : category A} (f : X ⟶ Y) :
    ((imageMapFunctor F).map f).hom = imageMapHom F f.hom := rfl

/-- The image-filtration functor on finite filtered objects is additive. -/
instance imageMapFunctor_additive : (imageMapFunctor F).Additive := sorry

end Finite
end CategoryTheory.FilteredObject
