/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Composition

@[expose] public section

/-!
# Functoriality of Bounded Homotopy Categories

@stack 014X

This leaf restricts an additive functor to the bounded-below, bounded-above, and bounded
homotopy categories. It owns the inclusion and composition comparisons and the induced
additive, shift-compatible, and triangulated instances.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v u

namespace CategoryTheory.Functor.Homotopy

variable {𝒜 : Type u} {ℬ : Type*}
  [Category.{v} 𝒜] [Category ℬ]
  [Preadditive 𝒜] [Preadditive ℬ]

namespace Plus

/-- An additive functor carries the bounded-below homotopy object property into the
bounded-below homotopy object property. -/
@[stacks 014X "preservation of bounded-below homotopy objects"]
theorem mapsTo (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory.plus 𝒜 ≤
      (HomotopyCategory.plus ℬ).inverseImage
        (F.mapHomotopyCategory (up ℤ)) := sorry

/-- An additive functor sends bounded-below homotopy objects to bounded-below homotopy
objects. -/
theorem obj_mem (F : 𝒜 ⥤ ℬ) [F.Additive]
    (X : HomotopyCategory.Plus 𝒜) :
    HomotopyCategory.plus ℬ ((F.mapHomotopyCategory (up ℤ)).obj X.obj) := sorry

/-- The bounded-below functor induced by an additive functor agrees with the ambient homotopy
functor after forgetting boundedness. -/
noncomputable def compInclusionIso (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.mapHomotopyCategoryPlus ⋙ (HomotopyCategory.plus ℬ).ι ≅
      (HomotopyCategory.plus 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ) :=
  ObjectProperty.liftCompιIso
    (HomotopyCategory.plus ℬ)
    ((HomotopyCategory.plus 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ))
    (obj_mem F)

end Plus

namespace Minus

/-- An additive functor carries the bounded-above homotopy object property into the
bounded-above homotopy object property. -/
@[stacks 014X "preservation of bounded-above homotopy objects"]
theorem mapsTo (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory.minus 𝒜 ≤
      (HomotopyCategory.minus ℬ).inverseImage
        (F.mapHomotopyCategory (up ℤ)) := sorry

/-- An additive functor sends bounded-above homotopy objects to bounded-above homotopy
objects. -/
theorem obj_mem (F : 𝒜 ⥤ ℬ) [F.Additive]
    (X : HomotopyCategory.Minus 𝒜) :
    HomotopyCategory.minus ℬ ((F.mapHomotopyCategory (up ℤ)).obj X.obj) := sorry

end Minus

/-- The functor between bounded-above homotopy categories induced by an additive functor. -/
@[stacks 014X "bounded-above homotopy functor"]
def _root_.CategoryTheory.Functor.mapHomotopyCategoryMinus (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory.Minus 𝒜 ⥤ HomotopyCategory.Minus ℬ :=
  ObjectProperty.FullSubcategory.restrict
    (F.mapHomotopyCategory (up ℤ)) (Minus.mapsTo F)

namespace Minus

/-- The bounded-above functor induced by an additive functor agrees with the ambient homotopy
functor after forgetting boundedness. -/
noncomputable def compInclusionIso (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.mapHomotopyCategoryMinus ⋙ (HomotopyCategory.minus ℬ).ι ≅
      (HomotopyCategory.minus 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ) :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (F.mapHomotopyCategory (up ℤ)) (mapsTo F)

/-- An isomorphism `F ⋙ G ≅ H` of additive functors induces the corresponding comparison
between the bounded-above homotopy functors. -/
noncomputable def compIso
    {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    {F : 𝒜 ⥤ ℬ} {G : ℬ ⥤ 𝒞} {H : 𝒜 ⥤ 𝒞} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] :
    F.mapHomotopyCategoryMinus ⋙ G.mapHomotopyCategoryMinus ≅
      H.mapHomotopyCategoryMinus :=
  (ObjectProperty.FullSubcategory.restrict.compIso
      (F.mapHomotopyCategory (up ℤ)) (G.mapHomotopyCategory (up ℤ))
      (mapsTo F) (mapsTo G)).symm ≪≫
    ObjectProperty.FullSubcategory.restrict.natIso
      (ObjectProperty.FullSubcategory.restrict.mapsToComp
        (mapsTo F) (mapsTo G))
      (mapsTo H) (Functor.mapHomotopyCategoryCompIso e (up ℤ))

/-- A full and faithful additive functor induces a full functor on bounded-above homotopy
categories. -/
instance (F : 𝒜 ⥤ ℬ) [F.Additive] [Full F] [Faithful F] :
    Full F.mapHomotopyCategoryMinus := sorry

/-- A full and faithful additive functor induces a faithful functor on bounded-above homotopy
categories. -/
instance (F : 𝒜 ⥤ ℬ) [F.Additive] [Full F] [Faithful F] :
    Faithful F.mapHomotopyCategoryMinus := sorry

/-- The bounded-above homotopy functor induced by an additive functor is additive. -/
instance additive (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.mapHomotopyCategoryMinus.Additive := sorry

/-- The bounded-above homotopy functor induced by an additive functor commutes with shifts. -/
@[stacks 014X "bounded-above homotopy shift comparison"]
noncomputable instance commShift (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.mapHomotopyCategoryMinus.CommShift ℤ :=
  inferInstanceAs (((HomotopyCategory.minus ℬ).lift
    ((HomotopyCategory.minus 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ))
    (obj_mem F)).CommShift ℤ)

/-- The bounded-above homotopy functor induced by an additive functor is triangulated. -/
@[stacks 014X "exactness on bounded-above homotopy categories"]
instance isTriangulated (F : 𝒜 ⥤ ℬ) [F.Additive]
    [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜] [HasZeroObject ℬ] [HasBinaryBiproducts ℬ] :
    F.mapHomotopyCategoryMinus.IsTriangulated := sorry

end Minus

namespace Bounded

/-- An additive functor carries the bounded homotopy object property into the bounded homotopy
object property. -/
@[stacks 014X "preservation of bounded homotopy objects"]
theorem mapsTo (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory.bounded 𝒜 ≤
      (HomotopyCategory.bounded ℬ).inverseImage
        (F.mapHomotopyCategory (up ℤ)) := sorry

/-- An additive functor sends bounded homotopy objects to bounded homotopy objects. -/
theorem obj_mem (F : 𝒜 ⥤ ℬ) [F.Additive]
    (X : HomotopyCategory.Bounded 𝒜) :
    HomotopyCategory.bounded ℬ ((F.mapHomotopyCategory (up ℤ)).obj X.obj) := sorry

end Bounded

/-- The functor between bounded homotopy categories induced by an additive functor. -/
@[stacks 014X "bounded homotopy functor"]
def _root_.CategoryTheory.Functor.mapHomotopyCategoryBounded (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory.Bounded 𝒜 ⥤ HomotopyCategory.Bounded ℬ :=
  ObjectProperty.FullSubcategory.restrict
    (F.mapHomotopyCategory (up ℤ)) (Bounded.mapsTo F)

namespace Bounded

/-- The bounded functor induced by an additive functor agrees with the ambient homotopy functor
after forgetting boundedness. -/
noncomputable def compInclusionIso (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.mapHomotopyCategoryBounded ⋙ (HomotopyCategory.bounded ℬ).ι ≅
      (HomotopyCategory.bounded 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ) :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (F.mapHomotopyCategory (up ℤ)) (mapsTo F)

/-- An isomorphism `F ⋙ G ≅ H` of additive functors induces the corresponding comparison
between the bounded homotopy functors. -/
noncomputable def compIso
    {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    {F : 𝒜 ⥤ ℬ} {G : ℬ ⥤ 𝒞} {H : 𝒜 ⥤ 𝒞} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] :
    F.mapHomotopyCategoryBounded ⋙ G.mapHomotopyCategoryBounded ≅
      H.mapHomotopyCategoryBounded :=
  (ObjectProperty.FullSubcategory.restrict.compIso
      (F.mapHomotopyCategory (up ℤ)) (G.mapHomotopyCategory (up ℤ))
      (mapsTo F) (mapsTo G)).symm ≪≫
    ObjectProperty.FullSubcategory.restrict.natIso
      (ObjectProperty.FullSubcategory.restrict.mapsToComp
        (mapsTo F) (mapsTo G))
      (mapsTo H) (Functor.mapHomotopyCategoryCompIso e (up ℤ))

/-- A full and faithful additive functor induces a full functor on bounded homotopy categories. -/
instance (F : 𝒜 ⥤ ℬ) [F.Additive] [Full F] [Faithful F] :
    Full F.mapHomotopyCategoryBounded := sorry

/-- A full and faithful additive functor induces a faithful functor on bounded homotopy
categories. -/
instance (F : 𝒜 ⥤ ℬ) [F.Additive] [Full F] [Faithful F] :
    Faithful F.mapHomotopyCategoryBounded := sorry

/-- The bounded homotopy functor induced by an additive functor is additive. -/
instance additive (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.mapHomotopyCategoryBounded.Additive := sorry

/-- The bounded homotopy functor induced by an additive functor commutes with shifts. -/
@[stacks 014X "bounded homotopy shift comparison"]
noncomputable instance commShift (F : 𝒜 ⥤ ℬ) [F.Additive] :
    F.mapHomotopyCategoryBounded.CommShift ℤ :=
  inferInstanceAs (((HomotopyCategory.bounded ℬ).lift
    ((HomotopyCategory.bounded 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ))
    (obj_mem F)).CommShift ℤ)

/-- The bounded homotopy functor induced by an additive functor is triangulated. -/
@[stacks 014X "exactness on bounded homotopy categories"]
instance isTriangulated (F : 𝒜 ⥤ ℬ) [F.Additive]
    [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜] [HasZeroObject ℬ] [HasBinaryBiproducts ℬ] :
    F.mapHomotopyCategoryBounded.IsTriangulated := sorry

end Bounded

end CategoryTheory.Functor.Homotopy


