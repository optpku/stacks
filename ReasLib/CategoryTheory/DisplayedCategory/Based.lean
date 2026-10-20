/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.NatTrans
public import ReasLib.CategoryTheory.DisplayedCategory.Based.Total

/-!
# Based-category bridges for displayed data

Same-base displayed functors and arbitrary-base displayed functors over identity transformations can
be consumed by Mathlib's based-category API.  This leaf keeps those bridges separate from the
dependent definitions themselves.
-/

@[expose] public section

namespace CategoryTheory

universe v u v' u'

variable {C : Type u} [Category.{v} C]
variable {D E : DisplayedCategory C}
variable {Φ Ψ : DisplayedFunctor D E (𝟭 C)}

namespace DisplayedFunctor

/-- A same-base displayed functor induces a strict based functor on total categories. -/
def toBased {E : DisplayedCategory C} (Φ : DisplayedFunctor D E (𝟭 C)) :
    DisplayedCategory.Total.toBased D ⥤ᵇ DisplayedCategory.Total.toBased E where
  toFunctor := DisplayedFunctor.total Φ
  w := DisplayedFunctor.total_forget_id Φ

/-- The based bridge for a displayed functor over an arbitrary base functor. -/
def toBasedOver {C' : Type u'} [Category.{v'} C']
    {E : DisplayedCategory C'} {F : C ⥤ C'}
    (Φ : DisplayedFunctor D E F) :
    BasedCategory.ofFunctor (DisplayedCategory.Total.forget D ⋙ F) ⥤ᵇ
      DisplayedCategory.Total.toBased E where
  toFunctor := DisplayedFunctor.total Φ
  w := DisplayedFunctor.total_forget Φ

/-- The underlying functor of the general based bridge is the displayed totalization. -/
@[simp]
theorem toBasedOver_toFunctor {C' : Type u'} [Category.{v'} C']
    {E : DisplayedCategory C'} {F : C ⥤ C'}
    (Φ : DisplayedFunctor D E F) :
    (toBasedOver Φ).toFunctor = DisplayedFunctor.total Φ := rfl

/-- The identity-base based bridge has the displayed totalization as underlying functor. -/
@[simp]
theorem toBased_toFunctor (Φ : DisplayedFunctor D E (𝟭 C)) :
    (DisplayedFunctor.toBased Φ).toFunctor = DisplayedFunctor.total Φ := rfl

end DisplayedFunctor

namespace DisplayedNatTrans

/-- A displayed natural transformation over the identity of an arbitrary base functor becomes a
based natural transformation between the corresponding general based bridges.

The source based category is `BasedCategory.ofFunctor (DisplayedCategory.Total.forget D ⋙ F)`, so
this construction applies even when the displayed functors change the base category. -/
def toBasedOver
    {C' : Type u'} [Category.{v'} C']
    {E : DisplayedCategory C'} {F : C ⥤ C'}
    {Φ Ψ : DisplayedFunctor D E F}
    (η : DisplayedNatTrans Φ Ψ (𝟙 F)) :
    DisplayedFunctor.toBasedOver Φ ⟶ DisplayedFunctor.toBasedOver Ψ where
  toNatTrans := DisplayedNatTrans.total η
  isHomLift' := fun X => by
    change (DisplayedCategory.Total.forget E).IsHomLift
      (𝟙 (F.obj X.base)) ((DisplayedNatTrans.total η).app X)
    apply DisplayedCategory.Total.isHomLift_of_eq ((DisplayedNatTrans.total η).app X)
    simp

/-- The underlying natural transformation of the general based bridge is the displayed
totalization. -/
@[simp]
theorem toBasedOver_toNatTrans
    {C' : Type u'} [Category.{v'} C']
    {E : DisplayedCategory C'} {F : C ⥤ C'}
    {Φ Ψ : DisplayedFunctor D E F}
    (η : DisplayedNatTrans Φ Ψ (𝟙 F)) :
    (toBasedOver η).toNatTrans = DisplayedNatTrans.total η := rfl

/-- A component of the general based bridge computes to the totalized displayed component. -/
@[simp]
theorem toBasedOver_app
    {C' : Type u'} [Category.{v'} C']
    {E : DisplayedCategory C'} {F : C ⥤ C'}
    {Φ Ψ : DisplayedFunctor D E F}
    (η : DisplayedNatTrans Φ Ψ (𝟙 F)) (X : DisplayedCategory.Total D) :
    (toBasedOver η).toNatTrans.app X = (DisplayedNatTrans.total η).app X := rfl

/-- The base component of a general based-bridge component is an identity at the image base
object. -/
@[simp]
theorem toBasedOver_app_base
    {C' : Type u'} [Category.{v'} C']
    {E : DisplayedCategory C'} {F : C ⥤ C'}
    {Φ Ψ : DisplayedFunctor D E F}
    (η : DisplayedNatTrans Φ Ψ (𝟙 F)) (X : DisplayedCategory.Total D) :
    ((toBasedOver η).toNatTrans.app X).base = 𝟙 (F.obj X.base) := sorry

/-- The displayed component of a general based-bridge component is the source displayed
component. -/
@[simp]
theorem toBasedOver_app_displayed
    {C' : Type u'} [Category.{v'} C']
    {E : DisplayedCategory C'} {F : C ⥤ C'}
    {Φ Ψ : DisplayedFunctor D E F}
    (η : DisplayedNatTrans Φ Ψ (𝟙 F)) (X : DisplayedCategory.Total D) :
    ((toBasedOver η).toNatTrans.app X).displayed = η.app X.obj := sorry

/-- A displayed natural transformation over the identity base transformation becomes a based
natural transformation between the totalized displayed functors. -/
def toBased (η : DisplayedNatTrans Φ Ψ (𝟙 (𝟭 C))) :
    DisplayedFunctor.toBased Φ ⟶ DisplayedFunctor.toBased Ψ where
  toNatTrans := DisplayedNatTrans.total η
  isHomLift' := fun X => by
    change (DisplayedCategory.Total.forget E).IsHomLift
      (𝟙 X.base) ((DisplayedNatTrans.total η).app X)
    apply DisplayedCategory.Total.isHomLift_of_eq ((DisplayedNatTrans.total η).app X)
    simp

/-- The underlying natural transformation of `toBased` is the totalization of the displayed one. -/
@[simp]
theorem toBased_toNatTrans
    (η : DisplayedNatTrans Φ Ψ (𝟙 (𝟭 C))) :
    (toBased η).toNatTrans = DisplayedNatTrans.total η := rfl

/-- The component of `toBased` computes to the totalized displayed component. -/
@[simp]
theorem toBased_app
    (η : DisplayedNatTrans Φ Ψ (𝟙 (𝟭 C))) (X : DisplayedCategory.Total D) :
    (toBased η).toNatTrans.app X = (DisplayedNatTrans.total η).app X := rfl

/-- The base component of a based displayed-transformation component is an identity. -/
@[simp]
theorem toBased_app_base
    (η : DisplayedNatTrans Φ Ψ (𝟙 (𝟭 C))) (X : DisplayedCategory.Total D) :
    ((toBased η).toNatTrans.app X).base = 𝟙 X.base := sorry

/-- The displayed component of a based displayed-transformation component is the source
displayed component. -/
@[simp]
theorem toBased_app_displayed
    (η : DisplayedNatTrans Φ Ψ (𝟙 (𝟭 C))) (X : DisplayedCategory.Total D) :
    ((toBased η).toNatTrans.app X).displayed = η.app X.obj := sorry

end DisplayedNatTrans

end CategoryTheory
