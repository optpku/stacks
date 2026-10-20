/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Injective objects detected by a functor

This leaf provides the object property on a source category consisting of objects whose images
under a chosen functor are injective.  It is independent of graded or differential graded
models, and it includes the product closure used by graded-injective resolutions.
-/

@[expose] public section

open CategoryTheory.Limits

universe w vD vC uD uC

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- The object property consisting of objects whose image under `F` is injective. -/
@[stacks 0FSP "injective after applying a functor"]
abbrev isInjectiveObj (F : C ⥤ D) : ObjectProperty C :=
  ObjectProperty.inverseImage (isInjective D) F

/-- The typeclass form of membership in `F.isInjectiveObj`. -/
@[stacks 0FSP]
abbrev IsInjectiveObj (F : C ⥤ D) (X : C) : Prop :=
  (F.isInjectiveObj).Is X

/-- An object that is injective after applying `F` has an injective image. -/
instance instInjectiveOfIsInjectiveObj (F : C ⥤ D) (X : C)
    [F.IsInjectiveObj X] : Injective (F.obj X) :=
  sorry

/-- An injective image gives the corresponding source-side object-property instance. -/
instance instIsInjectiveObjOfInjective (F : C ⥤ D) (X : C)
    [Injective (F.obj X)] : F.IsInjectiveObj X :=
  sorry

/-- Membership in `F.isInjectiveObj` is exactly injectivity of the image object. -/
theorem isInjectiveObj_iff (F : C ⥤ D) (X : C) :
    F.IsInjectiveObj X ↔ Injective (F.obj X) := sorry

/-- A product is injective after applying `F` when `F` preserves that product and every factor
is injective after applying `F`. -/
@[stacks 0FSR]
instance instIsInjectiveObjProduct
    {ι : Type w} (F : C ⥤ D) (X : ι → C)
    [HasProduct X] [HasProduct (fun i ↦ F.obj (X i))]
    [PreservesLimit (Discrete.functor X) F]
    [∀ i, F.IsInjectiveObj (X i)] :
    F.IsInjectiveObj (∏ᶜ X) := sorry

end CategoryTheory.Functor
