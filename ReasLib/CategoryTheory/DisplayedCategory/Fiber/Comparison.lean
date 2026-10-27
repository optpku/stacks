/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.HasFibers

/-!
# Comparison of displayed and strict fibers

This leaf connects the intrinsic displayed fiber with Mathlib's strict `Functor.Fiber`.  The
intrinsic category itself remains available from `DisplayedCategory.Fiber` without importing this
comparison layer.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace DisplayedCategory.Fiber

/-- The canonical functor from the intrinsic displayed fiber to Mathlib's strict fiber. -/
def toFunctorFiber (D : DisplayedCategory C) (X : C) :
    Fiber D X ⥤ Functor.Fiber (DisplayedCategory.Total.forget D) X :=
  Functor.Fiber.inducedFunctor (inclusion_comp_forget D X)

namespace toFunctorFiber

/-- The underlying total object of a `toFunctorFiber` image. -/
@[simp]
theorem obj_val (D : DisplayedCategory C) (X : C) (x : Fiber D X) :
    ((toFunctorFiber D X).obj x).1 =
      (⟨X, x⟩ : DisplayedCategory.Total D) := sorry

/-- The base equality carried by a `toFunctorFiber` object is canonical. -/
@[simp]
theorem obj_base (D : DisplayedCategory C) (X : C) (x : Fiber D X) :
    (DisplayedCategory.Total.forget D).obj ((toFunctorFiber D X).obj x).1 = X := sorry

/-- The underlying total morphism of a `toFunctorFiber` image. -/
@[simp]
theorem map_val {D : DisplayedCategory C} (X : C)
    {x y : Fiber D X} (f : x ⟶ y) :
    ((toFunctorFiber D X).map f).1 =
      (inclusion D X).map f := sorry

end toFunctorFiber

/-- Recover the displayed object and morphism from a strict-fiber object and morphism.

The stored base equalities transport both endpoints to `X`; the hom-lift certificate then
identifies the stored base arrow with `𝟙 X`.  No choice of a preimage is needed. -/
def fromFunctorFiber (D : DisplayedCategory C) (X : C) :
    Functor.Fiber (DisplayedCategory.Total.forget D) X ⥤ Fiber D X where
  obj a := DisplayedCategory.Obj.cast D a.2 a.1.obj
  map {a b} f := by
    rcases a with ⟨⟨A, a⟩, ha⟩
    rcases b with ⟨⟨B, b⟩, hb⟩
    change A = X at ha
    change B = X at hb
    cases ha
    cases hb
    exact DisplayedCategory.Hom.cast D
      (@IsHomLift.eq_of_isHomLift C (DisplayedCategory.Total D) _ _
        (DisplayedCategory.Total.forget D) ⟨X, a⟩ ⟨X, b⟩ (𝟙 X) f.1 f.2).symm
      f.1.displayed
  map_id a := by
    rcases a with ⟨⟨A, a⟩, h⟩
    change A = X at h
    cases h
    rfl
  map_comp := by
    intros
    sorry

/-- The inverse comparison transports the stored displayed object along its base equality. -/
@[simp]
theorem fromFunctorFiber_obj (D : DisplayedCategory C) (X : C)
    (a : Functor.Fiber (DisplayedCategory.Total.forget D) X) :
    (fromFunctorFiber D X).obj a = DisplayedCategory.Obj.cast D a.2 a.1.obj := rfl

/-- Recovering a morphism after the canonical comparison returns that morphism. -/
@[simp]
theorem fromFunctorFiber_map_toFunctorFiber {D : DisplayedCategory C} (X : C)
    {x y : Fiber D X} (f : x ⟶ y) :
    (fromFunctorFiber D X).map ((toFunctorFiber D X).map f) = f := rfl

/-- The strict-fiber object is recovered after transporting its displayed component. -/
@[simp]
theorem toFunctorFiber_obj_fromFunctorFiber (D : DisplayedCategory C) (X : C)
    (a : Functor.Fiber (DisplayedCategory.Total.forget D) X) :
    (toFunctorFiber D X).obj ((fromFunctorFiber D X).obj a) = a := by
  rcases a with ⟨⟨A, a⟩, h⟩
  change A = X at h
  cases h
  rfl

/-- The explicit categorical equivalence between the intrinsic displayed fiber and Mathlib's
strict fiber of the total-category projection.  Its inverse is equality transport, and its unit
and counit are the corresponding identity isomorphisms. -/
def equivalence (D : DisplayedCategory C) (X : C) :
    Fiber D X ≌ Functor.Fiber (DisplayedCategory.Total.forget D) X where
  functor := toFunctorFiber D X
  inverse := fromFunctorFiber D X
  unitIso := NatIso.ofComponents (fun x => Iso.refl x) (by
    intro x y f
    change f ≫ 𝟙 y = 𝟙 x ≫ f
    simp only [Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents
    (fun a => eqToIso (toFunctorFiber_obj_fromFunctorFiber D X a)) (by
      intros
      sorry)
  functor_unitIso_comp := by
    intros
    sorry

/-- The canonical displayed-fiber comparison is an equivalence. -/
theorem isEquivalence (D : DisplayedCategory C) (X : C) :
    (toFunctorFiber D X).IsEquivalence :=
  (equivalence D X).isEquivalence_functor

attribute [instance] isEquivalence

/-- The functor of `equivalence` is the canonical displayed-fiber comparison. -/
@[simp]
theorem equivalence_functor (D : DisplayedCategory C) (X : C) :
    (equivalence D X).functor = toFunctorFiber D X := rfl

/-- The inverse of `equivalence` is the explicit equality-transport comparison. -/
@[simp]
theorem equivalence_inverse (D : DisplayedCategory C) (X : C) :
    (equivalence D X).inverse = fromFunctorFiber D X := rfl

/-- The intrinsic displayed fibers form the canonical `HasFibers` structure on the total-category
projection. -/
instance hasFibers (D : DisplayedCategory C) :
    HasFibers (DisplayedCategory.Total.forget D) where
  Fib X := Fiber D X
  category X := category D X
  ι X := inclusion D X
  comp_const X := inclusion_comp_forget D X
  equiv X := isEquivalence D X

end DisplayedCategory.Fiber

end CategoryTheory
