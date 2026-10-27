/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Presheaf.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Vanishing of presheaves on a class of objects

A presheaf vanishes on a predicate when its value at each object satisfying
that predicate is a zero object in the coefficient category.
-/

@[expose] public section

universe uC vC uA vA

namespace CategoryTheory.PresheafWithValues

open Limits

variable {C : Type uC} [Category.{vC} C] {A : Type uA} [Category.{vA} A]

/-- The object property of presheaves whose values are zero on every object
satisfying `P`. -/
def vanishesOn (P : C → Prop) : ObjectProperty (PresheafWithValues C A) :=
  fun F ↦ ∀ x, P x → IsZero (F.obj (Opposite.op x))

/-- A presheaf vanishes on `P` exactly when its value at every `P`-object is zero. -/
theorem vanishesOn_iff (P : C → Prop) (F : PresheafWithValues C A) :
    vanishesOn P F ↔ ∀ x, P x → IsZero (F.obj (Opposite.op x)) :=
  Iff.rfl

/-- A presheaf vanishing on `P` has zero value at any specified `P`-object. -/
theorem vanishesOn.isZero {P : C → Prop} {F : PresheafWithValues C A}
    (hF : vanishesOn P F) {x : C} (hx : P x) :
    IsZero (F.obj (Opposite.op x)) :=
  hF x hx

end CategoryTheory.PresheafWithValues
