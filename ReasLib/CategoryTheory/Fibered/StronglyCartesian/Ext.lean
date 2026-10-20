/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Extensionality for morphisms via strongly cartesian postcomposition

The most common proof pattern in fibered-category arguments is: "Two morphisms with a common
codomain are equal because they agree after postcomposition with a strongly cartesian arrow."

This file provides the choice-free fiber-level API for this pattern. Specializations to a
chosen cleavage belong to the cleavage layer.

## Main declarations

* `Functor.IsStronglyCartesian.ext_fiber` — fiber morphisms equal iff postcomposites equal
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable {p : S ⥤ C}

namespace Functor.IsStronglyCartesian

/-- Two morphisms in the fiber over `V` with common source and target are equal when their
underlying total-category morphisms agree after postcomposition with a strongly cartesian
arrow. This is a direct wrapper around `IsStronglyCartesian.ext` specialized to the
fiber-morphism use case (both morphisms lift `𝟙 V`). -/
theorem ext_fiber {U V : C} {f : V ⟶ U}
    {x y : p.Fiber V} {z : S}
    {cart : y.1 ⟶ z} [p.IsStronglyCartesian f cart]
    (g h : x ⟶ y)
    (heq : g.1 ≫ cart = h.1 ≫ cart) :
    g = h := sorry

/-- Explicit-proof bridge for strongly-cartesian postcomposition extensionality in a fiber. -/
theorem ext_fiber.explicit {U V : C} {f : V ⟶ U}
    {x y : p.Fiber V} {z : S} {cart : y.1 ⟶ z}
    (hcart : p.IsStronglyCartesian f cart) (g h : x ⟶ y)
    (heq : g.1 ≫ cart = h.1 ≫ cart) :
    g = h := sorry

end Functor.IsStronglyCartesian

end CategoryTheory
