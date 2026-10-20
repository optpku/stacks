/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# Chosen cocartesian lifts

Mathlib's chosen cartesian pullback arrow for the opposite functor gives a
canonical strongly cocartesian arrow after taking opposites.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.IsPreFibered.PullbackMap

variable {C : Type u₁} [Category.{v₁} C]
variable {F : Type u₂} [Category.{v₂} F]

/- The chosen cartesian arrow is transported to the opposite cocartesian arrow. -/
/-- The opposite of Mathlib's chosen cartesian pullback arrow is strongly cocartesian. -/
instance unopStronglyCocartesian
    (p : F ⥤ C) [IsFibered p.op] {x : F} {V : C} (f : p.obj x ⟶ V) :
    p.IsStronglyCocartesian f ((IsPreFibered.pullbackMap (p := p.op) rfl f.op).unop) :=
  sorry

end PullbackMap
end IsPreFibered
end Functor
end CategoryTheory
