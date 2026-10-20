/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Reflexivity relative to a module

This file defines bidual reflexivity with respect to an explicit target module.
-/

@[expose] public section

universe u v w

namespace Module

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C]
variable (M : Type w) [AddCommMonoid M] [Module R M]

/-- A module is reflexive relative to `C` when its canonical evaluation map
`M → Hom_R(Hom_R(M, C), C)` is bijective. -/
def IsReflexiveRelativeTo : Prop :=
  Function.Bijective
    (LinearMap.applyₗ (R := R) : M →ₗ[R] (M →ₗ[R] C) →ₗ[R] C)

/-- Relative reflexivity is equivalent to bijectivity of the canonical evaluation map. -/
theorem isReflexiveRelativeTo_iff :
    IsReflexiveRelativeTo R C M ↔
      Function.Bijective
        (LinearMap.applyₗ (R := R) : M →ₗ[R] (M →ₗ[R] C) →ₗ[R] C) :=
  Iff.rfl

end Module
