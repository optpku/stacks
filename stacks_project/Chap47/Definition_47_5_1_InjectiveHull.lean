/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Injective.Hull

@[expose] public section

universe u v w

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  {I : Type w} [AddCommGroup I] [Module R I] [Module.Injective R I]

#check (LinearMap.IsInjectiveHull : (M →ₗ[R] I) → Prop)
