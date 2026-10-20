/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Injective

namespace Module.Injective

universe u v w

/-- An arbitrary dependent product of injective modules over a ring is injective. -/
public theorem product (R : Type u) [Ring R] {ι : Type w} (M : ι → Type v) [Small.{v} R]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Injective R (M i)] :
    Module.Injective R ((i : ι) → M i) :=
  Module.Injective.pi R M

end Module.Injective
