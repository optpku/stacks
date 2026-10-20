/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Shrink

/-!
# Projectivity and Shrunken Linear Maps

This leaf records projectivity transport for kernels of the canonical
universe-shrunk form of a linear map.
-/

@[expose] public section

universe u v w z

namespace LinearMap

variable {R : Type u} [Semiring R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- A kernel is projective exactly when the kernel of its shrunken linear map is projective. -/
@[stacks 00OF "projective kernel transport after shrinking"]
theorem projective_ker_shrink_iff [Small.{z} M] [Small.{z} N] (f : M →ₗ[R] N) :
    Module.Projective R (LinearMap.ker (shrink f)) ↔ Module.Projective R (LinearMap.ker f) := sorry

end LinearMap
