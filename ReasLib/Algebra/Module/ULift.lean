/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.ULift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear maps and equivalences across universe lifts

This leaf records the canonical transport of a linear map or linear equivalence through
independently chosen source and target `ULift`s.  It is independent of category-theoretic or
homological applications.
-/

@[expose] public section

noncomputable section

universe uR vM vN wM wN

namespace LinearMap

variable {R : Type uR} [Semiring R]
variable {M : Type vM} {N : Type vN}
variable [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- Lift a linear map with independently chosen source and target universe levels. -/
@[stacks 0G1X "universe lift of a linear map"]
def ulift (f : M →ₗ[R] N) : ULift.{wM} M →ₗ[R] ULift.{wN} N :=
  (ULift.moduleEquiv (R := R) (M := N)).symm.toLinearMap.comp
    (f.comp (ULift.moduleEquiv (R := R) (M := M)).toLinearMap)

/-- The lifted linear map evaluates by lifting the original map. -/
@[simp, stacks 0G1X "application of the universe lift of a linear map"]
theorem ulift_apply (f : M →ₗ[R] N) (x : ULift.{w} M) :
    f.ulift x = ULift.up (f x.down) := sorry

end LinearMap

namespace LinearEquiv

variable {R : Type uR} [Semiring R]
variable {M : Type vM} {N : Type vN}
variable [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- Lift a linear equivalence with independently chosen source and target universe levels. -/
@[stacks 0G1X "universe lift of a linear equivalence"]
def ulift (e : M ≃ₗ[R] N) : ULift.{wM} M ≃ₗ[R] ULift.{wN} N :=
  (ULift.moduleEquiv (R := R) (M := M)).trans
    (e.trans (ULift.moduleEquiv (R := R) (M := N)).symm)

/-- The forward application formula for a lifted linear equivalence. -/
@[simp, stacks 0G1X "forward application of a lifted linear equivalence"]
theorem ulift_apply (e : M ≃ₗ[R] N) (x : ULift.{w} M) :
    e.ulift x = ULift.up (e x.down) := sorry

/-- The inverse application formula for a lifted linear equivalence. -/
@[simp, stacks 0G1X "inverse application of a lifted linear equivalence"]
theorem ulift_symm_apply (e : M ≃ₗ[R] N) (y : ULift.{w} N) :
    e.ulift.symm y = ULift.up (e.symm y.down) := sorry

end LinearEquiv
