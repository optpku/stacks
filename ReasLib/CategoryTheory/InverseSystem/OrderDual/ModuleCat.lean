/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Preorder

/-!
# Linear Maps in Order-Dual Module Inverse Systems

This leaf presents the underlying linear maps of the transition morphisms of an
`OrderDual`-indexed inverse system of modules.  It avoids repeatedly exposing the categorical
implementation detail `.hom` in module arguments.
-/

@[expose] public section

open CategoryTheory

universe uI vI uR

namespace CategoryTheory.OrderDualInverseSystem

variable {I : Type uI} [Preorder I]
variable {R : Type uR} [Ring R]

/-- The underlying linear map of the transition from stage `j` to stage `i` in an
`OrderDual`-indexed inverse system of `R`-modules. -/
abbrev transitionLinearMap (F : OrderDualInverseSystem I (ModuleCat.{vI} R))
    {i j : I} (hij : i ≤ j) :
    F.obj (OrderDual.toDual j) →ₗ[R] F.obj (OrderDual.toDual i) :=
  (OrderDualInverseSystem.transitionMap F hij).hom

/-- Underlying linear transition maps compose through every intermediate stage. -/
theorem transitionLinearMap_comp (F : OrderDualInverseSystem I (ModuleCat.{vI} R))
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionLinearMap (le_trans hij hjk) =
      (F.transitionLinearMap hij).comp (F.transitionLinearMap hjk) := sorry

/-- The reflexive underlying linear transition map is the identity. -/
@[simp]
theorem transitionLinearMap_refl (F : OrderDualInverseSystem I (ModuleCat.{vI} R)) (i : I) :
    F.transitionLinearMap (le_refl i) =
      (LinearMap.id : F.obj (OrderDual.toDual i) →ₗ[R] F.obj (OrderDual.toDual i)) := sorry

end CategoryTheory.OrderDualInverseSystem
