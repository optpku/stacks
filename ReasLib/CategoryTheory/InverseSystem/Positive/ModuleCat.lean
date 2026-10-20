/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Positive
public import ReasLib.CategoryTheory.InverseSystem.OrderDual.ModuleCat

/-!
# Linear Maps in Positive Module Inverse Systems

This leaf specializes the generic order-dual module inverse-system API to the positive-natural
successor map.  It provides the corresponding underlying linear map and its factorization law.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.PNatInverseSystem

variable {R : Type u} [Ring R]

/-- The underlying linear map of the successor transition in a positive module inverse system. -/
abbrev stepLinearMap (F : PNatInverseSystem (ModuleCat.{v} R)) (n : ℕ+) :
    F.stage (n + 1) →ₗ[R] F.stage n :=
  (F.stepMap n).hom

/-- A long underlying linear transition factors through its final successor transition. -/
theorem transitionLinearMap_succ_factor (F : PNatInverseSystem (ModuleCat.{v} R))
    {i j : ℕ+} (hij : i ≤ j) :
    OrderDualInverseSystem.transitionLinearMap F (hij.trans (PNat.lt_succ_self j).le) =
      (OrderDualInverseSystem.transitionLinearMap F hij).comp (F.stepLinearMap j) := sorry

/-- Successivity of the positive stages makes every transition linear map surjective. -/
theorem transitionLinearMap_surjective_of_stepLinearMap_surjective
    (F : PNatInverseSystem (ModuleCat.{v} R))
    (h_step : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    {i j : ℕ+} (hij : i ≤ j) :
    Function.Surjective (OrderDualInverseSystem.transitionLinearMap F hij) := sorry

end CategoryTheory.PNatInverseSystem
