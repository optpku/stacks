/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Positive.Limits
public import ReasLib.CategoryTheory.InverseSystem.Positive.ModuleCat
public import ReasLib.CategoryTheory.InverseSystem.OrderDual.ModuleCat.Limits

/-!
# Limits of Positive Module Inverse Systems

This leaf specializes the generic order-dual linear limit compatibility to the positive-natural
successor map.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.PNatInverseSystem

variable {R : Type u} [Ring R]

/-- The linear map underlying the canonical projection from the limit of a positive inverse system
to its stage `n`. -/
abbrev limitProjectionLinearMap (F : PNatInverseSystem (ModuleCat.{v} R)) [HasLimit F]
    (n : ℕ+) :
    (limit F : ModuleCat.{v} R) →ₗ[R] F.stage n :=
  OrderDualInverseSystem.limitProjectionLinearMap F n

/-- The linear limit projection to the successor stage followed by the successor transition is
the current-stage linear limit projection. -/
theorem limitProjectionLinearMap_comp_stepLinearMap
    (F : PNatInverseSystem (ModuleCat.{v} R)) [HasLimit F] (n : ℕ+) :
    (F.stepLinearMap n).comp (F.limitProjectionLinearMap (n + 1)) =
      F.limitProjectionLinearMap n := sorry

/-- Surjectivity of all successor linear maps makes every canonical limit projection surjective. -/
theorem limitProjectionLinearMap_surjective_of_stepLinearMap_surjective
    (F : PNatInverseSystem (ModuleCat.{v} R)) [HasLimit F]
    (h_step : ∀ n : ℕ+, Function.Surjective (F.stepLinearMap n))
    (n : ℕ+) :
    Function.Surjective (F.limitProjectionLinearMap n) := sorry

end CategoryTheory.PNatInverseSystem
