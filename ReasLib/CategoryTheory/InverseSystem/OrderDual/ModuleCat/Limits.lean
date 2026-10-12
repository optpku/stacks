/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.OrderDual.Limits
public import ReasLib.CategoryTheory.InverseSystem.OrderDual.ModuleCat

/-!
# Limits of Order-Dual Module Inverse Systems

This leaf presents the canonical projections from a limit of an `OrderDual`-indexed module
inverse system as linear maps, together with their transition compatibility.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe uI vI uR

namespace CategoryTheory.OrderDualInverseSystem

variable {I : Type uI} [Preorder I]
variable {R : Type uR} [Ring R]

/-- The linear map underlying the canonical projection from the limit to a stage of an
`OrderDual`-indexed module inverse system. -/
abbrev limitProjectionLinearMap (F : OrderDualInverseSystem I (ModuleCat.{vI} R)) [HasLimit F]
    (i : I) :
    (limit F : ModuleCat.{vI} R) →ₗ[R] F.obj (OrderDual.toDual i) :=
  (limit.π F (OrderDual.toDual i)).hom

/-- The linear limit projection to a later stage followed by a transition is the earlier linear
limit projection. -/
theorem limitProjectionLinearMap_comp_transitionLinearMap
    (F : OrderDualInverseSystem I (ModuleCat.{vI} R)) [HasLimit F]
    {i j : I} (hij : i ≤ j) :
    (F.transitionLinearMap hij).comp (F.limitProjectionLinearMap j) =
      F.limitProjectionLinearMap i := sorry

end CategoryTheory.OrderDualInverseSystem
