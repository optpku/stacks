module

public import ReasLib.Algebra.Category.ModuleCat.Topology.Limit
public import ReasLib.CategoryTheory.InverseSystem.OrderDual.ModuleCat.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Topology on limits of module inverse systems

An order-dual inverse system of modules has a canonical limit topology when every stage is
discrete. The topology and its neighborhood filters are explicit data, so downstream statements
do not need a local topological-space instance on the limit carrier.
-/

@[expose] public section

open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe uI vI uR

namespace CategoryTheory.OrderDualInverseSystem

variable {I : Type uI} [Preorder I]
variable {R : Type uR} [Ring R]

/-- The kernel of the canonical projection from an inverse limit to stage `i`. -/
@[stacks 0GYM "projection kernel in a module inverse limit"]
abbrev limitKernel (F : OrderDualInverseSystem I (ModuleCat.{vI} R)) [HasLimit F] (i : I) :
    Submodule R (limit F : ModuleCat.{vI} R) :=
  Functor.limitKernel F (OrderDual.toDual i)

/-- Membership in a projection kernel is equivalent to vanishing at that stage. -/
@[simp]
theorem mem_limitKernel_iff
    (F : OrderDualInverseSystem I (ModuleCat.{vI} R)) [HasLimit F] (i : I)
    (x : (limit F : ModuleCat.{vI} R)) :
    x ∈ F.limitKernel i ↔ F.limitProjectionLinearMap i x = 0 := sorry

/-- Projection kernels decrease as the stage index increases. -/
theorem limitKernel_antitone
    (F : OrderDualInverseSystem I (ModuleCat.{vI} R)) [HasLimit F] :
    Antitone F.limitKernel := sorry

/-- A later projection kernel is contained in every earlier projection kernel. -/
theorem limitKernel_le
    (F : OrderDualInverseSystem I (ModuleCat.{vI} R)) [HasLimit F]
    {i j : I} (hij : i ≤ j) :
    F.limitKernel j ≤ F.limitKernel i := sorry

/-- For a directed index semilattice, projection kernels form a basis of neighborhoods of zero in
the limit topology. -/
theorem limitNhds_zero_hasBasis_limitKernel
    {J : Type uI} [SemilatticeSup J] [Nonempty J]
    (F : OrderDualInverseSystem J (ModuleCat.{vI} R)) [HasLimit F] :
    (Functor.limitNhds F 0).HasBasis
      (fun _ : J ↦ True)
      (fun i ↦ (F.limitKernel i : Set (limit F : ModuleCat.{vI} R))) := sorry

end CategoryTheory.OrderDualInverseSystem
