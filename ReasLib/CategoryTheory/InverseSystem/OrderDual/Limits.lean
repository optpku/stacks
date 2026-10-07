module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Preorder

/-!
# Limits of Order-Dual Inverse Systems

This leaf records the formal compatibility between a limit cone and the transition maps of a
diagram indexed by `OrderDual I`.  It is independent of the index-specific structure of `I` and
of any additive realization of the target category.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe uI vI uA vA

namespace CategoryTheory.OrderDualInverseSystem

variable {I : Type uI} [Preorder I]
variable {A : Type uA} [Category.{vA} A]

/-- A limit projection to stage `j`, followed by the transition from `j` to `i`, is the limit
projection to stage `i`. -/
theorem limitProjection_comp_transitionMap (F : OrderDualInverseSystem I A) [HasLimit F]
    {i j : I} (hij : i ≤ j) :
    limit.π F (OrderDual.toDual j) ≫ F.transitionMap hij =
      limit.π F (OrderDual.toDual i) := sorry

end CategoryTheory.OrderDualInverseSystem
