module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Topology on limits of module-valued diagrams

A diagram of modules has a canonical limit topology when every object is discrete.  The
construction depends only on the diagram and its limit; order-theoretic properties of a
particular indexing category belong in downstream inverse-system leaves.
-/

@[expose] public section

open CategoryTheory.Limits TopologicalSpace

noncomputable section

universe uD vD vM uR

namespace CategoryTheory.Functor

variable {D : Type uD} [Category.{vD} D]
variable {R : Type uR} [Ring R]

/-- The linear map underlying a canonical projection from the limit of a module-valued diagram. -/
abbrev limitProjectionLinearMap
    (F : D ⥤ ModuleCat.{vM} R) [HasLimit F] (j : D) :
    (limit F : ModuleCat.{vM} R) →ₗ[R] F.obj j :=
  (limit.π F j).hom

/-- The initial topology on a limit of modules whose diagram objects are discrete. -/
@[stacks 0GYM "limit topology of a module-valued diagram", implicit_reducible]
def limitTopology (F : D ⥤ ModuleCat.{vM} R) [HasLimit F] :
    TopologicalSpace (limit F : ModuleCat.{vM} R) :=
  ⨅ j : D, TopologicalSpace.induced (F.limitProjectionLinearMap j) ⊥

/-- Neighborhoods in the limit topology, without installing a local topology instance. -/
abbrev limitNhds (F : D ⥤ ModuleCat.{vM} R) [HasLimit F]
    (x : (limit F : ModuleCat.{vM} R)) : Filter (limit F : ModuleCat.{vM} R) :=
  @nhds (limit F : ModuleCat.{vM} R) (limitTopology F) x

/-- The kernel of a canonical projection from the limit of a module-valued diagram. -/
@[stacks 0GYM "projection kernel of a module-valued diagram"]
abbrev limitKernel (F : D ⥤ ModuleCat.{vM} R) [HasLimit F] (j : D) :
    Submodule R (limit F : ModuleCat.{vM} R) :=
  LinearMap.ker (F.limitProjectionLinearMap j)

/-- Membership in a projection kernel is equivalent to vanishing at that diagram object. -/
@[simp]
theorem mem_limitKernel_iff
    (F : D ⥤ ModuleCat.{vM} R) [HasLimit F] (j : D)
    (x : (limit F : ModuleCat.{vM} R)) :
    x ∈ F.limitKernel j ↔ F.limitProjectionLinearMap j x = 0 := sorry

end CategoryTheory.Functor
