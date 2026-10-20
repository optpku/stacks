module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Closure of submodules in linearly topologized modules
-/

@[expose] public section

open scoped Topology Pointwise

universe u v w

namespace Submodule

variable {R : Type u} {M : Type v}
  [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M]

/-- The closure of a submodule is the intersection of its sums with a neighborhood basis at zero. -/
theorem closure_eq_iInter_add {ι : Type w} {U : ι → Submodule R M}
    (hU : (nhds (0 : M)).HasBasis (fun _ ↦ True) (fun i ↦ (U i : Set M)))
    (N : Submodule R M) :
    closure (N : Set M) = ⋂ i, (N : Set M) + (U i : Set M) := sorry

variable [ContinuousConstSMul R M]

/-- The topological closure of a submodule is the infimum of its sums with a neighborhood basis at zero. -/
theorem topologicalClosure_eq_iInf_add {ι : Type w} {U : ι → Submodule R M}
    (hU : (nhds (0 : M)).HasBasis (fun _ ↦ True) (fun i ↦ (U i : Set M)))
    (N : Submodule R M) :
    N.topologicalClosure = ⨅ i, N + U i := sorry

/-- Membership in the topological closure of a submodule is equivalent to membership in every sum with a neighborhood basis element. -/
theorem mem_topologicalClosure_iff_mem_add {ι : Type w} {U : ι → Submodule R M}
    (hU : (nhds (0 : M)).HasBasis (fun _ ↦ True) (fun i ↦ (U i : Set M)))
    (N : Submodule R M) {x : M} :
    x ∈ N.topologicalClosure ↔ ∀ i, x ∈ N + U i := sorry

variable [IsLinearTopology R M]

/-- The topological closure of a submodule is the infimum of its sums with all open submodules. -/
theorem topologicalClosure_eq_iInf_open_add (N : Submodule R M) :
    N.topologicalClosure = ⨅ (U : Submodule R M) (_ : IsOpen (U : Set M)), N + U := sorry

end Submodule
