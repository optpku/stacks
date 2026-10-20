/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.Topology.Algebra.Module.Closure

/-!
# Lemma 87.4.2

The topological closure of a submodule of a linearly topologized module is the
infimum of its sums with a fundamental system of open submodules.
-/

@[expose] public section

open scoped Topology Pointwise

universe u v w

namespace Submodule

variable {R : Type u} {M : Type v}
  [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]

variable {ι : Type w} {U : ι → Submodule R M}
variable (hU : (nhds (0 : M)).HasBasis (fun _ ↦ True) (fun i ↦ (U i : Set M)))
variable (N : Submodule R M)

/- Lemma 87.4.2: If `R` is a topological ring, `M` is a linearly topologized `R`-module,
and `U` is a fundamental system of open submodules of `M`, then the topological closure of a
submodule `N` equals `⨅ i, N + U i`. -/
@[stacks 0AMS] #check (Submodule.topologicalClosure_eq_iInf_add (R := R) (M := M)
    (U := U) hU N :
    N.topologicalClosure = ⨅ i, N + U i)

#check (Submodule.closure_eq_iInter_add (R := R) (M := M) (U := U) hU N :
    closure (N : Set M) = ⋂ i, (N : Set M) + (U i : Set M))

#check (Submodule.mem_topologicalClosure_iff_mem_add (R := R) (M := M) (U := U) hU N :
    ∀ {x : M}, x ∈ N.topologicalClosure ↔ ∀ i, x ∈ N + U i)

#check (Submodule.topologicalClosure_eq_iInf_open_add (R := R) (M := M) N :
    N.topologicalClosure = ⨅ (U : Submodule R M) (_ : IsOpen (U : Set M)), N + U)

end Submodule
