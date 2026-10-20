/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Topology.Algebra.LinearTopology.Completion

/-!
# Lemma 87.4.4

Quotients of complete linearly topologized modules by closed submodules remain complete
when there is a countable fundamental system of neighbourhoods of `0`, and the canonical
quotient map is open.
-/

@[expose] public section

universe u v

open scoped Topology

/- Lemma 87.4.4: If `R` is a topological ring, `M` is a complete linearly topologized
`R`-module with a countable fundamental system of neighbourhoods of `0`, and `N` is a closed
submodule of `M`, then `M ⧸ N` is complete and the canonical quotient map `N.mkQ` is open. -/
@[stacks 0AMT] #check (IsLinearTopology.bijective_completion_of_quotient :
    ∀ {R : Type u} {M : Type v}
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M) [IsClosed (N : Set M)]
    (hcomplete : Function.Bijective
      (IsLinearTopology.Completion.of : M → IsLinearTopology.Completion R M))
    [(nhds (0 : M)).IsCountablyGenerated],
    Function.Bijective (IsLinearTopology.Completion.of :
      M ⧸ N → IsLinearTopology.Completion R (M ⧸ N)))

/- The canonical quotient map `N.mkQ : M → M ⧸ N` is open;
this holds whenever addition on `M` is continuous. -/
#check (Submodule.isOpenMap_mkQ :
    ∀ {R : Type u} {M : Type v} [Ring R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    (N : Submodule R M) [ContinuousAdd M], IsOpenMap N.mkQ)
