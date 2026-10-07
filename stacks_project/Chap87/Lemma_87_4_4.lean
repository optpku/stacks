module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_4_3_Completion

/-!
# Lemma 87.4.4

Quotients of complete linearly topologized modules by closed submodules remain complete
when there is a countable fundamental system of neighbourhoods of `0`, and the canonical
quotient map is open.
-/

@[expose] public section

universe u v

open scoped Topology

namespace IsLinearTopology

variable {R : Type u} {M : Type v}

/-- Lemma 87.4.4 (1): If `R` is a topological ring, `M` is a complete linearly topologized
`R`-module with a countable fundamental system of neighbourhoods of `0`, and `N` is a closed
submodule of `M`, then `M ⧸ N` is complete. -/
@[stacks 0AMT]
theorem bijective_completion_of_quotient
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M) [IsClosed (N : Set M)]
    (hcomplete : Function.Bijective (Completion.of : M → Completion R M))
    [(nhds (0 : M)).IsCountablyGenerated] :
    Function.Bijective (Completion.of : M ⧸ N → Completion R (M ⧸ N)) :=
  sorry

/-- Lemma 87.4.4 (2): If `R` is a topological ring, `M` is a complete linearly topologized
`R`-module with a countable fundamental system of neighbourhoods of `0`, and `N` is a closed
submodule of `M`, then the canonical map `N.mkQ : M → M ⧸ N` is open. -/
@[stacks 0AMT]
theorem isOpenMap_mkQ
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M) [IsClosed (N : Set M)]
    (hcomplete : Function.Bijective (Completion.of : M → Completion R M))
    [(nhds (0 : M)).IsCountablyGenerated] :
    IsOpenMap N.mkQ :=
  sorry

end IsLinearTopology
