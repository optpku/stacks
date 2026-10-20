module

public import ReasLib.Topology.Algebra.LinearTopology.Completion
import StacksCheckRecall

/-!
# Lemma 87.4.5

Exactness of the completed sequence along a submodule of a linearly topologized
module with a countable neighbourhood basis of `0`, identification of the
completed submodule with the closure of its image, and openness of the completed
quotient map.
-/

@[expose] public section

universe u v

open scoped Topology

/- Lemma 87.4.5 (1): If `R` is a topological ring, `M` is a linearly topologized
`R`-module with a countable fundamental system of neighbourhoods of `0`, and `N`
is a submodule of `M`, then
`0 → Completion R N → Completion R M → Completion R (M ⧸ N) → 0` is exact. -/
@[stacks 0AS0]
#check (IsLinearTopology.shortExact_completion_subtype_mkQ :
  ∀ {R : Type u} {M : Type v}
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M) [(nhds (0 : M)).IsCountablyGenerated],
    Function.Injective (IsLinearTopology.Completion.map_subtype N) ∧
      Function.Exact (IsLinearTopology.Completion.map_subtype N)
        (IsLinearTopology.Completion.map_mkQ N) ∧
      Function.Surjective (IsLinearTopology.Completion.map_mkQ N))

/- Lemma 87.4.5 (2): If `R` is a topological ring, `M` is a linearly topologized
`R`-module, and `N` is a submodule of `M`, then `Completion R N` is the closure
of the image of `N → Completion R M`. -/
@[stacks 0AS0]
#check (IsLinearTopology.range_map_subtype_eq_topologicalClosure :
  ∀ {R : Type u} {M : Type v}
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M),
    LinearMap.range (IsLinearTopology.Completion.map_subtype N) =
      (N.map (IsLinearTopology.Completion.of :
        M →ₗ[R] IsLinearTopology.Completion R M)).topologicalClosure)

/- Lemma 87.4.5 (3): If `R` is a topological ring, `M` is a linearly topologized
`R`-module with a countable fundamental system of neighbourhoods of `0`, and `N`
is a submodule of `M`, then `Completion.map_mkQ N : Completion R M → Completion R (M ⧸ N)`
is open. -/
@[stacks 0AS0]
#check (IsLinearTopology.isOpenMap_map_mkQ :
  ∀ {R : Type u} {M : Type v}
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M) [(nhds (0 : M)).IsCountablyGenerated],
    IsOpenMap (IsLinearTopology.Completion.map_mkQ N))
