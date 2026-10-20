/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Algebra.LinearTopology.Completion

import StacksCheckRecall

/-!
# Lemma 87.4.3

Left-exactness of completion of linearly topologized modules along a submodule,
and identification of the completed submodule with the closure of its image.
-/

@[expose] public section

universe u v

/- Lemma 87.4.3
The left-exactness statement for completion along a submodule. -/
@[stacks 0ARZ]
#check (IsLinearTopology.exact_completion_subtype_mkQ :
  ∀ {R : Type u} {M : Type v}
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M),
    Function.Injective (IsLinearTopology.Completion.map_subtype N) ∧
      Function.Exact (IsLinearTopology.Completion.map_subtype N)
        (IsLinearTopology.Completion.map_mkQ N))

/- Lemma 87.4.3
The range of the completed inclusion is the closure of the original image. -/
@[stacks 0ARZ]
#check (IsLinearTopology.range_map_subtype_eq_topologicalClosure :
  ∀ {R : Type u} {M : Type v}
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M),
    LinearMap.range (IsLinearTopology.Completion.map_subtype N) =
      (N.map (IsLinearTopology.Completion.of :
        M →ₗ[R] IsLinearTopology.Completion R M)).topologicalClosure)
