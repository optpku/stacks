/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_4_3
public import stacks_project.Chap87.Lemma_87_4_3_Completion
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

namespace IsLinearTopology

variable {R : Type u} {M : Type v}
variable [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
variable [AddCommGroup M] [Module R M] [TopologicalSpace M]
variable [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]

/-- Lemma 87.4.5 (1): If `R` is a topological ring, `M` is a linearly topologized
`R`-module with a countable fundamental system of neighbourhoods of `0`, and `N`
is a submodule of `M`, then
`0 → Completion R N → Completion R M → Completion R (M ⧸ N) → 0` is exact. -/
@[stacks 0AS0]
theorem shortExact_completion_subtype_mkQ (N : Submodule R M)
    [(nhds (0 : M)).IsCountablyGenerated] :
    Function.Injective (Completion.map_subtype N) ∧
      Function.Exact (Completion.map_subtype N) (Completion.map_mkQ N) ∧
      Function.Surjective (Completion.map_mkQ N) :=
  sorry

/- Lemma 87.4.5 (2): If `R` is a topological ring, `M` is a linearly topologized
`R`-module, and `N` is a submodule of `M`, then `Completion R N` is the closure
of the image of `N → Completion R M`. -/
@[stacks 0AS0] #check range_map_subtype_eq_topologicalClosure

/-- Lemma 87.4.5 (3): If `R` is a topological ring, `M` is a linearly topologized
`R`-module with a countable fundamental system of neighbourhoods of `0`, and `N`
is a submodule of `M`, then `Completion.map_mkQ N : Completion R M → Completion R (M ⧸ N)`
is open. -/
@[stacks 0AS0]
theorem isOpenMap_map_mkQ (N : Submodule R M)
    [(nhds (0 : M)).IsCountablyGenerated] :
    IsOpenMap (Completion.map_mkQ N) :=
  sorry

/-- The completed quotient map is surjective when `M` has a countable fundamental
system of neighbourhoods of `0`. -/
theorem surjective_map_mkQ (N : Submodule R M)
    [(nhds (0 : M)).IsCountablyGenerated] :
    Function.Surjective (Completion.map_mkQ N) :=
  sorry

end IsLinearTopology
