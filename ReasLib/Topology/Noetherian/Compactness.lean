module

public import Mathlib.Topology.Constructible
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Compactness Consequences of Noetherianity

Subset-level compactness and retrocompactness consequences of Mathlib's
`TopologicalSpace.NoetherianSpace`.
-/

@[expose] public section

universe u

open Set

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 5.12.13: every subset of a Noetherian topological space is retrocompact. -/
@[stacks 04ZA "retrocompactness of subsets of Noetherian spaces"]
theorem NoetherianSpace.isRetrocompact [NoetherianSpace X] (s : Set X) :
    IsRetrocompact s := by
  intro U _ _
  exact NoetherianSpace.isCompact (s ∩ U)

end TopologicalSpace
