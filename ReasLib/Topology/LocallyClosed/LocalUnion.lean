/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.LocallyClosed.Union.Basic

/-!
# Locally Unions of Locally Closed Subsets

This leaf localizes the arbitrary locally-closed-union predicate on the
ambient space, without conflating it with Mathlib's locally constructible
predicate.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 5.18.5: a subset is locally a union of locally closed subsets when
every ambient point has an open neighborhood with that property. -/
@[stacks 005X]
def IsLocallyUnionOfLocallyClosed (T : Set X) : Prop :=
  ∀ x, ∃ U ∈ 𝓝 x, IsOpen U ∧ IsUnionOfLocallyClosed (U ↓∩ T)

/-- The defining neighborhood condition for a locally union-of-locally-closed
subset. -/
@[stacks 005X]
theorem isLocallyUnionOfLocallyClosed_iff {T : Set X} :
    IsLocallyUnionOfLocallyClosed T ↔
      ∀ x, ∃ U ∈ 𝓝 x, IsOpen U ∧ IsUnionOfLocallyClosed (U ↓∩ T) := sorry

namespace IsLocallyUnionOfLocallyClosed

/-- A locally union-of-locally-closed presentation supplies the corresponding
neighborhood at each ambient point. -/
theorem exists_mem_nhds {T : Set X} (hT : IsLocallyUnionOfLocallyClosed T) (x : X) :
    ∃ U ∈ 𝓝 x, IsOpen U ∧ IsUnionOfLocallyClosed (U ↓∩ T) := sorry

end IsLocallyUnionOfLocallyClosed

/-- A locally closed subset is locally a union of locally closed subsets. -/
theorem IsLocallyClosed.isLocallyUnionOfLocallyClosed {T : Set X} (hT : IsLocallyClosed T) :
    IsLocallyUnionOfLocallyClosed T := sorry

/-- An arbitrary union of locally closed subsets is locally a union of locally
closed subsets. -/
theorem IsUnionOfLocallyClosed.isLocallyUnionOfLocallyClosed {T : Set X}
    (hT : IsUnionOfLocallyClosed T) : IsLocallyUnionOfLocallyClosed T := sorry
