/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locality of Nowhere Denseness

The canonical `IsOpenCover` owner packages the open-cover locality criterion.
-/

@[expose] public section

universe u v

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace.IsOpenCover

/-- Lemma 5.21.4: a subset is nowhere dense if and only if its trace on every
member of an open cover is nowhere dense. -/
@[stacks 03HP]
theorem isNowhereDense_iff_preimage
    {ι : Type v} {U : ι → Opens X} (hU : IsOpenCover U) {T : Set X} :
    IsNowhereDense T ↔ ∀ i, IsNowhereDense (Subtype.val ⁻¹' T : Set (U i)) := sorry

end TopologicalSpace.IsOpenCover
