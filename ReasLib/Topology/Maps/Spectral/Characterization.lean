/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Characterization of Spectral Maps

Mathlib's `IsSpectralMap` is the canonical predicate.  This module exposes the
source-facing conjunction as a rewrite-friendly characterization.
-/

@[expose] public section

universe u v

open Set TopologicalSpace

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y}

namespace IsSpectralMap

/-- Definition 5.23.1 (2): a map is spectral exactly when it is continuous and
pulls compact open subsets back to compact subsets. -/
@[stacks 08YG "spectral map characterization"]
theorem iff_continuous_and_isCompact_preimage_of_isOpen :
    IsSpectralMap f ↔
      Continuous f ∧
        ∀ ⦃U : Set Y⦄, IsOpen U → IsCompact U → IsCompact (f ⁻¹' U) := sorry

end IsSpectralMap
