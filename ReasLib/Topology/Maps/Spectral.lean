/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Constructible
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Maps.Spectral.Characterization

/-!
# Ranges of Spectral Maps

Range and image consequences of Mathlib's `IsSpectralMap` predicate.
-/

@[expose] public section

universe u v

open Set Topology TopologicalSpace

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

namespace IsSpectralMap

/-- Lemma 5.12.7 (2): the range of a spectral map is retrocompact. -/
@[stacks 04Z9 "ranges of quasi-compact maps are retrocompact"]
theorem isRetrocompact_range (hf : IsSpectralMap f) :
    IsRetrocompact (range f) := sorry

end IsSpectralMap
