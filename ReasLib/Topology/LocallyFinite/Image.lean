/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Topology.Spectral.Prespectral

@[expose] public section

open Set

universe u v w

namespace LocallyFinite

/-- A spectral map into a prespectral space sends a locally finite family of sets to a
locally finite family of direct images. -/
theorem image_of_isSpectralMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [PrespectralSpace Y] {I : Type w} {f : X → Y} {s : I → Set X}
    (hf : IsSpectralMap f) (hs : LocallyFinite s) :
    LocallyFinite (fun i ↦ f '' s i) := sorry

end LocallyFinite
