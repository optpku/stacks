/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Products of Spectral Spaces

The product instance belongs to the `SpectralSpace` owner and lets typeclass
search construct the standard product spectral structure directly.
-/

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

namespace SpectralSpace

/-- The product of two spectral spaces is spectral. -/
@[stacks 0907]
instance prod [SpectralSpace X] [SpectralSpace Y] : SpectralSpace (X × Y) := sorry

end SpectralSpace
