/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.GDelta.Basic

/-!
# Nowhere Dense Sets and Subspaces

Transport from a subtype to the ambient space is stated without an unnecessary
openness hypothesis on the subtype.
-/

@[expose] public section

universe u

open Set

variable {X : Type u} [TopologicalSpace X]

namespace IsNowhereDense

/-- A subset of an ambient space is nowhere dense when its trace is nowhere
dense in a containing subtype. -/
theorem of_subtypeVal {U T : Set X}
    (hT : IsNowhereDense (Subtype.val ⁻¹' T : Set U)) (hTU : T ⊆ U) :
    IsNowhereDense T := by
  have h := hT.image_val
  rw [image_preimage_eq_inter_range, Subtype.range_val, inter_eq_left.mpr hTU] at h
  exact h

end IsNowhereDense
