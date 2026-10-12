/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.LocallyFinite

/-!
# Refinements of locally finite families

This file records local-finiteness results for families obtained by refining the members of
another locally finite family.
-/

@[expose] public section

universe u v w

/-- A dependent family obtained by locally finite refinements of the members of a locally finite
family is locally finite when every refined set lies in its parent. -/
theorem LocallyFinite.sigma_of_subset {Y : Type u} [TopologicalSpace Y]
    {I : Type v} {J : I → Type w} {T : I → Set Y} {W : (i : I) → J i → Set Y}
    (hT : LocallyFinite T) (hW : ∀ i, LocallyFinite (W i))
    (hWT : ∀ i j, W i j ⊆ T i) :
    LocallyFinite (fun p : Σ i, J i ↦ W p.1 p.2) := sorry
