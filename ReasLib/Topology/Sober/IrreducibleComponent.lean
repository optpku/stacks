/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sober

/-!
# Generic points of irreducible components of a subset
-/

@[expose] public section

universe u

namespace IsGenericPoint

/-- A point `x` is a generic point of an irreducible component of a subset `T`. -/
def ofIrreducibleComponent {X : Type u} [TopologicalSpace X] (x : X) (T : Set X) : Prop :=
  ∃ hx : x ∈ T, (⟨x, hx⟩ : T) ∈ genericPoints T

/-- Membership in `ofIrreducibleComponent` unpacks as subspace membership in `genericPoints`. -/
theorem ofIrreducibleComponent_iff {X : Type u} [TopologicalSpace X] (x : X) (T : Set X) :
    ofIrreducibleComponent x T ↔
      ∃ hx : x ∈ T, (⟨x, hx⟩ : T) ∈ genericPoints T :=
  sorry

/-- A generic point of an irreducible component of `T` lies in `T`. -/
theorem mem_ofIrreducibleComponent {X : Type u} [TopologicalSpace X] {x : X} {T : Set X}
    (h : ofIrreducibleComponent x T) : x ∈ T :=
  sorry

end IsGenericPoint
