/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.KrullDimension

@[expose] public section

universe u

namespace TopologicalSpace

/-- A subset has pure codimension `d` when each of its irreducible components has ambient
coheight `d`. -/
def HasPureCodimension {T : Type u} [TopologicalSpace T] (Z : Set T) (d : ℕ) : Prop :=
  ∀ W : IrreducibleCloseds T,
    Maximal (fun V : IrreducibleCloseds T ↦ (V : Set T) ⊆ Z) W →
      Order.coheight W = (d : ℕ∞)

/-- Pure codimension is equivalent to equality of the ambient coheight on every irreducible
component. -/
theorem hasPureCodimension_iff {T : Type u} [TopologicalSpace T] (Z : Set T) (d : ℕ) :
    HasPureCodimension Z d ↔
      ∀ W : IrreducibleCloseds T,
        Maximal (fun V : IrreducibleCloseds T ↦ (V : Set T) ⊆ Z) W →
          Order.coheight W = (d : ℕ∞) := sorry

end TopologicalSpace
