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

/-- A subset has pure codimension `d` when the ambient closures of its irreducible
components have coheight `d`. -/
def HasPureCodimension {T : Type u} [TopologicalSpace T] (Z : Set T) (d : ℕ) : Prop :=
  ∀ W : Set T,
    (hW : Maximal (fun V : Set T ↦ IsIrreducible V ∧ V ⊆ Z) W) →
      Order.coheight (⟨closure W, IsIrreducible.closure hW.1.1,
        isClosed_closure⟩ : IrreducibleCloseds T) = (d : ℕ∞)

/-- Pure codimension is equivalent to equality of the ambient coheight on every
irreducible component of the subset. -/
theorem hasPureCodimension_iff {T : Type u} [TopologicalSpace T] (Z : Set T) (d : ℕ) :
    HasPureCodimension Z d ↔
      ∀ W : Set T,
        (hW : Maximal (fun V : Set T ↦ IsIrreducible V ∧ V ⊆ Z) W) →
          Order.coheight (⟨closure W, IsIrreducible.closure hW.1.1,
            isClosed_closure⟩ : IrreducibleCloseds T) = (d : ℕ∞) := sorry

end TopologicalSpace
