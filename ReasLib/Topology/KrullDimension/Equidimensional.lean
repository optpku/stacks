/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Equidimensional topological spaces

This module owns equidimensionality formulated through the canonical family of irreducible
components and their topological Krull dimensions.
-/

@[expose] public section

universe u v

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace

/-- A space is equidimensional when all of its irreducible components have the same topological
Krull dimension. -/
@[stacks 0058]
class EquidimensionalSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- Any two irreducible components have equal topological Krull dimension. -/
  topologicalKrullDim_eq (Z₁ Z₂ : irreducibleComponents X) :
    topologicalKrullDim Z₁ = topologicalKrullDim Z₂

/-- The defining componentwise constancy condition for equidimensionality. -/
theorem equidimensionalSpace_iff :
    EquidimensionalSpace X ↔
      ∀ Z₁ Z₂ : irreducibleComponents X,
        topologicalKrullDim Z₁ = topologicalKrullDim Z₂ := sorry

/-- A chosen common dimension for every irreducible component gives an equidimensional space. -/
theorem EquidimensionalSpace.of_forall_topologicalKrullDim_eq
    {d : WithBot ℕ∞} (h : ∀ Z : irreducibleComponents X, topologicalKrullDim Z = d) :
    EquidimensionalSpace X := sorry

/-- Equidimensionality is invariant under homeomorphism. -/
theorem _root_.Homeomorph.equidimensionalSpace_iff
    {Y : Type v} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    EquidimensionalSpace X ↔ EquidimensionalSpace Y := sorry

/-- In an equidimensional space, irreducible components viewed as subsets have equal topological
Krull dimension. -/
theorem topologicalKrullDim_eq_of_mem_irreducibleComponents [EquidimensionalSpace X]
    {Z₁ Z₂ : Set X} (hZ₁ : Z₁ ∈ irreducibleComponents X) (hZ₂ : Z₂ ∈ irreducibleComponents X) :
    topologicalKrullDim Z₁ = topologicalKrullDim Z₂ := sorry

/-- An irreducible topological space is equidimensional. -/
instance instEquidimensionalSpaceOfIrreducible [IrreducibleSpace X] :
    EquidimensionalSpace X where
  topologicalKrullDim_eq := sorry

end TopologicalSpace
