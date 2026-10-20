/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.NoetherianSpace
public import ReasLib.Topology.IrreducibleComponents.Equiv

/-!
# Neighbourhoods from Irreducible Components

This module provides the canonical neighbourhood obtained by removing every irreducible component
that does not contain a chosen point.
-/

@[expose] public section

universe u

open Set

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- The component neighbourhood of `x` consists of the points lying on no irreducible component
that misses `x`. This construction does not require a finite component family; finiteness enters
only when proving openness. -/
def irreducibleComponentNeighborhood (x : X) : Set X :=
  (⋃₀ {Z : Set X | Z ∈ irreducibleComponents X ∧ x ∉ Z})ᶜ

/-- A point `y` belongs to the component neighbourhood of `x` exactly when every irreducible
component containing `y` also contains `x`. -/
@[simp]
theorem mem_irreducibleComponentNeighborhood_iff (x y : X) :
    y ∈ irreducibleComponentNeighborhood x ↔
      ∀ Z : irreducibleComponents X, y ∈ (Z : Set X) → x ∈ (Z : Set X) := sorry

/-- Every point belongs to its own component neighbourhood. -/
@[simp]
theorem self_mem_irreducibleComponentNeighborhood (x : X) :
    x ∈ irreducibleComponentNeighborhood x := sorry

/-- If a space has only finitely many irreducible components, every component neighbourhood is
open. -/
theorem Set.Finite.isOpen_irreducibleComponentNeighborhood
    (hfin : (irreducibleComponents X).Finite) (x : X) :
    IsOpen (irreducibleComponentNeighborhood x) := sorry

/-- Component neighbourhoods are open in a Noetherian topological space. -/
theorem NoetherianSpace.isOpen_irreducibleComponentNeighborhood
    [NoetherianSpace X] (x : X) :
    IsOpen (irreducibleComponentNeighborhood x) := sorry

/-- The component neighbourhood of a point, bundled as an open neighbourhood in a Noetherian
space. Its underlying open set is canonical; Noetherianity supplies only the openness proof. -/
def NoetherianSpace.irreducibleComponentOpenNhdsOf [NoetherianSpace X] (x : X) :
    OpenNhdsOf x :=
  ⟨⟨irreducibleComponentNeighborhood x,
      NoetherianSpace.isOpen_irreducibleComponentNeighborhood x⟩,
    self_mem_irreducibleComponentNeighborhood x⟩

/-- The bundled component neighbourhood has `irreducibleComponentNeighborhood x` as its
underlying set. -/
@[simp]
theorem NoetherianSpace.coe_irreducibleComponentOpenNhdsOf
    [NoetherianSpace X] (x : X) :
    (NoetherianSpace.irreducibleComponentOpenNhdsOf x : Set X) =
      irreducibleComponentNeighborhood x := sorry

end TopologicalSpace
