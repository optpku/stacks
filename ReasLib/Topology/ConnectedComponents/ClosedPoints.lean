/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Spectral.Basic
public import ReasLib.Topology.ConnectedComponents.Profinite

/-!
# Closed points and connected components

The canonical map from closed points to connected components and the unique
closed-point specialization criterion.
-/

@[expose] public section

open Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

namespace ConnectedComponents

/-- The canonical composition `closedPoints X → X → ConnectedComponents X`. -/
abbrev fromClosedPoints : closedPoints X → ConnectedComponents X :=
  fun point ↦ mk (point : X)

/-- A closed point maps to the connected component of its underlying point. -/
theorem fromClosedPoints_apply (point : closedPoints X) :
    fromClosedPoints point = mk (point : X) := sorry

/-- The canonical map from closed points to connected components is continuous. -/
theorem continuous_fromClosedPoints :
    Continuous (fromClosedPoints : closedPoints X → ConnectedComponents X) := sorry

/-- The canonical map from closed points is injective exactly when distinct
closed points lie in distinct connected components. -/
theorem fromClosedPoints_injective_iff :
    Function.Injective (fromClosedPoints : closedPoints X → ConnectedComponents X) ↔
      ∀ ⦃point other : X⦄, point ∈ closedPoints X → other ∈ closedPoints X →
        point ≠ other → mk point ≠ mk other := sorry

/-- The canonical map from closed points is surjective exactly when every
connected component contains a closed point. -/
theorem fromClosedPoints_surjective_iff :
    Function.Surjective (fromClosedPoints : closedPoints X → ConnectedComponents X) ↔
      ∀ point : X, ∃ closedPoint ∈ closedPoints X, mk closedPoint = mk point := sorry

/-- A bijective canonical map from the closed points of a spectral space to its
connected components is a homeomorphism. -/
theorem isHomeomorph_fromClosedPoints [SpectralSpace X]
    (h_bijective :
      Function.Bijective (fromClosedPoints : closedPoints X → ConnectedComponents X)) :
    IsHomeomorph (fromClosedPoints : closedPoints X → ConnectedComponents X) := sorry

end ConnectedComponents

/-- Every point of a topological space specializes to a unique closed point. -/
def HasUniqueClosedPointSpecialization (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ point : X, ∃! closedPoint, closedPoint ∈ closedPoints X ∧ point ⤳ closedPoint

/-- Unique closed-point specialization is equivalent to existence and
uniqueness of closed specializations for every point. -/
theorem hasUniqueClosedPointSpecialization_iff {X : Type u} [TopologicalSpace X] :
    HasUniqueClosedPointSpecialization X ↔
      ∀ point : X, (∃ closedPoint, closedPoint ∈ closedPoints X ∧ point ⤳ closedPoint) ∧
        ∀ first second : X, first ∈ closedPoints X → second ∈ closedPoints X →
          point ⤳ first → point ⤳ second → first = second := sorry
