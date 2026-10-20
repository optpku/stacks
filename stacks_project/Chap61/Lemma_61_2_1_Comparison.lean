/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.ConnectedComponents.ClosedPoints

/-!
# Closed points compared with connected components

The canonical map `closedPoints X → ConnectedComponents X` and the unique
closed-point specialization criterion.
-/

@[expose] public section

open Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

#check (ConnectedComponents.fromClosedPoints : closedPoints X → ConnectedComponents X)

#check (ConnectedComponents.fromClosedPoints_apply :
  ∀ point : closedPoints X,
    ConnectedComponents.fromClosedPoints point = ConnectedComponents.mk (point : X))

#check (ConnectedComponents.continuous_fromClosedPoints :
  Continuous (ConnectedComponents.fromClosedPoints : closedPoints X → ConnectedComponents X))

#check (ConnectedComponents.fromClosedPoints_injective_iff :
  Function.Injective (ConnectedComponents.fromClosedPoints : closedPoints X → ConnectedComponents X) ↔
    ∀ ⦃point other : X⦄, point ∈ closedPoints X → other ∈ closedPoints X →
      point ≠ other → ConnectedComponents.mk point ≠ ConnectedComponents.mk other)

#check (ConnectedComponents.fromClosedPoints_surjective_iff :
  Function.Surjective (ConnectedComponents.fromClosedPoints : closedPoints X → ConnectedComponents X) ↔
    ∀ point : X, ∃ closedPoint ∈ closedPoints X,
      ConnectedComponents.mk closedPoint = ConnectedComponents.mk point)

#check (ConnectedComponents.isHomeomorph_fromClosedPoints :
  ∀ [SpectralSpace X],
    Function.Bijective (ConnectedComponents.fromClosedPoints : closedPoints X → ConnectedComponents X) →
      IsHomeomorph (ConnectedComponents.fromClosedPoints : closedPoints X → ConnectedComponents X))

#check (HasUniqueClosedPointSpecialization X : Prop)

#check (hasUniqueClosedPointSpecialization_iff :
  HasUniqueClosedPointSpecialization X ↔
    ∀ point : X, (∃ closedPoint, closedPoint ∈ closedPoints X ∧ point ⤳ closedPoint) ∧
      ∀ first second : X, first ∈ closedPoints X → second ∈ closedPoints X →
        point ⤳ first → point ⤳ second → first = second)
