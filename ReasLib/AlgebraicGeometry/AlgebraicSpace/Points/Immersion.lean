/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Immersions on algebraic-space points

An immersion of algebraic spaces induces a topological embedding on canonical point
spaces with locally closed image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsImmersion

/-- An immersion of algebraic spaces induces a topological embedding on their canonical
point spaces. -/
theorem isEmbedding_points {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (f : Z ⟶ X) [IsImmersion f] : Topology.IsEmbedding (Points.map f) :=
  sorry

/-- The image of an immersion on canonical algebraic-space point spaces is locally closed. -/
theorem isLocallyClosed_range_points {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (f : Z ⟶ X) [IsImmersion f] : IsLocallyClosed (Set.range (Points.map f)) :=
  sorry

/-- An immersion of algebraic spaces is a closed immersion if and only if its image
on canonical point spaces is closed. -/
theorem isClosedImmersion_iff_isClosed_range_points {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (f : Z ⟶ X) [IsImmersion f] :
    IsClosedImmersion f ↔ IsClosed (Set.range (Points.map f)) :=
  sorry

/-- An immersion of algebraic spaces with closed image on canonical point spaces
is a closed immersion. -/
theorem of_isClosed_range_points {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (f : Z ⟶ X) [IsImmersion f] (h : IsClosed (Set.range (Points.map f))) :
    IsClosedImmersion f :=
  (isClosedImmersion_iff_isClosed_range_points f).mpr h

end AlgebraicGeometry.AlgebraicSpace.IsImmersion

namespace AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion

/-- A closed immersion of algebraic spaces has closed image on canonical point spaces. -/
theorem isClosed_range_points {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (f : Z ⟶ X) [IsClosedImmersion f] : IsClosed (Set.range (Points.map f)) :=
  (IsImmersion.isClosedImmersion_iff_isClosed_range_points f).mp inferInstance

end AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion
