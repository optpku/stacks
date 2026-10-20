/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyOpen
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.ClosedImmersion

/-!
# Immersions on algebraic-stack points

An immersion of algebraic stacks induces a topological embedding on canonical
point spaces with locally closed image. Closed and open immersions induce closed
and open embeddings, respectively.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An immersion of algebraic stacks induces a topological embedding on their
canonical point spaces. -/
theorem isEmbedding_points {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Immersion f] :
    Topology.IsEmbedding (Points.map f) :=
  sorry

/-- The image of an immersion on canonical algebraic-stack point spaces is
locally closed. -/
theorem isLocallyClosed_range_points {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Immersion f] :
    IsLocallyClosed (Set.range (Points.map f)) :=
  sorry

/-- A closed immersion of algebraic stacks induces a closed embedding on their
canonical point spaces. -/
theorem isClosedEmbedding_points {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f] :
    Topology.IsClosedEmbedding (Points.map f) :=
  sorry

/-- An open immersion of algebraic stacks induces an open embedding on their
canonical point spaces. -/
theorem isOpenEmbedding_points {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [OpenImmersion f] :
    Topology.IsOpenEmbedding (Points.map f) :=
  sorry

/-- A closed immersion of algebraic stacks is a closed morphism. -/
instance instClosed_of_closedImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f] :
    Closed f :=
  sorry

/-- An open immersion of algebraic stacks is an open morphism. -/
instance instOpen_of_openImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [OpenImmersion f] :
    Open f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
