/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Jacobson
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Jacobson algebraic spaces and Jacobson spaces of points

For a decent algebraic space, the étale-local Jacobson property is equivalent to
the topological Jacobson property of the space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A decent algebraic space over a scheme is Jacobson if and only if its space of
points is Jacobson. -/
@[stacks 0BA6]
theorem isJacobson_iff_jacobsonSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] :
    IsJacobson X ↔ JacobsonSpace (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
