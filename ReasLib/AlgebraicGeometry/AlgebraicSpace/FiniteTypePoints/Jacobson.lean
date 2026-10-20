/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Jacobson

/-!
# Finite-type points of decent Jacobson algebraic spaces

On a decent Jacobson algebraic space, the finite-type points are exactly the
closed points of the space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The finite-type points of a decent Jacobson algebraic space over a scheme
are exactly the closed points of its space of points. -/
@[stacks 0BA5]
theorem finiteTypePoints_eq_closedPoints {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsJacobson X] :
    finiteTypePoints X = closedPoints (Points X) :=
  sorry

/-- A point of a decent Jacobson algebraic space is a finite-type point if and only
if it is a closed point of `Points X`. -/
theorem mem_finiteTypePoints_iff_mem_closedPoints {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] [IsJacobson X] {x : Points X} :
    x ∈ finiteTypePoints X ↔ x ∈ closedPoints (Points X) := by
  rw [finiteTypePoints_eq_closedPoints]

end AlgebraicGeometry.AlgebraicSpace
