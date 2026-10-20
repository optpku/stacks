/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing

/-!
# Codimension-zero points of algebraic spaces

Codimension-zero points are those at which the local ring has dimension zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The set of codimension-`0` points of an algebraic space. -/
noncomputable def codimZeroPoints {S : Scheme.{u}} (X : AlgebraicSpace S) : Set (Points X) :=
  {x | localRingDimAt x = 0}

/-- A point lies in `codimZeroPoints X` if and only if its local ring has dimension `0`. -/
theorem mem_codimZeroPoints {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} :
    x ∈ codimZeroPoints X ↔ localRingDimAt x = 0 :=
  sorry

/-- `codimZeroPoints X` is the set of points at which `localRingDimAt` equals `0`. -/
theorem codimZeroPoints_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    codimZeroPoints X = {x | localRingDimAt x = 0} :=
  sorry

/-- The points at which the local ring has dimension zero are dense in the canonical
topological space of points of an algebraic space. -/
@[stacks 0BAR]
theorem dense_setOf_localRingDimAt_eq_zero {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Dense (setOf fun x : Points X ↦ localRingDimAt x = 0) := sorry

end AlgebraicGeometry.AlgebraicSpace
