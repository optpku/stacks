/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Irreducible

/-!
# Generic points of irreducible decent algebraic spaces

An irreducible decent algebraic space has a unique generic point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An irreducible decent algebraic space has a generic point. -/
theorem exists_mem_genericPoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] [IsIrreducible X] : ∃ x, x ∈ genericPoints X :=
  sorry

/-- An irreducible decent algebraic space has at most one generic point. -/
theorem eq_of_mem_genericPoints {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsIrreducible X] {x y : Points X}
    (hx : x ∈ genericPoints X) (hy : y ∈ genericPoints X) : x = y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
