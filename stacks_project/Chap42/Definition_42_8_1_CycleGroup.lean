/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Dimension

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicCycle.dimensionSubgroup :
  {X : Scheme.{u}} → (X → ℤ) → ℤ → AddSubgroup (AlgebraicGeometry.AlgebraicCycle X ℤ))
