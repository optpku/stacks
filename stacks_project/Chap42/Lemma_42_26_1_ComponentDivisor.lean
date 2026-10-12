/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Divisor

@[expose] public section

#check (AlgebraicGeometry.CycleGroup.flatDivisorDegree :
  ∀ (n : ℤ) (r : ℕ), (n - 1) + (r : ℤ) = n + (r : ℤ) - 1)
