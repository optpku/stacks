/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Distance

@[expose] public section

#check (AlgebraicGeometry.Scheme.distanceTo :
  (Y : AlgebraicGeometry.Scheme) → [AlgebraicGeometry.IsNoetherian Y] →
    TopologicalSpace.Closeds Y → Y → ℕ∞)
