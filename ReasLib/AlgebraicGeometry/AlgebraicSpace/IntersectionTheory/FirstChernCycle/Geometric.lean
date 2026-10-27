/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.AssociatedCycle

/-!
# Geometric first-Chern intersection with closed-subspace cycles

First-Chern intersection with the associated cycle of a closed subspace is
represented by the zero subspace of a regular section of the restricted
invertible module, under the expected dimension bound.

Extension beyond algebraic spaces requires corresponding cycle and Chow theories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- For a closed subspace of relative dimension at most `k + 1`, first-Chern
intersection of its degree-`k + 1` associated cycle with an invertible module
is the Chow class of the degree-`k` zero-subspace cycle of any regular section
of that module restricted to the closed subspace. -/
theorem firstChernClassCap_closedSubspace_eq_zeroSchemeCycle
    (L : X.Modules) [isInvertibleObject L] (Y : ClosedSubspace X)
    (s : ((Modules.pullback Y.ι).obj L).sections)
    [IsRegularSection ((Modules.pullback Y.ι).obj L) s] (k : ℤ)
    (hY : closedSubspaceDeltaDimension f δ Y ≤ ((k + 1 : ℤ) : EInt)) :
    firstChernClassCap f δ L k (closedSubspaceCycleInDegree f δ Y (k + 1)) =
      chowMk f δ k
        (closedSubspaceCycleInDegree f δ (ClosedSubspace.zeroSchemeRestrict Y L s) k) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
