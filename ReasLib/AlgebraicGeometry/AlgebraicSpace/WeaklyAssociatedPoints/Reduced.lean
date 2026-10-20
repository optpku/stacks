/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.CodimensionZero

/-!
# Weakly associated points of reduced algebraic spaces

The weakly associated points of a reduced algebraic space are exactly its
codimension-zero points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The weakly associated points of a reduced algebraic space are exactly its
codimension-zero points. -/
@[stacks 0EN1]
theorem weakAss_eq_codimZeroPoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsReduced X] : X.weakAss = codimZeroPoints X :=
  sorry

/-- Membership in `X.weakAss` is equivalent to membership in `codimZeroPoints X`
when `X` is reduced. -/
theorem mem_weakAss_iff_mem_codimZeroPoints {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsReduced X] (x : Points X) :
    x ∈ X.weakAss ↔ x ∈ codimZeroPoints X := by
  rw [weakAss_eq_codimZeroPoints X]

end AlgebraicGeometry.AlgebraicSpace
