/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Enough points of associated sites

A category fibred in groupoids over `(Sch/S)_fppf` inherits enough points
on each associated standard site `𝒳_τ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The associated `τ`-site of a category fibred in groupoids over `(Sch/S)_fppf`
has enough points. -/
instance hasEnoughPoints {S : Scheme.{u}} (X : GroupoidsOver S)
    (τ : StandardTopology) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (X.associatedTopology τ) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
