/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-! # Relative dimension on open subspaces of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Membership in a relative-dimension-`d` open subspace implies relative
dimension `d` for the ambient morphism at that point. -/
theorem relativeDimensionAt_of_mem_pointsSet
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {U : OpenSubspace X} {d : ℕ} (h_dim : RelativeDimension (U.ι ≫ f) d)
    {x : Points X} (hx : x ∈ U.pointsSet) :
    RelativeDimensionAt f d x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
