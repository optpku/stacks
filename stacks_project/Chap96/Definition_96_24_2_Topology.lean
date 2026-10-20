/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.AffineTopology

@[expose] public section

universe u

/- The inherited topology on affine objects for each standard topology. -/
#check (AlgebraicGeometry.GroupoidsOver.associatedAffineTopology :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
    (τ : AlgebraicGeometry.StandardTopology),
    CategoryTheory.GrothendieckTopology (AlgebraicGeometry.GroupoidsOver.Affine X))
