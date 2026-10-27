/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.OpenCover

/-- Restricting a scheme morphism to the range of an affine member of an open
cover gives a separated morphism. -/
instance isSeparated_opensRange_comp {X Y : Scheme.{u}} (𝒰 : X.OpenCover.{v})
    (f : X ⟶ Y) [∀ i, IsAffine (𝒰.X i)] (i : 𝒰.I₀) :
    IsSeparated ((𝒰.f i).opensRange.ι ≫ f) := sorry

end AlgebraicGeometry.Scheme.OpenCover

end
