/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic

/-!
# Projective zero-space

The canonical structure morphism from projective zero-space over a commutative ring to the
spectrum of that ring is an isomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The canonical structure morphism from projective zero-space over a commutative ring to its
affine base is an isomorphism. -/
instance toSpec_zero_isIso (A : Type u) [CommRing A] : IsIso (toSpec A 0) := sorry

end AlgebraicGeometry.ProjectiveSpace
