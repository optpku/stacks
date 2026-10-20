/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Proper

/-!
# Topology of standard projective space

This file records basic topological properties of standard projective space.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Standard projective space over a nontrivial commutative ring is nonempty. -/
instance scheme_nonempty (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ) :
    Nonempty (scheme R n) := sorry

/-- Standard projective space over a commutative ring is compact. -/
instance scheme_compactSpace (R : Type u) [CommRing R] (n : ℕ) :
    CompactSpace (scheme R n) := sorry

end AlgebraicGeometry.ProjectiveSpace
