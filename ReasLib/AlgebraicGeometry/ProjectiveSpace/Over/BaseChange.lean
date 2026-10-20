/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over

/-!
# Base change of standard projective space in a slice

This file records the canonical slice-object comparison between standard
projective spaces after changing coefficients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Base change of standard projective `n`-space along a ring homomorphism is
isomorphic, as a slice object, to standard projective `n`-space over the target. -/
theorem schemeOver_baseChange
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) :
    Nonempty
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (schemeOver R n) ≅
        schemeOver S n) := sorry

end AlgebraicGeometry.ProjectiveSpace
