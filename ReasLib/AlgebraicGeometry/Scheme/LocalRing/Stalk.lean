/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Stalk local rings of schemes
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- The local ring of a scheme at a point is the stalk of its structure sheaf. -/
noncomputable abbrev localRing (X : Scheme.{u}) (x : X) : CommRingCat := X.presheaf.stalk x

end AlgebraicGeometry.Scheme
