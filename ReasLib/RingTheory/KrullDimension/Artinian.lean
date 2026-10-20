/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.HopkinsLevitzki

@[expose] public section

universe u

namespace Ring.KrullDimension

/-- A commutative ring is Artinian if and only if it is Noetherian and has
Krull dimension at most zero. -/
theorem isArtinianRing_iff_isNoetherianRing_krullDimLE_zero
    {R : Type u} [CommRing R] :
    IsArtinianRing R ↔ IsNoetherianRing R ∧ Ring.KrullDimLE 0 R :=
  _root_.isArtinianRing_iff_isNoetherianRing_krullDimLE_zero

end Ring.KrullDimension
