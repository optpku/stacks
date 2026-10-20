/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic

@[expose] public section

universe u

namespace IsLocalRing

/-- The Krull dimension of a Noetherian local ring equals the Krull dimension of the
associated graded ring of its maximal ideal. -/
theorem ringKrullDim_eq_associatedGraded
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R = ringKrullDim (Ideal.AssociatedGraded.ring (maximalIdeal R)) := sorry

end IsLocalRing
