/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.MatlisDuality.Completion
public import ReasLib.Algebra.Module.MatlisDuality.ArtinianCriterion
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

universe u v

namespace LinearMap.IsInjectiveHull

/-- An injective hull of the residue field over a Noetherian local ring is an
Artinian module. -/
theorem isArtinian
    (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    {ι : IsLocalRing.ResidueField R →ₗ[R] E} (hι : ι.IsInjectiveHull) :
    IsArtinian R E := sorry

end LinearMap.IsInjectiveHull
