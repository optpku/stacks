/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.IdealPowerTorsion.Action
public import ReasLib.Algebra.Module.Injective.MaximalIdeal
public import ReasLib.Algebra.Module.MatlisDuality.Artinian

@[expose] public section

universe u v

namespace LinearMap.IsInjectiveHull

/-- For a Noetherian local ring and an injective hull of its residue field, the
maximal-ideal-adic completion acts bijectively on the hull through its linear
endomorphisms. -/
theorem completionToEnd_bijective
    (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull) :
    Function.Bijective
      (Module.IsIdealPowerTorsion.completionToEnd (IsLocalRing.maximalIdeal R)
        (maximalIdealPowerTorsion R E ι hι)) := sorry

end LinearMap.IsInjectiveHull
