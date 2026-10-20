/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

universe u v w

namespace Module

/-- If the Matlis dual of an ideal-power-torsion module is finite over the adic completion,
then the module is Artinian. -/
theorem isArtinian_of_finite_dual_injectiveHull
    (R : Type u) (E : Type v) (N : Type w)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    [AddCommGroup N] [Module R N]
    [Module (AdicCompletion (IsLocalRing.maximalIdeal R) R) (N →ₗ[R] E)]
    [IsScalarTower R (AdicCompletion (IsLocalRing.maximalIdeal R) R) (N →ₗ[R] E)]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull)
    (hN : Module.IsIdealPowerTorsion (IsLocalRing.maximalIdeal R) N)
    [Module.Finite (AdicCompletion (IsLocalRing.maximalIdeal R) R) (N →ₗ[R] E)] :
    IsArtinian R N := sorry

end Module
