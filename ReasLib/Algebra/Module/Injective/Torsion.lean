/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Injective.Essential
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

universe u v

/-- The submodule of an injective module consisting of the elements annihilated by some
power of a fixed ring element is injective. -/
instance Module.Injective.fPowerTorsion
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Type v) [AddCommGroup I] [Module R I] [Module.Injective R I] (f : R) :
    Module.Injective R (Submodule.torsion' R I (Submonoid.powers f)) := sorry

/-- The ideal-power torsion submodule of an injective module over a Noetherian ring is
injective. -/
instance Module.Injective.primaryComponent
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Type v) [AddCommGroup I] [Module R I] [Module.Injective R I] (J : Ideal R) :
    Module.Injective R (J.primaryComponent I) := sorry
