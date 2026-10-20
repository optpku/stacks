/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flat.Fiber.Serre
public import ReasLib.RingTheory.Normal.Ring

/-!
# Normality Along Flat Maps

Normality ascends through a flat map under normality of the base and all
canonical residue-field fibers.

@stack 0C22
-/

@[expose] public section

namespace Algebra.Fiber

universe u v

/-- Lemma 10.163.8, tag `0C22`: a flat algebra over a normal Noetherian ring
is normal if all of its residue-field fibers are normal. -/
@[stacks 0C22]
theorem isNormalRing_of_flat
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] [IsNormalRing R]
    (hfiber : ∀ p : PrimeSpectrum R, IsNormalRing (p.asIdeal.Fiber S)) :
    IsNormalRing S := sorry

end Algebra.Fiber
