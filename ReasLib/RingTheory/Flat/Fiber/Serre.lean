/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.RingHom.Fiber.Quotient

/-!
# Serre Conditions Along Flat Maps

The two permanence theorems are separated by condition: one controls depth
and the other regularity in bounded codimension.  Both are phrased through
the canonical residue-field fibers.
-/

@[expose] public section

namespace Algebra.Fiber

universe u v

/-- A flat algebra over a ring satisfying `(S_k)` also satisfies `(S_k)` when every
residue-field fiber does. -/
@[stacks 0339]
theorem serreConditionS_of_flat
    {R : Type u} {S : Type v} {k : ℕ}
    [CommRing R] [CommRing S] [Algebra R S]
    [SerreConditionS R k] [IsNoetherianRing S] [Module.Flat R S]
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionS (p.asIdeal.Fiber S) k) :
    SerreConditionS S k := sorry

/-- A flat algebra over a ring satisfying `(R_k)` also satisfies `(R_k)` when every
residue-field fiber does. -/
@[stacks 033A]
theorem serreConditionR_of_flat
    {R : Type u} {S : Type v} {k : ℕ}
    [CommRing R] [CommRing S] [Algebra R S]
    [SerreConditionR R k] [IsNoetherianRing S] [Module.Flat R S]
    (hfiber : ∀ p : PrimeSpectrum R, SerreConditionR (p.asIdeal.Fiber S) k) :
    SerreConditionR S k := sorry

end Algebra.Fiber
