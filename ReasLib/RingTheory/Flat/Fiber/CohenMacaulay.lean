/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Flat.Fiber.Depth

/-!
# Cohen--Macaulayness Along Flat Local Maps

This leaf expresses the local Cohen--Macaulay criterion through the canonical
closed fiber of a flat local map.

@stack 045J
-/

@[expose] public section

open IsLocalRing

namespace Algebra.Fiber

universe u v

/-- Lemma 10.163.3, tag `045J`: for a flat local homomorphism `R → S` of
Noetherian local rings, `S` is Cohen--Macaulay if and only if both `R` and the
canonical closed fiber are Cohen--Macaulay. -/
@[stacks 045J]
theorem cohenMacaulayRing_iff_source_and_closed
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] :
    Module.CohenMacaulay S S ↔
      Module.CohenMacaulay R R ∧
        Module.CohenMacaulay ((maximalIdeal R).Fiber S) ((maximalIdeal R).Fiber S) := sorry

end Algebra.Fiber
