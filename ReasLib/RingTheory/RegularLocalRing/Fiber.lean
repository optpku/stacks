/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.KrullDimension.GoingDown
public import ReasLib.RingTheory.RingHom.Fiber.Quotient

@[expose] public section

/-!
# Regularity of closed fibers

@stack 031E

This leaf owns the two standard bridges between a closed fiber, its quotient
presentation, and regularity along a flat local homomorphism.  The statements
are formulated on `Ideal.Fiber`, rather than on a Chapter 10 presentation.
-/

universe u v

open IsLocalRing

namespace Ideal.Fiber

/-- Regularity of the quotient presentation of a closed fiber implies regularity of the canonical
closed fiber. -/
@[stacks 031E]
theorem isRegularLocalRing_of_quotient
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R]
    [IsRegularLocalRing
      (S ⧸ (maximalIdeal R).map (algebraMap R S))] :
    IsRegularLocalRing ((maximalIdeal R).Fiber S) :=
  IsRegularLocalRing.of_ringEquiv
    (Ideal.Fiber.closedQuotientAlgEquiv (R := R) (S := S)).symm.toRingEquiv

end Ideal.Fiber

namespace IsRegularLocalRing

/-- A flat local homomorphism from a regular local ring to a Noetherian local ring with regular
closed fiber has regular target. -/
@[stacks 031E]
theorem of_flat_localHom_of_regular_closedFiber
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularLocalRing R] [IsNoetherianRing S] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (hclosedFiber : IsRegularLocalRing ((maximalIdeal R).Fiber S)) :
    IsRegularLocalRing S := sorry

end IsRegularLocalRing
