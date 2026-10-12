/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Depth.AssociatedPrime
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded

@[expose] public section

/-!
# Associated primes of Cohen--Macaulay modules

This leaf records the dimension identity used whenever an associated prime of a
Cohen--Macaulay module is compared with the support of the module.

@stack 0BUS
-/

open scoped ENat

universe u v

namespace Module.CohenMacaulay

/-- The quotient by an associated prime of a Cohen--Macaulay module has the full support dimension.

This is the reusable dimension-sandwich API behind the regular-sequence and
regular-local applications in Chap10. -/
@[stacks 00NT "associated-prime quotient dimension bridge"]
theorem quotientDim_eq_supportDim_of_associatedPrime
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ p) = Module.supportDim R M := sorry

/-- Lemma 10.103.7 (2): an associated prime of a Cohen--Macaulay module is a minimal point of
its support. -/
@[stacks 0BUS "(2), minimal in the support"]
theorem minimal_support_of_associatedPrime
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ associatedPrimes R M) :
    Minimal (· ∈ Module.support R M) p := sorry

/-- Lemma 10.103.7 (3): a Cohen--Macaulay module has no embedded associated primes. -/
@[stacks 0BUS "(3), no embedded associated primes"]
theorem embeddedAssociatedPrimes_eq_empty
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M] :
    _root_.embeddedAssociatedPrimes R M = ∅ := sorry

end Module.CohenMacaulay
