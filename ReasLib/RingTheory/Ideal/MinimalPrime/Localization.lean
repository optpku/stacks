/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.OfDefinition

/-!
# Minimal-Prime Localizations

@stack 00EU
@stack 00EW
@stack 07FE

This leaf records the zero-dimensional, nilpotence, and field consequences of
localizing a commutative ring at a minimal prime.  The primary API is stated
for an arbitrary ideal equipped with `IsMinimalPrime`; the `minimalPrimes R`
namespace supplies the canonical indexed interface used by products over all
minimal primes.
-/

@[expose] public section

universe u v

namespace minimalPrimes

section

variable {R : Type u} [CommSemiring R]

/-- A bundled minimal prime carries its canonical primality instance. -/
@[stacks 00EU "minimal-prime subtype instance"]
instance instIsPrime (p : minimalPrimes R) : p.1.IsPrime :=
  p.2.isPrime

end

end minimalPrimes

namespace Ideal

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Localizing an ideal at one of its minimal primes identifies the radical of
the extended ideal with the extension of that prime.  This formulation is
independent of a chosen `IsLocalRing` instance on the localization model. -/
@[stacks 07FE "radical after localization at a minimal prime"]
theorem radical_map_atPrime_of_minimal (I : Ideal R) (q : PrimeSpectrum R)
    [IsLocalization.AtPrime A q.asIdeal]
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    (I.map (algebraMap R A)).radical =
      q.asIdeal.map (algebraMap R A) := sorry

/-- Localizing an ideal at one of its minimal primes produces an ideal of
definition in any localization model equipped with its local-ring structure. -/
@[stacks 07FE "minimal-prime localization as an ideal of definition"]
theorem isIdealOfDefinition_map_atPrime (I : Ideal R) (q : PrimeSpectrum R)
    [IsLocalization.AtPrime A q.asIdeal] [IsLocalRing A]
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    (I.map (algebraMap R A)).IsIdealOfDefinition := sorry

end

end Ideal

namespace IsMinimalPrime

section

variable {R : Type u} [CommSemiring R] {p : Ideal R} [p.IsPrime]

/-- Localizing at a minimal prime has Krull dimension at most zero. -/
@[stacks 00EU]
theorem krullDimLE_zero_localizationAtPrime (hp : IsMinimalPrime p) :
    Ring.KrullDimLE 0 (Localization.AtPrime p) := sorry

/-- In the localization at a minimal prime, the maximal ideal consists exactly of the
nilpotent elements. -/
@[stacks 00EU]
theorem isNilpotent_iff_mem_maximalIdeal_localizationAtPrime
    (hp : IsMinimalPrime p) {x : Localization.AtPrime p} :
    IsNilpotent x ↔ x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := sorry

end

section

variable {R : Type u} [CommRing R] [IsReduced R] {p : Ideal R} [p.IsPrime]

/-- The localization of a reduced ring at a minimal prime is a field. -/
@[stacks 00EU]
theorem isField_localizationAtPrime (hp : IsMinimalPrime p) :
    IsField (Localization.AtPrime p) := sorry

end

end IsMinimalPrime

namespace minimalPrimes

section

variable {R : Type u} [CommSemiring R]

/-- Every element of the maximal ideal of the localization at a bundled minimal prime is
nilpotent. -/
@[stacks 00EU "minimal-prime index form"]
theorem isNilpotent_of_mem_maximalIdeal_localizationAtPrime
    (p : minimalPrimes R) {x : Localization.AtPrime p.1}
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p.1)) :
    IsNilpotent x := sorry

end

section

variable {R : Type u} [CommRing R] [IsReduced R]

/-- The localization of a reduced ring at a bundled minimal prime is a field. -/
@[stacks 00EU "minimal-prime index form"]
theorem isField_localizationAtPrime (p : minimalPrimes R) :
    IsField (Localization.AtPrime p.1) := sorry

end

section

variable {R : Type u} [CommRing R] [IsReduced R]

/-- A reduced commutative ring embeds into the product of its localizations at all bundled
minimal primes. -/
@[stacks 00EW "minimal-prime localization product injection"]
theorem algebraMap_injective :
    Function.Injective (algebraMap R (∀ p : minimalPrimes R, Localization.AtPrime p.1)) := sorry

/-- In a reduced ring, the union of the minimal prime ideals is the set of zero divisors. -/
@[stacks 00EW "minimal primes and zero divisors"]
theorem iUnion_eq_setOf_exists_mul_eq_zero :
    (⋃ p : minimalPrimes R, (p.1 : Set R)) = { x | ∃ y, y ≠ 0 ∧ x * y = 0 } := sorry

end

end minimalPrimes
