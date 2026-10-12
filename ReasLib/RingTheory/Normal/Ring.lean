/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Normal Rings

A commutative ring is normal if for every prime ideal, the localization at that prime is a
normal domain (i.e., an integrally closed domain).

## Main definitions

* `IsNormalRing` — a ring whose localizations at all primes are integrally closed domains.

## Main results

* Instances: `IsDomain` and `IsIntegrallyClosed` at each localization (automatic via typeclass).
* `IsNormalRing.isReduced` — a normal ring is reduced.
* Integrally closed domains are normal.
* Normal rings are integrally closed in their total quotient rings.
-/

universe u v

variable {R : Type u} [CommRing R]

/-- A commutative ring is normal if for every prime ideal `p`, the localization at `p` is a
normal domain (an integrally closed domain). The two conditions are separate fields so that
downstream code obtains them as typeclass instances without `letI` unpacking. -/
@[stacks 00GV]
class IsNormalRing (R : Type u) [CommRing R] : Prop where
  /-- Each localization at a prime is a domain. -/
  isDomain_localizationAtPrime :
    ∀ p : PrimeSpectrum R, IsDomain (Localization.AtPrime p.asIdeal)
  /-- Each localization at a prime is integrally closed. -/
  isIntegrallyClosed_localizationAtPrime :
    ∀ p : PrimeSpectrum R, IsIntegrallyClosed (Localization.AtPrime p.asIdeal)

attribute [instance] IsNormalRing.isDomain_localizationAtPrime
  IsNormalRing.isIntegrallyClosed_localizationAtPrime

namespace IsNormalRing

/-- An integrally closed domain is a normal ring. -/
@[stacks 030B]
theorem of_isIntegrallyClosed {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsNormalRing R := sorry

/-- A ring equivalence transports normality to its target, including across carrier universes. -/
@[stacks 00GV "normal rings under ring equivalence"]
theorem of_ringEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNormalRing R] (e : R ≃+* S) : IsNormalRing S := sorry

/-- Normality is invariant under a ring equivalence. -/
@[stacks 00GV "normality and ring equivalence"]
theorem iff_of_ringEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) : IsNormalRing R ↔ IsNormalRing S := sorry

/-- A normal ring is integrally closed in its total quotient ring. -/
@[stacks 034M]
theorem isIntegrallyClosed {R : Type u} [CommRing R] [IsNormalRing R] :
    IsIntegrallyClosed R := sorry

/-- Integrally closedness follows automatically from normality. -/
instance instIsIntegrallyClosed {R : Type u} [CommRing R] [IsNormalRing R] :
    IsIntegrallyClosed R := sorry

section Pi

/-- A finite product of normal rings is normal. -/
@[stacks 0CYA]
theorem pi {ι : Type u} [Finite ι] {A : ι → Type v}
    [∀ i, CommRing (A i)] [∀ i, IsNormalRing (A i)] :
    IsNormalRing (∀ i, A i) := sorry

/-- Finite products carry the canonical normal-ring instance. -/
instance instPi {ι : Type u} [Finite ι] {A : ι → Type v}
    [∀ i, CommRing (A i)] [∀ i, IsNormalRing (A i)] :
    IsNormalRing (∀ i, A i) := sorry

end Pi

end IsNormalRing

/-- An integrally closed domain is a normal ring. -/
instance [IsDomain R] [IsIntegrallyClosed R] : IsNormalRing R where
  isDomain_localizationAtPrime := fun p ↦
    IsLocalization.isDomain_of_atPrime (Localization.AtPrime p.asIdeal) p.asIdeal
  isIntegrallyClosed_localizationAtPrime := fun p ↦ by
    have : IsDomain (Localization.AtPrime p.asIdeal) :=
      IsLocalization.isDomain_of_atPrime _ p.asIdeal
    exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors

/-- A normal ring is reduced. -/
instance IsNormalRing.instIsReduced [IsNormalRing R] : IsReduced R := sorry

/-- A normal ring has domain localizations at all prime ideals. -/
instance (p : Ideal R) [p.IsPrime] [IsNormalRing R] :
    IsDomain (Localization.AtPrime p) :=
  IsNormalRing.isDomain_localizationAtPrime ⟨p, inferInstance⟩

/-- A normal ring has integrally closed localizations at all prime ideals. -/
instance (p : Ideal R) [p.IsPrime] [IsNormalRing R] :
    IsIntegrallyClosed (Localization.AtPrime p) :=
  IsNormalRing.isIntegrallyClosed_localizationAtPrime ⟨p, inferInstance⟩
