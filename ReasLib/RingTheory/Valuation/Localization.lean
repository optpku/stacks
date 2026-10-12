/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localizations of Valuation Rings

@stack 088Y

This leaf owns the canonical domain and valuation-ring structures obtained by
localizing a valuation domain or quotienting it by a prime ideal.
-/

universe u

section

variable {A : Type u} [CommRing A] [IsDomain A]

namespace Localization

/-- Localizing a domain away from zero is again a domain. -/
theorem isDomain_of_nonzero
    (S : Submonoid A) [Fact ((0 : A) ∉ S)] :
    IsDomain (Localization S) := sorry

/-- The domain structure on a localization away from zero is canonical. -/
instance instIsDomainOfNonzero
    (S : Submonoid A) [Fact ((0 : A) ∉ S)] :
    IsDomain (Localization S) :=
  isDomain_of_nonzero S

end Localization

namespace ValuationRing

variable [ValuationRing A]

/-- Lemma 10.50.9: a localization of a valuation ring away from zero is a
valuation ring. -/
@[stacks 088Y]
theorem localization
    (S : Submonoid A) [Fact ((0 : A) ∉ S)] :
    ValuationRing (Localization S) := sorry

/-- The valuation-ring structure on a localization away from zero is
canonical. -/
@[stacks 088Y]
instance instLocalization
    (S : Submonoid A) [Fact ((0 : A) ∉ S)] :
    ValuationRing (Localization S) :=
  localization S

/-- Localization at a prime ideal of a valuation ring is a valuation ring. -/
@[stacks 088Y "localization at a prime"]
theorem localizationAtPrime
    (p : Ideal A) [p.IsPrime] :
    ValuationRing (Localization.AtPrime p) := sorry

/-- The valuation-ring structure on a prime localization is canonical. -/
@[stacks 088Y "localization-at-prime instance"]
instance instLocalizationAtPrime
    (p : Ideal A) [p.IsPrime] :
    ValuationRing (Localization.AtPrime p) :=
  localizationAtPrime p

/-- A quotient of a valuation ring by a prime ideal is a valuation ring. -/
@[stacks 088Y "quotient by a prime ideal"]
theorem quotient
    (p : Ideal A) [p.IsPrime] :
    ValuationRing (A ⧸ p) := sorry

/-- The valuation-ring structure on a prime quotient is canonical. -/
@[stacks 088Y "prime-quotient instance"]
instance instQuotient
    (p : Ideal A) [p.IsPrime] :
    ValuationRing (A ⧸ p) :=
  quotient p

end ValuationRing

end
