/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.Basic
public import ReasLib.RingTheory.CompleteIntersection.OverField.Localization

@[expose] public section

/-!
# Complete-Intersection Neighbourhoods of a Prime

This leaf owns the principal-open neighbourhood predicates for global and
local complete intersections over a field, together with their comparison to
the complete-intersection property of a prime localization.
-/

universe u v

namespace IsGlobalCompleteIntersection

/-- Lemma 10.135.4, tag `00SC`: a prime has a global complete-intersection
neighbourhood when some principal open containing it is a global complete
intersection over the base field. -/
@[stacks 00SC "global complete-intersection neighbourhood of a prime"]
def nearPrime (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S]
    (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ IsGlobalCompleteIntersection k (Localization.Away g)

end IsGlobalCompleteIntersection

namespace IsLocalCompleteIntersection

/-- Lemma 10.135.8, tag `00SG`: a prime has a local complete-intersection
neighbourhood when some principal open containing it is a local complete
intersection over the base field. -/
@[stacks 00SG "local complete-intersection neighbourhood of a prime"]
def nearPrime (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S]
    (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ IsLocalCompleteIntersection k (Localization.Away g)

end IsLocalCompleteIntersection

namespace IsGlobalCompleteIntersection

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- A global complete-intersection neighbourhood is also a local
complete-intersection neighbourhood. -/
@[stacks 00SC "global complete-intersection neighbourhoods are local complete-intersection neighbourhoods"]
theorem nearPrime_isLocalCompleteIntersection {q : PrimeSpectrum S}
    (h : nearPrime k q) :
    IsLocalCompleteIntersection.nearPrime k q := sorry

end IsGlobalCompleteIntersection

namespace IsLocalCompleteIntersection

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- A local complete-intersection neighbourhood contains a smaller global
complete-intersection neighbourhood of the same prime. -/
@[stacks 00SG "local complete-intersection neighbourhoods refine to global complete-intersection neighbourhoods"]
theorem nearPrime_isGlobalCompleteIntersection {q : PrimeSpectrum S}
    (h : nearPrime k q) :
    IsGlobalCompleteIntersection.nearPrime k q := sorry

/-- The local and global complete-intersection neighbourhood conditions at a
fixed prime are equivalent. -/
@[stacks 00SG "local and global complete-intersection neighbourhoods agree at a prime"]
theorem nearPrime_iff_globalNearPrime (q : PrimeSpectrum S) :
    nearPrime k q ↔ IsGlobalCompleteIntersection.nearPrime k q := sorry

end IsLocalCompleteIntersection

namespace Algebra.IsCompleteIntersectionOver

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- Lemma 10.135.8, tag `00SG`: for a finite-type algebra over a field, the
complete-intersection property of the local ring at a prime is equivalent to
having a global complete-intersection principal-open neighbourhood. -/
@[stacks 00SG "complete intersections over a field at a prime"]
theorem atPrime_iff_globalNearPrime [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) ↔
      IsGlobalCompleteIntersection.nearPrime k q := sorry

/-- Lemma 10.135.8, tag `00SG`: for a finite-type algebra over a field, the
complete-intersection property of the local ring at a prime is equivalent to
having a local complete-intersection principal-open neighbourhood. -/
@[stacks 00SG "local complete intersections over a field at a prime"]
theorem atPrime_iff_localNearPrime [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) ↔
      IsLocalCompleteIntersection.nearPrime k q := sorry

end Algebra.IsCompleteIntersectionOver
