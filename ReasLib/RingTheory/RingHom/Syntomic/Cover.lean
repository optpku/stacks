module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.StandardOpenCover
public import ReasLib.RingTheory.RingHom.Syntomic.AtPrime

@[expose] public section

/-!
# Relative-Global-Complete-Intersection Covers of Syntomic Maps

This leaf records finite principal-open covers on which a syntomic map is a
relative global complete intersection.  The structured cover is the primary
interface; the set-indexed form is retained for unit-ideal cover arguments.
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Syntomic

/-- A syntomic ring homomorphism admits a finite principal-open cover of its
target on whose members it is a relative global complete intersection. -/
@[stacks 00SY "principal-open relative-global-complete-intersection cover"]
theorem exists_relativeGlobalCompleteIntersectionStandardOpenCover
    {f : R →+* S} (hf : f.Syntomic) :
    ∃ U : PrimeSpectrum.StandardOpenCover (R := S),
      ∀ i : U.index,
        ((algebraMap S (Localization.Away (U.generator i))).comp f).IsRelativeGlobalCompleteIntersection := sorry

/-- A syntomic ring homomorphism admits a unit-ideal family of principal-open
relative-global-complete-intersection charts. -/
@[stacks 00SY "unit-ideal relative-global-complete-intersection cover"]
theorem exists_relativeGlobalCompleteIntersectionCover {f : R →+* S} (hf : f.Syntomic) :
    ∃ s : Set S, Ideal.span s = ⊤ ∧
      ∀ g ∈ s,
        ((algebraMap S (Localization.Away g)).comp f).IsRelativeGlobalCompleteIntersection := sorry

end Syntomic

end RingHom

namespace Algebra.Syntomic

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A syntomic algebra admits a finite principal-open cover by relative global
complete intersections over its given base ring. -/
@[stacks 00SY "syntomic algebra principal-open cover"]
theorem exists_relativeGlobalCompleteIntersectionStandardOpenCover
    (hS : (algebraMap R S).Syntomic) :
    ∃ U : PrimeSpectrum.StandardOpenCover (R := S),
      ∀ i : U.index,
        Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away (U.generator i)) := sorry

/-- A syntomic algebra admits a unit-ideal family of principal-open relative
global complete intersections over its given base ring. -/
@[stacks 00SY "syntomic algebra unit-ideal cover"]
theorem exists_relativeGlobalCompleteIntersectionCover (hS : (algebraMap R S).Syntomic) :
    ∃ s : Set S, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) := sorry

end Algebra.Syntomic
