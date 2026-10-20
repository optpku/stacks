module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Stability
public import ReasLib.RingTheory.RingHom.AtPrime

@[expose] public section

/-!
# Relative Global Complete Intersections of Ring Homomorphisms

This leaf presents `Algebra.IsRelativeGlobalCompleteIntersection` at the
intrinsic `RingHom` layer.  The pointwise form records the existence of a
principal-open relative-global-complete-intersection neighbourhood.

@stack 00SP
@stack 00SY
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism is a relative global complete intersection when its
canonical algebra structure has that property. -/
@[stacks 00SP "relative global complete intersection ring homomorphism",
  algebraize RingHom.IsRelativeGlobalCompleteIntersection.toAlgebra]
def IsRelativeGlobalCompleteIntersection (f : R →+* S) : Prop :=
  @Algebra.IsRelativeGlobalCompleteIntersection R S _ _ f.toAlgebra

namespace IsRelativeGlobalCompleteIntersection

/-- The ring-hom relative-global-complete-intersection predicate is its
canonical algebra predicate after installing `f.toAlgebra`. -/
theorem toAlgebra {f : R →+* S} (hf : f.IsRelativeGlobalCompleteIntersection) :
    @Algebra.IsRelativeGlobalCompleteIntersection R S _ _ f.toAlgebra := sorry

/-- The intrinsic ring-hom predicate on an algebra map is equivalent to the
ambient algebra-level relative-global-complete-intersection predicate. -/
@[stacks 00SP "relative global complete intersection algebra maps"]
theorem algebraMap_iff [Algebra R S] :
    (algebraMap R S).IsRelativeGlobalCompleteIntersection ↔
      Algebra.IsRelativeGlobalCompleteIntersection R S := sorry

end IsRelativeGlobalCompleteIntersection

namespace IsRelativeGlobalCompleteIntersection

/-- A ring homomorphism is relative globally a complete intersection at a target
prime when it is a relative global complete intersection on some principal-open
neighbourhood of that prime. -/
@[stacks 00SY "relative global complete intersection at a prime"]
def AtPrime (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  RingHom.AtPrime (fun g ↦ g.IsRelativeGlobalCompleteIntersection) f q

namespace AtPrime

/-- Relative global complete intersection at a target prime is the existence
of such a restriction to a principal-open neighborhood. -/
theorem iff_exists_away (f : R →+* S) (q : PrimeSpectrum S) :
    RingHom.IsRelativeGlobalCompleteIntersection.AtPrime f q ↔
      ∃ g : S, g ∉ q.asIdeal ∧
        ((algebraMap S (Localization.Away g)).comp f).IsRelativeGlobalCompleteIntersection := sorry

end AtPrime

/-- A relative-global-complete-intersection ring homomorphism has such a
principal-open neighbourhood at every target prime. -/
theorem atPrime {f : R →+* S} (hf : f.IsRelativeGlobalCompleteIntersection)
    (q : PrimeSpectrum S) : AtPrime f q := sorry

end IsRelativeGlobalCompleteIntersection

end RingHom
