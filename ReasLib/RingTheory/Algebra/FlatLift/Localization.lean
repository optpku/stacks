module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Algebra.FlatLift.Basic
public import ReasLib.RingTheory.RingHom.Syntomic.PrimesMeeting

/-!
# Flat algebra lifts versus localization
-/

@[expose] public section

universe u

namespace Algebra.NilpotentLift

/-- For a surjection of Noetherian rings with nilpotent kernel, a finite-type
flat algebra, and a submonoid meeting only syntomic primes, a flat lift exists
if and only if the localization at that submonoid admits a flat lift. -/
theorem existsFlatLift_iff_existsFlatLift_localization
    {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] [IsNoetherianRing A'] [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Flat A B]
    (hsurj : Function.Surjective (algebraMap A' A))
    (hker : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (S : Submonoid B) (hsyn : (algebraMap A B).SyntomicAtPrimesMeeting S) :
    existsFlatLift A' A B ↔ existsFlatLift A' A (Localization S) :=
  sorry

end Algebra.NilpotentLift

end
