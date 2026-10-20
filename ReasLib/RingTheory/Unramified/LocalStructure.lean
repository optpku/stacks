module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.EssFiniteType

@[expose] public section

universe u v

namespace RingHom.FormallyUnramified

/-- An essentially finite-type, formally unramified local homomorphism of local rings is a
quotient of a localization at a prime of a standard étale algebra. -/
theorem exists_standardEtale_quotient_localizationAtPrime
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] {φ : A →+* B} [IsLocalHom φ]
    (hφ : φ.FormallyUnramified) (hft : φ.EssFiniteType) :
    ∃ (P : StandardEtalePair A) (q : Ideal P.Ring) (_ : q.IsPrime)
      (ψ : Localization.AtPrime q →+* B),
      Function.Surjective ψ ∧
        φ = ψ.comp ((algebraMap P.Ring (Localization.AtPrime q)).comp
          (algebraMap A P.Ring)) := sorry

end RingHom.FormallyUnramified
