module

public import Mathlib.RingTheory.PicardGroup
public import ReasLib.RingTheory.Ideal.Localization

/-!
# Invertible modules as locally principal ideals

This leaf records local principality of invertible ideals and their realization over domains.
-/

@[expose] public section

universe u v

namespace Module.Invertible

/-- The extension of an invertible ideal to the localization at any prime is principal. -/
theorem isPrincipal_localizationAtPrime {R : Type u} [CommRing R] (I : Ideal R)
    [Module.Invertible R I] (p : PrimeSpectrum R) :
    (I.localizationAtPrime p).IsPrincipal := sorry

/-- Over a domain, an invertible module is linearly equivalent to an ideal that is principal at
every prime localization. -/
theorem exists_linearEquiv_ideal_locallyPrincipal (R : Type u) (M : Type v)
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.Invertible R M] :
    ∃ I : Ideal R, Nonempty (M ≃ₗ[R] I) ∧
      ∀ p : PrimeSpectrum R, (I.localizationAtPrime p).IsPrincipal := sorry

end Module.Invertible
