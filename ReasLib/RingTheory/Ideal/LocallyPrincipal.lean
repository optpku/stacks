module

public import Mathlib.RingTheory.PicardGroup
public import ReasLib.RingTheory.Ideal.Localization

@[expose] public section

universe u

namespace Module.Invertible

/-- There exists a domain with a nonzero ideal that is principal after localization at every
prime but is not invertible as a module over the domain. -/
theorem exists_ideal_locallyPrincipal_not_invertible :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (I : Ideal A),
      I ≠ ⊥ ∧ (∀ q : PrimeSpectrum A, (I.localizationAtPrime q).IsPrincipal) ∧
        ¬ Module.Invertible A I := sorry

end Module.Invertible
